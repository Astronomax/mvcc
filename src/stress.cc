#include "core/fiber.h"
#include "core/memory.h"
#include "trivia/util.h"

#include "box.h"
#include "memtx_tx.h"
#include "tuple.h"
#include "txn.h"
#include "wal.h"

#include <vector>
#include <variant>
#include <random>
#include <algorithm>
#include <iostream>
#include <map>

#include <unordered_map>

#define MAX_SPACES 1
#define MAX_INDEXES 7
#define MAX_TXNS 100
#define MAX_STMTS 50
//#define MAX_TXNS 5
//#define MAX_STMTS 7
#define MAX_KEY 30

static std::random_device rd;
int seed = rd();
static std::mt19937 gen(seed);

int
txn_commit_wal_error()
{
	struct txn *txn = in_txn();

	if (!txn)
		return 0;
	if (txn_check_can_complete(txn) != 0)
		return -1;

    struct journal_entry *req;
    txn->fiber = fiber();
	if (txn_prepare(txn) != 0)
        goto rollback;
	assert(!txn_has_flag(txn, TXN_IS_DONE));
	assert(in_txn() == txn);

	req = txn_journal_entry_new(txn);
    req->errinj_wal_io = true;

    fiber_set_txn(fiber(), NULL);
	journal_write_submit(req);

	while (!req->is_complete)
		fiber_yield();
	assert(req->res < 0);

	free(req);

rollback:
    /* rollback on WAL error */
	if (!txn_has_flag(txn, TXN_IS_DONE)) {
		fiber_set_txn(fiber(), txn);
		txn_rollback(txn);
	} else {
		assert(in_txn() == NULL);
	}
	txn_free(txn);
	return -1;
}


struct stmt_exec_result {
    int rc;
    std::variant<struct tuple *, std::vector<struct tuple *>> result;
};

struct txn_exec_result {
    int64_t psn;
    bool in_read_view;
    std::vector<stmt_exec_result> stmt_exec_results;
};

struct insert_stmt {
    struct memtx_space *space;
    struct tuple *tuple;
};

struct replace_stmt {
    struct memtx_space *space;
    struct tuple *tuple;
};

struct delete_stmt {
    struct memtx_space *space;
    uint32_t index_id;
    int key;
};

struct get_stmt {
    struct memtx_space *space;
    uint32_t index_id;
    int key;
};

struct select_stmt {
    struct memtx_space *space;
    uint32_t index_id;
    enum iterator_type type;
    struct key_or_null key;
};

typedef std::variant<
            insert_stmt,
            replace_stmt,
            delete_stmt,
            get_stmt,
            select_stmt> data_access_txn_stmt;

struct data_access_txn {
    std::vector<data_access_txn_stmt> stmts;
};

struct index_build_txn {
    struct memtx_space *space;
};

struct txn_to_exec {
    int64_t id;
    std::variant<struct data_access_txn, struct index_build_txn> txn;
};

static struct tuple *
create_tuple(const std::vector<int>& values)
{
    struct tuple *tuple = new struct tuple();
    tuple->flags = 0;
    tuple->data = values;
    return tuple;
}

static bool randomized_exec;
//static const struct txn_to_exec *current_txn_to_exec;

std::unordered_map<struct fiber *, int> txn_id;

CFORMAT(printf, 1, 2)
static void
stress_log(const char *format, ...)
{
	va_list ap;
	va_start(ap, format);
	printf("TX %ld: ", txn_id[fiber()]);
    vprintf(format, ap);
	va_end(ap);
    printf("\n");
    fflush(stdout);
}

void
random_yield()
{
    if (!randomized_exec)
        return;

    if (gen() % 2 == 0) {
        stress_log("sleep");
        fiber_sleep(0);
    }
}

bool
random_rollback()
{
    if (!randomized_exec)
        return false;

    if (gen() % 3 == 0) {
        stress_log("rolled back");
        box_txn_rollback();
        return true;
    } 
    if (gen() % 3 == 0) {
        stress_log("commit (rolled back with WAL error)");
        txn_commit_wal_error();
        return true;
    }
    return false;
}

void log_exec_stmt(const data_access_txn_stmt &stmt, const struct stmt_exec_result &result)
{
    if (std::holds_alternative<insert_stmt>(stmt)) {
        auto &s = std::get<insert_stmt>(stmt);
        stress_log("INSERT(space=%p, tuple=%s)", s.space, tuple_str(s.tuple).c_str());
        stress_log("result: rc=%d", result.rc);
    }
    else if (std::holds_alternative<replace_stmt>(stmt)) {
        auto &s = std::get<replace_stmt>(stmt);
        stress_log("REPLACE(space=%p, tuple=%s)", s.space, tuple_str(s.tuple).c_str());
        stress_log("result: rc=%d", result.rc);
    }
    else if (std::holds_alternative<delete_stmt>(stmt)) {
        auto &s = std::get<delete_stmt>(stmt);
        stress_log("REPLACE(space=%p, index=%u, key=%d)", s.space, s.index_id, s.key);
        auto deleted = std::get<struct tuple *>(result.result);
        stress_log("result: rc=%d, deleted=%s", result.rc, tuple_str(deleted).c_str());
    }
    else if (std::holds_alternative<get_stmt>(stmt)) {
        auto &s = std::get<get_stmt>(stmt);
        stress_log("GET(space=%p, index=%u, key=%d)", s.space, s.index_id, s.key);
        auto got = std::get<struct tuple *>(result.result);
        stress_log("result: rc=%d, got=%s", result.rc, tuple_str(got).c_str());
    }
    else if (std::holds_alternative<select_stmt>(stmt)) {
        auto &s = std::get<select_stmt>(stmt);
        stress_log("SELECT(space=%p, index=%u)", s.space, s.index_id);
        auto &selected = std::get<std::vector<struct tuple *>>(result.result);
        std::string got_str = "{}";
        if (!selected.empty()) {
            got_str = std::accumulate(selected.begin() + 1, selected.end(),
                "{" + tuple_str(selected[0]),
                [](const std::string& pref, struct tuple *tuple) {
                    return pref + ", " + tuple_str(tuple);
                }) + "}";
        }
        stress_log("result: got=%s", got_str.c_str());
    }
}

static void
assert_rc_equals(int actual, int expected)
{
    if (actual != expected) {
        fprintf(stderr, "Verification failed: expected %d, got %d\n",
            expected, actual);
        abort();
    }
}

static void
assert_tuple_equals(struct tuple *actual, struct tuple *expected)
{
    bool equals = (!expected && !actual) || (expected && actual &&
        expected->data == actual->data);

    if (!equals) {
        fprintf(stderr, "Verification failed: expected %s, got %s\n",
            tuple_str(expected).c_str(), tuple_str(actual).c_str());
        abort();
    }
}

static void
exec_stmt(const data_access_txn_stmt &stmt,
    struct stmt_exec_result *actual,
    struct stmt_exec_result *expected = NULL)
{
    int id = txn_id[fiber()];

    if (expected != NULL && expected->rc != 0)
        return;

    if (std::holds_alternative<insert_stmt>(stmt)) {
        auto &s = std::get<insert_stmt>(stmt);
        actual->rc = box_insert(s.space, s.tuple);
        log_exec_stmt(stmt, *actual);

        if (expected != NULL)
            assert_rc_equals(actual->rc, expected->rc);
    } else if (std::holds_alternative<replace_stmt>(stmt)) {
        auto &s = std::get<replace_stmt>(stmt);
        actual->rc = box_replace(s.space, s.tuple);
        log_exec_stmt(stmt, *actual);

        if (expected != NULL)
            assert_rc_equals(actual->rc, expected->rc);
    } else if (std::holds_alternative<delete_stmt>(stmt)) {
        auto &s = std::get<delete_stmt>(stmt);
        actual->result = (struct tuple *)NULL;
        auto deleted_actual = &std::get<struct tuple *>(actual->result);
        actual->rc = box_delete(s.space, s.index_id, s.key, deleted_actual);
        log_exec_stmt(stmt, *actual);

        if (expected != NULL) {
            assert_rc_equals(actual->rc, expected->rc);
            if (actual->rc == 0) {
                auto deleted_expected = &std::get<struct tuple *>(expected->result);
                assert_tuple_equals(*deleted_actual, *deleted_expected);
            }
        }
    } else if (std::holds_alternative<get_stmt>(stmt)) {
        auto &s = std::get<get_stmt>(stmt);
        actual->result = (struct tuple *)NULL;
        auto got_actual = &std::get<struct tuple *>(actual->result);
        actual->rc = box_get(s.space, s.index_id, s.key, got_actual);
        log_exec_stmt(stmt, *actual);

        if (expected != NULL) {
            assert_rc_equals(actual->rc, expected->rc);
            if (actual->rc == 0) {
                auto got_expected = &std::get<struct tuple *>(expected->result);
                assert_tuple_equals(*got_actual, *got_expected);
            }
        }
    } else if (std::holds_alternative<select_stmt>(stmt)) {
        auto &s = std::get<select_stmt>(stmt);
        struct iterator *it =
            index_create_iterator(s.space->index[s.index_id], s.type, s.key);
        int rc, i = 0;
        struct tuple *tuple;
        actual->result = std::vector<struct tuple *>({});
        auto &selected_actual =
            std::get<std::vector<struct tuple *>>(actual->result);

        stress_log("SELECT(space=%p, index=%u)", s.space, s.index_id);
        while ((rc = iterator_next_internal(it, &tuple)) == 0 && tuple != NULL) {
            stress_log("SELECT(space=%p, index=%u)", s.space, s.index_id);
            selected_actual.push_back(tuple);
            stress_log("result(%d): got=%s", i, tuple_str(tuple).c_str());

            if (expected != NULL) {
                auto &selected_expected =
                    std::get<std::vector<struct tuple *>>(expected->result);
                assert_tuple_equals(selected_actual[i], selected_expected[i]);
            }

            random_yield();
            ++i;
        }
        log_exec_stmt(stmt, *actual);
    }
}

static int
exec_txn(const txn_to_exec &txn_to_exec,
    struct txn_exec_result *actual,
    struct txn_exec_result *expected = NULL)
{
    assert(in_txn() == NULL);
    //assert(current_txn_to_exec == NULL);
    //current_txn_to_exec = &txn_to_exec;

    txn_id[fiber()] = txn_to_exec.id;

    actual->in_read_view = false;
    actual->psn = 0;

    if (std::holds_alternative<struct data_access_txn>(txn_to_exec.txn)) {
        const auto &txn = std::get<struct data_access_txn>(txn_to_exec.txn);

        box_txn_begin();
        actual->stmt_exec_results.resize(txn.stmts.size());
        for (int i = 0; i < txn.stmts.size(); i++) {
            const auto &stmt = txn.stmts[i];
            auto stmt_result_actual = &actual->stmt_exec_results[i];
            struct stmt_exec_result *stmt_result_expected =
                expected ? &expected->stmt_exec_results[i] : NULL;
            random_yield();
            exec_stmt(stmt, stmt_result_actual, stmt_result_expected);
        }
        if (random_rollback())
            return -1; // rolled back

        if (txn_has_flag(in_txn(), TXN_IS_CONFLICTED))
            return -1; // conflicted
 
        actual->in_read_view = (in_txn()->status == TXN_IN_READ_VIEW);
        actual->psn = actual->in_read_view ? in_txn()->rv_psn : txn_next_psn;

        stress_log("committed");
        if (box_txn_commit() != 0) {
            return -1;
        }
    }
    else if (std::holds_alternative<struct index_build_txn>(txn_to_exec.txn)) {
        const auto &txn = std::get<struct index_build_txn>(txn_to_exec.txn);

        stress_log("sleep");
        double timeout = (double)(gen() % 1000) / (double)1000.0;
        fiber_sleep(timeout);

        stress_log("build index space=%p", txn.space);
        if (box_space_build_index(txn.space) != 0) {
            stress_log("rolled back");
            return -1; // rolled back
        }
        stress_log("committed");
        // nothing expected

        actual->in_read_view = true;
        actual->psn = txn_next_psn;
    }
    return 0;
}

static void
exec_serial(
    const std::vector<std::pair<struct txn_to_exec, struct txn_exec_result>> &txns_results,
    const std::vector<struct memtx_space*> &spaces)
{
    std::cout << std::endl << std::endl << std::endl << "START serialized execution" << std::endl;

    assert(in_txn() == NULL);

    auto sorted_txns = txns_results;
    std::sort(sorted_txns.begin(), sorted_txns.end(), 
        [](const auto &a, const auto &b) {
            if (a.second.psn != b.second.psn)
                return a.second.psn < b.second.psn;
            return a.second.in_read_view && !b.second.in_read_view;
        });

    randomized_exec = false;

    for (auto &[txn_to_exec, result] : sorted_txns) {
        struct txn_exec_result serial_result;

        if (result.in_read_view)
            printf("rv_psn=%ld\n", result.psn);
        else
            printf("psn=%ld\n", result.psn);

        exec_txn(txn_to_exec, &serial_result, &result);

        if (std::holds_alternative<struct index_build_txn>(txn_to_exec.txn)) {
            const auto &txn = std::get<struct index_build_txn>(txn_to_exec.txn);
            uint32_t index_id[2] = {0, txn.space->index_count - 1};
            std::vector<struct tuple *> select_result[2];
            for (int i = 0; i < 2; i++) {
                box_txn_begin();
                struct iterator *it = index_create_iterator(txn.space->index[index_id[i]], ITER_ALL, key_or_null{0, true});
                int rc;
                struct tuple *tuple;
                while ((rc = iterator_next_internal(it, &tuple)) == 0 && tuple != NULL)
                    select_result[i].push_back(tuple);
                box_txn_commit();
            }
            std::sort(select_result[1].begin(), select_result[1].end(),
                [](auto &a, auto &b) { return a->data[0] < b->data[0]; });
            if (select_result[0].size() != select_result[1].size()) {
                fprintf(stderr, "Verification failed\n");
                fflush(stderr);
                abort();
            } else {
                for (int i = 0; i < select_result[0].size(); i++) {
                    if (select_result[0][i] != select_result[1][i]) {
                        fprintf(stderr, "Verification failed\n");
                        fflush(stderr);
                        abort();
                    }
                }
            }
        }

        assert(in_txn() == NULL);
    }
}

static int
txn_fiber_f(va_list ap)
{
    struct txn_to_exec *txn = va_arg(ap, struct txn_to_exec *);
    struct txn_exec_result *result = va_arg(ap, struct txn_exec_result *);
    return exec_txn(*txn, result);
}

uint32_t
gen_index_id(struct memtx_space *space)
{
    while (true) {
        uint32_t index_id = gen() % space->index_count;
        assert(space->index[index_id] != NULL);
        if (space->index[index_id]->built)
            return index_id;
    }
    return 0;
}

int
stress_f(va_list ap)
{
    int n_spaces = 1 + gen() % MAX_SPACES;
    std::vector<struct memtx_space*> spaces(n_spaces);
    std::vector<struct memtx_space*> serial_spaces(spaces.size());
    std::unordered_map<struct memtx_space *, int> index_count;
    for (int i = 0; i < n_spaces; i++) {
        spaces[i] = memtx_space_new(1 + gen() % MAX_INDEXES);
        serial_spaces[i] = memtx_space_new(spaces[i]->index_count);
        index_count[spaces[i]] = spaces[i]->index_count;
    }   

    int n_txns = 1 + gen() % MAX_TXNS;
    std::vector<std::pair<struct txn_to_exec, struct txn_exec_result>> txns(n_txns);

    for (int i = 0; i < n_txns; i++) {
        bool build_index = (gen() % 5 == 0); // 20% chance to build index
        struct memtx_space *space_to_build_index = spaces[gen() % n_spaces];

        txns[i].first.id = i;

        if (build_index && index_count[space_to_build_index] < MAX_INDEXES) {
            index_count[space_to_build_index]++;
            struct index_build_txn txn;
            txn.space = space_to_build_index;
            txns[i].first.txn = txn;
        } else {
            bool is_read_only = (gen() % 2 == 0); // 50% chance to read only
            int n_stmts = 1 + gen() % MAX_STMTS;
            
            struct data_access_txn txn;
            txn.stmts.resize(n_stmts);
            
            for (int j = 0; j < n_stmts; j++) {
                struct memtx_space *space = spaces[gen() % n_spaces];
                uint32_t field_count = MAX_INDEXES;//space->index_count;
                std::vector<int> values(field_count);
                for (uint32_t k = 0; k < field_count; k++)
                    values[k] = gen() % MAX_KEY;
                
                int type;
                if (is_read_only) {
                    static int read_only_types[2] = { 3 /* GET*/, 4 /* SELECT*/ };
                    type = read_only_types[gen() % 2];
                } else {
                    type = gen() % 5;
                }

                switch (type) {
                case 0: { // INSERT
                    struct tuple *tuple = create_tuple(values);
                    txn.stmts[j] = insert_stmt{space, tuple};
                    break;
                }
                case 1: { // REPLACE
                    struct tuple *tuple = create_tuple(values);
                    txn.stmts[j] = replace_stmt{space, tuple};
                    break;
                }
                case 2: { // DELETE
                    uint32_t index_id = gen_index_id(space);
                    int key = gen() % MAX_KEY;
                    txn.stmts[j] = delete_stmt{space, index_id, key};
                    break;
                }
                case 3: { // GET
                    uint32_t index_id = gen_index_id(space);
                    int key = gen() % MAX_KEY;
                    txn.stmts[j] = get_stmt{space, index_id, key};
                    break;
                }
                case 4: { // SELECT
                    uint32_t index_id = gen_index_id(space);
                    enum iterator_type types[3] = {ITER_ALL, ITER_GE, ITER_GT};
                    bool is_null[3] = { true, false, false };
                    int type_idx = gen() % 3;

                    txn.stmts[j] = select_stmt{space, index_id, types[type_idx],
                        key_or_null{(int)gen() % MAX_KEY, is_null[type_idx]}};
                    break;
                }
                }
            }
            txns[i].first.txn = txn;
        }
    }

    std::vector<std::pair<struct txn_to_exec, struct txn_exec_result>> serial_txns;
    //serial_txns.reserve(n_txns);

    std::vector<struct fiber*> fibers;
    //fibers.reserve(n_txns);

    randomized_exec = true;

    for (int i = 0; i < n_txns; i++) {
        struct fiber *f = fiber_new(txn_fiber_f);
        fiber_set_joinable(f, true);
        fiber_start(f, &txns[i].first, &txns[i].second);
        fibers.push_back(f);
    }

    for (int i = 0; i < n_txns; i++)
        if (fiber_join(fibers[i]) == 0)
            serial_txns.push_back(txns[i]);

    for (auto &[txn_to_exec, _] : serial_txns) {
        if (std::holds_alternative<struct data_access_txn>(txn_to_exec.txn)) {
            auto &txn = std::get<struct data_access_txn>(txn_to_exec.txn);
            for (auto &stmt : txn.stmts) {
                if (std::holds_alternative<insert_stmt>(stmt)) {
                    auto &s = std::get<insert_stmt>(stmt);
                    size_t space_idx = std::find(spaces.begin(), spaces.end(), s.space) - spaces.begin();
                    s.space = serial_spaces[space_idx];
                    s.tuple = create_tuple(s.tuple->data);
                }
                else if (std::holds_alternative<replace_stmt>(stmt)) {
                    auto &s = std::get<replace_stmt>(stmt);
                    size_t space_idx = std::find(spaces.begin(), spaces.end(), s.space) - spaces.begin();
                    s.space = serial_spaces[space_idx];
                    s.tuple = create_tuple(s.tuple->data);
                }
                else if (std::holds_alternative<delete_stmt>(stmt)) {
                    auto &s = std::get<delete_stmt>(stmt);
                    size_t space_idx = std::find(spaces.begin(), spaces.end(), s.space) - spaces.begin();
                    s.space = serial_spaces[space_idx];
                }
                else if (std::holds_alternative<get_stmt>(stmt)) {
                    auto &s = std::get<get_stmt>(stmt);
                    size_t space_idx = std::find(spaces.begin(), spaces.end(), s.space) - spaces.begin();
                    s.space = serial_spaces[space_idx];
                }
                else if (std::holds_alternative<select_stmt>(stmt)) {
                    auto &s = std::get<select_stmt>(stmt);
                    size_t space_idx = std::find(spaces.begin(), spaces.end(), s.space) - spaces.begin();
                    s.space = serial_spaces[space_idx];
                }
            }
        }
        else if (std::holds_alternative<struct index_build_txn>(txn_to_exec.txn)) {
            auto &txn = std::get<struct index_build_txn>(txn_to_exec.txn);
            size_t space_idx = std::find(spaces.begin(), spaces.end(), txn.space) - spaces.begin();
            txn.space = serial_spaces[space_idx];
        }
    }

    exec_serial(serial_txns, serial_spaces);
    return 0;
}

int main() {
    std::cout << seed << std::endl;
    memory_init();
    fiber_init(fiber_c_invoke);
    memtx_tx_manager_init();
    wal_init();

    cord()->loop = ev_loop_new(EVFLAG_AUTO | EVFLAG_ALLOCFD);
    if (cord()->loop == NULL) {
        fprintf(stderr, "Failed to allocate %u bytes in %s for %s\n", 0, "ev_loop_new", "ev_loop");
        memory_free();
        return -1;
    }

    struct fiber *stress_fiber = fiber_new(stress_f);
    fiber_wakeup(stress_fiber);
    ev_run(cord()->loop, 0);

    memtx_tx_manager_free();
    memory_free();
    return 0;
}
