#include "core/fiber.h"
#include "core/memory.h"
#include "trivia/util.h"

#include "box.h"
#include "memtx_tx.h"
#include "tuple.h"
#include "txn.h"

#include <vector>
#include <variant>
#include <random>
#include <algorithm>
#include <iostream>
#include <map>

#define MAX_SPACES 1
#define MAX_INDEXES 3
#define MAX_TXNS 10000
#define MAX_STMTS 10
#define MAX_KEY 10

static std::random_device rd;
int seed = rd();
static std::mt19937 gen(seed);

struct txn_info {
    int64_t psn;
    int64_t rv_psn;
    bool in_read_view;
    bool rollback;
    bool conflicted;
};

struct insert_stmt {
    struct memtx_space *space;
    struct tuple *tuple;
    int rc;
};

struct replace_stmt {
    struct memtx_space *space;
    struct tuple *tuple;
    int rc;
};

struct delete_stmt {
    struct memtx_space *space;
    uint32_t index_id;
    int key;
    int rc;
    struct tuple *result;
};

struct get_stmt {
    struct memtx_space *space;
    uint32_t index_id;
    int key;
    int rc;
    struct tuple *result;
};

typedef std::variant<insert_stmt, replace_stmt, delete_stmt, get_stmt> stress_txn_stmt;

struct stress_txn {
    int64_t id;
    txn_info info;
    std::vector<stress_txn_stmt> stmts;
};

static void
print_tuple(struct tuple *tuple)
{
    if (tuple == NULL) {
        std::cout << "NULL";
        return;
    }
    char *str = tuple_str(tuple);
    std::cout << str;
    free(str);
}

static struct tuple *
create_tuple(struct memtx_space *space, const std::vector<int>& values)
{
    struct tuple *tuple = new struct tuple();
    tuple->flags = 0;
    tuple->data = values;
    return tuple;
}

static void
execute_statement(stress_txn_stmt &stmt)
{
    if (std::holds_alternative<insert_stmt>(stmt)) {
        auto &s = std::get<insert_stmt>(stmt);
        std::cout << "INSERT space=" << s.space << " tuple=";
        print_tuple(s.tuple);
        s.rc = box_insert(s.space, s.tuple);
    } else if (std::holds_alternative<replace_stmt>(stmt)) {
        auto &s = std::get<replace_stmt>(stmt);
        std::cout << "REPLACE space=" << s.space << " tuple=";
        print_tuple(s.tuple);
        s.rc = box_replace(s.space, s.tuple);
    } else if (std::holds_alternative<delete_stmt>(stmt)) {
        auto &s = std::get<delete_stmt>(stmt);
        std::cout << "DELETE space=" << s.space << " index=" << s.index_id 
                  << " key=" << s.key;
        s.rc = box_delete(s.space, s.index_id, s.key, &s.result);
        std::cout << " rc=" << s.rc << " result=";
        print_tuple(s.result);
    } else if (std::holds_alternative<get_stmt>(stmt)) {
        auto &s = std::get<get_stmt>(stmt);
        std::cout << "GET space=" << s.space << " index=" << s.index_id 
                  << " key=" << s.key;
        s.rc = box_get(s.space, s.index_id, s.key, &s.result);
        std::cout << " rc=" << s.rc << " result=";
        print_tuple(s.result);
    }
}

static void
verify_statement(const stress_txn_stmt &stmt)
{
    if (std::holds_alternative<insert_stmt>(stmt)) {
        const auto &s = std::get<insert_stmt>(stmt);
        std::cout << "INSERT space=" << s.space << " tuple=";
        print_tuple(s.tuple);
        std::cout << " rc=" << s.rc << std::endl;
    } else if (std::holds_alternative<replace_stmt>(stmt)) {
        const auto &s = std::get<replace_stmt>(stmt);
        std::cout << "REPLACE space=" << s.space << " tuple=";
        print_tuple(s.tuple);
        std::cout << " rc=" << s.rc << std::endl;
    } else if (std::holds_alternative<delete_stmt>(stmt)) {
        const auto &s = std::get<delete_stmt>(stmt);
        std::cout << "DELETE space=" << s.space << " index=" << s.index_id 
                  << " key=" << s.key << " rc=" << s.rc << " result=";
        print_tuple(s.result);
        std::cout << std::endl;
    } else if (std::holds_alternative<get_stmt>(stmt)) {
        const auto &s = std::get<get_stmt>(stmt);
        std::cout << "GET space=" << s.space << " index=" << s.index_id 
                  << " key=" << s.key << " rc=" << s.rc << " result=";
        print_tuple(s.result);
        std::cout << std::endl;
    }
}

int
txn_commit_wal_error()
{
	struct txn *txn = in_txn();
	if (!txn)
		return 0;
	if (txn_check_can_complete(txn) != 0)
		return -1;

	txn_prepare(txn);
	assert(!txn_has_flag(txn, TXN_IS_DONE));
	assert(in_txn() == txn);
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

static txn_info
execute_transaction(stress_txn &txn)
{
    assert(in_txn() == NULL);

    box_txn_begin();
    txn_info info = {0};
    
    for (auto &stmt : txn.stmts) {
        if (gen() % 2 == 0) {
            std::cout << "TX" << txn.id << ": sleep" << std::endl;
            fiber_sleep(0);
        }
        std::cout << "TX" << txn.id << ": ";
        execute_statement(stmt);
        std::cout << std::endl;
    }

    info.rollback = txn.info.rollback;

    if (txn.info.rollback) {
        if (gen() % 3 == 0) {
            std::cout << "TX" << txn.id << ": rollback" << std::endl;
            box_txn_rollback();
        } else {
            std::cout << "TX" << txn.id << ": commit (failed with WAL error)" << std::endl;
            txn_commit_wal_error();
        }
    } else {
        struct txn *txn_ = in_txn();
        enum txn_status status = txn_->status;
        std::cout << "TX" << txn.id << ": commit, rc = ";
        std::cout << box_txn_commit() << std::endl;

        info.in_read_view = (status == TXN_IN_READ_VIEW);

        if (info.in_read_view) {
            info.rv_psn = txn_->rv_psn;
            std::cout << "rv_psn=" << info.rv_psn << std::endl;
        } else {
            info.psn = txn_->psn;
            std::cout << "psn=" << info.psn << std::endl;
        }
        info.conflicted = txn_has_flag(txn_, TXN_IS_CONFLICTED);
        std::cout << "conflicted = " << (info.conflicted ? "true" : "false") << std::endl;
    }
    
    return info;
}

void verify_results(struct tuple *expected, struct tuple *actual) {
    if (!expected && actual) {
        std::cerr << "Verification failed: expected NULL, got ";
        print_tuple(actual);
        std::cerr << std::endl;
        abort();
    } else if (expected && !actual) {
        std::cerr << "Verification failed: expected ";
        print_tuple(expected);
        std::cerr << ", got NULL" << std::endl;
        abort();
    } else if (expected && actual && expected->data != actual->data) {
        std::cerr << "Verification failed: expected ";
        print_tuple(expected);
        std::cerr << ", got ";
        print_tuple(actual);
        std::cerr << std::endl;
        abort();
    }
}

static void
execute_serial_verification(const std::vector<std::pair<txn_info, stress_txn>> &txns, 
                           const std::vector<struct memtx_space*> &spaces)
{
    std::cout << std::endl << std::endl << std::endl << "START serialized execution" << std::endl;

    assert(in_txn() == NULL);

    std::vector<struct memtx_space*> verify_spaces(spaces.size());
    for (size_t i = 0; i < spaces.size(); i++) {
        verify_spaces[i] = memtx_space_new(spaces[i]->index_count);
    }

    std::vector<std::pair<txn_info, stress_txn>> sorted_txns = txns;
    std::sort(sorted_txns.begin(), sorted_txns.end(), 
        [](const auto &a, const auto &b) {
            if (a.first.in_read_view && b.first.in_read_view) {
                return a.first.rv_psn < b.first.rv_psn;
            } else if (!a.first.in_read_view && !b.first.in_read_view) {
                return a.first.psn < b.first.psn;
            } else if (a.first.in_read_view && !b.first.in_read_view) {
                if (a.first.rv_psn != b.first.psn)
                    return a.first.rv_psn < b.first.psn;
                return true;
            } else {
                if (a.first.psn != b.first.rv_psn)
                    return a.first.psn < b.first.rv_psn;
                return false;
            }
        });

    int in_read_view = 0;

    for (const auto &[info, txn] : sorted_txns) {
        if (info.rollback || info.conflicted) continue;

        in_read_view += (int)info.in_read_view;
        std::cout << info.psn << " " << info.rv_psn << std::endl;

        assert(in_txn() == NULL);
        box_txn_begin();

        for (const auto &stmt : txn.stmts) {
            std::cout << "TX" << txn.id << ": ";

            if (std::holds_alternative<insert_stmt>(stmt)) {
                const auto &s = std::get<insert_stmt>(stmt);
                size_t space_idx = std::find(spaces.begin(), spaces.end(), s.space) - spaces.begin();
                struct tuple *tuple = new struct tuple(*s.tuple);
                tuple->flags = 0;
                std::cout << "INSERT space=" << s.space << " tuple=";
                print_tuple(tuple);
                std::cout << std::endl;
                box_insert(verify_spaces[space_idx], tuple);
            } 
            else if (std::holds_alternative<replace_stmt>(stmt)) {
                const auto &s = std::get<replace_stmt>(stmt);
                size_t space_idx = std::find(spaces.begin(), spaces.end(), s.space) - spaces.begin();
                struct tuple *tuple = new struct tuple(*s.tuple);
                tuple->flags = 0;
                std::cout << "REPLACE space=" << s.space << " tuple=";
                print_tuple(tuple);
                std::cout << std::endl;
                box_replace(verify_spaces[space_idx], tuple);
            }
            else if (std::holds_alternative<delete_stmt>(stmt)) {
                const auto &s = std::get<delete_stmt>(stmt);
                size_t space_idx = std::find(spaces.begin(), spaces.end(), s.space) - spaces.begin();
                struct tuple *result;
                std::cout << "DELETE space=" << s.space << " index=" << s.index_id 
                  << " key=" << s.key;
                std::cout << std::endl;
                box_delete(verify_spaces[space_idx], s.index_id, s.key, &result);
                verify_results(s.result, result);
            }
            else if (std::holds_alternative<get_stmt>(stmt)) {
                const auto &s = std::get<get_stmt>(stmt);
                size_t space_idx = std::find(spaces.begin(), spaces.end(), s.space) - spaces.begin();
                struct tuple *result;
                std::cout << "GET space=" << s.space << " index=" << s.index_id 
                  << " key=" << s.key;
                std::cout << std::endl;
                box_get(verify_spaces[space_idx], s.index_id, s.key, &result);
                verify_results(s.result, result);
            }
        }
        box_txn_commit();
    }
    std::cout << "in_read_view: " << in_read_view << std::endl;
}

static int
txn_fiber_f(va_list ap)
{
    stress_txn *txn = va_arg(ap, stress_txn*);
    txn->info = execute_transaction(*txn);
    return 0;
}

int
stress_f(va_list ap)
{
    int n_spaces = 1 + gen() % MAX_SPACES;
    std::vector<struct memtx_space*> spaces(n_spaces);
    for (int i = 0; i < n_spaces; i++) {
        spaces[i] = memtx_space_new(1 + gen() % MAX_INDEXES);
    }

    int n_txns = 1 + gen() % MAX_TXNS;
    std::vector<stress_txn> txns(n_txns);
    
    for (int i = 0; i < n_txns; i++) {
        txns[i].id = i;
        txns[i].info.rollback = (gen() % 5 == 0); // 20% chance to rollback
        bool is_read_only = (gen() % 2 == 0); // 20% chance to read only

        int n_stmts = 1 + gen() % MAX_STMTS;
        txns[i].stmts.resize(n_stmts);
        
        for (int j = 0; j < n_stmts; j++) {
            struct memtx_space *space = spaces[gen() % n_spaces];
            uint32_t field_count = space->index_count;
            std::vector<int> values(field_count);
            for (uint32_t k = 0; k < field_count; k++)
                values[k] = gen() % MAX_KEY;
            
            int type = (is_read_only ? 3 /*GET*/ : (gen() % 4));

            switch (type) {
            case 0: { // INSERT
                struct tuple *tuple = create_tuple(space, values);
                txns[i].stmts[j] = insert_stmt{space, tuple, 0};
                break;
            }
            case 1: { // REPLACE
                struct tuple *tuple = create_tuple(space, values);
                txns[i].stmts[j] = replace_stmt{space, tuple, 0};
                break;
            }
            case 2: { // DELETE
                uint32_t index_id = gen() % space->index_count;
                int key = gen() % MAX_KEY;
                txns[i].stmts[j] = delete_stmt{space, index_id, key, 0, NULL};
                break;
            }
            case 3: { // GET
                uint32_t index_id = gen() % space->index_count;
                int key = gen() % MAX_KEY;
                txns[i].stmts[j] = get_stmt{space, index_id, key, 0, NULL};
                break;
            }
            }
        }
    }

    std::vector<struct fiber*> fibers;
    for (int i = 0; i < n_txns; i++) {
        struct fiber *f = fiber_new(txn_fiber_f);
        fiber_set_joinable(f, true);
        fiber_start(f, &txns[i]);
        fibers.push_back(f);
    }

    for (auto f : fibers) {
        fiber_join(f);
    }

    std::vector<std::pair<txn_info, stress_txn>> completed_txns;
    for (auto &txn : txns) {
        completed_txns.emplace_back(txn.info, txn);
    }

    execute_serial_verification(completed_txns, spaces);
    return 0;
}

int main() {
    std::cout << seed << std::endl;
    memory_init();
    fiber_init(fiber_c_invoke);
    memtx_tx_manager_init();

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
