/*
 * Copyright 2010-2025, Tarantool AUTHORS, please see AUTHORS file.
 *
 * Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following
 * conditions are met:
 *
 * 1. Redistributions of source code must retain the above
 *    copyright notice, this list of conditions and the
 *    following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials
 *    provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY <COPYRIGHT HOLDER> ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * <COPYRIGHT HOLDER> OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

------------------------------ MODULE memtx_tx ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

\* User-facing bounds (only these are provided via .cfg):
CONSTANTS MaxSpace, MaxIndexesPerSpace, MaxTxn, MaxStmtPerTxn, MaxKey

VARIABLES 
    \* Transaction state - now a map from txn to record
    txns,           \* [txn -> TxnType]

    \* Space configuration: which indexes belong to each space
    spaceIndexes,   \* [space -> sequence of Index] - indexes for each space (first is primary)
    spaceIndexCount,\* [space -> 1..MaxIndexesPerSpace] - active index count for each space
    
    \* Story chains: for each (index, key) we maintain a chain of stories
    \* Each story represents a version of a tuple with that key
    \* Stories are ordered: rolled_back ... committed ... prepared ... in_progress
    storyChains,    \* [index -> [key -> sequence of stories]]

    \* Story state - now a map from story to record
    stories,        \* [story -> StoryType]

    \* Statement state - now a map from stmt to record
    stmts,          \* [stmt -> StmtType]

    \* Gap trackers: transactions that read gap at each story for each index position
    gapTrackers,    \* [story -> Seq(SUBSET Txn)] - gap trackers for each story

    \* Read trackers: transactions that read each story
    readTrackers,   \* [story -> SUBSET Txn] - read trackers for each story

    \* Point holes: transactions that searched for keys but found nothing
    pointHoles,     \* [index -> [key -> set of txns]] - point holes storage
    
    \* Index state: which tuple is currently in the index for each (index, key)
    indexState,     \* [index -> [key -> tuple | NULL]]
    
    \* Tuple mapping: from tuple ID to TupleType
    tuples,         \* [tuple -> TupleType] - mapping from tuple ID to tuple structure

    \* History mapping: from tuple ID to story
    history,        \* [tuple -> Story] - mapping from tuple ID to story

    \* Global state - ID generators
    nextTxnId,      \* Next transaction ID to assign
    nextStmtId,     \* Next statement ID to assign
    nextStoryId,    \* Next story ID to assign
    nextTupleId,    \* Next tuple ID to assign
    nextPSN,        \* Next PSN to assign
    allStories,     \* Set of all stories
    allTxns,        \* Set of all transactions
    allStmts        \* Set of all statements

\* Helper sets
Txn == 1..MaxTxn
Key == 1..MaxKey
MaxIndex == MaxSpace * MaxIndexesPerSpace
Index == 1..MaxIndex
Space == 1..MaxSpace
\* Story and Stmt are just natural numbers - we'll use a large enough range
MaxStmt == MaxTxn * MaxStmtPerTxn
MaxPSN == MaxTxn + 2
Story == 1..MaxStmt
Tuple == 1..MaxStmt
Stmt == 1..MaxStmt
NULL == 0
ROLLBACKED_PSN == 1

\* Deterministic mapping: the i-th index of space s (1-based).
\* This ensures: each space has up to MaxIndexesPerSpace indexes and
\* no index belongs to more than one space.
IndexId(s, i) == (s - 1) * MaxIndexesPerSpace + i

\* States
INPROGRESS == 1
PREPARED == 2
IN_READ_VIEW == 3
COMMITTED == 4
ABORTED == 5

\* Transaction structure
TxnType == [
    status: {INPROGRESS, PREPARED, IN_READ_VIEW, COMMITTED, ABORTED},
    psn: Nat,           \* PSN | 0 if not prepared
    rv_psn: Nat,        \* rv_psn | 0 if not in read view
    stmts: Seq(Stmt)    \* sequence of statements
]

\* Story structure
StoryType == [
    add_stmt: Stmt \cup {NULL},     \* statement that created this story
    add_psn: Nat,                   \* PSN of transaction that created this story
    del_stmts: SUBSET Stmt,         \* set of statements that deleted this story
    del_psn: Nat,                   \* PSN of transaction that deleted this story
    tuple: Tuple,                   \* the actual data
    in_index: Index \cup {NULL},    \* which index contains this story's tuple
    index: Index,                   \* which index this story belongs to
    is_own_change: Seq(BOOLEAN)    \* Array of is_own_change for each index from CheckDup
]

\* Statement structure
StmtType == [
    txn: Txn,                       \* transaction that owns this statement
    space: Space,                   \* space this statement operates on
    add_story: Story \cup {NULL},   \* story created by this statement
    del_story: Story \cup {NULL},   \* story deleted by this statement
    is_own_change: BOOLEAN          \* whether this is own change
]

\* Tuple structure: contains keys
TupleType == [
    keys: Seq(Key)                  \* sequence of keys
]

\* Helper functions
\* NOTE: txns/stmts/stories are modeled as total functions; existence is tracked by allTxns/allStmts/allStories.
IsInProgress(txn) == txn \in allTxns /\ txns[txn].status = INPROGRESS
IsPrepared(txn) == txn \in allTxns /\ txns[txn].status = PREPARED /\ txns[txn].psn # 0
IsInReadView(txn) == txn \in allTxns /\ txns[txn].status = IN_READ_VIEW /\ txns[txn].rv_psn # 0
IsCommitted(txn) == txn \in allTxns /\ txns[txn].status = COMMITTED
IsAborted(txn) == txn \in allTxns /\ txns[txn].status = ABORTED

IsInProgressStory(story) == 
    story \in allStories /\ stories[story].add_psn = 0 /\
    stories[story].add_stmt # NULL

IsPreparedStory(story) ==
    story \in allStories /\ stories[story].add_psn # 0 /\
    stories[story].add_stmt # NULL

\* Let's assume that the rolled back one is also committed
\* provided that there is a committed dummy "delete" statement
\* (del_psn = ROLLBACKED_PSN)
IsCommittedStory(story) ==
    story \in allStories /\ stories[story].add_stmt = NULL

IsRolledBackStory(story) ==
    story \in allStories /\ stories[story].del_psn # ROLLBACKED_PSN

IsPreparedOrCommittedStory(story) == ~IsInProgressStory(story)

\* Get the last prepared/committed story in a chain
LastPreparedCommittedStory(index, key) ==
    IF index \in DOMAIN storyChains /\ key \in DOMAIN storyChains[index]
    THEN 
        LET chain == storyChains[index][key] IN
        \* Check positions from newest to oldest
        LET CheckPosition[pos \in 1..Len(chain)] ==
            LET story == chain[pos] IN
            IF IsPreparedOrCommittedStory(story)
            THEN story  \* Found the last (rightmost) prepared/committed story
            ELSE IF pos = 1
                 THEN NULL  \* No prepared/committed story found
                 ELSE CheckPosition[pos - 1]  \* Check older story
        IN CheckPosition[Len(chain)]  \* Start from newest
    ELSE NULL

--------------------------------------------------------------------------------
\* Invariants.
--------------------------------------------------------------------------------                

\* Property 0: Block structure in story chains
\* Stories in chain must be ordered: in_progress -> prepared -> committed -> rolled_back
Property0 ==
    \A index \in Index, key \in Key:
        LET chain == storyChains[index][key] IN
        \A i \in 2..Len(chain):
            IF i \in DOMAIN chain /\ (i-1) \in DOMAIN chain
            THEN LET next == chain[i]
                     prev == chain[i-1]
                 IN
                 \* in_progress block
                (IsInProgressStory(next) =>
                     IsInProgressStory(prev) \/ IsPreparedStory(prev) \/ IsCommittedStory(prev))
                 /\
                 \* prepared block
                 (IsPreparedStory(next) =>
                     IsPreparedStory(prev) \/ IsCommittedStory(prev))
                 /\
                 \* committed block
                 (IsCommittedStory(next) => IsCommittedStory(prev))
                 /\
                 \* rolled_back block
                 (IsRolledBackStory(next) => IsRolledBackStory(prev))
            ELSE TRUE

\* Property 2: del_psn != 0 => add_psn != 0
Property2 ==
    \A story \in allStories:
        stories[story].del_psn # 0 /\ stories[story].del_psn # ROLLBACKED_PSN
        => stories[story].add_psn # 0

\* Property 3: In committed/prepared block, del_story links form a chain
Property3 ==
    \A index \in Index, key \in Key:
        LET chain == storyChains[index][key] IN
        \A i \in 2..Len(chain):
            IF i \in DOMAIN chain /\ (i-1) \in DOMAIN chain
            THEN LET next == chain[i]
                prev == chain[i-1] IN
                 (IsPreparedOrCommittedStory(next) =>
                  stmts[stories[next].add_stmt].del_story \in {NULL, prev})
            ELSE TRUE

\* Property 4: For each story and each index-position i of its space:
\* if the story is not the last in the corresponding chain (for the i-th index),
\* then it must have no gap trackers for that index-position: gapTrackers[story][i] = {}.
Property4 ==
    \A story \in allStories:
        IF stories[story].add_stmt = NULL
        THEN \A i \in 1..MaxIndexesPerSpace: gapTrackers[story][i] = {}
        ELSE
            LET stmt_id == stories[story].add_stmt
            IN IF stmt_id \notin Stmt
            THEN \A i \in 1..MaxIndexesPerSpace: gapTrackers[story][i] = {}
            ELSE
            LET space == stmts[stmt_id].space
                indexes == spaceIndexes[space]
                tuple_id == stories[story].tuple
            IN \A i \in 1..MaxIndexesPerSpace:
                IF i > spaceIndexCount[space]
                THEN gapTrackers[story][i] = {}
                ELSE
                    LET idx == indexes[i]
                        key == tuples[tuple_id].keys[i]
                        chain == storyChains[idx][key]
                    IN IF Len(chain) = 0 \/ chain[Len(chain)] # story
                       THEN gapTrackers[story][i] = {}
                       ELSE TRUE

Invariants ==
    /\ Property0
    /\ Property2
    /\ Property3
    /\ Property4

--------------------------------------------------------------------------------
\* Implementation.
--------------------------------------------------------------------------------

StoryInsertIsVisible(txn, story) ==
    IF story \notin DOMAIN stories
    THEN [visible |-> FALSE, is_own_change |-> FALSE]
    ELSE LET
             is_own_change == stories[story].add_stmt # NULL /\
                              stmts[stories[story].add_stmt].txn = txn
             rv_psn == IF txn \in DOMAIN txns /\ txns[txn].rv_psn # 0
                       THEN txns[txn].rv_psn
                       ELSE MaxPSN
         IN
         IF is_own_change
         THEN [visible |-> TRUE, is_own_change |-> TRUE]
         ELSE IF stories[story].add_psn # 0 /\ stories[story].add_psn < rv_psn
              THEN [visible |-> TRUE, is_own_change |-> FALSE]  \* prepared transaction
              ELSE IF stories[story].add_stmt = NULL /\ stories[story].add_psn < rv_psn
                   THEN [visible |-> TRUE, is_own_change |-> FALSE]  \* committed transaction
                   ELSE IF stories[story].add_psn = 0 /\ stories[story].add_stmt = NULL
                        THEN [visible |-> TRUE, is_own_change |-> FALSE]  \* committed and GCed transaction
                        ELSE [visible |-> FALSE, is_own_change |-> FALSE]

StoryDeleteIsVisible(txn, story) ==
    IF story \notin DOMAIN stories
    THEN [visible |-> FALSE, is_own_change |-> FALSE]
    ELSE LET
             is_own_change == \E stmt \in stories[story].del_stmts : stmts[stmt].txn = txn
             rv_psn == IF txn \in DOMAIN txns /\ txns[txn].rv_psn # 0
                       THEN txns[txn].rv_psn
                       ELSE MaxPSN
         IN
         IF is_own_change
         THEN [visible |-> TRUE, is_own_change |-> TRUE]
         ELSE IF stories[story].del_psn # 0 /\ stories[story].del_psn < rv_psn
              THEN [visible |-> TRUE, is_own_change |-> FALSE]  \* prepared delete
         ELSE IF stories[story].del_stmts = {} /\ stories[story].del_psn < rv_psn
              THEN [visible |-> TRUE, is_own_change |-> FALSE]  \* committed delete
                   ELSE [visible |-> FALSE, is_own_change |-> FALSE]

\* Returns [visible_tuple |-> tuple | NULL, is_own_change |-> BOOLEAN]
FindVisibleTuple(txn, index, key, tuple) ==
    IF index \in DOMAIN storyChains /\ key \in DOMAIN storyChains[index] /\ Len(storyChains[index][key]) > 0
    THEN
        LET chain == storyChains[index][key] IN
        \* Check positions from newest to oldest
        LET CheckPosition[pos \in 1..Len(chain)] ==
            LET story == chain[pos]
                delete_result == StoryDeleteIsVisible(txn, story)
                insert_result == StoryInsertIsVisible(txn, story)
            IN IF delete_result.visible
               THEN [visible_tuple |-> NULL, is_own_change |-> delete_result.is_own_change]
               ELSE IF insert_result.visible
                    THEN [visible_tuple |-> stories[story].tuple, is_own_change |-> insert_result.is_own_change]
                    ELSE IF pos = 1
                         THEN [visible_tuple |-> NULL, is_own_change |-> FALSE]  \* End of chain
                         ELSE CheckPosition[pos - 1]  \* Check older story
        IN CheckPosition[Len(chain)]  \* Start from newest
    ELSE \* Chain is empty (GC collected all stories) - return tuple from index if it exists
         [visible_tuple |-> tuple, is_own_change |-> FALSE]

--------------------------------------------------------------------------------
\* Index.
--------------------------------------------------------------------------------

\* Inverse helpers for IndexId (work for the disjoint-block layout).
SpaceOfIndex(idx) == ((idx - 1) \div MaxIndexesPerSpace) + 1

PosInSpace(idx) == ((idx - 1) % MaxIndexesPerSpace) + 1

\* Get tuple from index (returns NULL if not found)
IndexGetTuple(index, key) ==
    IF index \in DOMAIN indexState /\ key \in DOMAIN indexState[index]
    THEN indexState[index][key]
    ELSE NULL

\* Update index state for all indexes in space with corresponding keys from tuple
IndexReplace(index_state_map, space, tuple, tuple_id) ==
    LET indexes == spaceIndexes[space]
    IN [idx \in Index |->
        IF idx \in {indexes[i] : i \in 1..spaceIndexCount[space]}
        THEN LET idx_pos == PosInSpace(idx)
                 key == tuple.keys[idx_pos]
             IN [index_state_map[idx] EXCEPT ![key] = tuple_id]
        ELSE index_state_map[idx]]

--------------------------------------------------------------------------------
\* Txn.
--------------------------------------------------------------------------------

\* Create a new statement record
CreateStmt(stmts_map, stmt_id, txn, space, add_story, del_story, is_own_change) ==
    [stmts_map EXCEPT ![stmt_id] = [
        txn |-> txn,
        space |-> space,
        add_story |-> add_story,
        del_story |-> del_story,
        is_own_change |-> is_own_change]]

\* Add a statement to a transaction's statement list
TxnAddStmt(txns_map, txn, stmt_id) ==
    [txns_map EXCEPT ![txn].stmts = Append(txns_map[txn].stmts, stmt_id)]

--------------------------------------------------------------------------------
\* Story.
--------------------------------------------------------------------------------

\* Create a new story record
CreateStory(stories_map, story_id, stmt_id, tuple_val, index, space, is_own_change) ==
    LET new_story_record == [
            add_stmt |-> stmt_id,
            add_psn |-> 0,
            del_stmts |-> {},
            del_psn |-> 0,
            tuple |-> tuple_val,
            in_index |-> index,
            index |-> index,
            is_own_change |-> is_own_change]
    IN IF story_id \in DOMAIN stories_map
       THEN [stories_map EXCEPT ![story_id] = new_story_record]
       ELSE [s \in DOMAIN stories_map \cup {story_id} |->
             IF s = story_id THEN new_story_record ELSE stories_map[s]]

\* Link a statement as deleting a story
StoryLinkDeletedBy(stories_map, story_id, stmt_id) ==
    IF story_id # NULL
    THEN [stories_map EXCEPT ![story_id].del_stmts = stories_map[story_id].del_stmts \cup {stmt_id}]
    ELSE stories_map

\* Add transaction to gap trackers for a story at a specific index position
\* index_pos is the position in spaceIndexes[space] (1-based)
AddGapTracker(gap_trackers_map, story_id, index_pos, txn) ==
    [gap_trackers_map EXCEPT ![story_id] = 
     [gap_trackers_map[story_id] EXCEPT ![index_pos] = 
      gap_trackers_map[story_id][index_pos] \cup {txn}]]

\* Add transaction to read trackers for a story
\* Only track if story is not committed (i.e., in-progress or prepared)
AddReadTracker(read_trackers_map, stories_map, story_id, txn) ==
    IF story_id \in DOMAIN stories_map /\ stories_map[story_id].add_stmt # NULL
    THEN [read_trackers_map EXCEPT ![story_id] = 
         read_trackers_map[story_id] \cup {txn}]
    ELSE read_trackers_map

\* Move gap trackers during INSERT/REPLACE:
\* 1) Populate gapTrackers[nextStoryId][i] from either replaced story's gap trackers or pointHoles.
\*    For each index i:
\*      - If directly_replaced_stories[i] # NULL:
\*             copy from replaced story's gap trackers
\*      - If directly_replaced_stories[i] = NULL (<=> directly_replaced[i] = NULL):
\*             copy from point holes (inserting into gap)
\* 2) Clear gap trackers on directly replaced stories for their corresponding index-positions.
MoveGapTrackersOnInsertReplace(gap_trackers_map, space, tuple, directly_replaced_stories) ==
    LET indexes == spaceIndexes[space]
    IN \* Build final map in one pass (similar style to MoveGapTrackersOnPrepare)
       [s \in Story |->
          [i \in 1..MaxIndexesPerSpace |->
             IF i <= Len(directly_replaced_stories) /\ directly_replaced_stories[i] = s
             THEN {} \* cleared at source
             ELSE IF s = nextStoryId
                  THEN
                      IF i > spaceIndexCount[space]
                      THEN gap_trackers_map[nextStoryId][i]
                      ELSE
                          LET idx == indexes[i]
                              key == tuple.keys[i]
                          IN IF directly_replaced_stories[i] # NULL
                             THEN gap_trackers_map[nextStoryId][i] \cup gap_trackers_map[directly_replaced_stories[i]][i]
                             ELSE IF idx \in DOMAIN pointHoles /\ key \in DOMAIN pointHoles[idx]
                                  THEN gap_trackers_map[nextStoryId][i] \cup pointHoles[idx][key]
                                  ELSE gap_trackers_map[nextStoryId][i]
                  ELSE gap_trackers_map[s][i]]]

--------------------------------------------------------------------------------
\* Chain.
--------------------------------------------------------------------------------

\* Append new story to story chains for all indexes in space with corresponding keys from tuple
StoryChainAppendNewStory(story_chains_map, space, tuple) ==
    LET indexes == spaceIndexes[space]
    IN [idx \in Index |->
        IF \E i \in 1..spaceIndexCount[space] : indexes[i] = idx
        THEN LET i == PosInSpace(idx)
             IN [story_chains_map[idx] EXCEPT ![tuple.keys[i]] =
                Append(story_chains_map[idx][tuple.keys[i]], nextStoryId)]
        ELSE story_chains_map[idx]]

--------------------------------------------------------------------------------
\* PointHoles.
--------------------------------------------------------------------------------

\* Clear point holes for all indexes in space with corresponding keys from tuple
\* Only clear if directly_replaced[i] = NULL (inserting into gap, not replacing)
ClearPointHoles(point_holes_map, space, tuple, directly_replaced) ==
    LET indexes == spaceIndexes[space]
    IN [idx \in Index |->
        IF idx \in {indexes[i] : i \in 1..spaceIndexCount[space]}
        THEN LET idx_pos == PosInSpace(idx)
                 key == tuple.keys[idx_pos]
             IN IF directly_replaced[idx_pos] = NULL
                THEN [point_holes_map[idx] EXCEPT ![key] = {}]
                ELSE point_holes_map[idx]
        ELSE point_holes_map[idx]]

\* Check for duplicates across all indexes of a space
\* directly_replaced: sequence of tuples replaced in each index
\* tuple_keys: sequence of keys corresponding to each index
CheckDup(txn, space, directly_replaced, tuple_keys, mode) ==
    LET
        indexes == spaceIndexes[space]
        \* Find visible tuple for all indexes - compute once and reuse
        visible_results ==
            [i \in 1..spaceIndexCount[space] |->
                FindVisibleTuple(txn, indexes[i], tuple_keys[i], directly_replaced[i])]
        \* Extract visible tuples and is_own_change arrays
        visible_tuples == [i \in 1..spaceIndexCount[space] |-> visible_results[i].visible_tuple]
        is_own_change == [i \in 1..spaceIndexCount[space] |-> visible_results[i].is_own_change]
        primary_visible_tuple == visible_tuples[1]
        \* Check for duplicates on primary key
        primary_is_duplicate ==
            IF mode = "INSERT" /\ primary_visible_tuple # NULL
            THEN TRUE  \* INSERT but tuple exists - duplicate
            ELSE IF mode = "REPLACE" /\ primary_visible_tuple = NULL
                THEN TRUE  \* REPLACE but no tuple to replace - duplicate
                ELSE FALSE
        \* Check secondary indexes: visible tuple must be NULL or same as primary
        \* If secondary index shows a different tuple than primary, it's a duplicate error
        \* Find first secondary index with duplicate
        secondary_duplicate_tuple ==
            LET CheckSecondary[i \in 2..spaceIndexCount[space]] ==
                LET sec_visible == visible_tuples[i]
                IN IF sec_visible # NULL /\ sec_visible # primary_visible_tuple
                    THEN sec_visible
                    ELSE IF i = spaceIndexCount[space]
                        THEN NULL
                        ELSE CheckSecondary[i + 1]
            IN IF spaceIndexCount[space] >= 2 THEN CheckSecondary[2] ELSE NULL
        is_duplicate == primary_is_duplicate \/ secondary_duplicate_tuple # NULL
        duplicate_tuple ==
            IF primary_is_duplicate THEN primary_visible_tuple
            ELSE secondary_duplicate_tuple
    IN
    [is_duplicate |-> is_duplicate,
     primary_visible_tuple |-> primary_visible_tuple,
     duplicate_tuple |-> duplicate_tuple,
     is_own_change |-> is_own_change]

\* Initial state
Init ==
    \* MaxIndex is derived as MaxSpace * MaxIndexesPerSpace.
    /\ allStories = {}
    /\ allTxns = {}
    /\ allStmts = {}
    /\ nextTxnId = 1
    /\ nextStmtId = 1
    /\ nextStoryId = 1
    /\ nextTupleId = 1
    /\ txns = [t \in Txn |->
               [status |-> INPROGRESS,
                psn |-> 0,
                rv_psn |-> 0,
                stmts |-> <<>>]]
    \* Each space owns a disjoint block of MaxIndexesPerSpace indexes.
    /\ spaceIndexes = [s \in Space |-> [i \in 1..MaxIndexesPerSpace |-> IndexId(s, i)]]
    \* Each space has a nondeterministic active index count in 1..MaxIndexesPerSpace.
    /\ spaceIndexCount \in [Space -> 1..MaxIndexesPerSpace]
    /\ storyChains = [i \in Index |-> [k \in Key |-> <<>>]]
    /\ stories = [s \in Story |->
                  [add_stmt |-> NULL,
                   add_psn |-> 0,
                   del_stmts |-> {},
                   del_psn |-> 0,
                   tuple |-> NULL,
                   in_index |-> NULL,
                   index |-> NULL,
                   is_own_change |-> <<>>]]
    \* IMPORTANT: gapTrackers/readTrackers must be total over Story, otherwise EXCEPT updates
    \* won't add entries for newly created stories and invariants like Property4 won't be exercised.
    /\ gapTrackers = [s \in Story |-> [i \in 1..MaxIndexesPerSpace |-> {}]]
    /\ readTrackers = [s \in Story |-> {}]
    /\ stmts = [s \in Stmt |->
                [txn |-> NULL,
                 space |-> NULL,
                 add_story |-> NULL,
                 del_story |-> NULL,
                 is_own_change |-> FALSE]]
    /\ pointHoles = [i \in Index |-> [k \in Key |-> {}]]
    /\ indexState = [i \in Index |-> [k \in Key |-> NULL]]
    /\ tuples = [t \in Tuple |->
                 [keys |-> <<>>]]
    /\ history = [t \in Tuple |-> NULL]
    /\ nextPSN = 2

BeginTxn ==
    /\ LET new_txn == nextTxnId
       IN /\ new_txn \in Txn
          /\ new_txn \notin allTxns
          /\ txns' = [txns EXCEPT ![new_txn] =
                      [status |-> INPROGRESS,
                       psn |-> 0,
                       rv_psn |-> 0,
                       stmts |-> <<>>]]
          /\ allTxns' = allTxns \cup {new_txn}
          /\ nextTxnId' = nextTxnId + 1
          /\ UNCHANGED <<storyChains, stories, stmts,
                        indexState, tuples, history, nextPSN, nextStmtId, nextStoryId, nextTupleId, allStories, allStmts,
                        pointHoles, spaceIndexes, spaceIndexCount, gapTrackers, readTrackers>>

InsertReplace(txn, space, tuple, tuple_id, mode) ==
    LET
        indexes == spaceIndexes[space]
        primary_index == indexes[1]
        \* Extract primary key from tuple.keys
        key == tuple.keys[1]
        \* Build directly_replaced sequence: tuple replaced in each index by corresponding key
        directly_replaced ==
            [i \in 1..spaceIndexCount[space] |->
                IndexGetTuple(indexes[i], tuple.keys[i])]
        directly_replaced_stories ==
            [i \in 1..Len(directly_replaced) |->
                IF directly_replaced[i] # NULL
                THEN history[directly_replaced[i]]
                ELSE NULL]
        \* Check for duplicates
        dup_result == CheckDup(txn, space, directly_replaced, tuple.keys, mode)
        is_duplicate == dup_result.is_duplicate
        primary_visible_tuple == dup_result.primary_visible_tuple
        primary_visible_story ==
            IF dup_result.primary_visible_tuple # NULL
            THEN history[dup_result.primary_visible_tuple]
            ELSE NULL
        duplicate_tuple == dup_result.duplicate_tuple
        is_own_change == dup_result.is_own_change
    IN
    /\ nextStmtId \in Stmt
    /\ nextStoryId \in Story
    /\ allStmts' = allStmts \cup {nextStmtId}
    /\ nextStmtId' = nextStmtId + 1
    /\ txns' = TxnAddStmt(txns, txn, nextStmtId)
    /\ IF ~is_duplicate
       THEN \* No duplicate - proceed with insertion/replacement
            /\ stmts' = CreateStmt(stmts, nextStmtId, txn, space, nextStoryId, primary_visible_story, is_own_change[1])
            /\ allStories' = allStories \cup {nextStoryId}
            /\ nextStoryId' = nextStoryId + 1
            \* Create new story
            /\ LET created_story == CreateStory(stories, nextStoryId, nextStmtId, tuple_id, primary_index, space, is_own_change)
               IN stories' = StoryLinkDeletedBy(created_story, primary_visible_story, nextStmtId)
            \* Initialize gap trackers for new story
            /\ LET gap_trackers_init == 
                   \* IMPORTANT: keep gapTrackers[nextStoryId] total over 1..MaxIndexesPerSpace
                   [i \in 1..MaxIndexesPerSpace |->
                    IF i <= spaceIndexCount[space] /\ i = 1 /\ ~is_own_change[1] /\ mode = "INSERT"
                    THEN {txn}  \* Track gap for new story (inserting into gap)
                    ELSE {}]
                   gap_trackers_with_new == [gapTrackers EXCEPT ![nextStoryId] = gap_trackers_init]
                   \* Populate new story trackers and clear replaced stories in one step
                   moved_gap_trackers == MoveGapTrackersOnInsertReplace(gap_trackers_with_new, space, tuple, directly_replaced_stories)
               IN gapTrackers' = moved_gap_trackers
            \* Initialize read trackers for new story
            /\ readTrackers' = [readTrackers EXCEPT ![nextStoryId] = {}]
            /\ history' = [history EXCEPT ![tuple_id] = nextStoryId]
            \* Update story chains for all indexes in the space
            /\ storyChains' = StoryChainAppendNewStory(storyChains, space, tuple)
            \* Update index state for all indexes
            /\ indexState' = IndexReplace(indexState, space, tuple, tuple_id)
            \* Clear point holes for all indexes
            /\ pointHoles' = ClearPointHoles(pointHoles, space, tuple, directly_replaced)
       ELSE \* Duplicate found - track read for duplicate tuple
            /\ stmts' = CreateStmt(stmts, nextStmtId, txn, space, NULL, NULL, FALSE)
            /\ IF duplicate_tuple # NULL
               THEN LET duplicate_story == history[duplicate_tuple]
                    IN readTrackers' = AddReadTracker(readTrackers, stories, duplicate_story, txn)
               ELSE UNCHANGED <<readTrackers>>
            /\ UNCHANGED <<allStories, stories, gapTrackers, nextStoryId, history, storyChains, indexState, pointHoles>>
    /\ UNCHANGED <<nextPSN, nextTxnId, allTxns, spaceIndexes, spaceIndexCount>>

Get(txn, index, key) ==
    /\ IsInProgress(txn) \/ IsInReadView(txn)
    /\ index \in Index
    /\ key \in Key
    /\ LET tuple == IndexGetTuple(index, key)
           visible_result == FindVisibleTuple(txn, index, key, tuple)
           \* Find space that contains this index (disjoint-block layout)
           space == SpaceOfIndex(index)
       IN
       IF ~visible_result.is_own_change
       THEN IF visible_result.visible_tuple # NULL
            THEN \* Found visible tuple - track read
                 LET visible_story == history[visible_result.visible_tuple]
                 IN /\ readTrackers' = AddReadTracker(readTrackers, stories, visible_story, txn)
                    /\ UNCHANGED <<pointHoles, stories, gapTrackers>>
            ELSE \* Nothing visible found
                 IF tuple # NULL
                 THEN \* Track gap for top_story
                      LET top_story == history[tuple]
                          index_pos == PosInSpace(index)
                      IN /\ UNCHANGED <<pointHoles, stories, readTrackers>>
                         /\ gapTrackers' = AddGapTracker(gapTrackers, top_story, index_pos, txn)
                 ELSE \* tuple = NULL - track point hole
                      /\ pointHoles' = [pointHoles EXCEPT
                                      ![index][key] = pointHoles[index][key] \cup {txn}]
                      /\ UNCHANGED <<stories, gapTrackers, readTrackers>>
       ELSE \* Own change - no tracking
            /\ UNCHANGED <<pointHoles, stories, gapTrackers, readTrackers>>
    /\ UNCHANGED <<txns, storyChains, stmts, indexState, tuples, history,
                  nextTxnId, nextStmtId, nextStoryId, nextTupleId, nextPSN,
                  allStories, allTxns, allStmts, spaceIndexes, spaceIndexCount>>

\* Action: Delete operation
Delete(txn, space, index, key) ==
    /\ IsInProgress(txn)
    /\ nextStmtId \in Stmt
    /\ space \in Space
    /\ index \in Index
    /\ key \in Key
    /\ SpaceOfIndex(index) = space
    /\ LET tuple == IndexGetTuple(index, key)
           visible_result == FindVisibleTuple(txn, index, key, tuple)
       IN /\ allStmts' = allStmts \cup {nextStmtId}
          /\ nextStmtId' = nextStmtId + 1
          /\ txns' = TxnAddStmt(txns, txn, nextStmtId)
          /\ IF visible_result.visible_tuple # NULL
             THEN \* Found visible tuple - delete it
                  LET visible_story == history[visible_result.visible_tuple]
                      \* Determine is_own_change: TRUE if this transaction inserted the story
                      is_own_change ==
                          IF visible_story # NULL /\
                             stories[visible_story].add_stmt # NULL
                          THEN stmts[stories[visible_story].add_stmt].txn = txn
                          ELSE FALSE
                  IN /\ stmts' = CreateStmt(stmts, nextStmtId, txn, space, NULL, visible_story, is_own_change)
                     /\ stories' = StoryLinkDeletedBy(stories, visible_story, nextStmtId)
                     /\ IF ~visible_result.is_own_change
                        THEN readTrackers' = AddReadTracker(readTrackers, stories, visible_story, txn)
                        ELSE UNCHANGED <<readTrackers>>
                     /\ UNCHANGED <<gapTrackers, pointHoles>>
             ELSE \* Nothing visible found - still create statement
                  /\ stmts' = CreateStmt(stmts, nextStmtId, txn, space, NULL, NULL, FALSE)
            /\ UNCHANGED <<stories, readTrackers>>
            /\ IF ~visible_result.is_own_change
               THEN IF tuple # NULL /\ tuple \in DOMAIN history /\ history[tuple] # NULL
                    THEN \* Track gap for top_story
                         LET top_story == history[tuple]
                             index_pos == PosInSpace(index)
                         IN /\ gapTrackers' = AddGapTracker(gapTrackers, top_story, index_pos, txn)
                            /\ UNCHANGED <<pointHoles>>
                    ELSE \* tuple = NULL - track point hole
                         /\ UNCHANGED <<gapTrackers>>
                         /\ pointHoles' = [pointHoles EXCEPT
                                         ![index][key] = pointHoles[index][key] \cup {txn}]
               ELSE \* Own change - no tracking
                    /\ UNCHANGED <<gapTrackers, pointHoles>>
    /\ UNCHANGED <<storyChains, indexState, tuples, history,
                  nextTxnId, nextStoryId, nextTupleId, nextPSN,
                  allStories, allTxns, spaceIndexes, spaceIndexCount>>

\* Helper function: Find the position of the last prepared/committed story in a chain
\* Returns the position (1-based) of the last prepared/committed story, or 0 if none found
LastPreparedCommittedPosition(chain) ==
    IF Len(chain) = 0
    THEN 0
    ELSE LET CheckPosition[pos \in 1..Len(chain)] ==
             LET story == chain[pos]
             IN IF IsPreparedOrCommittedStory(story)
                THEN pos  \* Found prepared/committed story
                ELSE IF pos = 1
                     THEN 0  \* No prepared/committed story found
                     ELSE CheckPosition[pos - 1]  \* Check older story
         IN CheckPosition[Len(chain)]  \* Start from newest

\* Helper function: Move all txn stories to end of prepared block in a chain
\* Returns new chain with txn stories moved after last prepared/committed story
MoveTxnStoriesToPreparedBlock(chain, txn_stories) ==
    LET \* Find stories from this transaction in the chain
        txn_stories_in_chain == {s \in txn_stories : s \in {chain[i] : i \in DOMAIN chain}}
    IN IF txn_stories_in_chain = {}
       THEN chain  \* No stories from this transaction in chain
       ELSE \* Find position of last prepared/committed story
            LET last_prep_pos == LastPreparedCommittedPosition(chain)
                \* Build new chain by iterating through original chain positions
                \* Collect: [stories before last_prep_pos] ++ [txn stories] ++ [non-txn stories after last_prep_pos]
                last_prep_pos_after == last_prep_pos + Cardinality(txn_stories_in_chain)
            IN [i \in 1..Len(chain) |->
               IF i <= last_prep_pos
               THEN chain[i]  \* Stories before last_prep_pos
               ELSE IF i <= last_prep_pos_after
                    THEN \* Txn story: find (i - last_prep_pos)-th txn story by position
                        LET pos == CHOOSE p \in (last_prep_pos + 1)..Len(chain) :
                                     chain[p] \in txn_stories_in_chain /\
                                     Cardinality({q \in (last_prep_pos + 1)..(p - 1) :
                                         chain[q] \in txn_stories_in_chain}) = i - last_prep_pos - 1
                        IN chain[pos]
                    ELSE \* Non-txn story after last_prep_pos: find (i - last_prep_pos_after)-th non-txn story
                        LET pos == CHOOSE p \in (last_prep_pos + 1)..Len(chain) :
                                     chain[p] \notin txn_stories_in_chain /\
                                     Cardinality({q \in (last_prep_pos + 1)..(p - 1) :
                                         chain[q] \notin txn_stories_in_chain}) = i - last_prep_pos_after - 1
                        IN chain[pos]]

StoryChainFindNewTopOnPrepare(chain, txn_stories) ==
    \* Find the newest in-progress story in chain that is NOT in txn_stories (excluding the top element).
    IF Len(chain) < 2 THEN NULL
    ELSE
        LET start == Len(chain) - 1
            Check[pos \in Nat] ==
                IF pos < 1 THEN NULL
                ELSE LET s == chain[pos] IN
                    \* Stop as soon as we leave the in-progress suffix.
                    IF ~IsInProgressStory(s) THEN NULL
                    ELSE IF s \notin txn_stories THEN s
                    ELSE Check[pos - 1]
        IN Check[start]

MoveGapTrackersOnPrepare(gap_trackers_map, story_chains_map, txn_stories) ==
    LET movedTriples ==
            {<<top, target, pos>> \in (Story \X Story \X (1..MaxIndexesPerSpace)) :
                \E idx \in DOMAIN story_chains_map:
                  \E key \in DOMAIN story_chains_map[idx]:
                    LET chain == story_chains_map[idx][key]
                        top0 == chain[Len(chain)]
                        target0 == StoryChainFindNewTopOnPrepare(chain, txn_stories)
                    IN /\ Len(chain) > 0
                       /\ top0 \in txn_stories
                       /\ target0 # NULL
                       /\ top = top0 /\ target = target0 /\ pos = PosInSpace(idx)}
    IN [s \in Story |->
         [i \in 1..MaxIndexesPerSpace |->
            IF \E t \in movedTriples: t[1] = s /\ t[3] = i
            THEN {} \* cleared at source
            ELSE gap_trackers_map[s][i] \cup
                 UNION {IF t[2] = s /\ t[3] = i
                        THEN gap_trackers_map[t[1]][t[3]]
                        ELSE {} :
                        t \in movedTriples}]]

\* Helper: rebind physical indexState when PrepareTxn changes the top of a chain.
\* If top of (idx,key) chain is a txn story and StoryChainFindNewTopOnPrepare returns new_top,
\* then indexState[idx][key] must point to stories[new_top].tuple.
RebindIndexStateOnPrepare(index_state_map, story_chains_map, stories_map, txn_stories) ==
    [idx \in Index |->
        [key \in Key |->
            LET chain == story_chains_map[idx][key] IN
            IF Len(chain) = 0 THEN index_state_map[idx][key]
            ELSE
                LET top == chain[Len(chain)]
                    new_top == IF top \in txn_stories
                              THEN StoryChainFindNewTopOnPrepare(chain, txn_stories)
                              ELSE NULL
                IN IF new_top # NULL THEN stories_map[new_top].tuple
                ELSE index_state_map[idx][key]]]

\* Action: Prepare transaction
\* Moves all stories of the transaction to the end of prepared blocks in their chains
PrepareTxn(txn) ==
    /\ IsInProgress(txn)
    /\ LET \* Find all stories created by this transaction
        txn_stories ==
            {stmts[txns[txn].stmts[i]].add_story :
                i \in DOMAIN txns[txn].stmts} \ {NULL}
        IN \* Update story chains: for each chain, move all txn stories after last prepared/committed story 
            /\ storyChains' =
                [index \in DOMAIN storyChains |->
                    [key \in DOMAIN storyChains[index] |->
                        MoveTxnStoriesToPreparedBlock(storyChains[index][key], txn_stories)]]
            /\ stories' =
                [s \in DOMAIN stories |->
                    IF s \in txn_stories
                    THEN [stories[s] EXCEPT !.add_psn = nextPSN]
                    ELSE stories[s]]
            /\ gapTrackers' = MoveGapTrackersOnPrepare(gapTrackers, storyChains, txn_stories)
            /\ indexState' = RebindIndexStateOnPrepare(indexState, storyChains, stories, txn_stories)
            /\ txns' = [txns EXCEPT ![txn].status = PREPARED,
                                    ![txn].psn = nextPSN]
            /\ nextPSN' = nextPSN + 1
            /\ UNCHANGED <<stmts, pointHoles, tuples, history,
                        nextTxnId, nextStmtId, nextStoryId, nextTupleId,
                        allStories, allTxns, allStmts, spaceIndexes, spaceIndexCount,
                        readTrackers>>

\* Next state relation
Next ==
    \/ BeginTxn
    \/ \E txn \in allTxns:
       \E space \in Space:
       \E mode \in {"INSERT", "REPLACE"}:
       \E keys \in [1..spaceIndexCount[space] -> Key]:
         /\ IsInProgress(txn)
         /\ LET tuple == [keys |-> keys]
            IN /\ nextTupleId \in Tuple
               /\ nextTupleId' = nextTupleId + 1
               /\ tuples' = [tuples EXCEPT ![nextTupleId] = tuple]
               /\ InsertReplace(txn, space, tuple, nextTupleId, mode)
    \/ \E txn \in allTxns, index \in Index, key \in Key :
       /\ IsInProgress(txn)
       /\ Get(txn, index, key)
    \/ \E txn \in allTxns, space \in Space, index \in Index, key \in Key :
       /\ IsInProgress(txn)
       /\ Delete(txn, space, index, key)
    \* \/ \E txn \in allTxns : PrepareTxn(txn)
    \* TODO: Add other actions when implemented
    \* \/ \E txn \in allTxns : CommitTxn(txn)
    \* \/ \E txn \in allTxns : RollbackTxn(txn)

\* Specification
Spec == Init /\ [][Next]_<<txns, storyChains, stories, stmts,
                      gapTrackers, readTrackers,
                      pointHoles, indexState, tuples, history,
                      nextTxnId, nextStmtId, nextStoryId, nextTupleId, nextPSN,
                      allStories, allTxns, allStmts, spaceIndexes, spaceIndexCount>>

THEOREM Spec => []Invariants

\* WARNING: This specification does NOT verify serializability!
\* It only verifies structural invariants (Property 1-9).
===============================================================================
