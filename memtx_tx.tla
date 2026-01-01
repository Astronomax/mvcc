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

CONSTANTS MaxTxn, MaxStmt, MaxSpace, MaxKey, MaxIndex, MaxPSN, MaxIndexesPerSpace

VARIABLES 
    \* Transaction state - now a map from txn to record
    txns,           \* [txn -> TxnType]

    \* Space configuration: which indexes belong to each space
    spaceIndexes,   \* [space -> sequence of Index] - indexes for each space (first is primary)
    
    \* Story chains: for each (index, key) we maintain a chain of stories
    \* Each story represents a version of a tuple with that key
    \* Stories are ordered: rolled_back ... committed ... prepared ... in_progress
    storyChains,    \* [index -> [key -> sequence of stories]]

    \* Story state - now a map from story to record
    stories,        \* [story -> StoryType]

    \* Statement state - now a map from stmt to record
    stmts,          \* [stmt -> StmtType]

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
Index == 1..MaxIndex
Space == 1..MaxSpace
\* Story and Stmt are just natural numbers - we'll use a large enough range
Story == 1..(MaxTxn * MaxStmt)
Tuple == 1..(MaxTxn * MaxStmt)
Stmt == 1..(MaxTxn * MaxStmt)
NULL == 0
ROLLBACKED_PSN == 1

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
    gapTrackers: Seq(SUBSET Txn),  \* transactions that read gap at this story for each index position
    readTrackers: SUBSET Txn       \* transactions that read this story
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
IsInProgress(txn) == txn \in DOMAIN txns /\ txns[txn].status = INPROGRESS
IsPrepared(txn) == txn \in DOMAIN txns /\ txns[txn].status = PREPARED /\ txns[txn].psn # 0
IsInReadView(txn) == txn \in DOMAIN txns /\ txns[txn].status = IN_READ_VIEW /\ txns[txn].rv_psn # 0
IsCommitted(txn) == txn \in DOMAIN txns /\ txns[txn].status = COMMITTED
IsAborted(txn) == txn \in DOMAIN txns /\ txns[txn].status = ABORTED

IsInProgressStory(story) == 
    story \in DOMAIN stories /\ stories[story].add_psn = 0 /\
    stories[story].add_stmt # NULL

IsPreparedStory(story) ==
    story \in DOMAIN stories /\ stories[story].add_psn # 0 /\
    stories[story].add_stmt # NULL

\* Let's assume that the rolled back one is also committed
\* provided that there is a committed dummy "delete" statement
\* (del_psn = ROLLBACKED_PSN)
IsCommittedStory(story) ==
    story \in DOMAIN stories /\ stories[story].add_stmt = NULL

IsRolledBackStory(story) ==
    story \in DOMAIN stories /\ stories[story].del_psn # ROLLBACKED_PSN

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

Invariants ==
    /\ Property0
    /\ Property2
    /\ Property3

--------------------------------------------------------------------------------
\* Implementation.
--------------------------------------------------------------------------------

\* Initial state
Init ==
    /\ allStories = {}
    /\ allTxns = {}
    /\ allStmts = {}
    /\ nextTxnId = 1
    /\ nextStmtId = 1
    /\ nextStoryId = 1
    /\ nextTupleId = 1
    /\ txns = [t \in allTxns |->
               [status |-> INPROGRESS,
                psn |-> 0,
                rv_psn |-> 0,
                stmts |-> <<>>]]
    /\ spaceIndexes = [s \in Space |-> <<s>>]  \* Each space has at least primary index (same as space number)
    /\ storyChains = [i \in Index |-> [k \in Key |-> <<>>]]
    /\ stories = [s \in allStories |->
                  [add_stmt |-> NULL,
                   add_psn |-> 0,
                   del_stmts |-> {},
                   del_psn |-> 0,
                   tuple |-> NULL,
                   in_index |-> NULL,
                   index |-> NULL,
                   gapTrackers |-> <<>>,
                   readTrackers |-> {}]]
    /\ stmts = [s \in allStmts |->
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
       IN /\ new_txn \notin allTxns
          /\ txns' = [txns EXCEPT ![new_txn] =
                      [status |-> INPROGRESS,
                       psn |-> 0,
                       rv_psn |-> 0,
                       stmts |-> <<>>]]
          /\ allTxns' = allTxns \cup {new_txn}
          /\ nextTxnId' = nextTxnId + 1
          /\ UNCHANGED <<storyChains, stories, stmts,
                        indexState, tuples, history, nextPSN, nextStmtId, nextStoryId, nextTupleId, allStories, allStmts,
                        pointHoles, spaceIndexes>>

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

\* Get tuple from index (returns NULL if not found)
IndexGetTuple(index, key) ==
    IF index \in DOMAIN indexState /\ key \in DOMAIN indexState[index]
    THEN indexState[index][key]
    ELSE NULL

\* Update index state for all indexes in space with corresponding keys from tuple
IndexReplace(index_state_map, space, tuple, tuple_id) ==
    LET indexes == spaceIndexes[space]
    IN [idx \in Index |->
        IF idx \in {indexes[i] : i \in DOMAIN indexes}
        THEN LET idx_pos == CHOOSE i \in DOMAIN indexes : indexes[i] = idx
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
CreateStory(stories_map, story_id, stmt_id, tuple_val, index, space) ==
    LET indexes == spaceIndexes[space]
        \* Create sequence of empty sets for gapTrackers
        gapTrackers_init == [i \in 1..Len(indexes) |-> {}]
        new_story_record == [
            add_stmt |-> stmt_id,
            add_psn |-> 0,
            del_stmts |-> {},
            del_psn |-> 0,
            tuple |-> tuple_val,
            in_index |-> index,
            index |-> index,
            gapTrackers |-> gapTrackers_init,
            readTrackers |-> {}]
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
AddGapTracker(stories_map, story_id, index_pos, txn) ==
    [stories_map EXCEPT ![story_id].gapTrackers = 
     [stories_map[story_id].gapTrackers EXCEPT ![index_pos] = 
      stories_map[story_id].gapTrackers[index_pos] \cup {txn}]]

\* Add transaction to read trackers for a story
\* Only track if story is not committed (i.e., in-progress or prepared)
AddReadTracker(stories_map, story_id, txn) ==
    IF story_id \in DOMAIN stories_map /\ stories_map[story_id].add_stmt # NULL
    THEN [stories_map EXCEPT ![story_id].readTrackers = 
         stories_map[story_id].readTrackers \cup {txn}]
    ELSE stories_map

\* Copy gap trackers from directly_replaced stories to new_story
\* For each index i, if directly_replaced[i] # NULL, copy gapTrackers[i] from replaced story to new_story
CopyGapTrackersToNewTop(stories_map, new_story, directly_replaced_stories) ==
    [stories_map EXCEPT ![new_story].gapTrackers = 
        [i \in 1..Len(directly_replaced_stories) |->
            IF directly_replaced_stories[i] # NULL
            THEN stories_map[new_story].gapTrackers[i] \cup
                stories_map[directly_replaced_stories[i]].gapTrackers[i]
            ELSE stories_map[new_story].gapTrackers[i]]]

\* Clear gap trackers from replaced stories for corresponding indexes
\* For each replaced story, clear gap trackers for all indexes where it was replaced
ClearGapTrackers(stories_map, directly_replaced_stories) ==
    [s \in DOMAIN stories_map |->
        IF \E i \in 1..Len(directly_replaced_stories) : directly_replaced_stories[i] = s
        THEN [stories_map[s] EXCEPT !.gapTrackers = 
            [i \in 1..Len(directly_replaced_stories) |->
                IF directly_replaced_stories[i] = s
                THEN {}
                ELSE stories_map[s].gapTrackers[i]]]
        ELSE stories_map[s]]

\* Copy point holes to gap trackers in story for all indexes in space with corresponding keys from tuple
\* Only transfer gap trackers if directly_replaced[i] = NULL (inserting into gap, not replacing)
CopyPointHolesToGapTrackers(stories_map, story_id, holes, space, tuple, directly_replaced) ==
    LET indexes == spaceIndexes[space]
    IN [stories_map EXCEPT ![story_id].gapTrackers = 
        [i \in 1..Len(indexes) |->
         LET idx == indexes[i]
             key == tuple.keys[i]
         IN IF directly_replaced[i] = NULL /\
               idx \in DOMAIN holes /\
               key \in DOMAIN holes[idx]
            THEN stories_map[story_id].gapTrackers[i] \cup holes[idx][key]
            ELSE stories_map[story_id].gapTrackers[i]]]

--------------------------------------------------------------------------------
\* Chain.
--------------------------------------------------------------------------------

\* Append new story to story chains for all indexes in space with corresponding keys from tuple
StoryChainAppend(story_chains_map, space, tuple, new_story) ==
    LET indexes == spaceIndexes[space]
    IN [idx \in Index |->
        IF \E i \in DOMAIN indexes : indexes[i] = idx
        THEN LET i == CHOOSE pos \in DOMAIN indexes : indexes[pos] = idx
             IN [story_chains_map[idx] EXCEPT ![tuple.keys[i]] = Append(story_chains_map[idx][tuple.keys[i]], new_story)]
        ELSE story_chains_map[idx]]

--------------------------------------------------------------------------------
\* PointHoles.
--------------------------------------------------------------------------------

\* Clear point holes for all indexes in space with corresponding keys from tuple
\* Only clear if directly_replaced[i] = NULL (inserting into gap, not replacing)
ClearPointHoles(point_holes_map, space, tuple, directly_replaced) ==
    LET indexes == spaceIndexes[space]
    IN [idx \in Index |->
        IF idx \in {indexes[i] : i \in DOMAIN indexes}
        THEN LET idx_pos == CHOOSE i \in DOMAIN indexes : indexes[i] = idx
                 key == tuple.keys[idx_pos]
                 replaced_tuple == directly_replaced[idx_pos]
             IN IF replaced_tuple = NULL
                THEN [point_holes_map[idx] EXCEPT ![key] = {}]
                ELSE point_holes_map[idx]
        ELSE point_holes_map[idx]]

\* Check for duplicates across all indexes of a space
\* directly_replaced: sequence of tuples replaced in each index
\* tuple_keys: sequence of keys corresponding to each index
CheckDup(txn, space, directly_replaced, tuple_keys, mode) ==
    LET
        indexes == spaceIndexes[space]
        primary_index == indexes[1]
        primary_key == tuple_keys[1]
        primary_tuple == directly_replaced[1]
        \* Find visible tuple for primary index
        primary_visible_result ==
            FindVisibleTuple(txn, primary_index, primary_key, primary_tuple)
        primary_visible_tuple == primary_visible_result.visible_tuple
        primary_is_own_change == primary_visible_result.is_own_change
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
            LET CheckSecondary[i \in 2..Len(indexes)] ==
                LET sec_index == indexes[i]
                    sec_key == tuple_keys[i]
                    sec_tuple == directly_replaced[i]
                    sec_visible ==
                        FindVisibleTuple(txn, sec_index, sec_key, sec_tuple).visible_tuple
                IN IF sec_visible # NULL /\ sec_visible # primary_visible_tuple
                    THEN sec_visible
                    ELSE IF i = Len(indexes)
                        THEN NULL
                        ELSE CheckSecondary[i + 1]
            IN IF Len(indexes) >= 2 THEN CheckSecondary[2] ELSE NULL
        is_duplicate == primary_is_duplicate \/ secondary_duplicate_tuple # NULL
        duplicate_tuple ==
            IF secondary_duplicate_tuple # NULL THEN secondary_duplicate_tuple
            ELSE IF primary_is_duplicate THEN primary_visible_tuple
            ELSE NULL
    IN
    [is_duplicate |-> is_duplicate,
     primary_visible_tuple |-> primary_visible_tuple,
     duplicate_tuple |-> duplicate_tuple,
     is_own_change |-> primary_is_own_change]

InsertReplace(txn, space, tuple, tuple_id, mode) ==
    LET
        indexes == spaceIndexes[space]
        primary_index == indexes[1]
        \* Extract primary key from tuple.keys
        key == tuple.keys[1]
        \* Build directly_replaced sequence: tuple replaced in each index by corresponding key
        directly_replaced ==
            [i \in 1..Len(indexes) |->
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
        \* Prepare new entities
        new_story == IF ~is_duplicate THEN nextStoryId ELSE NULL
        new_stmt == IF ~is_duplicate THEN nextStmtId ELSE NULL
    IN
    /\ IF ~is_duplicate
       THEN \* No duplicate - proceed with insertion/replacement
            /\ allStmts' = allStmts \cup {new_stmt}
            /\ nextStmtId' = nextStmtId + 1
            /\ txns' = TxnAddStmt(txns, txn, new_stmt)
            /\ stmts' = CreateStmt(stmts, new_stmt, txn, space, new_story, primary_visible_story, is_own_change)
            /\ allStories' = allStories \cup {new_story}
            /\ nextStoryId' = nextStoryId + 1
            /\ LET created_story == CreateStory(stories, new_story, new_stmt, tuple_id, primary_index, space)
                   linked_story == StoryLinkDeletedBy(created_story, primary_visible_story, new_stmt)
                   updated_stories == CopyPointHolesToGapTrackers(linked_story, new_story, pointHoles, space, tuple, directly_replaced)
                   copied_trackers == CopyGapTrackersToNewTop(updated_stories, new_story, directly_replaced_stories)
                   cleared_trackers == ClearGapTrackers(copied_trackers, directly_replaced_stories)
               IN stories' = IF ~is_own_change /\ mode = "INSERT"
                            THEN \* Track gap for new story (inserting into gap)
                                 AddGapTracker(cleared_trackers, new_story, 1, txn)
                            ELSE cleared_trackers
            /\ history' = [history EXCEPT ![tuple_id] = new_story]
            \* Update story chains for all indexes in the space
            /\ storyChains' = StoryChainAppend(storyChains, space, tuple, new_story)
            \* Update index state for all indexes
            /\ indexState' = IndexReplace(indexState, space, tuple, tuple_id)
            \* Clear point holes for all indexes
            /\ pointHoles' = ClearPointHoles(pointHoles, space, tuple, directly_replaced)
       ELSE \* Duplicate found - track read for duplicate tuple
            /\ IF duplicate_tuple # NULL
               THEN LET duplicate_story == history[duplicate_tuple]
                    IN stories' = AddReadTracker(stories, duplicate_story, txn)
               ELSE stories' = stories
            /\ UNCHANGED <<allStories, nextStoryId, allStmts, nextStmtId, history, stmts, storyChains, indexState, txns, pointHoles>>
    /\ UNCHANGED <<nextPSN, nextTxnId, allTxns, spaceIndexes>>

\* Action: Read (get) operation
Get(txn, index, key) ==
    /\ IsInProgress(txn) \/ IsInReadView(txn)
    /\ index \in Index
    /\ key \in Key
    /\ LET tuple == IndexGetTuple(index, key)
           visible_result == FindVisibleTuple(txn, index, key, tuple)
       IN
       IF visible_result.visible_tuple # NULL
       THEN \* Found visible tuple - track read
            LET visible_story == history[visible_result.visible_tuple]
            IN stories' = AddReadTracker(stories, visible_story, txn)
            /\ pointHoles' = pointHoles
       ELSE \* Nothing found - create point hole
            pointHoles' = [pointHoles EXCEPT
                          ![index][key] = pointHoles[index][key] \cup {txn}]
            /\ stories' = stories
    /\ UNCHANGED <<txns, storyChains, stmts, indexState, tuples, history,
                  nextTxnId, nextStmtId, nextStoryId, nextTupleId, nextPSN,
                  allStories, allTxns, allStmts, spaceIndexes>>

\* Next state relation
Next ==
    \/ BeginTxn
    \/ \E txn \in allTxns, space \in Space, keys \in UNION {[1..i -> Key] : i \in 1..MaxIndexesPerSpace}, mode \in {"INSERT", "REPLACE"} :
       LET tuple == [keys |-> keys]
           new_tuple_id == nextTupleId
       IN /\ nextTupleId' = nextTupleId + 1
          /\ tuples' = [tuples EXCEPT ![new_tuple_id] = tuple]
          /\ InsertReplace(txn, space, tuple, new_tuple_id, mode)
    \/ \E txn \in allTxns, index \in Index, key \in Key :
       Get(txn, index, key)
    \* TODO: Add other actions when implemented
    \* \/ \E txn \in allTxns, space \in Space, index \in Index, key \in Key :
    \*    Delete(txn, space, index, key)
    \* \/ \E txn \in allTxns : PrepareTxn(txn)
    \* \/ \E txn \in allTxns : CommitTxn(txn)
    \* \/ \E txn \in allTxns : RollbackTxn(txn)

\* Specification
Spec == Init /\ [][Next]_<<txns, storyChains, stories, stmts,
                      pointHoles, indexState, tuples, history, nextTxnId, nextStmtId,
                      nextStoryId, nextTupleId, nextPSN, allStories, allTxns, allStmts>>

THEOREM Spec => []Invariants

\* WARNING: This specification does NOT verify serializability!
\* It only verifies structural invariants (Property 1-9).
===============================================================================
