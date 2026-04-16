module gfd_stage3

/*
 * Stage 3 — Merges to Transactions
 * =================================
 *
 * Adds Pipeline and Run on top of the stage-2 merge model. A pipeline
 * is a planned sequence of table writes; a run steps through that plan
 * one createSnapshot at a time and can succeed or fail.
 *
 * Two scenarios demonstrate the point:
 *
 *   Scenario A ("naive on Main"): run the pipeline directly on Main.
 *   If it fails mid-way, Main is left in a half-written state.
 *   check MainNeverHalfWritten_Naive  →  COUNTEREXAMPLE
 *
 *   Scenario B ("transactional"): open a temp branch, run on it,
 *   merge back on success only. If the run fails, Main is untouched.
 *   check MainNeverHalfWritten_TxBranch  →  NO COUNTEREXAMPLE
 *
 * Run in Alloy Analyzer 6.1.0+ (temporal mode).
 */


/* ---------- Primitives (same as stage 2, minus smartMergeBuggy) ---------- */

sig Snapshot {}
sig Table {}

var sig Commit {
    var tables: Table -> lone Snapshot,
    var parent: set Commit
}

sig Branch {
    var commit: one Commit
}
one sig Main extends Branch {}

fact initialState {
    one Commit
    no Commit.parent
    all t: Table | lone t.(Commit.tables)
    all b: Branch | b.commit in Commit
}

fun resolve[t: Table, b: Branch]: lone Snapshot { t.(b.commit.tables) }

fun diff[a, b: Commit]: set Table {
    { t: Table | t.(a.tables) != t.(b.tables) }
}

pred isMergeBase[p, x, y: Commit] {
    p in x.*parent & y.*parent
    all q: x.*parent & y.*parent | q in p.*parent
}

fun mergeBase[x, y: Commit]: one Commit {
    { p: Commit | isMergeBase[p, x, y] }
}


/* ---------- Low-level actions ---------- */

pred stutter {
    Commit' = Commit
    tables' = tables
    parent' = parent
    commit' = commit
    Run.onBranch' = Run.onBranch
    Run.idx' = Run.idx
    Run.status' = Run.status
}

pred createSnapshot[b: Branch, t: Table] {
    some s: Snapshot, co: Commit' - Commit {
        no tables.s
        Commit' = Commit + co
        tables' = tables + (co -> (b.commit.tables ++ t -> s))
        parent' = parent + (co -> b.commit)
        commit' = commit ++ (b -> co)
    }
}

pred fastForwardMerge[b: Branch, c: Commit] {
    c in b.commit.^(~parent)
    commit' = commit ++ (b -> c)
    Commit' = Commit
    tables' = tables
    parent' = parent
}

pred smartMerge[b: Branch, c: Commit] {
    c not in b.commit.*parent
    c not in b.commit.^(~parent)
    let p = mergeBase[b.commit, c] |
    one n: Commit' - Commit {
        Commit' = Commit + n
        parent' = parent + (n -> b.commit) + (n -> c)
        commit' = commit ++ (b -> n)
        no (diff[p, b.commit] & diff[p, c])
        all x: Commit, t: Table | x.tables'[t] = x.tables[t]
        all t: Table {
            (t in diff[p, b.commit]) implies n.tables'[t] = b.commit.tables[t]
            else n.tables'[t] = c.tables[t]
        }
    }
}

pred merge[b: Branch, c: Commit] {
    fastForwardMerge[b, c] or smartMerge[b, c]
}


/* ---------- Pipelines and Runs ---------- */

// A Pipeline is a planned sequence of tables to write.
sig Pipeline {
    plan: seq Table
}

// Status values for a Run.
abstract sig Status {}
one sig Pending, Running, Succeeded, Failed extends Status {}

// A Run steps through a Pipeline on a branch.
sig Run {
    pipeline: one Pipeline,
    var onBranch: lone Branch,
    var idx: lone Int,
    var status: one Status
}

// A run is active when it has a branch and is Running.
pred active[r: Run] { r.status = Running and some r.onBranch }

// How many steps this pipeline plans.
fun planLen[r: Run]: Int { #(r.pipeline.plan.elems) }

// The next table to write.
fun nextTable[r: Run]: lone Table { r.pipeline.plan[r.idx] }


/* ---------- Run lifecycle ---------- */

// Begin: transition Pending → Running, assign a branch.
pred beginRun[r: Run, b: Branch] {
    r.status = Pending
    no r.onBranch
    no r.idx

    // run state update
    r.status' = Running
    r.onBranch' = b
    r.idx' = 0

    // all other runs unchanged
    all other: Run - r {
        other.status' = other.status
        other.onBranch' = other.onBranch
        other.idx' = other.idx
    }

    // world unchanged
    Commit' = Commit
    tables' = tables
    parent' = parent
    commit' = commit
}

// One successful step: write the next planned table.
pred stepOK[r: Run] {
    active[r]
    some nextTable[r]
    r.idx < planLen[r]

    // write the table
    createSnapshot[r.onBranch, nextTable[r]]

    // advance index
    r.idx' = r.idx.plus[1]
    r.status' = Running
    r.onBranch' = r.onBranch

    // all other runs unchanged
    all other: Run - r {
        other.status' = other.status
        other.onBranch' = other.onBranch
        other.idx' = other.idx
    }
}

// Finish successfully: all steps done.
pred finishOK[r: Run] {
    active[r]
    r.idx = planLen[r]

    r.status' = Succeeded
    r.onBranch' = r.onBranch
    r.idx' = r.idx

    all other: Run - r {
        other.status' = other.status
        other.onBranch' = other.onBranch
        other.idx' = other.idx
    }

    Commit' = Commit
    tables' = tables
    parent' = parent
    commit' = commit
}

// Fail at any point during execution.
pred failRun[r: Run] {
    active[r]

    r.status' = Failed
    r.onBranch' = r.onBranch
    r.idx' = r.idx

    all other: Run - r {
        other.status' = other.status
        other.onBranch' = other.onBranch
        other.idx' = other.idx
    }

    Commit' = Commit
    tables' = tables
    parent' = parent
    commit' = commit
}

// Merge a run's branch into a target (only allowed when Succeeded).
pred mergeRun[r: Run, target: Branch] {
    r.status = Succeeded
    some r.onBranch
    r.onBranch != target

    merge[target, r.onBranch.commit]

    // run state unchanged
    all x: Run {
        x.status' = x.status
        x.onBranch' = x.onBranch
        x.idx' = x.idx
    }
}


/* ---------- Trace ---------- */

fact initialRunState {
    all r: Run | r.status = Pending and no r.onBranch and no r.idx
}

fact trace {
    always (
        (some r: Run, b: Branch | beginRun[r, b])
        or (some r: Run | stepOK[r])
        or (some r: Run | finishOK[r])
        or (some r: Run | failRun[r])
        or (some r: Run, b: Branch | mergeRun[r, b])
        or stutter
    )
}


/* ---------- Consistency predicate ---------- */

// A commit is "consistent with respect to run r" iff either r never
// touched it, or r completed all its planned writes and this commit
// contains all of them.
//
// For the seminar we use a simpler notion: Main is half-written if
// some run wrote to Main, failed, and Main's current commit contains
// at least one but not all planned tables.

// Did run r write table t on branch b at some point in the past?
pred wroteOnBranch[r: Run, b: Branch] {
    once (r.onBranch = b and r.status = Running)
}

// Main is half-written if some run that wrote directly on Main failed,
// AND Main has advanced past its starting point (i.e., some tables
// were actually materialized before the failure).
pred mainHalfWritten {
    some r: Run {
        r.status = Failed
        wroteOnBranch[r, Main]
        // Main's commit has changed since the run started
        some t: r.pipeline.plan.elems |
            some resolve[t, Main]
    }
}


/* ---------- Properties ---------- */

// SCENARIO A: runs happen directly on Main.
// This SHOULD FAIL — a mid-pipeline failure leaves Main half-written.
assert MainNeverHalfWritten_Naive {
    always not mainHalfWritten
}
check MainNeverHalfWritten_Naive for 6 but 2 Table, 1 Pipeline, 1 Run, 8 steps

// SCENARIO B: runs happen on a non-Main branch, merged only on success.
// This assertion restricts attention to traces where runs only begin
// on non-Main branches and only merge into Main on success.
assert MainNeverHalfWritten_TxBranch {
    (always all r: Run, b: Branch | beginRun[r, b] implies b != Main)
    implies
    always not mainHalfWritten
}
check MainNeverHalfWritten_TxBranch for 6 but 2 Table, 1 Pipeline, 1 Run, 8 steps


/* ---------- Example traces ---------- */

// Scenario A demo: run directly on Main, fail mid-way.
run NaiveRunOnMainFails {
    one r: Run, disj t1, t2: Table {
        r.pipeline.plan = 0 -> t1 + 1 -> t2
        beginRun[r, Main];
        stepOK[r];
        failRun[r]
    }
} for 6 but 2 Table, 1 Pipeline, 1 Run, 5 steps

// Scenario B demo: run on a temp branch, succeed, merge.
run TransactionalRunSucceeds {
    some apo: Branch - Main {
        one r: Run, disj t1, t2: Table {
            r.pipeline.plan = 0 -> t1 + 1 -> t2
            beginRun[r, apo];
            stepOK[r];
            stepOK[r];
            finishOK[r];
            mergeRun[r, Main]
        }
    }
} for 7 but 2 Table, 1 Pipeline, 1 Run, 7 steps
