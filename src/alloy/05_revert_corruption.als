module gfd_stage5

/*
 * Stage 5 — Innocuous Primitives Compose to Corruption
 * ====================================================
 *
 * Stage 4 surfaced one unintended model (nested branches let a second
 * actor leak failed-run state to Main). The "obvious" fix — disallowing
 * forks off transactional branches — would also kill the legitimate
 * retry pattern where an agent forks off an aborted commit, fixes the
 * one bad node, and re-runs from there. That trade-off is a real open
 * question and is left as an exercise for the reader (see slides).
 *
 * This stage shows a SECOND unintended model that needs no second actor
 * and no nested branches. It uses only the transactional pipeline from
 * stage 3 AND the per-table revert from stage 1 — both individually
 * "safe" primitives — and combines them into a state on Main that no
 * pipeline run could have produced.
 *
 * Scenario:
 *   - The initial commit on Main maps t1 and t2 to old snapshots.
 *   - A pipeline run on a temp branch overwrites t1 and t2 atomically
 *     and merges into Main.
 *   - The user reverts ONLY t1 back to its initial snapshot.
 *   - Main now holds {t1: old_snapshot, t2: pipeline_snapshot}. The
 *     pipeline's atomic guarantee — "every consumer of t1 sees the same
 *     version of t1 the pipeline used to compute t2" — is broken
 *     post-hoc, by a primitive (revertTable) that touched only one table.
 *
 * Properties:
 *   check PipelineWriteAtomicityAcrossRevert      SAT (counterexample)
 *   run   RevertCorruptsMain                      SAT (explicit trace)
 *
 * Run in Alloy Analyzer 6.1.0+ (temporal mode).
 */


/* ---------- Primitives ---------- */

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


/* ---------- Initial state ---------- */

fact initialState {
    one Commit
    no Commit.parent
    all t: Table | lone t.(Commit.tables)
    all b: Branch | b.commit in Commit
}


/* ---------- Helpers ---------- */

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

// NEW in stage 5: per-table revert. Creates a new commit on b whose
// mapping for t is taken from an ancestor commit src. Other tables
// keep b's current values. (Same as stage 1, with run-state frame.)
pred revertTable[b: Branch, t: Table, src: Commit] {
    src in b.commit.*parent
    some t.(src.tables)
    some co: Commit' - Commit {
        Commit' = Commit + co
        tables' = tables + (co -> (b.commit.tables ++ t -> t.(src.tables)))
        parent' = parent + (co -> b.commit)
        commit' = commit ++ (b -> co)
    }
    Run.onBranch' = Run.onBranch
    Run.idx' = Run.idx
    Run.status' = Run.status
}


/* ---------- Pipeline / Run (same as stage 3) ---------- */

sig Pipeline { plan: seq Table }

abstract sig Status {}
one sig Pending, Running, Succeeded, Failed extends Status {}

sig Run {
    pipeline: one Pipeline,
    var onBranch: lone Branch,
    var idx: lone Int,
    var status: one Status
}

pred active[r: Run] { r.status = Running and some r.onBranch }
fun planLen[r: Run]: Int { #(r.pipeline.plan.elems) }
fun nextTable[r: Run]: lone Table { r.pipeline.plan[r.idx] }

pred beginRun[r: Run, b: Branch] {
    r.status = Pending
    no r.onBranch
    no r.idx

    r.status' = Running
    r.onBranch' = b
    r.idx' = 0

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

pred stepOK[r: Run] {
    active[r]
    some nextTable[r]
    r.idx < planLen[r]

    createSnapshot[r.onBranch, nextTable[r]]

    r.idx' = r.idx.plus[1]
    r.status' = Running
    r.onBranch' = r.onBranch

    all other: Run - r {
        other.status' = other.status
        other.onBranch' = other.onBranch
        other.idx' = other.idx
    }
}

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

pred mergeRun[r: Run, target: Branch] {
    r.status = Succeeded
    some r.onBranch
    r.onBranch != target
    merge[target, r.onBranch.commit]

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
        or (some b: Branch, t: Table, c: Commit | revertTable[b, t, c])
        or stutter
    )
}


/* ---------- The property ---------- */

// Main has tables from mixed provenance: some still match what a
// successful run wrote, others have drifted. No single pipeline run
// could have produced this state.
pred mainHasInconsistentTables {
    some r: Run, disj t1, t2: Table {
        r.status = Succeeded
        once mergeRun[r, Main]
        t1 in r.pipeline.plan.elems
        t2 in r.pipeline.plan.elems
        // Main's t1 has drifted from what r wrote, but t2 still matches
        resolve[t1, Main] != t1.(r.onBranch.commit.tables)
        resolve[t2, Main] = t2.(r.onBranch.commit.tables)
    }
}

assert PipelineWriteAtomicityAcrossRevert {
    always not mainHasInconsistentTables
}
check PipelineWriteAtomicityAcrossRevert for 6 but 2 Table, 1 Pipeline, 1 Run, 8 steps


/* ---------- Example trace ---------- */

run RevertCorruptsMain {
    some apo: Branch - Main {
        one r: Run, disj t1, t2: Table, root: Commit {
            no root.parent
            // Initial commit must map both tables (else there's nothing to revert to)
            some t1.(root.tables)
            some t2.(root.tables)
            r.pipeline.plan = 0 -> t1 + 1 -> t2

            beginRun[r, apo];
            stepOK[r];
            stepOK[r];
            finishOK[r];
            mergeRun[r, Main];
            revertTable[Main, t1, root]
        }
    }
    eventually mainHasInconsistentTables
} for 6 but 2 Table, 1 Pipeline, 1 Run, 8 steps
