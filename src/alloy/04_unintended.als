module gfd_stage4

/*
 * Stage 4 — The Unintended Model
 * ================================
 *
 * Same model as stage 3, plus two new actions:
 *   forkBranch  — point any non-Main branch at any commit
 *                 (Git's "create branch from commit" primitive)
 *   mergeBranch — a user-initiated merge, not coupled to a Run
 *
 * The assertion MainCleanFromFailedRuns asks: even if all runs go
 * through transactional branches (never on Main directly), can Main
 * still end up containing state from a run that ultimately failed?
 *
 * Stage 3 said no — a failed run never merges. But forkBranch opens
 * a loophole: a SECOND actor can branch off the aborted commit and
 * merge it into Main, because branches are just movable pointers.
 *
 * Alloy finds this in 5 steps.
 *
 * Run in Alloy Analyzer 6.1.0+ (temporal mode).
 *
 * IMPORTANT: do not use `;` to separate conjuncts inside a pred body —
 * `;` in Alloy 6 is sequential composition (`P ; Q` = `P and after Q`).
 * Use newlines or `and` for conjunction. `;` is only correct inside a
 * `run` block where you actually want to sequence actions over time.
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

// NEW in stage 4: point any non-Main branch at any commit.
pred forkBranch[nb: Branch, src: Commit] {
    nb != Main
    commit' = commit ++ (nb -> src)
    Commit' = Commit
    tables' = tables
    parent' = parent
    Run.onBranch' = Run.onBranch
    Run.idx' = Run.idx
    Run.status' = Run.status
}

// NEW in stage 4: a user-initiated merge, not coupled to any Run.
pred mergeBranch[b: Branch, c: Commit] {
    merge[b, c]
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
        or (some nb: Branch, c: Commit | forkBranch[nb, c])
        or (some b: Branch, c: Commit | mergeBranch[b, c])
        or stutter
    )
}


/* ---------- The stronger property ---------- */

// c was *produced* by r: c came into existence at a step where r
// was Running. Stricter than "branch happened to point at c" — root
// is never produced (it pre-exists), so it can't trigger a vacuous
// contamination.
pred producedByRun[c: Commit, r: Run] {
    once (c not in Commit and after (c in Commit) and r.status = Running)
}

// Main is contaminated if some commit produced by a failed run is
// reachable from Main.
pred mainContaminated {
    some r: Run, c: Commit {
        r.status = Failed
        producedByRun[c, r]
        c in Main.commit.*parent
    }
}

// Even if every run begins on a non-Main branch (the stage-3 fix),
// Main can still end up contaminated by state from a failed run.
// Expected to FAIL: a second actor forks the aborted branch and
// merges it into Main.
assert MainCleanFromFailedRuns {
    (always all r: Run, b: Branch | beginRun[r, b] implies b != Main)
    implies always not mainContaminated
}
check MainCleanFromFailedRuns for 6 but 2 Table, 1 Pipeline, 1 Run, 8 steps


/* ---------- Example trace: the nested-branch counterexample ---------- */

run NestedBranchAttack {
    some disj tx, feature: Branch - Main {
        one r: Run, t: Table {
            r.pipeline.plan = 0 -> t
            beginRun[r, tx];                      // run starts on temp branch
            stepOK[r];                            // tx advances (t materialized)
            failRun[r];                           // run fails — tx commit lingers
            forkBranch[feature, tx.commit];       // second actor forks from that commit
            mergeBranch[Main, feature.commit]     // second actor merges to Main
        }
    }
    eventually mainContaminated
} for 7 but 1 Table, 1 Pipeline, 1 Run, 7 steps
