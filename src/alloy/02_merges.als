module gfd_stage2

/*
 * Stage 2 — Branches to Merges
 * ============================
 *
 * Adds fast-forward and 3-way ("smart") merge on top of stage 1.
 *
 * The micro-drama
 * ---------------
 * smartMerge is defined twice: once with the conflict-free guard
 * (smartMerge) and once without (smartMergeBuggy). Both have the same
 * per-table rule for building the new merge commit: "if b changed this
 * table, take b's snapshot, else take c's". With the guard, the rule is
 * harmless. Without the guard, Alloy finds a trace where both sides
 * modified the same table and the buggy merge silently drops c's
 * change. NoSilentOverwrite_Buggy is expected to FAIL on `check`.
 *
 * Run in Alloy Analyzer 6.1.0+ (temporal mode).
 */


/* ---------- Primitives ---------- */

sig Snapshot {}
sig Table {}

// Commits now have `set` parents (0, 1, or 2) so merge commits fit.
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


/* ---------- Observation helpers ---------- */

fun resolve[t: Table, b: Branch]: lone Snapshot {
    t.(b.commit.tables)
}

// Set of tables whose snapshot differs between commits a and b.
fun diff[a, b: Commit]: set Table {
    { t: Table | t.(a.tables) != t.(b.tables) }
}

// p is a merge-base of x and y iff it's a common ancestor and every
// other common ancestor is also an ancestor of p. (Borrowed from git.)
pred isMergeBase[p, x, y: Commit] {
    p in x.*parent & y.*parent
    all q: x.*parent & y.*parent | q in p.*parent
}

fun mergeBase[x, y: Commit]: one Commit {
    { p: Commit | isMergeBase[p, x, y] }
}


/* ---------- Actions ---------- */

pred stutter {
    Commit' = Commit
    tables' = tables
    parent' = parent
    commit' = commit
}

// Write a new snapshot for table t on branch b. (Same as stage 1.)
pred createSnapshot[b: Branch, t: Table] {
    some s: Snapshot, co: Commit' - Commit {
        no tables.s
        Commit' = Commit + co
        tables' = tables + (co -> (b.commit.tables ++ t -> s))
        parent' = parent + (co -> b.commit)
        commit' = commit ++ (b -> co)
    }
}

// Fast-forward: c must be a strict descendant of b's current commit.
// No new commit; b's pointer just jumps forward along parent.
pred fastForwardMerge[b: Branch, c: Commit] {
    c in b.commit.^(~parent)

    commit' = commit ++ (b -> c)
    Commit' = Commit
    tables' = tables
    parent' = parent
}

// 3-way merge WITH the conflict-free guard.
// Builds a fresh commit whose parents are b's current head and c.
pred smartMerge[b: Branch, c: Commit] {
    // guards: b and c have genuinely diverged
    c not in b.commit.*parent
    c not in b.commit.^(~parent)

    let p = mergeBase[b.commit, c] |
    one n: Commit' - Commit {
        Commit' = Commit + n
        parent' = parent + (n -> b.commit) + (n -> c)
        commit' = commit ++ (b -> n)

        // *** THE LOAD-BEARING LINE ***
        // refuse to merge when both sides touched the same table
        no (diff[p, b.commit] & diff[p, c])

        // old commits' table mappings are frozen
        all x: Commit, t: Table | x.tables'[t] = x.tables[t]

        // per-table reconciliation for the new commit n
        all t: Table {
            (t in diff[p, b.commit]) implies n.tables'[t] = b.commit.tables[t]
            else n.tables'[t] = c.tables[t]
        }
    }
}

// Same merge WITHOUT the conflict-free guard. Load the gun, pull the trigger.
pred smartMergeBuggy[b: Branch, c: Commit] {
    c not in b.commit.*parent
    c not in b.commit.^(~parent)

    let p = mergeBase[b.commit, c] |
    one n: Commit' - Commit {
        Commit' = Commit + n
        parent' = parent + (n -> b.commit) + (n -> c)
        commit' = commit ++ (b -> n)

        // *** guard deliberately removed ***

        all x: Commit, t: Table | x.tables'[t] = x.tables[t]

        all t: Table {
            (t in diff[p, b.commit]) implies n.tables'[t] = b.commit.tables[t]
            else n.tables'[t] = c.tables[t]
        }
    }
}


/* ---------- Trace ---------- */

fact trace {
    always (
        (some b: Branch, t: Table | createSnapshot[b, t])
        or (some b: Branch, c: Commit | fastForwardMerge[b, c])
        or (some b: Branch, c: Commit | smartMerge[b, c])
        or (some b: Branch, c: Commit | smartMergeBuggy[b, c])
        or stutter
    )
}


/* ---------- Properties ---------- */

// Carryover from stage 1: the parent graph never grows a cycle.
assert Acyclic {
    always no c: Commit | c in c.^parent
}
check Acyclic for 6 but 2 Table, 8 steps

// Carryover from stage 1: once a commit exists, its mapping is frozen.
assert CommitImmutability {
    always all c: Commit |
        c in Commit' implies c.tables = c.tables'
}
check CommitImmutability for 6 but 2 Table, 8 steps

// Guarded smart merge: every change c made to a table (relative to the
// merge base) is still visible on b in the next state.
assert NoSilentOverwrite_Guarded {
    always all b: Branch, c: Commit |
        smartMerge[b, c] implies
            let p = mergeBase[b.commit, c] |
                all t: diff[p, c] |
                    after (resolve[t, b] = t.(c.tables))
}
check NoSilentOverwrite_Guarded for 6 but 2 Table, 8 steps

// SAME PROPERTY, UNGUARDED VERSION. Expected to FAIL: Alloy should find
// a trace where both sides modified the same table and the merge drops
// c's change on the floor.
assert NoSilentOverwrite_Buggy {
    always all b: Branch, c: Commit |
        smartMergeBuggy[b, c] implies
            let p = mergeBase[b.commit, c] |
                all t: diff[p, c] |
                    after (resolve[t, b] = t.(c.tables))
}
check NoSilentOverwrite_Buggy for 6 but 2 Table, 8 steps


/* ---------- Example traces ---------- */

// 3-way merge: Main and apo both advance from the root, then Main
// merges apo in. mergeBase is the root; diffs are disjoint by table;
// the guard passes.
run ThreeWayMerge {
    some apo: Branch - Main {
        some disj t1, t2: Table {
            createSnapshot[Main, t1];
            createSnapshot[apo, t2];
            smartMerge[Main, apo.commit]
        }
    }
} for 6 but 2 Table, 5 steps

// Fast-forward: Main sits still while apo advances, then Main catches
// up by pointer-move only.
run FastForwardScenario {
    some apo: Branch - Main {
        one t: Table {
            createSnapshot[apo, t];
            fastForwardMerge[Main, apo.commit]
        }
    }
} for 5 but 1 Table, 4 steps
