module gfd_stage1

/*
 * Stage 1 — Snapshots, Commits, Branches
 * ======================================
 *
 * Lift Iceberg single-table snapshots into lakehouse-wide commits,
 * introduce branches as movable pointers, and model revert as a
 * history-preserving undo.
 *
 * No merges in stage 1 — see 02_merges.als.
 *
 * Run in Alloy Analyzer 6.2.0+ (temporal mode).
 */


/* ---------- Primitives ---------- */

sig Snapshot {}
sig Table {}

// A Commit is a point-in-time mapping of tables to snapshots, plus a
// parent pointer. In stage 1 a commit has at most one parent (no merges).
var sig Commit {
    var tables: Table -> lone Snapshot,
    var parent: lone Commit
}

// A Branch is a movable pointer to a commit.
sig Branch {
    var commit: one Commit
}
one sig Main extends Branch {}


/* ---------- Initial state ---------- */

fact initialState {
    one Commit                                 // exactly one root commit
    no Commit.parent                           // root has no parent
    all t: Table | lone t.(Commit.tables)      // root maps every table to at most one snapshot
    all b: Branch | b.commit in Commit         // every branch pointer is live
}


/* ---------- Observation helpers ---------- */

// What does branch b see for table t right now?
fun resolve[t: Table, b: Branch]: lone Snapshot {
    t.(b.commit.tables)
}

// Time travel: what was table t's snapshot at commit c?
fun timeTravel[t: Table, c: Commit]: lone Snapshot {
    t.(c.tables)
}


/* ---------- Actions ---------- */

pred stutter {
    Commit' = Commit
    tables' = tables
    parent' = parent
    commit' = commit
}

// Write a new snapshot for table t on branch b. Allocates a fresh Commit
// whose tables mapping overrides t with a fresh Snapshot atom.
// Models both "create new table" and "overwrite existing table".
pred createSnapshot[b: Branch, t: Table] {
    some s: Snapshot, co: Commit' - Commit {
        no tables.s                                             // s is a fresh snapshot atom
        Commit' = Commit + co
        tables' = tables + (co -> (b.commit.tables ++ t -> s))
        parent' = parent + (co -> b.commit)
        commit' = commit ++ (b -> co)
    }
}

// Revert: create a NEW commit that re-maps table t on branch b to the
// snapshot it had at ancestor commit src. History is preserved — revert
// adds a commit, it doesn't rewrite one. Matches `client.revert_table(...)`
// in the Bauplan SDK.
pred revertTable[b: Branch, t: Table, src: Commit] {
    src in b.commit.*parent                                     // src is reachable along parent
    some t.(src.tables)                                         // t was mapped at src
    some co: Commit' - Commit {
        Commit' = Commit + co
        tables' = tables + (co -> (b.commit.tables ++ t -> t.(src.tables)))
        parent' = parent + (co -> b.commit)
        commit' = commit ++ (b -> co)
    }
}


/* ---------- Trace ---------- */

fact trace {
    always (
        (some b: Branch, t: Table | createSnapshot[b, t])
        or
        (some b: Branch, t: Table, c: Commit | revertTable[b, t, c])
        or
        stutter
    )
}


/* ---------- Properties ---------- */

// History is acyclic: no commit is its own ancestor.
assert Acyclic {
    always no c: Commit | c in c.^parent
}
check Acyclic for 5 but 2 Table, 8 steps

// Commits are immutable: once a commit exists, its table mapping never
// changes. This is the formal core of time-travel.
assert CommitImmutability {
    always all c: Commit |
        c in Commit' implies c.tables = c.tables'
}
check CommitImmutability for 5 but 2 Table, 8 steps

// And the parent pointer is equally immutable.
assert ParentImmutability {
    always all c: Commit |
        c in Commit' implies c.parent = c.parent'
}
check ParentImmutability for 5 but 2 Table, 8 steps

// At most one branch moves per step. This is the "frame condition"
// that makes branches isolated from each other.
assert BranchPointerFrame {
    always all disj b1, b2: Branch |
        b1.commit != b1.commit' implies b2.commit = b2.commit'
}
check BranchPointerFrame for 5 but 2 Table, 8 steps

// After a revert, the branch observes the ancestor snapshot.
assert RevertRestoresSnapshot {
    always all b: Branch, t: Table, src: Commit |
        revertTable[b, t, src] implies
            after resolve[t, b] = t.(src.tables)
}
check RevertRestoresSnapshot for 5 but 2 Table, 8 steps


/* ---------- Example traces ---------- */

// Two branches diverge by one commit each.
run DivergingBranches {
    some apo: Branch - Main {
        some disj t1, t2: Table {
            createSnapshot[Main, t1];
            createSnapshot[apo, t2]
        }
    }
    eventually Main.commit != (Branch - Main).commit
} for 4 but 2 Table, 4 steps

// Write a table, overwrite it, then revert to the first value.
run RevertDemo {
    one t: Table {
        createSnapshot[Main, t];
        createSnapshot[Main, t];
        some src: Commit | revertTable[Main, t, src]
    }
} for 5 but 1 Table, 5 steps
