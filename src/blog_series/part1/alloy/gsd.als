module gfd

/**
 A Snapshot represents a particular version of a Table (i.e., a schema and a set of rows).
*/
sig Snapshot {}

/**
 Table identifiers.
*/
sig Table {}

/**
 A Commit represents the state of the lakehouse in a particular point in time, mapping
tables to snapshots.  The `parent` relation maps each Commit to the parents that gave rise to it:
 - 0 parents if it is the initial commit;
 - 1 parents if it results from a Transformation;
 - 2 parents if it results from a non-fast-forward merge operation.
*/
var sig Commit {
    var tables: Table -> Snapshot,
    var parent: set Commit
}

/**
 A Branch is a movable pointer to a commit. It is automatically updated on a Transformation.
*/
sig Branch {
    var commit: one Commit
}
one sig Main extends Branch {}

// Constraints on the initial state.
fact initialState {
    one Commit // Only the initial commit exists.
    no Commit.parent // The initial commit has 0 parents.
    all t: Table | lone t.(Commit.tables) // The initial commit maps every table to *at most* one snapshot.
}

// Given a table `t` and a commit `c`, `resolve[t, c]` is the Snapshot that `t` is mapped to in Commit `c`.
fun resolve[t: Table, c: Commit]: Snapshot {
    t.(c.tables)
}

// Given a table `t` and a branch `b`, `resolve[t, b]` is the Snapshot that `t` is mapped to in the commit pointed to by `b`.
fun resolve[t: Table, b: Branch]: Snapshot {
    resolve[t, b.commit]
}

fact {
    always (
        (some b: Branch, t: Table | create[b, t])
	or
        (some b: Branch, c: Commit | merge[b, c])
        or
        stutter
    )
}

pred stutter {
    Commit' = Commit
    tables' = tables
    parent' = parent
    commit' = commit
}

// The action of creating a new table.
pred create[b: Branch, t: Table] {
    t not in b.commit.tables.Snapshot
    one s: Snapshot | createSnapshot[b, t, s]
}


/**
The `createSnapshot[b, t, s]` predicate models a generic transformation on a branch `b` that creates a new snapshot `s`
for table `t`. A new table is created if `t` was not previously mapped to any snapshot
on branch `b`.
*/
pred createSnapshot[b: Branch, t: Table, s: Snapshot] {
    one co: Commit' - Commit {
        Commit' = Commit + co
        no tables.s
        tables' = tables + (co -> (b.commit.tables ++ t -> s))
        parent' = parent + (co -> b.commit)
        commit' = commit ++ (b -> co)
    }
}

// The action of incorporating the changes in commit `c` into branch `b`.
pred merge[b: Branch, c: Commit] {
    fastForwardMerge[b, c] or smartMerge[b, c]
}

// The action of incorporating the changes in branch `c` into branch `b`.
pred merge[b, c: Branch] {
    merge[b, c.commit]
}

/**
 A fast-forward merge only needs to update the commit that `b` points to.
 Like in git, this is possible when `c` can be reached from `b` by following a linear sequence of commits 
 (i.e., when `c` is reachable from `b` in the converse of the `parent` relation).
*/
pred fastForwardMerge[b: Branch, c: Commit] {
    // The guard --- the condition for this action to happen
    c in b.commit.^(~parent)

    // The effect --- the change in the state of the system produced by this action
    commit' = commit ++ b -> c

    // The frame conditions --- what remains unchanged in the system
    Commit' = Commit
    tables' = tables
    parent' = parent
}

/**
 A merge of diverging commits. This is only possible if the sets of tables that were modified since `b` and `c` diverged from
 their most recent common ancestor are disjoint.
*/
pred smartMerge[b: Branch, c: Commit] {
    c not in b.commit.*parent
    c not in b.commit.^(~parent)
    let p = mergeBase[b.commit, c] | 
    one n: Commit' - Commit {
        Commit' = Commit + n
        commit' = commit ++ b -> n
        parent' = parent + n -> b.commit + n -> c
        no (diff[p, b.commit] & diff[p, c])
        all t: Table {
            all x: Commit | x.tables'[t] = x.tables[t]
            t in diff[p, b.commit] 
            implies n.tables'[t] = b.commit.tables[t]
            else (
                t in diff[p, c] 
                implies n.tables'[t] = c.tables[t]
                else n.tables'[t] = c.tables[t]
            )
        }
    }
}

/**
 `diff[a, b]` is the set of Tables whose snapshots differ between commits `a` and `b`.
*/
fun diff[a, b: Commit]: set Table {
    { t: Table | t.(a.tables) != t.(b.tables) }
}

/**
 `mergeBase[t, s]` is the most recent common ancestor commit (aka merge-base) of commits `t` and `s`. 
 The term is borrowed from git: https://git-scm.com/docs/git-merge-base.
*/
fun mergeBase[t, s: Commit]: one Commit {
	{ p: Commit | p.isMergeBase[t, s] }
}

/**
 `isMergeBase[p, t, s]` holds iff commit `p` is the most recent common ancestor (aka merge-base) of commits `t` and `s`.
*/
pred isMergeBase[p, t, s: Commit] {
	p in t.*parent & s.*parent
	all x: t.*parent & s.*parent | x in p.*parent
}

// this is a 3-way merge with Apo and Luca involved

run standardMerge {
    some disj apo, big: Branch, disj t1, t2: Table { 
        apo + big = Branch - Main
        create[apo, t1];
        merge[Main, apo]; 
	    create[big, t2]; 
	    merge[Main, big]
    }
} for 4 but exactly 2 Table

// this is a fast-forward merge, with only Apo involved
/**
run ffMerge {
    some apo: Branch, t1: Table { 
        apo = Branch - Main
        create[apo, t1];
        merge[Main, apo]
    }
} for 4 but exactly 1 Table
*/