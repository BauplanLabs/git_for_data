# Git for Data

A collection of "Git-for-Data" snippets, models, and resources.

## Overview

This repository contains a collection of code snippets, models, and resources related to "Git-for-Data," (roughly understood as) the idea that we should treat data assets similarly to how we treat code assets in software development.

In particular, it explores the idea of applying Git-like version control concepts to data management, in the context of modern cloud lakehouses — with a special focus on agentic workloads, coding agents, and the broader question of how data systems should behave when the primary "user" is an autonomous agent rather than a human (e.g. [Building a Correct-by-Design Lakehouse](https://arxiv.org/abs/2602.02335) and [Trustworthy AI in the Agentic Lakehouse](https://arxiv.org/abs/2511.16402)), on top of open formats such as [Apache Iceberg](https://iceberg.apache.org/).

Of course, "Git-for-Data" per se is not a new phrase, and a quick Google search highlights a few existing projects. Aside from high-level similarities, however, they all differ in scope, implementation, and intended usage: one of the main motivations for this project is to provide a precise definition of fuzzy concepts, and promote a more formal, shared understanding of the core primitives of a data management system built around "version control."

## Formal modeling: a guided tour

We model Bauplan's Git-for-Data semantics in [Alloy 6](https://alloytools.org/), building progressively. Each stage adds one concept and either proves an invariant or surfaces a counterexample. Run them in order:

1. [`01_commits_and_branches.als`](./src/alloy/01_commits_and_branches.als) — snapshots, commits, branches. Lifts Iceberg snapshots to lakehouse-wide commits; branches as movable pointers; per-table revert. Asserts acyclicity, commit immutability, branch isolation.

2. [`02_merges.als`](./src/alloy/02_merges.als) — fast-forward and 3-way merge. Without the conflict-free guard, Alloy finds a trace where one side's write is silently overwritten; with it, the counterexample disappears.

3. [`03_transactions.als`](./src/alloy/03_transactions.als) — pipelines as atomic publish. A naive run on `Main` that fails mid-way leaves Main half-written; wrapping the run in a temp branch and merging on success keeps Main consistent.

4. [`04_unintended.als`](./src/alloy/04_unintended.als) — the first unintended model. Even with the transactional wrapper, a *second actor* can fork off the aborted commit of a failed run and merge it into `Main`. Branches are too permissive an abstraction for transactional pipelines.

5. [`05_revert_corruption.als`](./src/alloy/05_revert_corruption.als) — the second unintended model. Transactional pipeline + per-table revert: each is individually safe, but a user can revert one table from a multi-table run, leaving Main in a state no run could have produced.

## Previous iterations: the original blog series

The two-part blog series — [Part 1](https://www.bauplanlabs.com/post/git-for-data-formal-semantics-of-branching-merging-and-rollbacks-part-1) and [Part 2](https://www.bauplanlabs.com/post/git-for-data-formal-semantics-part-2-branching-merging-and-rollbacks) — preceded the latest models above:

- **Part 1**'s original model still lives at [`src/blog_series/part1/alloy/gsd.als`](./src/blog_series/part1/alloy/gsd.als). The SDK example is preserved at [`src/blog_series/part1/bpln/commit_api.py`](./src/blog_series/part1/bpln/commit_api.py); a newer, more comprehensive walkthrough is available [here](https://github.com/BauplanLabs/bauplan/tree/main/examples/learn/05-advanced-git-for-data).
- **Part 2** is best understood as the combination of stages 3 (transactional pipelines) and 4 (the nested-branch unintended model).

## Bugbash slides

The talk slides are in [`bugbash/bugbash_seminar_slides.pdf`](./bugbash/bugbash_seminar_slides.pdf), and the seminar handout is in [`bugbash/bugbash_seminar_handout_2026.pdf`](./bugbash/bugbash_seminar_handout_2026.pdf). The talk was delivered at the [Bugbash conference 2026](https://antithesis.com/bugbash/conference2026/).

## Running the models

### Setup

- Alloy ships as a self-contained executable: you can download it [here](https://alloytools.org/download.html). The code in this repo has been written and tested with Alloy 6.2.0. To learn more about Alloy, you can check out the [official book](https://alloytools.org/book.html).
- Get a Bauplan sandbox account [here](https://accounts.bauplanlabs.com/sign-up): follow the instructions to create an API key and install the CLI / SDK.

### How to run the Alloy models

**GUI (recommended for visualizing traces):** open any `src/alloy/*.als` file in Alloy Analyzer 6, then execute each `check` and `run` from the Execute menu. Each file's header says what to expect.

**Headless:**
```
java -Dsat4j=yes -cp /path/to/org.alloytools.alloy.dist.jar \
     edu.mit.csail.sdg.alloy4whole.SimpleCLI src/alloy/01_commits_and_branches.als
```

`SAT` = instance found (run produced a trace, or assertion has a counterexample).
`UNSAT` = no instance (assertion holds within scope, or run is over-constrained).

## Acknowledgements

Our interest in "Git-for-Data" started at the very beginning of Bauplan, given our focus on [reproducible data pipelines](https://arxiv.org/pdf/2404.13682). However, we would not have been able to reach such a maturity without our 2025 summer interns: Manuel Barros (CMU), Jinlang Wang (University of Wisconsin–Madison), Weiming Sheng (Columbia), who did fantastic work in exploring both the formal semantics and the Alloy implementation of these concepts.
