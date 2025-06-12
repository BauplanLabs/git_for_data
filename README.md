# Git for Data
A collection of "git for data" snippets, models, resources

## Overview
This repository contains a collection of code snippets, models, and resources related to "git for data", (roughly understood as) the idea that we should treat data assets similarly to how we treat code assets in software development.

In particular, it explores the idea of applying git-like version control concepts to data management, in the context of modern cloud lakehouses (e.g. the [Bauplan paper](https://arxiv.org/pdf/2404.13682) on reproducible cloud pipelines) and open formats (e.g. [Apache Iceberg](https://iceberg.apache.org/)).

Of course, "git for data" per se is not a new phrase, and a quick Google search highlights a few existing projects. Aside from high-level similarities, however they all differ in scope, implementation and intended usage: one of the main motivation for this project (and therefore the content in this repository) is to provide a precise definition of fuzzy concepts, and promote a more formal, shared understanding of the core primitives of a data management system built around "version control".

## Setup

Depending on the project, you may need a few tools to run the code yourself if you wish to do so. Basic dependencies include bauplan and Alloy.

### Install Alloy

Alloy ships as a self-contained executable: you can download it [here](https://alloytools.org/download.html). The code in this repo has been written and tested with Alloy 6.2.0.

To learn more about Alloy, you can check out the [official book](https://alloytools.org/book.html).

### Get Bauplan

Get a bauplan free sandbox account [here](https://accounts.bauplanlabs.com/sign-up): follow the instructions to create an API KEY, install the CLI / SDK in a Python virtual environment and run the [tutorial](https://docs.bauplanlabs.com/en/latest/) to get acquainted with the platform.

## Content

### Blog Series

#### Git for Data: Part 1

A very simple Alloy model to demonstrate the basic interplay between table versions ("snapshots"), lakehouse "commits", and how people can collaborate through "feature branches" using git-style merges at the end.

The companion blog post (LINK TBC) discusses the different in the commit history between a three way merge and a fast-forward merge. You can reproduce the visual instances in the blog post by commenting / uncommenting `standardMerge` (you'll get [this](/src/blog_series/part1/images/3way.png)) and `ffMerge` (you'll get [this](/src/blog_series/part1/images/ff.png)) at the end of the `gsd.als` file.

The script in the `bpln` folder showcases how bauplan currently works, i.e. leveraging lakehouse management in Python, data branching, and auditability APIs to programmatically investigate the commit history through typed Python objects.

Can you spot the differences between the implementation and the formal specification?

#### Git for Data: Part 2

TBC

### Paper

TBC

## Acknowledgements

Our interest in "git-for-data" started at the very beginning of Bauplan, given our focus on [reproducible data pipelines](https://arxiv.org/pdf/2404.13682). However, we would not have been able to reach such a maturity without our 2025 summer interns: Manuel Barros (CMU), Jinlang Wang (Umadison), Weiming Sheng (Columbia), who carried out a fantastic job in exploring both the formal semantics and the Alloy implementation of these concepts.