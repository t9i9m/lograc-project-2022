# Priority queues in Agda

Repository for the Logika v računalništvu student projects

This repository is set up as an Agda library and it contains:

* `lograc-project.agda-lib`: the library configuration file which contains
  the list of file system paths that Agda should include

* `agda-stdlib/`: Agda standard library as a git submodule

* `agda-categories/`: Agda categories library as a git submodule

* `project/`: the top-level source code directory for the Agda code
  * `project/Simple` contains simple implementations of priority queues _without_ additional rank information: `Simple.Tree.LeftistHeap` and `Simple.List.Unordered`.
  * `project/Ranked` contains implementations of priority queues _with_ additional rank information: `Ranked.Tree.LeftistHeap` and `Ranked.Vec.Unordered`.

## Sources

- Chris Okasaki (1998). Purely Functional Data Structures. Cambridge University Press. ISBN: 0521663504

- Jan Stolarek (May 2022). Verifying weight biased leftist heaps using dependent types. URL: https://jstolarek.github.io/files/dep-typed-wbl-heaps.pdf
