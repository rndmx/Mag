# TauCeti (adapted)

This folder contains 275 Lean modules adapted from Tau Ceti
(github.com/TauCetiProject/TauCeti, commit d2083f0): the import closure needed for the
reductive-group results (Reductive.Basic, Dynamic.Parabolic, Dynamic.Tangent.Weights,
Dynamic.Diagonalizable), plus compatibility shims in `TauCeti/Compat/`.

The files were adapted to compile against Mathlib 16edf57 (the version pinned by
AxiomMath/Stacks 012108f). Per-file changes are listed in `CHANGES.md`.

License: Apache 2.0, as upstream; each file keeps its Apache-2.0 header.
The root module `TauCeti.lean` imports all of them.
