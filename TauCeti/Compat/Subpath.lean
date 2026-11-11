/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
Adapted from Tau Ceti (github.com/TauCetiProject/TauCeti, commit d2083f0); see TauCeti/CHANGES.md
-/
import Mathlib.Topology.Subpath

/-!
# Backport (compat, not Tau Ceti code)

`Path.Homotopic.subpath_trans_subpath` and `Path.Homotopic.mk_subpath_trans_mk_subpath`, copied
verbatim from `Mathlib/Topology/Subpath.lean` at Mathlib 1b1ccf4 (absent from 16edf57, whose file
already has `Path.Homotopy.subpathTransSubpath`).
-/

open unitInterval

variable {X : Type*} [TopologicalSpace X] {a b : X}

namespace Path.Homotopic

/-- Two consecutive subpaths are homotopic to the subpath between their outer endpoints. -/
@[simp]
theorem subpath_trans_subpath (γ : Path a b) (s t u : I) :
    Homotopic ((γ.subpath s t).trans (γ.subpath t u)) (γ.subpath s u) :=
  ⟨Homotopy.subpathTransSubpath γ s t u⟩

/-- Composition of consecutive subpath classes is the class of the subpath between their outer
endpoints. -/
@[simp]
theorem mk_subpath_trans_mk_subpath (γ : Path a b) (s t u : I) :
    (Quotient.mk (γ.subpath s t)).trans (.mk (γ.subpath t u)) = .mk (γ.subpath s u) := by
  rw [← Quotient.mk_trans]
  exact Quotient.eq.mpr (Path.Homotopic.subpath_trans_subpath γ s t u)

end Path.Homotopic
