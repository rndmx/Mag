/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.AttractorReflects
import AlgMag.Reductive.RootSystemCombinatoricsMathlib

/-!
# Split reductive data with a root datum

`SplitReductiveData.WithRootDatum π`: split reductive data together with a Mathlib root datum
`P : RootPairing ι ℤ X N` (finite, crystallographic, reduced) and a base `b`, such that the roots
of `P` are the roots of `G` and the Weyl group of `P` acts on `X` as `W`.

`WithRootDatum.bijOn_parabolic`: **Theorem `thm:red-parabolic` for `G`**: `N ↦ N ∩ Φ` is a
bijection from the pure magnets of `G` containing a basis `wB` onto the parabolic subsets of
`Φ` (closed, `R ∪ -R = Φ`), inverse `R ↦ [R⟩`. The only input is `ReductiveInput`
(Theorem `thm:red-pure`).
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv Set

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- Split reductive data with a compatible root datum. -/
structure SplitReductiveData.WithRootDatum (π : H →ₐc[k] MonoidAlgebra k X) extends
    SplitReductiveData π where
  /-- Index set of the roots. -/
  ι : Type u
  [finite_ι : Finite ι]
  /-- The coweight lattice. -/
  N : Type u
  [addCommGroup_N : AddCommGroup N]
  /-- The root datum on `X`. -/
  P : RootPairing ι ℤ (Additive X) N
  [crystallographic : P.IsCrystallographic]
  [reduced : P.IsReduced]
  /-- A base. -/
  b : P.Base
  /-- The roots of `P` are the roots of `G`. -/
  range_root : range P.root = roots π
  /-- The Weyl group of `P` acts on `X` as `W`. -/
  weyl_eq : range (fun g : P.weylGroup => RootSystem.RootDatum.act P g) =
    range (fun w : W => actW (w : X ≃* X))

lemma reductiveHull_mono_of_range {M : Type*} [AddCommGroup M] {Φ : Set M} {W₁ W₂ : Type*}
    {act₁ : W₁ → M →+ M} {act₂ : W₂ → M →+ M} (h : range act₁ ⊆ range act₂)
    (N : AddSubmonoid M) : Rooted.reductiveHull Φ act₁ N ≤ Rooted.reductiveHull Φ act₂ N := by
  refine sup_le_sup le_rfl (iSup₂_le fun w hw => ?_)
  obtain ⟨w', hw'⟩ := h ⟨w, rfl⟩
  have hw2 : Rooted.weylMagnet (act₂ w') ≤ N := by rw [hw']; exact hw
  rw [← hw']
  exact le_iSup₂ (f := fun w (_ : w ∈ {w | Rooted.weylMagnet (act₂ w) ≤ N}) =>
    Rooted.weylMagnet (act₂ w)) w' hw2

/-- `reductiveHull` only depends on the set of maps `{act w}`. -/
lemma reductiveHull_congr {M : Type*} [AddCommGroup M] {Φ : Set M} {W₁ W₂ : Type*}
    {act₁ : W₁ → M →+ M} {act₂ : W₂ → M →+ M} (h : range act₁ = range act₂)
    (N : AddSubmonoid M) : Rooted.reductiveHull Φ act₁ N = Rooted.reductiveHull Φ act₂ N :=
  le_antisymm (reductiveHull_mono_of_range h.le N) (reductiveHull_mono_of_range h.ge N)

lemma reductiveInput_congr {M : Type*} [AddCommGroup M] {Φ : Set M} {W₁ W₂ : Type*}
    {act₁ : W₁ → M →+ M} {act₂ : W₂ → M →+ M} (h : range act₁ = range act₂)
    {Q : AddSubmonoid M → Prop} (H : Rooted.ReductiveInput Q Φ act₂) :
    Rooted.ReductiveInput Q Φ act₁ where
  pure_iff N := by rw [reductiveHull_congr h]; exact H.pure_iff N
  hull_pure N := by rw [reductiveHull_congr h]; exact H.hull_pure N

namespace SplitReductiveData.WithRootDatum

variable {π : H →ₐc[k] MonoidAlgebra k X} (D : SplitReductiveData.WithRootDatum π)

attribute [instance] finite_ι addCommGroup_N crystallographic reduced

/-- **Theorem `thm:red-parabolic` for `G`**, for any pure-magnet predicate `Q` satisfying
`ReductiveInput` for the Weyl action of `W` on `X`. -/
theorem bijOn_parabolic {Q : AddSubmonoid (Additive X) → Prop}
    (H : Rooted.ReductiveInput Q (roots π) (fun w : D.W => actW (w : X ≃* X))) :
    Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | Q N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} ∧
      Set.InvOn AddSubmonoid.closure
        (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | Q N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} := by
  have H' := reductiveInput_congr D.weyl_eq H
  rw [← D.range_root] at H' ⊢
  exact RootSystem.RootDatum.bijOn_parabolic_rootPairing D.P D.b H'

/-- **Theorem `thm:red-parabolic` for the pure magnets of `G`** (`G^N = affineY N`). -/
theorem bijOn_parabolic_pure
    (H : Rooted.ReductiveInput (IsPure (affineY (torusGrading π))) (roots π)
      (fun w : D.W => actW (w : X ≃* X))) :
    Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} ∧
      Set.InvOn AddSubmonoid.closure
        (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} :=
  D.bijOn_parabolic H

end SplitReductiveData.WithRootDatum

end AlgMag.Reductive
