/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The size hypothesis `#M < B.cutoff`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). The paper takes `M` finitely generated
(or countable) so that the affine schemes `Spec R[M]` used in its proofs are objects of the big fppf
site `B`. Membership in the site depends only on `#M < B.cutoff`; this file provides
`contains_addMonoidAlgebra` and the instances `fact_cutoff_of_fg`, `fact_cutoff_of_countable` and
`fact_cutoff_sub`, so that statements with `[Fact (Cardinal.mk M < B.cutoff)]` apply to finitely
generated and to countable `M`, and to submonoids.
-/

open AlgebraicGeometry

universe u

namespace AlgMag

variable {B : BigFppfSite.{u}}

/-- Size: `Spec R` lies in the site if and only if `#R` is below the cutoff. -/
lemma contains_iff_card {R : Type u} [CommRing R] :
    B.Contains (Spec (.of R)) ↔ Cardinal.mk R < B.cutoff := by
  have e : Cardinal.mk (Γ(Spec (CommRingCat.of R), ⊤)) = Cardinal.mk R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.cardinal_eq
  constructor
  · intro h₁
    rw [BigFppfSite.Contains, Scheme.size_of_isAffine, e] at h₁
    exact (le_max_right _ _).trans_lt h₁
  · intro h
    rw [BigFppfSite.Contains, Scheme.size_of_isAffine, e]
    exact max_lt B.aleph0_lt_cutoff h

/-- Size: `Spec R[P]` lies in the site when `Spec R` does and `#P` is below the cutoff. -/
lemma contains_addMonoidAlgebra {R P : Type u} [CommRing R] [AddCommMonoid P]
    (hP : Cardinal.mk P < B.cutoff) (hR : B.Contains (Spec (.of R))) :
    B.Contains (Spec (.of (AddMonoidAlgebra R P))) := by
  refine contains_iff_card.2 ?_
  have e : Cardinal.mk (AddMonoidAlgebra R P) ≤ Cardinal.mk (P →₀ R) :=
    Cardinal.mk_le_of_injective (f := fun x : AddMonoidAlgebra R P => x.coeff) (fun x y h => by
      ext m
      exact DFunLike.congr_fun h m)
  have ha := B.aleph0_lt_cutoff
  have hR' := contains_iff_card.1 hR
  have h₁ : Cardinal.mk (P →₀ R) ≤ Cardinal.mk (Finset (P × R)) := by
    classical
    exact Cardinal.mk_le_of_injective (Finsupp.graph_injective P R)
  refine e.trans_lt (h₁.trans_lt ?_)
  by_cases hf : Finite (P × R)
  · have : Finite (Finset (P × R)) := inferInstance
    exact (Cardinal.lt_aleph0_of_finite _).trans ha
  · have : Infinite (P × R) := not_finite_iff_infinite.1 hf
    rw [Cardinal.mk_finset_of_infinite, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt ha.le hP hR'

/-- A finitely generated additive monoid is countable. -/
lemma countable_of_addMonoid_fg (M : Type*) [AddMonoid M] [h : AddMonoid.FG M] : Countable M := by
  obtain ⟨s, hs, φ, hφ⟩ := AddMonoid.fg_iff_exists_freeAddMonoid_hom_surjective.mp h
  have : Countable s := hs.to_subtype.to_countable
  exact hφ.countable

/-- The cutoff hypothesis `#M < B.cutoff` holds for `M` countable. -/
instance fact_cutoff_of_countable {M : Type u} [Countable M] : Fact (Cardinal.mk M < B.cutoff) :=
  ⟨Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff⟩

/-- The cutoff hypothesis `#M < B.cutoff` holds for `M` finitely generated. -/
instance fact_cutoff_of_fg {M : Type u} [AddMonoid M] [AddMonoid.FG M] :
    Fact (Cardinal.mk M < B.cutoff) :=
  haveI := countable_of_addMonoid_fg M
  ⟨Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff⟩

/-- A submonoid inherits the cutoff hypothesis. -/
instance fact_cutoff_sub {M : Type u} [AddMonoid M] [h : Fact (Cardinal.mk M < B.cutoff)]
    (N : AddSubmonoid M) : Fact (Cardinal.mk N < B.cutoff) :=
  ⟨(Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt h.out⟩

end AlgMag
