/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Ring step of Lemma 1.1 of `notes/thm153-wall.md` (Theorem 15.3, `M^gp` not finitely generated)

For `δ : P → Γ` and `Γ = ⋃ Γ_α` (finitely generated subgroups), `R[P] = ⋃ R[δ⁻¹ Γ_α]`: every finite
subset of `R[P]` lies in `R[δ⁻¹ Γ_α]` for one finitely generated `Γ_α`. This is the presentation
`A(P)_T = lim A(δ⁻¹ Γ_α)_T` used with the limit preservation of `X` (Tag 049J).
-/

namespace AlgMag.NonFG

variable {R P Γ : Type*} [CommRing R] [AddCommMonoid P] [AddCommGroup Γ]

/-- Every finite subset of `R[P]` has all its degrees in `δ⁻¹ Γ_α` for a finitely generated
subgroup `Γ_α`. -/
theorem exists_fg_subgroup (δ : P →+ Γ) (s : Finset (AddMonoidAlgebra R P)) :
    ∃ G : AddSubgroup Γ, G.FG ∧ ∀ x ∈ s, ∀ p ∈ x.coeff.support, δ p ∈ G := by
  classical
  let t : Finset Γ := (s.biUnion fun x => x.coeff.support).image δ
  refine ⟨AddSubgroup.closure (t : Set Γ), ⟨t, rfl⟩, fun x hx p hp => ?_⟩
  refine AddSubgroup.subset_closure ?_
  simp only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion]
  exact ⟨p, ⟨x, hx, hp⟩, rfl⟩

/-- An element of `R[P]` with degrees in a submonoid `Q` comes from `R[Q]`. -/
theorem mem_range_of_support {Q : AddSubmonoid P} (x : AddMonoidAlgebra R P)
    (hx : ∀ p ∈ x.coeff.support, p ∈ Q) :
    x ∈ RingHom.range (AddMonoidAlgebra.mapDomainRingHom R Q.subtype) := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single x]
  refine Subring.sum_mem _ fun p hp => ?_
  exact ⟨AddMonoidAlgebra.single ⟨p, hx p hp⟩ (x.coeff p), by
    simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]⟩

/-- **Ring step of Lemma 1.1** (thm153-wall.md): `R[P]` is the directed union of the
`R[δ⁻¹ Γ_α]`, `Γ_α ⊂ Γ` finitely generated. -/
theorem exists_fg_range (δ : P →+ Γ) (s : Finset (AddMonoidAlgebra R P)) :
    ∃ G : AddSubgroup Γ, G.FG ∧ ∀ x ∈ s,
      x ∈ RingHom.range (AddMonoidAlgebra.mapDomainRingHom R (G.toAddSubmonoid.comap δ).subtype) := by
  obtain ⟨G, hG, h⟩ := exists_fg_subgroup δ s
  exact ⟨G, hG, fun x hx => mem_range_of_support x fun p hp => h x hx p hp⟩

end AlgMag.NonFG

#print axioms AlgMag.NonFG.exists_fg_range
