/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Opposite

/-!
# The open cell on points: injectivity of multiplication

For a cocharacter `λ` of an affine group `G` and every coefficient algebra `A`,
`U(-λ)(A) ∩ P(λ)(A) = 1` (CGP Proposition 2.1.8 (2)), so the multiplication maps
`U(-λ)(A) × P(λ)(A) → G(A)` and `U(-λ)(A) × Z(λ)(A) × U(λ)(A) → G(A)` are injective. Hence the
multiplication morphism of the open cell is a monomorphism of functors, the first step towards
CGP Proposition 2.1.8 (3).
-/

open WithConv

namespace TauCeti.Cocharacter

variable {R H A : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [CommSemiring A] [Algebra R A]
variable (l : H →ₐc[R] LaurentPolynomial R)

/-- **CGP 2.1.8 (2).** `U(-λ) ∩ P(λ) = 1` on `A`-points. -/
theorem unipotent_opposite_inf_parabolic :
    unipotent A l.oppositeCocharacter ⊓ parabolic A l = ⊥ := by
  rw [eq_bot_iff]
  intro g ⟨hu, hp⟩
  have hl : g ∈ levi A l.oppositeCocharacter := by
    rw [levi_oppositeCocharacter, ← parabolic_inf_oppositeCocharacter]
    exact ⟨hp, unipotent_le_parabolic hu⟩
  rw [← unipotent_inf_levi (A := A) (l := l.oppositeCocharacter)]
  exact ⟨hu, hl⟩

omit [Algebra R A] in
/-- In a group, if `U ⊓ P = ⊥` then `(u, p) ↦ u * p` is injective on `U × P`. -/
theorem _root_.Subgroup.mul_injective_of_inf_eq_bot {G : Type*} [Group G] {U P : Subgroup G}
    (hUP : U ⊓ P = ⊥) {u u' p p' : G} (hu : u ∈ U) (hu' : u' ∈ U) (hp : p ∈ P) (hp' : p' ∈ P)
    (h : u * p = u' * p') : u = u' ∧ p = p' := by
  have key : u'⁻¹ * u = p' * p⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * p) * p⁻¹ := by group
      _ = u'⁻¹ * (u' * p') * p⁻¹ := by rw [h]
      _ = p' * p⁻¹ := by group
  have hm : u'⁻¹ * u ∈ U ⊓ P :=
    ⟨U.mul_mem (U.inv_mem hu') hu, key ▸ P.mul_mem hp' (P.inv_mem hp)⟩
  rw [hUP, Subgroup.mem_bot, inv_mul_eq_one] at hm
  subst hm
  exact ⟨rfl, mul_left_cancel h⟩

/-- Multiplication `U(-λ)(A) × P(λ)(A) → G(A)` is injective. -/
theorem mul_injective_unipotent_opposite_parabolic
    {u u' : WithConv (H →ₐ[R] A)} {p p' : WithConv (H →ₐ[R] A)}
    (hu : u ∈ unipotent A l.oppositeCocharacter) (hu' : u' ∈ unipotent A l.oppositeCocharacter)
    (hp : p ∈ parabolic A l) (hp' : p' ∈ parabolic A l) (h : u * p = u' * p') :
    u = u' ∧ p = p' :=
  Subgroup.mul_injective_of_inf_eq_bot (unipotent_opposite_inf_parabolic l) hu hu' hp hp' h

/-- Multiplication `U(-λ)(A) × Z(λ)(A) × U(λ)(A) → G(A)` is injective. -/
theorem mul_injective_openCell
    {u u' z z' v v' : WithConv (H →ₐ[R] A)}
    (hu : u ∈ unipotent A l.oppositeCocharacter) (hu' : u' ∈ unipotent A l.oppositeCocharacter)
    (hz : z ∈ levi A l) (hz' : z' ∈ levi A l) (hv : v ∈ unipotent A l)
    (hv' : v' ∈ unipotent A l) (h : u * z * v = u' * z' * v') :
    u = u' ∧ z = z' ∧ v = v' := by
  rw [mul_assoc, mul_assoc] at h
  obtain ⟨h1, h2⟩ := mul_injective_unipotent_opposite_parabolic l hu hu'
    (Subgroup.mul_mem _ (levi_le_parabolic hz) (unipotent_le_parabolic hv))
    (Subgroup.mul_mem _ (levi_le_parabolic hz') (unipotent_le_parabolic hv')) h
  have hZU : levi A l ⊓ unipotent A l = ⊥ := by rw [inf_comm]; exact unipotent_inf_levi
  obtain ⟨h3, h4⟩ := Subgroup.mul_injective_of_inf_eq_bot hZU hz hz' hv hv' h2
  exact ⟨h1, h3, h4⟩

end TauCeti.Cocharacter
