/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import TauCeti.Algebra.AlgebraicGroup.Connected.Comultiplication
import TauCeti.Algebra.AlgebraicGroup.Connected.Translation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
import TauCeti.Algebra.AlgebraicGroup.Derived.PointClosure
import TauCeti.Topology.NoetherianSpace.ConnectedComponents
import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.Coalgebra.Cocommutative

/-!
# `ClosureInput`: some power of a `k`-point lies in a reduced commutative connected closed subgroup

Setting: `k = k̄`, `H` a finite-type Hopf algebra. Let `I₀` be the vanishing ideal of the points
`g^n` (closure of `⟨g⟩`) and `J = I₀.identityComponent`. Then

* `H ⧸ I₀` is reduced and commutative (`commutator_quotientPointsSubgroup_vanishingIdeal_le`
  plus point separation), hence so is the quotient `H ⧸ J`;
* `Spec (H ⧸ I₀)` is Noetherian so has finitely many connected components, and the points
  `g^n` fall in finitely many of them; translating by `g^{-m}` gives `N > 0` with `g^N` in the
  identity component, i.e. `g^N` vanishes on `J`.

The final theorem `closurePower` has exactly the statement of
`AlgMag.Reductive.NoTorusUnipotent.ClosureInput g` (this file does not import it, so that it can
be built independently).
-/

open WithConv TauCeti TauCeti.HopfAlgebra
open scoped TensorProduct

namespace AlgMag.Reductive.ClosurePower

universe u

/-! ### Dynamics on connected components -/

section Dynamics

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [CommRing B] [_root_.HopfAlgebra k B]
  [Algebra.FiniteType k B]

open AlgebraicGeometry in
/-- Some positive power of a `k`-point lies in the identity component, i.e. vanishes on the
identity-component Hopf ideal. -/
theorem exists_pow_vanishes_identityComponent (b : WithConv (B →ₐ[k] k)) :
    ∃ N : ℕ, 0 < N ∧
      ∀ y ∈ (identityComponentHopfIdeal (k := k) (H := B)).toIdeal, (b ^ N).ofConv y = 0 := by
  classical
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : Finite (ConnectedComponents (PrimeSpectrum B)) :=
    finite_connectedComponents_of_noetherianSpace
  let p : ℕ → PrimeSpectrum B := fun n ↦ AlgHom.kernelPoint (b ^ n).ofConv
  have key : ∀ m n : ℕ, m < n → p n ∈ connectedComponent (p m) →
      ∃ N : ℕ, 0 < N ∧ ∀ y ∈ (identityComponentHopfIdeal (k := k) (H := B)).toIdeal,
        (b ^ N).ofConv y = 0 := by
    intro m n hlt hmem
    refine ⟨n - m, Nat.sub_pos_of_lt hlt, ?_⟩
    have himg := rightTranslationHomeomorph_image_connectedComponent (k := k) (b ^ m)⁻¹ (p m)
    have h1 : rightTranslationHomeomorph (b ^ m)⁻¹ (p m) = Bialgebra.augmentationPoint k B := by
      rw [show p m = AlgHom.kernelPoint (b ^ m).ofConv from rfl,
        rightTranslationHomeomorph_kernelPoint, mul_inv_cancel]
      rfl
    have h2 : rightTranslationHomeomorph (b ^ m)⁻¹ (p n) = AlgHom.kernelPoint (b ^ (n - m)).ofConv := by
      rw [show p n = AlgHom.kernelPoint (b ^ n).ofConv from rfl,
        rightTranslationHomeomorph_kernelPoint]
      congr 3
      rw [← mul_inv_cancel_right (b ^ (n - m)) (b ^ m), ← pow_add, Nat.sub_add_cancel hlt.le]
    have hm : AlgHom.kernelPoint (b ^ (n - m)).ofConv ∈
        connectedComponent (Bialgebra.augmentationPoint k B) := by
      rw [← h2, ← h1, ← himg]
      exact ⟨_, hmem, rfl⟩
    have he := map_connectedComponentIdempotent_augmentationPoint_eq_one_of_mem
      (b ^ (n - m)) hm
    intro y hy
    rw [identityComponentHopfIdeal_toIdeal] at hy
    obtain ⟨a, rfl⟩ := PrimeSpectrum.mem_connectedComponentIdeal_iff.mp hy
    rw [map_mul, map_sub, map_one, he, sub_self, mul_zero]
  obtain ⟨m, n, hmn, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ ↦ (ConnectedComponents.mk (p n)))
  have h' : connectedComponent (p m) = connectedComponent (p n) :=
    ConnectedComponents.coe_eq_coe.mp h
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · exact key m n hlt (h' ▸ mem_connectedComponent)
  · exact key n m hlt (h' ▸ mem_connectedComponent)

end Dynamics

/-! ### Assembly -/

section Assembly

variable {k : Type u} [Field k] [IsAlgClosed k] {H : Type u} [CommRing H] [_root_.HopfAlgebra k H]
  [Algebra.FiniteType k H]

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
/-- The reduced closure of a commutative point subgroup is cocommutative. -/
theorem isCocomm_quotient_vanishingIdeal (S : Subgroup (WithConv (H →ₐ[k] k)))
    (hS : ⁅S, S⁆ = ⊥) :
    Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.vanishingIdeal S)) := by
  rw [← CommHopfAlgCat.derivedDefiningIdeal_eq_augmentation_iff_isCocomm]
  have h := CommHopfAlgCat.comapOfSurjective_derivedDefiningIdeal_quotient_vanishingIdeal_eq_vanishingIdeal_commutator
    (H := _root_.CommHopfAlgCat.of k H) S
  rw [hS, HopfIdeal.vanishingIdeal_bot, ← HopfIdeal.comapOfSurjective_augmentation
    _ (_root_.CommHopfAlgCat.mkQuotient_surjective _ _)] at h
  exact le_antisymm
    (HopfIdeal.le_of_comapOfSurjective_le_comapOfSurjective _ _ h.le)
    (HopfIdeal.le_of_comapOfSurjective_le_comapOfSurjective _ _ h.ge)

/-- **`ClosureInput`**: some positive power of a `k`-point lies in a reduced commutative
connected closed subgroup, namely `(closure ⟨g⟩)°`. Same statement as
`AlgMag.Reductive.NoTorusUnipotent.ClosureInput g`. -/
theorem closurePower (g : WithConv (H →ₐ[k] k)) :
    ∃ (J : HopfIdeal k H) (N : ℕ), 0 < N ∧ IsReduced (H ⧸ J.toIdeal) ∧
      Coalgebra.IsCocomm k (H ⧸ J.toIdeal) ∧
      geometricallyConnectedCommHopfAlgProperty k (CommHopfAlgCat.of k (H ⧸ J.toIdeal)) ∧
      ∀ y ∈ J.toIdeal, (g ^ N).ofConv y = 0 := by
  classical
  let Hc : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of k H
  let S : Subgroup (WithConv (H →ₐ[k] k)) := Subgroup.zpowers g
  have hS : ⁅S, S⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (zpow_mul_comm g n m)
  let I0 : HopfIdeal k Hc := HopfIdeal.vanishingIdeal S
  let J : HopfIdeal k Hc := I0.identityComponent
  let B := FiniteTypeCommHopfAlgCat.quotient Hc I0
  have hgI0 : ∀ y : H, y ∈ I0 → g.ofConv y = 0 := fun y hy ↦
    (HopfIdeal.mem_vanishingIdeal S y).mp hy ⟨g, Subgroup.mem_zpowers g⟩
  let b : WithConv (B →ₐ[k] k) :=
    CommHopfAlgCat.liftQuotientPoint Hc.obj I0 (CommAlgCat.of k k) g hgI0
  obtain ⟨N, hN, hb⟩ := exists_pow_vanishes_identityComponent (k := k) (B := B) b
  -- reducedness of `B` and smoothness of the identity component
  have : IsReduced B := HopfIdeal.isReduced_quotient_vanishingIdeal S
  have : Algebra.Smooth k B := (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k B.obj)
  have hsm : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient Hc J) :=
    HopfIdeal.smooth_identityComponent I0
  refine ⟨J, N, hN, ?_, ?_, HopfIdeal.geometricallyConnected_identityComponent I0, ?_⟩
  · exact (smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k
      (FiniteTypeCommHopfAlgCat.quotient Hc J).obj).mp ((smoothCommHopfAlgProperty_iff _).mpr hsm)
  · have := isCocomm_quotient_vanishingIdeal (k := k) (H := H) S hS
    exact TauCeti.Coalgebra.IsCocomm.of_surjective
      (FiniteTypeCommHopfAlgCat.toBialgHom
        (FiniteTypeCommHopfAlgCat.quotientMapOfLe Hc (HopfIdeal.le_identityComponent I0)))
      (FiniteTypeCommHopfAlgCat.quotientMapOfLe_surjective Hc _)
  · intro y hy
    have hy' := (HopfIdeal.mem_identityComponent I0 y).mp hy
    have h1 := hb _ hy'
    have h2 : CommHopfAlgCat.quotientPointsHom Hc.obj I0 (CommAlgCat.of k k) (b ^ N) = g ^ N := by
      rw [map_pow, CommHopfAlgCat.quotientPointsHom_liftQuotientPoint]
    rw [← h2, CommHopfAlgCat.quotientPointsHom_apply]
    exact h1

end Assembly

#print axioms closurePower

end AlgMag.Reductive.ClosurePower
