/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RuZUnip
import AlgMag.Reductive.T2Proof
import TauCeti.Algebra.AlgebraicGroup.Solvable.Reductive
import TauCeti.Algebra.AlgebraicGroup.Reductive.AlgebraicallyClosed

/-!
# Item 4 of run 2's list: T2 from `R_u(G) ⊆ R_u(Z(μ))`

If `Ru ⊥ ≤ Ru (Z μ)` for every cocharacter `μ` of `T` (the output of (c)+(d), `ruZ_le_ruG`),
then `hT2` of `condI_condII_condIII_of_reductive_classical` holds:

* `Z = G^{ℤδ} = Z(μ)` for a suitable `μ` (`magnetIdeal_lineMagnet_eq_levi`);
* `R_u(G) = 1` (reductive) gives `R_u(Z) = 1`, so `Z` (smooth, connected) is reductive;
* if `Z(k)` were solvable, `Z` would be commutative (`isCocomm_of_geometricallySolvable`), so
  both parabolics `P_Z(λ^{±1})` are `Z`, contradicting `parZ_ne_of_root`.
-/

suppress_compilation
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Magnetism TauCeti TauCeti.Cocharacter AlgMag.Weyl CategoryTheory

namespace AlgMag.Reductive.T2Solv

open AlgMag.Reductive AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorelRouteReal
  AlgMag.Reductive.T2Classical R1Build R1Dis

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-- For a commutative group every dynamic parabolic is everything. -/
theorem parabolicDefiningHopfIdeal_eq_bot_of_isCocomm {Z : Type u} [CommRing Z]
    [HopfAlgebra k Z] [Coalgebra.IsCocomm k Z] (l : Z →ₐc[k] LaurentPolynomial k) :
    parabolicDefiningHopfIdeal l = ⊥ := by
  have h := TauCeti.Cocharacter.parabolic_eq_top (A := Z) (l := l)
  have hg : (WithConv.toConv (AlgHom.id k Z) : HopfAlgebra.points (R := k)
      (H := _root_.CommHopfAlgCat.of k Z) (CommAlgCat.of k Z)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k Z)
        (parabolicDefiningHopfIdeal l) (CommAlgCat.of k Z) := by
    rw [TauCeti.Cocharacter.quotientPointsSubgroup_parabolicDefiningHopfIdeal, h]
    trivial
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have := hg x hx
    simpa using this
  · simp at hx
    rw [hx]
    exact (parabolicDefiningHopfIdeal l).toIdeal.zero_mem

/-- `R_u(G) = 1` and `R_u(G) ⊆ R_u(V(S))` give `R_u(V(S)) = 1`. -/
theorem ru_quot_eq_aug (hred : reductiveCommHopfAlgProperty k Hf) (S : HopfIdeal k H)
    (h : Ru (⊥ : HopfIdeal k H) ≤ Ru S) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (FiniteTypeCommHopfAlgCat.quotient Hf S) =
      HopfIdeal.augmentation k (FiniteTypeCommHopfAlgCat.quotient Hf S) := by
  have hr0 : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient Hf ⊥) :=
    (reductiveCommHopfAlgProperty k).prop_of_iso
      (FiniteTypeCommHopfAlgCat.quotientBotIso Hf).symm hred
  have h0 : Ru (⊥ : HopfIdeal k H) = HopfIdeal.augmentation k H := by
    rw [Ru, hr0.unipotentRadicalDefiningIdeal_eq_augmentation,
      HopfIdeal.comapOfSurjective_augmentation]
  refine le_antisymm (HopfIdeal.le_augmentation _ _ _) ?_
  apply HopfIdeal.le_of_comapOfSurjective_le_comapOfSurjective _
    (Bialgebra.Quotient.mkBialgHom_surjective S.toIdeal)
  rw [HopfIdeal.comapOfSurjective_augmentation, ← h0]
  exact h

/-- **T2 from `R_u(G) ⊆ R_u(Z(μ))`** (instance form). -/
theorem not_isSolvable_of_ru [Algebra.Smooth k H] [ConnectedSpace (PrimeSpectrum H)]
    [IrreducibleSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    (π : H →ₐc[k] MonoidAlgebra k X) (hred : reductiveCommHopfAlgProperty k Hf)
    (hRu : ∀ μ : X →* Multiplicative ℤ, Ru (⊥ : HopfIdeal k H) ≤ Ru (Z (π.cocharacter μ)))
    (δ : Additive X) (hδ0 : δ ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ)
    (hroot : ∃ α ∈ roots π, α ∈ lineMagnet δ) :
    ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k)) := by
  intro hsolv
  obtain ⟨α, hα, hαδ⟩ := hroot
  -- `Z = Z(μ)`
  set R := {β | β ∈ roots π ∧ ¬ ∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ}
  have hR : R.Finite := (roots_finite π).subset fun β hβ => hβ.1
  obtain ⟨ψ, μ, hψδ, hμδ, hμR⟩ := exists_perp_cocharacter hδ0 R hR
    (fun β hβ m n hn h => hβ.2 ⟨m, n, hn, h⟩)
  have hgen : ∀ β ∈ roots π, pairingHom μ β = 0 → β ∈ lineMagnet δ := by
    intro β hβ h0
    by_cases hr : ∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ
    · exact hRay β hβ hr
    · exact absurd h0 (hμR β ⟨hβ, hr⟩)
  have heq : magnetHopfIdeal π (lineMagnet δ) = Z (π.cocharacter μ) := by
    ext x
    rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal, magnetHopfIdeal_toIdeal,
      magnetIdeal_lineMagnet_eq_levi π hμδ hgen]
  have hrad := ru_quot_eq_aug hred _ (heq ▸ hRu μ)
  -- `Z` is reductive
  have hconn : ConnectedSpace (PrimeSpectrum (ZAlg π δ)) :=
    connectedSpace_lineAttractor π hδ0 hRay
  have hgc : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)).obj :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).2 hconn
  haveI : Algebra.Smooth k (ZAlg π δ) := smooth_quotient_magnetHopfIdeal π _
  haveI : IsReduced (ZAlg π δ) := isReduced_of_smooth k (ZAlg π δ)
  have hZred : reductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient Hf (magnetHopfIdeal π (lineMagnet δ))) :=
    (reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation k _).2
      ⟨inferInstanceAs (Algebra.Smooth k (ZAlg π δ)), hgc, hrad⟩
  have hgeo : geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)).obj :=
    (geometricallySolvablePointsCommHopfAlgProperty.iff_exists_derivedSeriesDefiningIdeal_eq_augmentation
      (FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)).obj).mpr
      ((FiniteTypeCommHopfAlgCat.of k (ZAlg π δ)).obj.isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation.mp
        hsolv)
  haveI : Coalgebra.IsCocomm k (ZAlg π δ) := hZred.isCocomm_of_geometricallySolvable hgeo
  have hα0 : α ≠ 0 := ne_zero_of_mem_roots hα
  exact parZ_ne_of_root π δ ψ ((mem_tangentWeights_iff_mem_roots hα0).2 hα) hαδ
    (pairingHom_ne_zero_of_mem_lineMagnet ψ hα0 hαδ hψδ)
    ((parabolicDefiningHopfIdeal_eq_bot_of_isCocomm _).trans
      (parabolicDefiningHopfIdeal_eq_bot_of_isCocomm _).symm)

/-- **`hT2` of `condI_condII_condIII_of_reductive_classical`**, in its exact form, from
`R_u(G) ⊆ R_u(Z(μ))` for all cocharacters `μ` of `T`. -/
theorem hT2_of_ru [Module.IsTorsionFree ℤ (Additive X)]
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hRu : ∀ μ : X →* Multiplicative ℤ, Ru (⊥ : HopfIdeal k H) ≤ Ru (Z (π.cocharacter μ))) :
    letI : Algebra.Smooth k H := hred.smooth
    ∀ δ : Additive X, δ ≠ 0 →
      (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
      (∃ α ∈ roots π, α ∈ lineMagnet δ) →
      ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k)) := by
  letI : Algebra.Smooth k H := hred.smooth
  have : Algebra.FiniteType k (MonoidAlgebra k X) :=
    Algebra.FiniteType.of_surjective π.toAlgHom hπ
  haveI : Monoid.FG X := MonoidAlgebra.fg_of_finiteType (R := k)
  haveI : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : Module.Finite ℤ (Additive X) :=
    Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2
      (Monoid.fg_iff_add_fg.1 inferInstance))
  haveI : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  haveI : ConnectedSpace (PrimeSpectrum H) :=
    connectedSpace_of_geometricallyConnected k H hred.geometricallyConnected
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  exact fun δ hδ0 hRay hroot => not_isSolvable_of_ru π hred hRu δ hδ0 hRay hroot

end AlgMag.Reductive.T2Solv

#print axioms AlgMag.Reductive.T2Solv.hT2_of_ru
