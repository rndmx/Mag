/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorelRoute
import TauCeti.Algebra.AlgebraicGroup.Borel.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Borel.Radical
import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic

/-!
# A real `BorelBridge` from Tau Ceti's Borel theory

`IsBorelIn S B` := `S ≤ B`, `V(B)` Borel in `V(S)` (`IsBorelOverAlgClosed` of the quotient), and,
when `S = ⊥`, `V(B)` Borel in `G` itself.  `Ru S` := pullback of `R_u(V(S))`.

* `map_of_le`, `le_Ru`, `le_one`: proved from Tau Ceti (`IsBorelOverAlgClosed.map_of_le`,
  `le_unipotentRadicalDefiningIdeal`, `le_augmentation`).
* L1, first half (`U(μ) ⊆ B`): proved (`U_le_of_borel_le_parabolic`) from Tau Ceti's
  `IsSolvableRadicalCandidate.le_of_minimal_isBorelCandidate` applied in `V(P(μ))`, given the
  named fact `UCand μ`: `U(μ)` is a connected normal smooth solvable subgroup of `P(μ)`.
* L1, second half (`B ∩ Z(μ)` Borel of `Z(μ)`): named hypothesis `L1b`.
-/

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive.BorelRouteReal

open AlgMag.Reductive.BorelRoute

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-- The quotient map `H → H/S`. -/
noncomputable abbrev mk (S : HopfIdeal k H) := Bialgebra.Quotient.mkBialgHom (R := k) S.toIdeal

/-- `V(B)` is a Borel subgroup of `V(S)`. -/
def IsBorelIn (S B : HopfIdeal k H) : Prop :=
  S ≤ B ∧ (S = ⊥ → HopfIdeal.IsBorelOverAlgClosed k Hf B) ∧
    HopfIdeal.IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.quotient Hf S) (B.map (mk S))

/-- Pullback to `H` of the unipotent radical of `V(S)`. -/
noncomputable def Ru (S : HopfIdeal k H) : HopfIdeal k H :=
  (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
    (FiniteTypeCommHopfAlgCat.quotient Hf S)).comapOfSurjective (mk S)
    (Bialgebra.Quotient.mkBialgHom_surjective S.toIdeal)

theorem isBorelIn_bot_iff {B : HopfIdeal k H} :
    IsBorelIn ⊥ B ↔ HopfIdeal.IsBorelOverAlgClosed k Hf B := by
  refine ⟨fun h => h.2.1 rfl, fun h => ⟨bot_le, fun _ => h, h.map_of_le bot_le⟩⟩

theorem map_of_le' {S B : HopfIdeal k H} (hB : IsBorelIn ⊥ B) (hSB : S ≤ B) : IsBorelIn S B :=
  ⟨hSB, fun hS => by subst hS; exact hB.2.1 rfl, (hB.2.1 rfl).map_of_le hSB⟩

theorem le_Ru' {S B : HopfIdeal k H} (hB : IsBorelIn S B) : B ≤ Ru S :=
  (HopfIdeal.map_le_iff_le_comapOfSurjective _).1 hB.2.2.le_unipotentRadicalDefiningIdeal

/-- `U(μ)` is a connected normal smooth solvable closed subgroup of `P(μ)` (named input). -/
def UCand (μ : H →ₐc[k] LaurentPolynomial k) : Prop :=
  HopfIdeal.IsSolvableRadicalCandidate (FiniteTypeCommHopfAlgCat.quotient Hf (P μ))
    ((U μ).map (mk (P μ)))

/-- **L1, first half.** A Borel `B ⊆ P(μ)` contains `U(μ)`. -/
theorem U_le_of_borel_le_parabolic {B : HopfIdeal k H} (μ : H →ₐc[k] LaurentPolynomial k)
    (hB : HopfIdeal.IsBorelOverAlgClosed k Hf B) (hPB : P μ ≤ B) (hU : UCand μ) :
    B ≤ U μ := by
  have hq := hB.map_of_le hPB
  have h := hU.le_of_minimal_isBorelCandidate hq.2
  have h2 := HopfIdeal.comapOfSurjective_mono (mk (P μ))
    (Bialgebra.Quotient.mkBialgHom_surjective _) h
  rwa [HopfIdeal.comapOfSurjective_map_mkBialgHom hPB,
    HopfIdeal.comapOfSurjective_map_mkBialgHom
      (BialgHom.parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal μ)] at h2

/-- **L1, second half** (named): for a Borel `B ⊆ P(μ)`, `B ∩ Z(μ)` is a Borel of `Z(μ)`. -/
def L1b : Prop :=
  ∀ {B : HopfIdeal k H} (μ : H →ₐc[k] LaurentPolynomial k), IsBorelIn ⊥ B → P μ ≤ B →
    IsBorelIn (Z μ) (B ⊔ Z μ)

/-- **The real bridge.** -/
noncomputable def realBridge (hU : ∀ μ : H →ₐc[k] LaurentPolynomial k, UCand μ)
    (hL1b : L1b (k := k) (H := H)) : BorelBridge k H where
  IsBorelIn := IsBorelIn
  Ru := Ru
  one := HopfIdeal.augmentation k H
  le_one I := HopfIdeal.le_augmentation k H I
  map_of_le := map_of_le'
  le_Ru := le_Ru'
  L1 μ hB hPB := ⟨U_le_of_borel_le_parabolic μ (hB.2.1 rfl) hPB (hU μ), hL1b μ hB hPB⟩

/-- **(Bor)**, precise form (named): for `G` reductive and `ν` regular, `P(ν)` is Borel. -/
def BorHyp (C : HopfIdeal k H) : Prop :=
  reductiveCommHopfAlgProperty k Hf → ∀ ν : H →ₐc[k] LaurentPolynomial k, IsRegular C ν →
    HopfIdeal.IsBorelOverAlgClosed k Hf (P ν)

/-- `BorHyp` gives the abstract `Bor` of `BorelRoute` for the real bridge. -/
theorem bor_of_borHyp (hU : ∀ μ : H →ₐc[k] LaurentPolynomial k, UCand μ)
    (hL1b : L1b (k := k) (H := H)) {C : HopfIdeal k H} (h : BorHyp C) :
    Bor (realBridge hU hL1b) (reductiveCommHopfAlgProperty k Hf) C :=
  fun hG ν hν => isBorelIn_bot_iff.2 (h hG ν hν)

end AlgMag.Reductive.BorelRouteReal
