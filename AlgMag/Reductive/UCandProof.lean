/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorelRouteReal
import AlgMag.Reductive.ParabolicGenStep
import AlgMag.Reductive.L1bProof
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Reductive

/-!
# `UCand l`: `U(λ)` is a solvable-radical candidate of `P(λ)` (smooth `G`)

Transport Tau Ceti's `isUnipotentRadicalCandidate_unipotentDefiningHopfIdeal` (stated for a group
with `P = G`) to `V(P(λ))` with the induced cocharacter `λ̄ = parCochar λ`, using
`P(λ̄) = ⊥` (`parabolic_parCochar_eq_bot`) and `U(λ̄) = U(λ).map mk_P`.
-/

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive.UCandProof

open AlgMag.Reductive AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorelRouteReal

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [Algebra.Smooth k H]

/-- `U(λ̄) = U(λ).map mk_P` as ideals. -/
theorem map_unipotent_toIdeal [DecidableEq H] (l : H →ₐc[k] LaurentPolynomial k) :
    Ideal.map (Ideal.Quotient.mk (parabolicDefiningHopfIdeal l).toIdeal)
        (BialgHom.unipotentDefiningHopfIdeal l).toIdeal =
      (BialgHom.unipotentDefiningHopfIdeal (parCochar l)).toIdeal := by
  classical
  set f := Ideal.Quotient.mk (parabolicDefiningHopfIdeal l).toIdeal
  have hgen : ∀ h : H, f ((conjugationAlgHom l h).coeff 0 -
      algebraMap k H (Coalgebra.counit (R := k) h)) =
      (conjugationAlgHom (parCochar l) (f h)).coeff 0 -
        algebraMap k _ (Coalgebra.counit (R := k) (f h)) := by
    intro h
    have e1 := coeff_conj_parMk l h 0
    have e2 : Coalgebra.counit (R := k) (parMk l h) = Coalgebra.counit (R := k) h :=
      CoalgHomClass.counit_comp_apply (parMk l) h
    change parMk l _ = (conjugationAlgHom (parCochar l) (parMk l h)).coeff 0 -
      algebraMap k _ (Coalgebra.counit (R := k) (parMk l h))
    rw [e1, e2, map_sub]
    congr 1
  rw [BialgHom.unipotentDefiningHopfIdeal_toIdeal l,
    BialgHom.unipotentDefiningHopfIdeal_toIdeal (parCochar l), Ideal.map_sup, Ideal.map_span,
    Ideal.map_quotient_self, parabolic_parCochar_eq_bot, HopfIdeal.bot_toIdeal, bot_sup_eq,
    bot_sup_eq]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨f h, (hgen h).symm⟩
  · rintro ⟨y', rfl⟩
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y'
    exact ⟨_, ⟨h, rfl⟩, hgen h⟩

/-- `U(λ).map mk_P = U(λ̄)` as Hopf ideals. -/
theorem map_unipotent_eq [DecidableEq H] (l : H →ₐc[k] LaurentPolynomial k) :
    (U l).map (mk (P l)) = BialgHom.unipotentDefiningHopfIdeal (parCochar l) := by
  have h : ((U l).map (mk (P l))).toIdeal = _ :=
    (HopfIdeal.map_toIdeal (U l) (mk (P l))).trans (map_unipotent_toIdeal l)
  exact HopfIdeal.ext fun x => by
    rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal]
    exact Iff.of_eq (congrArg (x ∈ ·) h)

/-- **`UCand l`** for smooth `G`. -/
theorem uCand (l : H →ₐc[k] LaurentPolynomial k) : UCand (k := k) l := by
  classical
  have : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (P l)) := smooth_parQuot l
  unfold UCand
  rw [map_unipotent_eq l]
  have h := BialgHom.isUnipotentRadicalCandidate_unipotentDefiningHopfIdeal
    (H := FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) (P l))
    (parCochar l) (parabolic_parCochar_eq_bot l)
  exact h.isSolvableRadicalCandidate

/-- The real bridge with no named input left (smooth `G`). -/
noncomputable def realBridgeSmooth : BorelBridge k H :=
  realBridge (fun l => uCand l) (L1bProof.l1b fun l => uCand l)

end AlgMag.Reductive.UCandProof
