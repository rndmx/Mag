/-
Released under Apache 2.0 license as described in the file LICENSE.
Backport (compat, not Tau Ceti code), 2026-11-10: names used by Tau Ceti 7ca783d4 that are absent or
renamed in Mathlib 16edf57. Statements and proofs copied from Mathlib 1b1ccf4 (files named below),
or aliases of the 16edf57 declarations under their old names. See TauCeti/CHANGES.md.
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.TensorProduct.Basic

/-- 1b1ccf4 `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`. -/
lemma Ideal.height_span_le_card_of_span_ne_top {R : Type*} [CommRing R] [IsNoetherianRing R]
    {s : Finset R} (ht : Ideal.span (s : Set R) ≠ ⊤) :
    (Ideal.span (s : Set R)).height ≤ s.card := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes ht
  exact (Ideal.height_mono hp.1.2).trans (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hp)

/-- 1b1ccf4 `Mathlib/RingTheory/Nakayama.lean` (16edf57: `..._jacobson_bot`, with `jacobson ⊥`). -/
theorem Submodule.eq_bot_of_le_smul_of_le_jacobson {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) (N : Submodule R M) (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ Ring.jacobson R) : N = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I N hN hIN (by rwa [Ideal.jacobson_bot])

/-- 1b1ccf4 `Mathlib/RingTheory/Nakayama.lean`. -/
theorem Submodule.le_of_le_smul_of_le_jacobson {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ Ring.jacobson R) (hNN : N' ≤ N ⊔ I • N') : N' ≤ N :=
  Submodule.le_of_le_smul_of_le_jacobson_bot hN' (by rwa [Ideal.jacobson_bot]) hNN

alias IsLocalRing.local_hom_tfae := IsLocalRing.local_hom_TFAE

alias AlgebraicGeometry.Scheme.Hom.closedPoints_subset_preimage_closedPoints :=
  AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints

alias finrank_eq_one_iff_of_ne_zero' := finrank_eq_one_iff_of_nonzero'

alias IsConcreteLE.exists_of_lt := SetLike.exists_of_lt
alias IsConcreteLE.lt_iff_le_and_exists := SetLike.lt_iff_le_and_exists
alias IsConcreteLE.not_le_iff_exists := SetLike.not_le_iff_exists

/-- 1b1ccf4 `Mathlib/RingTheory/Spectrum/Prime/Noetherian.lean`. -/
lemma IsArtinianRing.exists_notMem_forall_mem_of_ne {R : Type*} [CommRing R] [IsArtinianRing R]
    (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, IsIdempotentElem r ∧ ∀ q : Ideal R, q.IsPrime → q ≠ p → r ∈ q := by
  classical
  obtain ⟨r, hr⟩ := PrimeSpectrum.toPiLocalization_bijective.2 (Pi.single ⟨p, inferInstance⟩ 1)
  have : algebraMap R (Localization p.primeCompl) r = 1 := by
    simpa [PrimeSpectrum.toPiLocalization,
      -FaithfulSMul.algebraMap_eq_one_iff] using funext_iff.mp hr ⟨p, inferInstance⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, this]
    simp
  · apply PrimeSpectrum.toPiLocalization_bijective.injective
    simp [map_mul, hr, ← Pi.single_mul]
  · intro q hq e
    have : PrimeSpectrum.mk q inferInstance ≠ ⟨p, inferInstance⟩ := ne_of_apply_ne (·.1) e
    have : (algebraMap R (Localization.AtPrime q)) r = 0 := by
      simpa [PrimeSpectrum.toPiLocalization, this,
        -FaithfulSMul.algebraMap_eq_zero_iff] using funext_iff.mp hr ⟨q, inferInstance⟩
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, this]
    simp

/-- 1b1ccf4 `Mathlib/RingTheory/QuasiFinite/Basic.lean` (anonymous instance there). -/
instance Algebra.QuasiFinite.isArtinianRing_localization_atPrime_quotient_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] [q.IsPrime] [Algebra.QuasiFinite R S] :
    IsArtinianRing (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
  have : p.IsPrime := Ideal.isPrime_of_liesOver q p
  let r := PrimeSpectrum.primesOverOrderIsoFiber R S p (Ideal.primesOver.mk p q)
  have : q = r.1.comap Algebra.TensorProduct.includeRight := by
    rw [← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply, OrderIso.symm_apply_apply]
  let := Localization.AtPrime.algebraOfLiesOver p (r.1.comap Algebra.TensorProduct.includeRight)
  convert (Ideal.Fiber.localizationAlgEquivQuotient p r.1).toRingEquiv.isArtinianRing

open scoped TensorProduct in
/-- Backport helper (Tau Ceti 7ca783d4 uses this 1b1ccf4-or-later lemma): `map f g` after
`rTensor h` is `rTensor (f ∘ h)` after `lTensor g`. -/
theorem Algebra.TensorProduct.map_rTensor_eq_rTensor_lTensor {R A B C D M : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [AddCommMonoid M] [Module R M]
    (f : A →ₐ[R] B) (g : C →ₐ[R] D) (h : M →ₗ[R] A) (x : M ⊗[R] C) :
    Algebra.TensorProduct.map f g (h.rTensor C x) =
      (f.toLinearMap ∘ₗ h).rTensor D (g.toLinearMap.lTensor M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp
  | add x y hx hy => simp only [map_add, hx, hy]
/-! 1b1ccf4 `comap` -> `under` renames in `Mathlib/RingTheory/Ideal/GoingUp.lean`. -/
alias Ideal.IsIntegral.under_lt_under := Ideal.IsIntegral.comap_lt_comap
alias Ideal.isMaximal_under_of_isIntegral_of_isMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal

/-- 1b1ccf4 `Mathlib/RingTheory/KrullDimension/Polynomial.lean`. -/
lemma MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite {R : Type*} [CommRing R]
    [IsNoetherianRing R] {ι : Type*} [Finite ι] :
    ringKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    convert ← H using 1
    · exact ringKrullDim_eq_of_ringEquiv (MvPolynomial.renameEquiv _ e).toRingEquiv
    · rw [Nat.card_congr e]
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv,
      Polynomial.ringKrullDim_of_isNoetherianRing, IH]