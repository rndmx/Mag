/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.OpenCell.HopfKaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat

/-!
# A connected affine group with zero Lie algebra is trivial

Over an algebraically closed field `k`, let `A` be a finite-type commutative Hopf algebra with
zero cotangent space at the unit and connected spectrum. Then `A = k`.

Proof: `Ω[A⁄k] ≃ A ⊗ ω = 0` (invariant differentials, `AlgMag.OpenCellNotes.kaehlerEquivInv`),
so `A` is unramified, hence étale over `k`, hence `A ≃ (Spec A → k)`; connectedness and
discreteness of `Spec A` leave one point.

Used for the converse of the reductivity criterion: a nontrivial smooth connected closed subgroup
has a nonzero Lie algebra.
-/

suppress_compilation

open TensorProduct

namespace AlgMag.Reductive

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [CommRing A] [HopfAlgebra k A]
variable [Algebra.FiniteType k A]

/-- **Zero Lie algebra and connected ⇒ trivial**: `dim_k A = 1`. -/
theorem finrank_eq_one_of_subsingleton_cotangent
    [Subsingleton (TauCeti.Bialgebra.CotangentSpace k A)] [ConnectedSpace (PrimeSpectrum A)] :
    Module.finrank k A = 1 := by
  have : Subsingleton (A ⊗[k] TauCeti.Bialgebra.CotangentSpace k A) := by
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ z : A ⊗[k] TauCeti.Bialgebra.CotangentSpace k A, z = 0 := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul a c => rw [Subsingleton.elim c 0, TensorProduct.tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    rw [h0 x, h0 y]
  have : Subsingleton Ω[A⁄k] := (AlgMag.OpenCellNotes.kaehlerEquivInv k A).toEquiv.subsingleton
  have : Algebra.FormallyUnramified k A := ⟨inferInstance⟩
  have : Algebra.FormallyEtale k A := Algebra.FormallyEtale.of_formallyUnramified_of_field k A
  have : Module.Finite k A := Algebra.FormallyUnramified.finite_of_free k A
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  have : Nontrivial A := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrArg (Coalgebra.counit (R := k) (A := A)) h
    rw [map_zero, Bialgebra.counit_one] at this
    exact zero_ne_one this
  have : Subsingleton (PrimeSpectrum A) := by
    refine ⟨fun p q => ?_⟩
    by_contra hpq
    have hclo : IsClopen ({p} : Set (PrimeSpectrum A)) :=
      ⟨isClosed_discrete _, isOpen_discrete _⟩
    rcases isClopen_iff.1 hclo with h | h
    · exact Set.singleton_ne_empty p h
    · have : q ∈ ({p} : Set (PrimeSpectrum A)) := h ▸ Set.mem_univ q
      exact hpq (this.symm)
  have : Nonempty (PrimeSpectrum A) := inferInstance
  let : Unique (PrimeSpectrum A) := uniqueOfSubsingleton (Classical.arbitrary _)
  rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed k A).toLinearEquiv.finrank_eq,
    Module.finrank_pi, Fintype.card_unique]

omit [Algebra.FiniteType k A] in
/-- **A closed subgroup `V(I)` with connected coordinate ring and zero Lie algebra is trivial.** -/
theorem eq_augmentation_of_lie_eq_zero {H : Type u} [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] (I : TauCeti.HopfIdeal k H)
    [ConnectedSpace (PrimeSpectrum (H ⧸ I.toIdeal))]
    (hlie : ∀ d ∈ I.lieSubalgebra (B := k), d = 0) :
    I = TauCeti.HopfIdeal.augmentation k H := by
  have hder : ∀ e : Derivation k (H ⧸ I.toIdeal)
      (TauCeti.Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k), e = 0 := by
    intro e
    apply TauCeti.HopfIdeal.quotientLieHom_injective (B := k) I
    rw [map_zero]
    exact hlie _ ((LieHom.mem_range _ _).2 ⟨e, rfl⟩)
  have hdual : Subsingleton
      (Module.Dual k (TauCeti.Bialgebra.CotangentSpace k (H ⧸ I.toIdeal))) := by
    let e := Derivation.cotangentLinearEquiv (R := k) (A := H ⧸ I.toIdeal) (B := k)
    refine ⟨fun f g => e.injective ?_⟩
    rw [hder (e f), hder (e g)]
  have : Subsingleton (TauCeti.Bialgebra.CotangentSpace k (H ⧸ I.toIdeal)) :=
    (Module.subsingleton_dual_iff k).1 hdual
  have h1 := finrank_eq_one_of_subsingleton_cotangent k (H ⧸ I.toIdeal)
  have hnt : (1 : H ⧸ I.toIdeal) ≠ 0 := by
    intro h
    have := congrArg (Coalgebra.counit (R := k) (A := H ⧸ I.toIdeal)) h
    rw [map_zero, Bialgebra.counit_one] at this
    exact one_ne_zero this
  ext x
  refine ⟨fun hx => TauCeti.HopfIdeal.le_augmentation k H I hx, fun hx => ?_⟩
  have hx0 := (TauCeti.HopfIdeal.mem_augmentation k H).1 hx
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : H ⧸ I.toIdeal) hnt).1 h1
    (Ideal.Quotient.mk I.toIdeal x)
  have hcz : c = 0 := by
    have := congrArg (Coalgebra.counit (R := k) (A := H ⧸ I.toIdeal)) hc
    rw [map_smul, Bialgebra.counit_one, Bialgebra.Quotient.counit_mk, hx0, smul_eq_mul,
      mul_one] at this
    exact this
  rw [hcz, zero_smul, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc
  exact hc

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
/-- Geometric connectedness (Tau Ceti) gives connectedness of `Spec A` (take `K = k`). -/
theorem connectedSpace_of_geometricallyConnected
    (h : TauCeti.geometricallyConnectedCommHopfAlgProperty k (CommHopfAlgCat.of k A)) :
    ConnectedSpace (PrimeSpectrum A) := by
  have := h k
  let e := PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.rid k k A).toRingEquiv
  exact e.surjective.connectedSpace e.continuous

end AlgMag.Reductive
