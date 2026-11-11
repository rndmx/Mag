/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# From an open cell to an irreducible middle factor

Topological step of CGP Proposition 2.1.8 (4): if `Spec(B ⊗ C ⊗ D)` (over a field) maps by an open
embedding into an irreducible `Spec H`, and `B`, `D` are nonzero, then `Spec C` is irreducible,
hence connected. Applied to the open cell `U(-λ) × Z(λ) × U(λ) → G` of a connected smooth group
over an algebraically closed field, it gives the irreducibility of `Z(λ)`.
-/

open scoped TensorProduct

namespace AlgMag.Reductive

variable {k B C D H : Type*} [Field k] [CommRing B] [CommRing C] [CommRing D] [CommRing H]
variable [Algebra k B] [Algebra k C] [Algebra k D]

/-- Over a field, `Spec(A ⊗ M) → Spec A` is surjective for `M` nonzero. -/
lemma comap_includeLeft_surjective (A M : Type*) [CommRing A] [Algebra k A] [CommRing M]
    [Algebra k M] [Nontrivial M] :
    Function.Surjective (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] M).toRingHom) := by
  have : Module.FaithfullyFlat A (A ⊗[k] M) := inferInstance
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := A ⊗[k] M)

/-- Over a field, `Spec(M ⊗ A) → Spec A` is surjective for `M` nonzero. -/
lemma comap_includeRight_surjective (A M : Type*) [CommRing A] [Algebra k A] [CommRing M]
    [Algebra k M] [Nontrivial M] :
    Function.Surjective (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[k] M ⊗[k] A).toRingHom) := by
  have e := comap_includeLeft_surjective (k := k) A M
  let σ := (Algebra.TensorProduct.comm k A M : A ⊗[k] M ≃ₐ[k] M ⊗[k] A)
  have hcomp : (Algebra.TensorProduct.includeRight : A →ₐ[k] M ⊗[k] A).toRingHom =
      σ.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] M).toRingHom := by
    refine RingHom.ext fun a => ?_
    show (1 : M) ⊗ₜ[k] a = Algebra.TensorProduct.comm k A M (a ⊗ₜ[k] (1 : M))
    rw [Algebra.TensorProduct.comm_tmul]
  rw [hcomp]
  intro p
  obtain ⟨q, hq⟩ := e p
  refine ⟨PrimeSpectrum.comapEquiv σ.toRingEquiv q, ?_⟩
  rw [PrimeSpectrum.comap_comp_apply]
  have h1 : PrimeSpectrum.comap σ.toRingEquiv.toRingHom
      (PrimeSpectrum.comapEquiv σ.toRingEquiv q) = q :=
    (PrimeSpectrum.comapEquiv σ.toRingEquiv).symm_apply_apply q
  rw [h1, hq]

/-- **Open cell ⇒ irreducible middle factor.** If `φ : H → (B ⊗ C) ⊗ D` induces an open embedding
of spectra, `Spec H` is irreducible and `B`, `C`, `D` are nonzero, then `Spec C` is irreducible. -/
theorem irreducibleSpace_of_isOpenEmbedding_tensor [Nontrivial B] [Nontrivial C] [Nontrivial D]
    [IrreducibleSpace (PrimeSpectrum H)] (φ : H →+* (B ⊗[k] C) ⊗[k] D)
    (hφ : Topology.IsOpenEmbedding (PrimeSpectrum.comap φ)) :
    IrreducibleSpace (PrimeSpectrum C) := by
  have : Nontrivial (B ⊗[k] C) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k B C
      (FaithfulSMul.algebraMap_injective k C)
  have : Nontrivial ((B ⊗[k] C) ⊗[k] D) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k (B ⊗[k] C) D
      (FaithfulSMul.algebraMap_injective k D)
  -- `Spec S` is irreducible: it is homeomorphic to a nonempty open of `Spec H`.
  have hS : IrreducibleSpace (PrimeSpectrum ((B ⊗[k] C) ⊗[k] D)) := by
    let f := PrimeSpectrum.comap φ
    have hne : (Set.range f).Nonempty := Set.range_nonempty f
    have hirr : IsIrreducible (Set.range f) :=
      ⟨hne, (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum H)).2.open_subset
        hφ.isOpen_range (Set.subset_univ _)⟩
    have := Subtype.irreducibleSpace hirr
    let e := hφ.isEmbedding.toHomeomorph
    exact Function.Surjective.irreducibleSpace e.symm.continuous e.symm.surjective
  -- `Spec S → Spec C` is surjective.
  let ι : C →+* (B ⊗[k] C) ⊗[k] D :=
    (Algebra.TensorProduct.includeLeft : B ⊗[k] C →ₐ[k] (B ⊗[k] C) ⊗[k] D).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[k] B ⊗[k] C).toRingHom
  have hsurj : Function.Surjective (PrimeSpectrum.comap ι) := by
    rw [show PrimeSpectrum.comap ι = _ from PrimeSpectrum.comap_comp _ _]
    exact (comap_includeRight_surjective (k := k) C B).comp
      (comap_includeLeft_surjective (k := k) (B ⊗[k] C) D)
  exact Function.Surjective.irreducibleSpace (PrimeSpectrum.continuous_comap ι) hsurj

/-- The middle factor of an open cell is connected. -/
theorem connectedSpace_of_isOpenEmbedding_tensor [Nontrivial B] [Nontrivial C] [Nontrivial D]
    [IrreducibleSpace (PrimeSpectrum H)] (φ : H →+* (B ⊗[k] C) ⊗[k] D)
    (hφ : Topology.IsOpenEmbedding (PrimeSpectrum.comap φ)) :
    ConnectedSpace (PrimeSpectrum C) := by
  have := irreducibleSpace_of_isOpenEmbedding_tensor φ hφ
  infer_instance

end AlgMag.Reductive
