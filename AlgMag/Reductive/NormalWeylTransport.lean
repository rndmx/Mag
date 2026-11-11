/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.FromR1R2
import AlgMag.Reductive.NormalLieRoots
import AlgMag.Weyl.WeylGroup

/-!
# Transport of root vectors of a normal subgroup by a normalizing point

If `U = V(I)` is normal and `n ∈ N_G(T)(k)` acts on `X` by `σ`, then conjugation by `n` preserves
`I`, hence `Lie U`, and sends `Lie U ∩ 𝔤_α` to `Lie U ∩ 𝔤_{σα}`. With a Weyl element
(`σ α = -α`) this gives `𝔤_{-α} ⊆ Lie U` from `𝔤_α ⊆ Lie U`, hence (`le_of_root_group`)
`U_{-α} ⊆ U` from `U_α ⊆ U`.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv AlgMag.Weyl

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

omit [CommGroup X] [DecidableEq X] in
/-- **A normal Hopf ideal is stable under conjugation by a rational point.** -/
theorem pointConjugation_mem_of_isNormal {I : HopfIdeal k H} (hI : I.IsNormal)
    (n : WithConv (H →ₐ[k] k)) {x : H} (hx : x ∈ I.toIdeal) :
    HopfAlgebra.pointConjugationAlgHom n x ∈ I.toIdeal := by
  have hc := hI.conjugation_mem hx
  set f := Algebra.TensorProduct.productMap
      (AlgHom.mapValue (H := H) (Algebra.ofId k H) n).ofConv (AlgHom.id k H)
  have hmap := Ideal.mem_map_of_mem f.toRingHom hc
  rw [Ideal.rightTensorIdeal_def, Ideal.map_map] at hmap
  have hid : f.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := k) (A := H) (B := H)).toRingHom = RingHom.id H := by
    ext y
    simp [f]
  rw [hid, Ideal.map_id] at hmap
  exact hmap

/-- **Normalizing points transport root vectors of a normal subgroup**: a nonzero vector of
`Lie U ∩ 𝔤_α` gives a nonzero vector of `Lie U ∩ 𝔤_{σα}`. -/
theorem exists_rootSpace_lie_of_isNormalizingWith {I : HopfIdeal k H} (hI : I.IsNormal)
    {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X} (hn : IsNormalizingWith π k n σ)
    {α : Additive X} {e : Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (he : e ∈ I.lieSubalgebra (B := k)) (heα : e ∈ rootSpace π α) (he0 : e ≠ 0) :
    ∃ e' ∈ I.lieSubalgebra (B := k),
      e' ∈ rootSpace π (Additive.ofMul (σ (Additive.toMul α))) ∧ e' ≠ 0 := by
  let e' := derivationComp (B := k) (HopfAlgebra.pointConjugationBialgEquiv n⁻¹ : H →ₐc[k] H) e
  have happ : ∀ h, e' h = e (HopfAlgebra.pointConjugationAlgHom n⁻¹ h) := by
    intro h
    rw [derivationComp_apply, HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
  refine ⟨e', ?_, ?_, ?_⟩
  · rw [HopfIdeal.mem_lieSubalgebra_iff] at he ⊢
    intro x hx
    rw [happ]
    exact he _ (pointConjugation_mem_of_isNormal hI n⁻¹ hx)
  · intro χ hχ h hh
    rw [happ]
    have hmem := pointConjugation_mem_torusGrading π hn.inv hh
    apply heα _ _ _ hmem
    intro hc
    apply hχ
    have : σ⁻¹ (Additive.toMul χ) = Additive.toMul α := by
      have := congrArg Additive.toMul hc
      simpa using this
    have h2 : Additive.toMul χ = σ (Additive.toMul α) := by
      rw [← this]; simp
    rw [← h2]; rfl
  · intro h0
    apply he0
    ext h
    have h1 := congrArg (fun d => d (HopfAlgebra.pointConjugationAlgHom n h)) h0
    simp only [happ, Derivation.zero_apply] at h1
    have hinv : HopfAlgebra.pointConjugationAlgHom n⁻¹ (HopfAlgebra.pointConjugationAlgHom n h) = h := by
      have := AlgHom.congr_fun (HopfAlgebra.pointConjugationAlgHom_mul n n⁻¹) h
      simpa using this.symm
    rw [hinv] at h1
    rw [h1]; rfl

end AlgMag.Reductive
