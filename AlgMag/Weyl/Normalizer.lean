/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.AttractorSubgroup

/-!
# Normalizing points, Weyl magnets and the attractor

For the conjugation action of `T = D(X)` on `G` (closed embedding `π : k[G] → k[X]`), a point
`g ∈ G(A)` *normalizes `T` with automorphism `σ` of `X`* when `g t g⁻¹ = σ_*(t)` for the universal
point `t` of `T`. Main results:
* `orbitHom_normalizing` : the conjugation formula `t g t⁻¹ = g · (σ⁻¹(t) t⁻¹)`;
* `mem_attractorSubgroup_iff_joinIrredWeylMagnets` : `g ∈ G^N(A) ↔ (1 - σ)M ⊆ N` (`A` nontrivial),
  from Theorem 3.20 (`attractorSubgroup`).
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Weyl

open AlgMag.Reductive

universe u v w

variable {k : Type u} {H : Type v} {X : Type w}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable {A : Type*} [CommRing A] [Algebra k A]

variable (A) in
/-- The universal point of `T` pushed along an endomorphism `f` of `X`:
`h ↦ 1 ⊗ f_*(π h)`. -/
def twistPoint (f : X →* X) : WithConv (H →ₐ[k] A ⊗[k] MonoidAlgebra k X) :=
  toConv ((Algebra.TensorProduct.includeRight).comp
    ((MonoidAlgebra.mapDomainAlgHom k k f).comp π.toAlgHom))

lemma twistPoint_id : twistPoint π A (MonoidHom.id X) = torusPoint π A := by
  rw [twistPoint, torusPoint, MonoidAlgebra.mapDomainAlgHom_id, AlgHom.id_comp]

lemma twistPoint_mul (f f' : X →* X) :
    twistPoint π A f * twistPoint π A f' = twistPoint π A (f * f') := by
  have hφ : toConv ((Algebra.TensorProduct.includeRight (R := k) (A := A)).comp
        (MonoidAlgebra.mapDomainAlgHom k k f)) *
      toConv ((Algebra.TensorProduct.includeRight (R := k) (A := A)).comp
        (MonoidAlgebra.mapDomainAlgHom k k f')) =
      toConv ((Algebra.TensorProduct.includeRight (R := k) (A := A)).comp
        (MonoidAlgebra.mapDomainAlgHom k k (f * f'))) := by
    apply WithConv.ofConv_injective
    ext x
    rw [ofConv_toConv, AlgHom.convMul_apply]
    simp [Algebra.TensorProduct.tmul_mul_tmul,
      MonoidAlgebra.single_mul_single]
  have := AlgHom.convMul_comp_bialgHom_distrib
    (toConv ((Algebra.TensorProduct.includeRight (R := k) (A := A)).comp
        (MonoidAlgebra.mapDomainAlgHom k k f)))
    (toConv ((Algebra.TensorProduct.includeRight (R := k) (A := A)).comp
        (MonoidAlgebra.mapDomainAlgHom k k f'))) π
  rw [hφ] at this
  apply WithConv.ofConv_injective
  simp only [twistPoint, ofConv_toConv] at this ⊢
  rw [AlgHom.comp_assoc] at this
  rw [this, toConv_ofConv, AlgHom.comp_assoc, AlgHom.comp_assoc]

variable (A) in
/-- The endomorphism `id ⊗ f_*` of `A ⊗ k[X]`. -/
def twistValue (f : X →* X) : A ⊗[k] MonoidAlgebra k X →ₐ[k] A ⊗[k] MonoidAlgebra k X :=
  Algebra.TensorProduct.map (AlgHom.id k A) (MonoidAlgebra.mapDomainAlgHom k k f)

lemma mapValue_twistValue_const (f : X →* X) (g : WithConv (H →ₐ[k] A)) :
    AlgHom.mapValue (twistValue A f)
        (AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) g) =
      AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) g := by
  rw [AlgHom.mapValue_apply, AlgHom.mapValue_apply, ofConv_toConv, ← AlgHom.comp_assoc,
    twistValue, Algebra.TensorProduct.map_comp_includeLeft, AlgHom.comp_id]

lemma mapValue_twistValue_twistPoint (f f' : X →* X) :
    AlgHom.mapValue (twistValue A f) (twistPoint π A f') = twistPoint π A (f.comp f') := by
  rw [AlgHom.mapValue_apply, twistPoint, twistPoint, ofConv_toConv, ← AlgHom.comp_assoc,
    twistValue, Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_assoc,
    ← AlgHom.comp_assoc (MonoidAlgebra.mapDomainAlgHom k k f),
    ← MonoidAlgebra.mapDomainAlgHom_comp]

variable (A) in
/-- `g ∈ G(A)` **normalizes `T` with automorphism `σ`**: `g t g⁻¹ = σ_*(t)`, `t` the universal
point of `T = D(X)` (all in `G(A ⊗ k[X])`). -/
def IsNormalizingWith (g : WithConv (H →ₐ[k] A)) (σ : X ≃* X) : Prop :=
  MulAut.conj (AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) g)
    (torusPoint π A) = twistPoint π A σ.toMonoidHom

/-- Conjugating a twisted point: if `g t g⁻¹ = σ(t)` then `g f(t) g⁻¹ = (f ∘ σ)(t)`. -/
lemma IsNormalizingWith.conj_twistPoint {g : WithConv (H →ₐ[k] A)} {σ : X ≃* X}
    (hg : IsNormalizingWith π A g σ) (f : X →* X) :
    MulAut.conj (AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) g)
      (twistPoint π A f) = twistPoint π A (f.comp σ.toMonoidHom) := by
  have := congrArg (AlgHom.mapValue (twistValue A f)) hg
  rw [MulAut.conj_apply] at this
  rw [map_mul, map_mul, map_inv, mapValue_twistValue_const,
    ← twistPoint_id, mapValue_twistValue_twistPoint, mapValue_twistValue_twistPoint,
    MonoidHom.comp_id] at this
  rw [MulAut.conj_apply, this]

/-- **Conjugation formula (F4).** For `g` normalizing `T` with automorphism `σ`,
`t g t⁻¹ = g · (σ⁻¹(t) t⁻¹)`: the orbit map of `g` is `g` times the torus point pushed along
`χ ↦ σ⁻¹(χ) χ⁻¹`. -/
theorem orbitHom_normalizing {g : WithConv (H →ₐ[k] A)} {σ : X ≃* X}
    (hg : IsNormalizingWith π A g σ) :
    orbitHom π A g =
      AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) g *
        twistPoint π A (σ.symm.toMonoidHom / MonoidHom.id X) := by
  set gg := AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) g
  have hs := hg.conj_twistPoint π σ.symm.toMonoidHom
  have hc : σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id X := by
    ext x; simp
  rw [hc, twistPoint_id, MulAut.conj_apply] at hs
  have hm : twistPoint π A (σ.symm.toMonoidHom / MonoidHom.id X) * torusPoint π A =
      twistPoint π A σ.symm.toMonoidHom := by
    rw [← twistPoint_id, twistPoint_mul, div_mul_cancel]
  have hm2 := eq_mul_inv_of_mul_eq (G := WithConv (H →ₐ[k] A ⊗[k] MonoidAlgebra k X)) hm
  rw [hm2, orbitHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have key : ∀ a b c : WithConv (H →ₐ[k] A ⊗[k] MonoidAlgebra k X),
      a * b * a⁻¹ * a * c⁻¹ = a * (b * c⁻¹) := fun a b c =>
    (congrArg (· * c⁻¹) (inv_mul_cancel_right (a * b) a)).trans (mul_assoc a b c⁻¹)
  nth_rewrite 1 [← hs]
  exact key gg _ _

/-- **Weyl magnets** `(1 - σ)M = {χ - σ χ}` (additive notation on `M = Additive X`). -/
def joinIrredWeylMagnets (σ : X ≃* X) : Set (Additive X) :=
  Set.range fun χ : Additive X => χ - Additive.ofMul (σ (Additive.toMul χ))

/-- The **Weyl magnet magnet**: the magnet generated by the Weyl magnets of `σ`. -/
def weylMagnet (σ : X ≃* X) : Magnet (Additive X) := AddSubmonoid.closure (joinIrredWeylMagnets σ)

variable [DecidableEq X]

/-- **Key lemma (F6).** A point `g ∈ G(A)` (`A` nontrivial) normalizing `T` with automorphism `σ`
lies in the attractor `G^N(A)` iff `(1 - σ)M ⊆ N`. -/
theorem mem_attractorSubgroup_iff_joinIrredWeylMagnets [Nontrivial A] (hπ : Function.Surjective π)
    {g : WithConv (H →ₐ[k] A)} {σ : X ≃* X} (hg : IsNormalizingWith π A g σ)
    (N : Magnet (Additive X)) :
    g ∈ attractorSubgroup π N A ↔ joinIrredWeylMagnets σ ⊆ (N : Set (Additive X)) := by
  set S := subalgebraPoints (H := H) (magnetSubalgebra (R := k) A N)
  set f : X →* X := σ.symm.toMonoidHom / MonoidHom.id X
  have hconst : AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) g ∈ S := by
    intro h
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, MonoidAlgebra.one_def]
    have := tmul_mem_magnetSubalgebra (R := k) (g.ofConv h) N.zero_mem
    rwa [toMul_zero] at this
  have hf : ∀ ψ : X, f (σ ψ) = ψ / σ ψ := by
    intro ψ; simp [f]
  change orbitHom π A g ∈ S ↔ _
  rw [orbitHom_normalizing π hg, Subgroup.mul_mem_cancel_left _ hconst]
  constructor
  · rintro hτ _ ⟨χ, rfl⟩
    obtain ⟨h, hh⟩ := hπ (MonoidAlgebra.single (σ (Additive.toMul χ)) 1)
    have hmem := hτ h
    simp only [twistPoint, ofConv_toConv, AlgHom.comp_apply] at hmem
    erw [hh] at hmem
    rw [ MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single, hf,
      Algebra.TensorProduct.includeRight_apply] at hmem
    by_contra hN
    have hN' : Additive.ofMul (Additive.toMul χ / σ (Additive.toMul χ)) ∉ N := by
      rwa [ofMul_div]
    have h0 := tensorComponent_eq_zero_of_mem hmem hN'
    rw [LinearMap.tensorComponent_tmul, Comodule.monoidCoeff_apply, toMul_ofMul,
      MonoidAlgebra.coeff_single_apply, ite_eq_left_iff.mpr (fun h => absurd rfl h), one_smul] at h0
    exact one_ne_zero h0
  · intro hW h
    simp only [twistPoint, ofConv_toConv, AlgHom.comp_apply]
    suffices hall : ∀ p : MonoidAlgebra k X, Algebra.TensorProduct.includeRight (A := A)
        (MonoidAlgebra.mapDomainAlgHom k k f p) ∈ magnetSubalgebra (R := k) A N from hall _
    intro p
    induction p using MonoidAlgebra.induction_linear with
    | zero => rw [map_zero, map_zero]; exact Subalgebra.zero_mem _
    | add p q hp hq => rw [map_add, map_add]; exact Subalgebra.add_mem _ hp hq
    | single x c =>
      have hx : Additive.ofMul (f x) ∈ N := by
        have h1 := hW ⟨Additive.ofMul (σ.symm x), rfl⟩
        have h2 : f x = σ.symm x / x := by
          conv_lhs => rw [← MulEquiv.apply_symm_apply σ x]
          rw [hf, MulEquiv.apply_symm_apply]
        rw [h2, ofMul_div]
        simpa using h1
      have hs : (MonoidAlgebra.single x c : MonoidAlgebra k X) =
          c • MonoidAlgebra.single x 1 := by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul]
      refine Subalgebra.smul_mem _ ?_ c
      rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
        Algebra.TensorProduct.includeRight_apply]
      have := tmul_mem_magnetSubalgebra (R := k) (1 : A) hx
      rwa [toMul_ofMul] at this

/-- The key lemma in terms of the Weyl magnet magnet: `g ∈ G^N(A) ↔ ⟨(1 - σ)M⟩ ⊆ N`. -/
theorem mem_attractorSubgroup_iff_weylMagnet_le [Nontrivial A] (hπ : Function.Surjective π)
    {g : WithConv (H →ₐ[k] A)} {σ : X ≃* X} (hg : IsNormalizingWith π A g σ)
    (N : Magnet (Additive X)) :
    g ∈ attractorSubgroup π N A ↔ weylMagnet σ ≤ N := by
  rw [mem_attractorSubgroup_iff_joinIrredWeylMagnets π hπ hg, weylMagnet, AddSubmonoid.closure_le]

end AlgMag.Weyl
