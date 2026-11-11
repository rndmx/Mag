/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Tactic.LinearCombination

/-!
# Point derivations of tensor products and translations (C2(d), part (a), item 1)

`pointDer ε` = derivations `A → k` at the point `ε : A →ₐ[k] k`, as a submodule of
`A →ₗ[k] k`.

* `pointDerCongr σ ε`: an algebra isomorphism `σ : A ≃ A'` transports point derivations
  (left translation from `t₀` to `e`).
* `pointDerTensorEquiv εA εB`: `Der_{(εA, εB)}(A ⊗ B, k) ≃ Der_{εA}(A, k) × Der_{εB}(B, k)`.

For `sliceSource = ((H⧸U⁻) ⊗ (H⧸U⁺)) ⊗ k[X]` at `(e, e, t₀)` this gives
`Der ≃ (Lie U⁻ × Lie U⁺) × Der_{t₀}(k[X], k)`, and translation by `t₀` gives `Lie T`.
-/

namespace AlgMag.Reductive

open TensorProduct

variable {k A A' B : Type*} [CommRing k] [CommRing A] [CommRing A'] [CommRing B]
  [Algebra k A] [Algebra k A'] [Algebra k B]

/-- Derivations `A → k` at the point `ε`. -/
def pointDer (ε : A →ₐ[k] k) : Submodule k (A →ₗ[k] k) where
  carrier := {D | ∀ a b, D (a * b) = ε a * D b + ε b * D a}
  add_mem' := by
    intro D E hD hE a b
    simp only [Set.mem_ofPred_eq, LinearMap.add_apply] at *
    rw [hD a b, hE a b]; ring
  zero_mem' := by intro a b; simp
  smul_mem' := by
    intro c D hD a b
    simp only [Set.mem_ofPred_eq, LinearMap.smul_apply, smul_eq_mul] at *
    rw [hD a b]; ring

lemma pointDer_leibniz {ε : A →ₐ[k] k} (D : pointDer ε) (a b : A) :
    D.1 (a * b) = ε a * D.1 b + ε b * D.1 a := D.2 a b

lemma pointDer_one {ε : A →ₐ[k] k} (D : pointDer ε) : D.1 1 = 0 := by
  have h := pointDer_leibniz D 1 1
  rw [mul_one, _root_.map_one ε, one_mul] at h
  linear_combination -h

/-- Transport of point derivations along an algebra isomorphism. -/
def pointDerCongr (σ : A ≃ₐ[k] A') (ε : A' →ₐ[k] k) :
    pointDer ε ≃ₗ[k] pointDer (ε.comp σ.toAlgHom) where
  toFun D := ⟨D.1 ∘ₗ σ.toLinearMap, fun a b => by
    simpa using pointDer_leibniz D (σ a) (σ b)⟩
  invFun D := ⟨D.1 ∘ₗ σ.symm.toLinearMap, fun a b => by
    simpa using pointDer_leibniz D (σ.symm a) (σ.symm b)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv D := by ext a; simp
  right_inv D := by ext a; simp

variable (εA : A →ₐ[k] k) (εB : B →ₐ[k] k)

/-- The point `(εA, εB)` of `A ⊗ B`. -/
abbrev tensorPoint : A ⊗[k] B →ₐ[k] k :=
  Algebra.TensorProduct.productMap εA εB

@[simp] lemma tensorPoint_tmul (a : A) (b : B) : tensorPoint εA εB (a ⊗ₜ b) = εA a * εB b :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ a b

/-- The bilinear form `(a, b) ↦ D₁ a · εB b + εA a · D₂ b`. -/
def pointDerTensorBil (D₁ : A →ₗ[k] k) (D₂ : B →ₗ[k] k) : A →ₗ[k] B →ₗ[k] k :=
  LinearMap.mk₂ k (fun a b => D₁ a * εB b + εA a * D₂ b)
    (fun a a' b => by simp only [map_add]; ring)
    (fun c a b => by simp only [map_smul, smul_eq_mul]; ring)
    (fun a b b' => by simp only [map_add]; ring)
    (fun c a b => by simp only [map_smul, smul_eq_mul]; ring)

lemma pointDerTensor_mem (D₁ : pointDer εA) (D₂ : pointDer εB) :
    TensorProduct.lift (pointDerTensorBil εA εB D₁.1 D₂.1) ∈
      pointDer (tensorPoint εA εB) := by
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']; ring
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']; ring
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.lift.tmul,
        pointDerTensorBil, LinearMap.mk₂_apply, tensorPoint_tmul,
        pointDer_leibniz, map_mul]
      ring

/-- **Point derivations of a tensor product.** -/
def pointDerTensorEquiv :
    pointDer (tensorPoint εA εB) ≃ₗ[k] pointDer εA × pointDer εB where
  toFun D :=
    (⟨D.1 ∘ₗ (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toLinearMap,
      fun a b => by
        simpa [tensorPoint_tmul] using
          pointDer_leibniz D (a ⊗ₜ 1) (b ⊗ₜ 1)⟩,
     ⟨D.1 ∘ₗ (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toLinearMap,
      fun a b => by
        simpa [tensorPoint_tmul] using
          pointDer_leibniz D (1 ⊗ₜ a) (1 ⊗ₜ b)⟩)
  invFun p := ⟨_, pointDerTensor_mem εA εB p.1 p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv D := by
    apply Subtype.ext
    apply TensorProduct.ext'
    intro a b
    have h := pointDer_leibniz D (a ⊗ₜ 1) (1 ⊗ₜ b)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      tensorPoint_tmul, map_one] at h
    simp only [TensorProduct.lift.tmul, pointDerTensorBil, LinearMap.mk₂_apply,
      LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, h]
    ring
  right_inv p := by
    ext a
    · simp [pointDerTensorBil, pointDer_one]
    · simp [pointDerTensorBil, pointDer_one]

section Torus

variable {X : Type*} [CommGroup X] {B' : Type*} [Semiring B'] [Algebra k B']

lemma monoidAlgebra_algHom_ext {f g : MonoidAlgebra k X →ₐ[k] B'}
    (h : ∀ x, f (MonoidAlgebra.single x 1) = g (MonoidAlgebra.single x 1)) : f = g :=
  MonoidAlgebra.algHom_ext h (Subsingleton.elim _ _)

/-- Multiplication by a character `c`: `single x 1 ↦ c x • single x 1`. -/
noncomputable def charTranslate (c : X →* kˣ) : MonoidAlgebra k X →ₐ[k] MonoidAlgebra k X :=
  MonoidAlgebra.lift k (MonoidAlgebra k X) X
    { toFun := fun x => ((c x : kˣ) : k) • MonoidAlgebra.single x 1
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := fun x y => by
        simp [MonoidAlgebra.single_mul_single, mul_comm] }

@[simp] lemma charTranslate_single (c : X →* kˣ) (x : X) :
    charTranslate c (MonoidAlgebra.single x 1) = ((c x : kˣ) : k) • MonoidAlgebra.single x 1 := by
  simp [charTranslate, MonoidAlgebra.lift_single]

/-- **Translation by a point of the torus**, as an algebra automorphism. -/
noncomputable def torusTranslate (c : X →* kˣ) : MonoidAlgebra k X ≃ₐ[k] MonoidAlgebra k X :=
  AlgEquiv.ofAlgHom (charTranslate c) (charTranslate c⁻¹)
    (monoidAlgebra_algHom_ext fun x => by
      rw [AlgHom.comp_apply, charTranslate_single, map_smul, charTranslate_single, smul_smul,
        ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one, one_smul,
        AlgHom.id_apply])
    (monoidAlgebra_algHom_ext fun x => by
      rw [AlgHom.comp_apply, charTranslate_single, map_smul, charTranslate_single, smul_smul,
        ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul,
        AlgHom.id_apply])

/-- The character of a point `τ` of the torus. -/
noncomputable def pointChar (τ : MonoidAlgebra k X →ₐ[k] k) : X →* kˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => τ (MonoidAlgebra.single x 1)
      map_one' := by rw [← MonoidAlgebra.one_def, map_one]
      map_mul' := fun x y => by rw [← map_mul, MonoidAlgebra.single_mul_single, mul_one] }

/-- Translating the unit point by `τ` gives `τ`: `e ∘ L_τ = τ`. -/
theorem counit_comp_torusTranslate (τ : MonoidAlgebra k X →ₐ[k] k) :
    (Bialgebra.counitAlgHom k (MonoidAlgebra k X)).comp
      (torusTranslate (pointChar τ)).toAlgHom = τ :=
  monoidAlgebra_algHom_ext fun x => by
    simp [torusTranslate, pointChar]

/-- Point derivations at `τ` are point derivations at `e` (Lie T), by translation. -/
noncomputable def pointDerTorusEquiv (τ : MonoidAlgebra k X →ₐ[k] k) :
    pointDer (Bialgebra.counitAlgHom k (MonoidAlgebra k X)) ≃ₗ[k] pointDer τ :=
  (pointDerCongr (torusTranslate (pointChar τ)) _).trans
    (LinearEquiv.ofEq _ _ (by rw [counit_comp_torusTranslate]))

end Torus

end AlgMag.Reductive
