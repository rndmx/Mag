/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.PointDerivations
import AlgMag.Reductive.KaehlerFibreTangent
import AlgMag.Reductive.LieIdentityComponent
import Mathlib.Algebra.DualNumber

/-!
# Bridges between the models of derivations at a point (C2(d), part (a), item 3)

* (b1) `derivationEquivPointDer`: `Derivation k B k` (module structure from `[Algebra B k]`)
  is `pointDer` at the point `B → k`; under it `tangentPullback` is precomposition
  (`bijective_tangentPullback_iff`).
* (b2) `pointDerEquivDual`: point derivations at `e₀` are the lifts of `e₀` to dual numbers,
  `a ↦ e₀ a + e₀·D a`; compatible with composition (`pointDerEquivDual_comp`).
* (b3) `derAt_eq_pointDer` (in LieIdentityComponent): `derAt t = pointDer t.ofConv`.
-/

namespace AlgMag.Reductive

open TensorProduct TrivSqZeroExt

/-! ### (b1) -/

section B1

variable (k : Type*) {A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra B k] [IsScalarTower k B k]

/-- `Derivation k B k` (with `B` acting through `B → k`) is `pointDer` at that point. -/
def derivationEquivPointDer :
    Derivation k B k ≃ₗ[k] pointDer (IsScalarTower.toAlgHom k B k) where
  toFun D := ⟨D.toLinearMap, fun a b => by
    change D (a * b) = _
    rw [Derivation.leibniz, Algebra.smul_def, Algebra.smul_def]
    rfl⟩
  invFun D := Derivation.mk' D.1 (fun a b => by
    rw [pointDer_leibniz D a b, Algebra.smul_def, Algebra.smul_def]
    rfl)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma derivationEquivPointDer_apply (D : Derivation k B k) (b : B) :
    (derivationEquivPointDer k D).1 b = D b := rfl

variable {k}

/-- Precomposition of point derivations with an algebra map. -/
def pointDerComp (φ : A →ₐ[k] B) (e₀ : B →ₐ[k] k) :
    pointDer e₀ →ₗ[k] pointDer (e₀.comp φ) where
  toFun D := ⟨D.1 ∘ₗ φ.toLinearMap, fun a b => by
    simpa using pointDer_leibniz D (φ a) (φ b)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Algebra B k] [IsScalarTower k B k] in
@[simp] lemma pointDerComp_apply (φ : A →ₐ[k] B) (e₀ : B →ₐ[k] k) (D : pointDer e₀) (a : A) :
    (pointDerComp φ e₀ D).1 a = D.1 (φ a) := rfl

end B1

section B1'

variable (k : Type*) {A B : Type*} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra B k] [IsScalarTower k B k]

/-- **The tangent map in `pointDer` form.** -/
theorem bijective_tangentPullback_iff [Algebra A B] [IsScalarTower k A B]
    [Algebra A k] [IsScalarTower A B k] [IsScalarTower k A k] :
    Function.Bijective (tangentPullback k A B k) ↔
      Function.Bijective
        (pointDerComp (IsScalarTower.toAlgHom k A B) (IsScalarTower.toAlgHom k B k)) := by
  have hpt : (IsScalarTower.toAlgHom k B k).comp (IsScalarTower.toAlgHom k A B) =
      IsScalarTower.toAlgHom k A k := by
    ext a; simp [← IsScalarTower.algebraMap_apply]
  let eA : pointDer ((IsScalarTower.toAlgHom k B k).comp (IsScalarTower.toAlgHom k A B)) ≃ₗ[k]
      pointDer (IsScalarTower.toAlgHom k A k) := LinearEquiv.ofEq _ _ (by rw [hpt])
  have h : tangentPullback k A B k =
      ((derivationEquivPointDer k).symm.toEquiv : _ → _) ∘ (eA.toEquiv : _ → _) ∘
        pointDerComp (IsScalarTower.toAlgHom k A B) (IsScalarTower.toAlgHom k B k) ∘
          ((derivationEquivPointDer k).toEquiv : _ → _) := by
    funext D
    ext a
    rfl
  rw [h, Equiv.comp_bijective, Equiv.comp_bijective, Equiv.bijective_comp]

end B1'

/-! ### (b2) -/

section B2

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The dual-number lift `a ↦ e₀ a + e₀·D a` of a point derivation. -/
def pointDerToDual {e₀ : A →ₐ[k] k} (D : pointDer e₀) : A →ₐ[k] DualNumber k where
  toFun a := inl (e₀ a) + inr (D.1 a)
  map_one' := by simp [pointDer_one]
  map_mul' a b := by
    ext
    · simp
    · simp [pointDer_leibniz D a b]; ring
  map_zero' := by simp
  map_add' a b := by
    ext <;> simp
  commutes' c := by
    ext
    · simp [Algebra.algebraMap_eq_smul_one]
    · simp [Algebra.algebraMap_eq_smul_one, pointDer_one]

@[simp] lemma fst_pointDerToDual {e₀ : A →ₐ[k] k} (D : pointDer e₀) (a : A) :
    fst (pointDerToDual D a) = e₀ a := by simp [pointDerToDual]

@[simp] lemma snd_pointDerToDual {e₀ : A →ₐ[k] k} (D : pointDer e₀) (a : A) :
    snd (pointDerToDual D a) = D.1 a := by simp [pointDerToDual]

/-- **Point derivations are dual-number lifts.** -/
def pointDerEquivDual (e₀ : A →ₐ[k] k) :
    pointDer e₀ ≃ {φ : A →ₐ[k] DualNumber k // (fstHom k k k).comp φ = e₀} where
  toFun D := ⟨pointDerToDual D, by ext a; simp⟩
  invFun φ := ⟨(sndHom k k).comp φ.1.toLinearMap, fun a b => by
    have h : ∀ x, fst (φ.1 x) = e₀ x := fun x => congrArg (fun f => f x) φ.2
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      sndHom_apply, map_mul, snd_mul, smul_eq_mul, op_smul_eq_mul, h]
    ring⟩
  left_inv D := by ext a; simp
  right_inv φ := by
    have h : ∀ x, fst (φ.1 x) = e₀ x := fun x => congrArg (fun f => f x) φ.2
    ext a
    · simp [h]
    · simp

/-- Composition: the dual lift of `D ∘ φ` is the dual lift of `D` composed with `φ`. -/
lemma pointDerEquivDual_comp (φ : A →ₐ[k] B) (e₀ : B →ₐ[k] k) (D : pointDer e₀) :
    pointDerToDual (pointDerComp φ e₀ D) = (pointDerToDual D).comp φ := by
  ext a
  · simp
  · rw [snd_pointDerToDual, AlgHom.comp_apply, snd_pointDerToDual]; rfl

end B2

end AlgMag.Reductive
