/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Basic
import AlgMag.Sec10PrintedPl

/-!
# Proposition 10.1 for a general affine flat `G`: base change of the thickening

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Proposition 10.1 (p. 168), with `X'`
affine. For `G = Spec H` the proof evaluates the torsor of lifts on `T = Spec B`, with `B = R`, `H`,
`H ⊗ H`. This file proves the ring input for these `T`: the base change `B ⊗ A₁ → B ⊗ A` of the first
order thickening `A₁ → A` is again a first order thickening, and its ideal is `B ⊗ I` when `B` is flat.
-/

open TensorProduct

universe u

namespace AlgMag.Prop101General

variable {R : Type u} [CommRing R] (B : Type u) [CommRing B] [Algebra R B]
  {A₁ A : Type u} [CommRing A₁] [CommRing A] [Algebra R A₁] [Algebra R A] (φ : A₁ →ₐ[R] A)

/-- The base change `B ⊗ A₁ → B ⊗ A`. -/
noncomputable abbrev phB : B ⊗[R] A₁ →ₐ[R] B ⊗[R] A :=
  Algebra.TensorProduct.map (AlgHom.id R B) φ

/-- `B ⊗ I → B ⊗ A₁`, with `I = ker φ`. -/
noncomputable abbrev incB : B ⊗[R] (LinearMap.ker φ.toLinearMap) →ₗ[R] B ⊗[R] A₁ :=
  LinearMap.lTensor B (LinearMap.ker φ.toLinearMap).subtype

lemma phB_toLinearMap : (phB B φ).toLinearMap = LinearMap.lTensor B φ.toLinearMap := by
  refine TensorProduct.ext' fun x y => ?_
  rfl

variable {φ}

theorem phB_surjective (hs : Function.Surjective φ) : Function.Surjective (phB B φ) := by
  have := LinearMap.lTensor_surjective B (g := φ.toLinearMap) hs
  intro z
  obtain ⟨x, hx⟩ := this z
  exact ⟨x, by rw [← hx, ← phB_toLinearMap]; rfl⟩

/-- The kernel of the base change is the image of `B ⊗ I` (right exactness). -/
theorem ker_phB (hs : Function.Surjective φ) (x : B ⊗[R] A₁) (hx : phB B φ x = 0) :
    ∃ y, incB B φ y = x := by
  have ex := lTensor_exact B (LinearMap.exact_subtype_ker_map φ.toLinearMap) hs
  have : (LinearMap.lTensor B φ.toLinearMap) x = 0 := by rw [← phB_toLinearMap]; exact hx
  exact (ex x).1 this

lemma incB_mul (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (s t : B ⊗[R] (LinearMap.ker φ.toLinearMap)) :
    incB B φ s * incB B φ t = 0 := by
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_mul]
  | add s s' h h' => rw [map_add, add_mul, h, h', add_zero]
  | tmul b i =>
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero]
    | add t t' h h' => rw [map_add, mul_add, h, h', add_zero]
    | tmul b' i' =>
      change (b ⊗ₜ[R] (i : A₁)) * (b' ⊗ₜ[R] (i' : A₁)) = 0
      rw [Algebra.TensorProduct.tmul_mul_tmul, hq _ _ i.2 i'.2, TensorProduct.tmul_zero]

/-- **The base change is a first order thickening.** -/
theorem phB_sq (hs : Function.Surjective φ) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (x y : B ⊗[R] A₁) (hx : phB B φ x = 0) (hy : phB B φ y = 0) : x * y = 0 := by
  obtain ⟨s, rfl⟩ := ker_phB B hs x hx
  obtain ⟨t, rfl⟩ := ker_phB B hs y hy
  exact incB_mul B hq s t

/-- **For `B` flat its ideal is `B ⊗ I`**: `B ⊗ I → ker (B ⊗ A₁ → B ⊗ A)` is bijective. -/
theorem incB_injective [Module.Flat R B] : Function.Injective (incB B φ) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)

theorem phB_incB (y : B ⊗[R] (LinearMap.ker φ.toLinearMap)) : phB B φ (incB B φ y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add s t h h' => rw [map_add, map_add, h, h', add_zero]
  | tmul b i =>
    change Algebra.TensorProduct.map (AlgHom.id R B) φ (b ⊗ₜ[R] (i : A₁)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    have : φ i = 0 := i.2
    rw [this, TensorProduct.tmul_zero]


/-! ### The ideal of a first order thickening is a module over the quotient -/

section KerModule

variable {E₁ E : Type u} [CommRing E₁] [CommRing E] {ψ : E₁ →+* E} (hs : Function.Surjective ψ)
  (hq : ∀ x y, ψ x = 0 → ψ y = 0 → x * y = 0)

include hq in
lemma lift_mul_eq (r : E) (s : E₁) (hs' : ψ s = r) (n : RingHom.ker ψ) :
    Function.surjInv hs r * n = s * n := by
  have h0 : ψ (Function.surjInv hs r - s) = 0 := by
    rw [map_sub, Function.surjInv_eq hs, hs', sub_self]
  have := hq _ _ h0 n.2
  rwa [sub_mul, sub_eq_zero] at this

include hq in
/-- `I` as an `E₁ / I`-module. -/
@[reducible] noncomputable def kerModule : Module E (RingHom.ker ψ) where
  smul r n := ⟨Function.surjInv hs r * n, Ideal.mul_mem_left _ _ n.2⟩
  one_smul n := Subtype.ext ((lift_mul_eq hs hq 1 1 (map_one ψ) n).trans (one_mul _))
  mul_smul r r' n := Subtype.ext (by
    change Function.surjInv hs (r * r') * n = Function.surjInv hs r * (Function.surjInv hs r' * n)
    rw [← mul_assoc, lift_mul_eq hs hq (r * r') (Function.surjInv hs r * Function.surjInv hs r') (by rw [map_mul, Function.surjInv_eq hs, Function.surjInv_eq hs]) n])
  smul_zero r := Subtype.ext (mul_zero _)
  smul_add r n n' := Subtype.ext (mul_add _ _ _)
  add_smul r r' n := Subtype.ext (by
    change Function.surjInv hs (r + r') * n = Function.surjInv hs r * n + Function.surjInv hs r' * n
    rw [← add_mul, lift_mul_eq hs hq (r + r') (Function.surjInv hs r + Function.surjInv hs r') (by rw [map_add, Function.surjInv_eq hs, Function.surjInv_eq hs]) n])
  zero_smul n := Subtype.ext ((lift_mul_eq hs hq 0 0 (map_zero ψ) n).trans (zero_mul _))

include hq in
lemma kerModule_hN (x : E₁) (n : RingHom.ker ψ) :
    ((@HSMul.hSMul _ _ _ (@instHSMul _ _ (kerModule hs hq).toSMul) (ψ x) n : RingHom.ker ψ) : E₁) = x * n :=
  lift_mul_eq hs hq _ x rfl n

end KerModule

/-! ### The torsor of lifts on `T = Spec B`

`P(B)` is the set of lifts `Spec (B ⊗ A₁) → Y` over `Z` of `a`, and `F(B)` is
`Hom(a^*Ω_{Y/Z}, C)` on `X'_T`, as lifts `Spec (B ⊗ A)[C_T] → Y` over `Z` of `a`. The printed
torsor structure holds for every `B`. -/

section TorsorB

open CategoryTheory AlgebraicGeometry AlgMag.GB AlgMag.Lifts AlgMag.Sec10Printed

variable {B}
variable (hs : Function.Surjective φ) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) (a : Spec (CommRingCat.of A) ⟶ Y)
  (b : Spec (CommRingCat.of A₁) ⟶ Z) (w : a ≫ f = sp φ.toRingHom ≫ b)

/-- `a` on `X_T`. -/
noncomputable abbrev aB : Spec (CommRingCat.of (B ⊗[R] A)) ⟶ Y :=
  sp (Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom ≫ a

/-- `b` on `X'_T`. -/
noncomputable abbrev bB : Spec (CommRingCat.of (B ⊗[R] A₁)) ⟶ Z :=
  sp (Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom ≫ b

include hs hq in
lemma phB_sq' : ∀ x y, (phB B φ).toRingHom x = 0 → (phB B φ).toRingHom y = 0 → x * y = 0 :=
  phB_sq B hs hq

theorem wB (w : a ≫ f = sp φ.toRingHom ≫ b) :
    aB (B := B) a ≫ f = sp (phB B φ).toRingHom ≫ bB (B := B) b := by
  rw [Category.assoc, w, ← Category.assoc, ← Category.assoc, ← sp_comp, ← sp_comp]
  congr 2

/-- **The printed torsor of lifts on `T = Spec B`, for every `R`-algebra `B`**: the lifts
`Spec (B ⊗ A₁) → Y` over `Z` of `a` form a torsor under the group `F(B)` of lifts
`Spec (B ⊗ A)[ker] → Y` over `Z` of `a`, with `diff` the difference; `ker = B ⊗ I` for `B` flat
(`incB_injective`). -/
theorem torsorB (w : a ≫ f = sp φ.toRingHom ≫ b) :
    letI := kerModule (phB_surjective B hs) (phB_sq' hs hq (B := B))
    let ψ := (phB B φ).toRingHom
    let hψ := phB_surjective B hs
    let hN := kerModule_hN hψ (phB_sq' hs hq (B := B))
    let hQ := phB_sq' hs hq (B := B)
    (∀ x y z : Pl ψ f (aB a) (bB b) PUnit.{u + 1},
        diffL hψ hN hQ (wB f a b w) x y + diffL hψ hN hQ (wB f a b w) y z =
          diffL hψ hN hQ (wB f a b w) x z) ∧
      (∀ x y : Pl ψ f (aB a) (bB b) PUnit.{u + 1}, diffL hψ hN hQ (wB f a b w) x y = 0 → x = y) ∧
      (∀ (y : Pl ψ f (aB a) (bB b) PUnit.{u + 1}) (v : L f (aB a) (RingHom.ker ψ) PUnit.{u + 1}),
        ∃ x, diffL hψ hN hQ (wB f a b w) x y = v) := by
  letI := kerModule (phB_surjective B hs) (phB_sq' hs hq (B := B))
  exact ⟨fun x y z => diffL_add _ _ _ _ x y z, fun x y h => Pl_eq_of_diffL _ _ _ _ x y h,
    fun y v => ⟨_, diffL_addL _ _ _ _ y v⟩⟩

end TorsorB

end AlgMag.Prop101General

