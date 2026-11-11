/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Prop101General2
import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Proposition 10.1 for a general affine flat `G`: the action of `G(T)` on `X'_T`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), proof of Proposition 10.1 (p. 169).
Setting: `S = Spec R` affine, `G = Spec H` with `H` a commutative Hopf `R`-algebra, `X' = Spec A₁`
affine (agreed erratum), the action of `G` on `X'` given by a coaction `ρ : A₁ → H ⊗ A₁`.
A point `g ∈ G(T) = Hom(H, B)` of `T = Spec B` acts on `X'_T = Spec (B ⊗ A₁)` by the ring map
`τ g : b ⊗ x ↦ b · (g ⊗ 1)(ρ x)`, and `τ (g' * g) = τ g ∘ τ g'` (convolution product).
-/

open TensorProduct

universe u

namespace AlgMag.Prop101General

open Algebra.TensorProduct

variable {R : Type u} [CommRing R] {Hh : Type u} [CommRing Hh] [HopfAlgebra R Hh]
  {A₁ : Type u} [CommRing A₁] [Algebra R A₁]

/-- A comodule algebra structure: coassociative and counital coaction. -/
structure Coact (Hh A₁ : Type u) [CommRing Hh] [HopfAlgebra R Hh] [CommRing A₁] [Algebra R A₁] where
  ρ : A₁ →ₐ[R] Hh ⊗[R] A₁
  coassoc : (map (Bialgebra.comulAlgHom R Hh) (AlgHom.id R A₁)).comp ρ =
    (Algebra.TensorProduct.assoc R R R Hh Hh A₁).symm.toAlgHom.comp ((map (AlgHom.id R Hh) ρ).comp ρ)
  counit : (map (Bialgebra.counitAlgHom R Hh) (AlgHom.id R A₁)).comp ρ =
    (Algebra.TensorProduct.lid R A₁).symm.toAlgHom

variable (c : Coact (R := R) Hh A₁) {B : Type u} [CommRing B] [Algebra R B]

/-- `x ↦ (g ⊗ 1)(ρ x)`. -/
noncomputable def kap (g : Hh →ₐ[R] B) : A₁ →ₐ[R] B ⊗[R] A₁ := (map g (AlgHom.id R A₁)).comp c.ρ

/-- **The action of `g` on `X'_T`**, as a ring map of `B ⊗ A₁`. -/
noncomputable def tau (g : Hh →ₐ[R] B) : B ⊗[R] A₁ →ₐ[R] B ⊗[R] A₁ :=
  lift includeLeft (kap c g) (fun _ _ => Commute.all _ _)

lemma tau_tmul (g : Hh →ₐ[R] B) (b : B) (x : A₁) : tau c g (b ⊗ₜ x) = (b ⊗ₜ 1) * kap c g x := by
  simp [tau]

lemma tau_left (g : Hh →ₐ[R] B) : (tau c g).comp includeLeft = includeLeft :=
  AlgHom.ext fun b => by simp [tau]

lemma tau_right (g : Hh →ₐ[R] B) : (tau c g).comp includeRight = kap c g :=
  AlgHom.ext fun x => by simp [tau]

/-- `τ 1 = id`. -/
theorem tau_one : tau c (WithConv.ofConv (1 : WithConv (Hh →ₐ[R] B))) = AlgHom.id R _ := by
  refine Algebra.TensorProduct.ext (by ext b; simp [tau]) ?_
  have e : kap c (WithConv.ofConv (1 : WithConv (Hh →ₐ[R] B))) = includeRight := by
    have : (map (WithConv.ofConv (1 : WithConv (Hh →ₐ[R] B))) (AlgHom.id R A₁)) =
        (map (Algebra.ofId R B) (AlgHom.id R A₁)).comp (map (Bialgebra.counitAlgHom R Hh) (AlgHom.id R A₁)) := by
      rw [← Algebra.TensorProduct.map_comp]; rfl
    rw [kap, this, AlgHom.comp_assoc, c.counit]
    ext x
    simp
  change (tau c _).comp includeRight = (AlgHom.id R _).comp includeRight
  rw [tau_right, e]
  rfl

/-- `τ (g' * g) = τ g ∘ τ g'`. -/
theorem tau_mul (g g' : Hh →ₐ[R] B) :
    tau c (WithConv.ofConv (WithConv.toConv g' * WithConv.toConv g)) = (tau c g).comp (tau c g') := by
  refine Algebra.TensorProduct.ext ?_ ?_
  · ext b; simp [tau]
  change (tau c _).comp includeRight = ((tau c g).comp (tau c g')).comp includeRight
  rw [AlgHom.comp_assoc, tau_right, tau_right]
  -- both sides are `A₁ → B ⊗ A₁`, factor through `ρ`
  have e₁ : kap c (WithConv.ofConv (WithConv.toConv g' * WithConv.toConv g)) =
      ((Algebra.TensorProduct.map (lmul' R) (AlgHom.id R A₁)).comp
        ((Algebra.TensorProduct.map (Algebra.TensorProduct.map g' g) (AlgHom.id R A₁)).comp
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R Hh) (AlgHom.id R A₁)))).comp c.ρ := by
    rw [kap, AlgHom.convMul_def]
    congr 1
    refine Algebra.TensorProduct.ext ?_ ?_ <;> ext <;> simp
  have e₂ : (tau c g).comp (kap c g') = (lift (includeLeft.comp g') (kap c g) (fun _ _ => Commute.all _ _)).comp c.ρ := by
    rw [kap, ← AlgHom.comp_assoc]
    congr 1
    refine Algebra.TensorProduct.ext ?_ ?_ <;> ext <;> simp [tau, ← Algebra.TensorProduct.one_def]
  rw [e₁, e₂, AlgHom.comp_assoc, AlgHom.comp_assoc, c.coassoc, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc]
  congr 1
  refine Algebra.TensorProduct.ext ?_ ?_
  · ext h; simp [Algebra.TensorProduct.one_def]
  · ext x
    have hl : ∀ y : Hh ⊗[R] A₁, (Algebra.TensorProduct.map (lmul' R) (AlgHom.id R A₁))
        ((Algebra.TensorProduct.map (Algebra.TensorProduct.map g' g) (AlgHom.id R A₁))
          ((Algebra.TensorProduct.assoc R R R Hh Hh A₁).symm ((1 : Hh) ⊗ₜ y))) =
        (Algebra.TensorProduct.map g (AlgHom.id R A₁)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => rw [TensorProduct.tmul_add, map_add, map_add, map_add, hy, hz, map_add]
      | tmul h y => simp
    have := hl (c.ρ x)
    simp only [AlgHom.restrictScalars_apply, AlgHom.comp_apply, includeRight_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom] at this ⊢
    rw [this, Algebra.TensorProduct.lift_tmul, kap, AlgHom.comp_apply, AlgHom.comp_apply, map_one, map_one, one_mul]

end AlgMag.Prop101General
