/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.

Compiled; no sorry.
-/
import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The tangent space of a product: `Lie(G₁ × G₂) = Lie G₁ × Lie G₂`

For bialgebras `A`, `B` over a field `k`, the point derivations at the counit satisfy
`Der_ε(A ⊗ B) ≃ₗ[k] Der_ε(A) × Der_ε(B)`, `D ↦ (D(· ⊗ 1), D(1 ⊗ ·))`, with inverse
`(D₁, D₂) ↦ (a ⊗ b ↦ ε(b) D₁ a + ε(a) D₂ b)`. Hence
`dim ω_{A⊗B} = dim ω_A + dim ω_B` (`finrank_cotangentSpace_tensorProduct`).
-/

namespace AlgMag.OpenCellNotes

open scoped TensorProduct
open TensorProduct

universe u

variable {k : Type u} [Field k]

/-- Point derivations at the counit with values in `k`. -/
abbrev PtDer (A : Type u) [CommRing A] [Bialgebra k A] :=
  Derivation k A (TauCeti.Bialgebra.CounitAlgebra k A k)

local notation "τ" => TauCeti.Bialgebra.CounitAlgebra.algEquivSelf

section Generic

variable {A : Type u} [CommRing A] [Bialgebra k A]

/-- Leibniz rule of a point derivation, read in `k`. -/
lemma ptDer_mul (D : PtDer (k := k) A) (x y : A) :
    τ k A k (D (x * y)) =
      Coalgebra.counit (R := k) x * τ k A k (D y) + Coalgebra.counit (R := k) y * τ k A k (D x) := by
  rw [Derivation.leibniz, map_add, TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul,
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul]
  simp

lemma ptDer_ext {D D' : PtDer (k := k) A} (h : ∀ x, τ k A k (D x) = τ k A k (D' x)) : D = D' :=
  Derivation.ext fun x => (τ k A k).injective (h x)

/-- The `k`-valued linear map underlying a point derivation. -/
noncomputable def val (D : PtDer (k := k) A) : A →ₗ[k] k :=
  (τ k A k).toLinearMap ∘ₗ D.toLinearMap

@[simp] lemma val_apply (D : PtDer (k := k) A) (x : A) : val D x = τ k A k (D x) := rfl

/-- A point derivation from a `k`-valued linear map satisfying the Leibniz rule. -/
noncomputable def mkPt (f : A →ₗ[k] k)
    (h : ∀ x y, f (x * y) = Coalgebra.counit (R := k) x * f y + Coalgebra.counit (R := k) y * f x) :
    PtDer (k := k) A :=
  Derivation.mk' ((τ k A k).symm.toLinearMap ∘ₗ f) fun x y => by
    apply (τ k A k).injective
    rw [map_add, TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul,
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul]
    simp [h]; rfl

@[simp] lemma algEquivSelf_mkPt (f : A →ₗ[k] k) (h) (x : A) :
    τ k A k (mkPt f h x) = f x := rfl

end Generic

variable {A B : Type u} [CommRing A] [CommRing B] [Bialgebra k A] [Bialgebra k B]

lemma counit_tmul' (a : A) (b : B) :
    Coalgebra.counit (R := k) (a ⊗ₜ[k] b) =
      Coalgebra.counit (R := k) a * Coalgebra.counit (R := k) b := by
  rw [TensorProduct.counit_tmul, smul_eq_mul, mul_comm]

/-- Restriction of a point derivation along `a ↦ a ⊗ 1`. -/
noncomputable def restrictLeft (D : PtDer (k := k) (A ⊗[k] B)) : PtDer (k := k) A :=
  mkPt (val D ∘ₗ (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toLinearMap)
    fun a a' => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.includeLeft_apply, val_apply]
      rw [show (a * a') ⊗ₜ[k] (1 : B) = (a ⊗ₜ[k] (1 : B)) * (a' ⊗ₜ[k] (1 : B)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], ptDer_mul, counit_tmul',
        counit_tmul', Bialgebra.counit_one, mul_one, mul_one]

/-- Restriction of a point derivation along `b ↦ 1 ⊗ b`. -/
noncomputable def restrictRight (D : PtDer (k := k) (A ⊗[k] B)) : PtDer (k := k) B :=
  mkPt (val D ∘ₗ (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toLinearMap)
    fun b b' => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.includeRight_apply, val_apply]
      rw [show (1 : A) ⊗ₜ[k] (b * b') = ((1 : A) ⊗ₜ[k] b) * ((1 : A) ⊗ₜ[k] b') by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], ptDer_mul, counit_tmul',
        counit_tmul', Bialgebra.counit_one, one_mul, one_mul]

@[simp] lemma algEquivSelf_restrictLeft (D : PtDer (k := k) (A ⊗[k] B)) (a : A) :
    τ k A k (restrictLeft D a) = τ k (A ⊗[k] B) k (D (a ⊗ₜ 1)) := rfl

@[simp] lemma algEquivSelf_restrictRight (D : PtDer (k := k) (A ⊗[k] B)) (b : B) :
    τ k B k (restrictRight D b) = τ k (A ⊗[k] B) k (D (1 ⊗ₜ b)) := rfl

/-- The glued linear map `a ⊗ b ↦ D₁ a · ε(b) + ε(a) · D₂ b`. -/
noncomputable def glueLin (D₁ : PtDer (k := k) A) (D₂ : PtDer (k := k) B) :
    A ⊗[k] B →ₗ[k] k :=
  LinearMap.mul' k k ∘ₗ TensorProduct.map (val D₁) (Coalgebra.counit (R := k) (A := B)) +
    LinearMap.mul' k k ∘ₗ TensorProduct.map (Coalgebra.counit (R := k) (A := A)) (val D₂)

lemma glueLin_tmul (D₁ : PtDer (k := k) A) (D₂ : PtDer (k := k) B) (a : A) (b : B) :
    glueLin D₁ D₂ (a ⊗ₜ b) =
      τ k A k (D₁ a) * Coalgebra.counit (R := k) b +
        Coalgebra.counit (R := k) a * τ k B k (D₂ b) := by
  simp [glueLin]; rfl

lemma glueLin_leibniz (D₁ : PtDer (k := k) A) (D₂ : PtDer (k := k) B) (x y : A ⊗[k] B) :
    glueLin D₁ D₂ (x * y) =
      Coalgebra.counit (R := k) x * glueLin D₁ D₂ y +
        Coalgebra.counit (R := k) y * glueLin D₁ D₂ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]; ring
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, glueLin_tmul, glueLin_tmul, glueLin_tmul,
        counit_tmul', counit_tmul', ptDer_mul, ptDer_mul, Bialgebra.counit_mul,
        Bialgebra.counit_mul]
      ring

/-- The glued point derivation. -/
noncomputable def glue (D₁ : PtDer (k := k) A) (D₂ : PtDer (k := k) B) :
    PtDer (k := k) (A ⊗[k] B) :=
  mkPt (glueLin D₁ D₂) (glueLin_leibniz D₁ D₂)

/-- **`Der_ε(A ⊗ B) ≃ Der_ε(A) × Der_ε(B)`.** -/
noncomputable def ptDerTensorEquiv :
    PtDer (k := k) (A ⊗[k] B) ≃ₗ[k] PtDer (k := k) A × PtDer (k := k) B where
  toFun D := (restrictLeft D, restrictRight D)
  map_add' D D' := Prod.ext (ptDer_ext fun x => rfl) (ptDer_ext fun x => rfl)
  map_smul' c D := Prod.ext (ptDer_ext fun x => rfl) (ptDer_ext fun x => rfl)
  invFun p := glue p.1 p.2
  left_inv D := by
    refine ptDer_ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, ← map_add, ← map_add]
    | tmul a b =>
      have hab : a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : B)) * ((1 : A) ⊗ₜ[k] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      simp only [glue, algEquivSelf_mkPt, glueLin_tmul, algEquivSelf_restrictLeft,
        algEquivSelf_restrictRight]
      rw [hab, ptDer_mul, counit_tmul', counit_tmul', Bialgebra.counit_one, Bialgebra.counit_one]
      ring
  right_inv p := by
    obtain ⟨D₁, D₂⟩ := p
    refine Prod.ext (ptDer_ext fun a => ?_) (ptDer_ext fun b => ?_)
    · change glueLin D₁ D₂ (a ⊗ₜ[k] 1) = τ k A k (D₁ a)
      rw [glueLin_tmul, Bialgebra.counit_one, Derivation.map_one_eq_zero, map_zero]
      ring
    · change glueLin D₁ D₂ (1 ⊗ₜ[k] b) = τ k B k (D₂ b)
      rw [glueLin_tmul, Bialgebra.counit_one, Derivation.map_one_eq_zero, map_zero]
      ring

/-- **`dim ω_{A⊗B} = dim ω_A + dim ω_B`.** -/
theorem finrank_cotangentSpace_tensorProduct
    [Module.Finite k (TauCeti.Bialgebra.CotangentSpace k A)]
    [Module.Finite k (TauCeti.Bialgebra.CotangentSpace k B)] :
    Module.finrank k (TauCeti.Bialgebra.CotangentSpace k (A ⊗[k] B)) =
      Module.finrank k (TauCeti.Bialgebra.CotangentSpace k A) +
        Module.finrank k (TauCeti.Bialgebra.CotangentSpace k B) := by
  rw [← Derivation.finrank_eq_finrank_cotangentSpace,
    ← Derivation.finrank_eq_finrank_cotangentSpace,
    ← Derivation.finrank_eq_finrank_cotangentSpace]
  exact (ptDerTensorEquiv (k := k) (A := A) (B := B)).finrank_eq.trans Module.finrank_prod

end AlgMag.OpenCellNotes
