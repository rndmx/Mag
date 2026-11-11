/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.OpenCellLevi

/-!
# The open cell map is a monomorphism

On `A`-points, `openCellMap λ` is the multiplication `(u, z, v) ↦ u z v` of
`U(-λ)(A) × Z(λ)(A) × U(λ)(A)` into `G(A)` (`toConv_comp_openCellMap`). Since that map is
injective (`TauCeti.Cocharacter.mul_injective_openCell`), two `k`-algebra maps out of the open
cell ring agreeing after `openCellMap λ` are equal (`openCellMap_comp_injective`): the open cell
`U(-λ) × Z(λ) × U(λ) → G` is a monomorphism of affine `k`-schemes.
-/

suppress_compilation

open TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable (l : H →ₐc[k] LaurentPolynomial k)
variable {A : Type u} [CommRing A] [Algebra k A]

/-- A `k`-algebra map out of `(B ⊗ C) ⊗ D` is the product of its three restrictions. -/
lemma algHom_tensor3_eq {B C D : Type*} [CommRing B] [CommRing C] [CommRing D] [Algebra k B]
    [Algebra k C] [Algebra k D] (f : (B ⊗[k] C) ⊗[k] D →ₐ[k] A) :
    f = (Algebra.TensorProduct.lmul' k).comp (Algebra.TensorProduct.map
      ((Algebra.TensorProduct.lmul' k).comp (Algebra.TensorProduct.map
        (f.comp ((Algebra.TensorProduct.includeLeft (S := k)).comp
          (Algebra.TensorProduct.includeLeft (S := k))))
        (f.comp ((Algebra.TensorProduct.includeLeft (S := k)).comp
          Algebra.TensorProduct.includeRight))))
      (f.comp Algebra.TensorProduct.includeRight)) := by
  apply Algebra.TensorProduct.ext'
  intro x d
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
  | tmul b c =>
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit [HopfAlgebra k H] in
lemma map_comp_map_assoc {B₁ B₂ B₃ C₁ C₂ C₃ E : Type*} [CommRing B₁] [CommRing B₂] [CommRing B₃]
    [CommRing C₁] [CommRing C₂] [CommRing C₃] [CommRing E] [Algebra k B₁] [Algebra k B₂]
    [Algebra k B₃] [Algebra k C₁] [Algebra k C₂] [Algebra k C₃] [Algebra k E]
    (f₂ : B₂ →ₐ[k] B₃) (f₁ : B₁ →ₐ[k] B₂) (g₂ : C₂ →ₐ[k] C₃) (g₁ : C₁ →ₐ[k] C₂)
    (e : E →ₐ[k] B₁ ⊗[k] C₁) :
    (Algebra.TensorProduct.map f₂ g₂).comp ((Algebra.TensorProduct.map f₁ g₁).comp e) =
      (Algebra.TensorProduct.map (f₂.comp f₁) (g₂.comp g₁)).comp e := by
  rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp]

/-- The `U(-λ)`-coordinate of an `A`-point of the open cell. -/
def openCellPoint₁ (f : OpenCellRing l →ₐ[k] A) : WithConv (H →ₐ[k] A) :=
  toConv ((f.comp ((Algebra.TensorProduct.includeLeft (S := k)).comp
    (Algebra.TensorProduct.includeLeft (S := k)))).comp (Ideal.Quotient.mkₐ k _))

/-- The `Z(λ)`-coordinate of an `A`-point of the open cell. -/
def openCellPoint₂ (f : OpenCellRing l →ₐ[k] A) : WithConv (H →ₐ[k] A) :=
  toConv ((f.comp ((Algebra.TensorProduct.includeLeft (S := k)).comp
    Algebra.TensorProduct.includeRight)).comp (Ideal.Quotient.mkₐ k _))

/-- The `U(λ)`-coordinate of an `A`-point of the open cell. -/
def openCellPoint₃ (f : OpenCellRing l →ₐ[k] A) : WithConv (H →ₐ[k] A) :=
  toConv ((f.comp Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ k _))

/-- **On points, the open cell map is multiplication `(u, z, v) ↦ u z v`.** -/
theorem toConv_comp_openCellMap (f : OpenCellRing l →ₐ[k] A) :
    toConv (f.comp (openCellMap l)) =
      openCellPoint₁ l f * openCellPoint₂ l f * openCellPoint₃ l f := by
  rw [AlgHom.convMul_def, AlgHom.convMul_def]
  congr 1
  conv_lhs => rw [algHom_tensor3_eq f]
  simp only [openCellMap, openCellPoint₁, openCellPoint₂, openCellPoint₃, ofConv_toConv,
    AlgHom.comp_assoc]
  simp only [AlgHom.comp_id, AlgHom.comp_assoc, map_comp_map_assoc]

lemma mem_of_quotient_point {I : HopfIdeal k H} (g : H ⧸ I.toIdeal →ₐ[k] A)
    (x : H) (hx : x ∈ I) : (g.comp (Ideal.Quotient.mkₐ k I.toIdeal)) x = 0 := by
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr ((HopfIdeal.mem_toIdeal (I := I)).mpr hx), map_zero]

theorem openCellPoint₁_mem (f : OpenCellRing l →ₐ[k] A) :
    openCellPoint₁ l f ∈ unipotent A l.oppositeCocharacter := by
  rw [← BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  exact fun x hx => mem_of_quotient_point _ x hx

theorem openCellPoint₂_mem (f : OpenCellRing l →ₐ[k] A) :
    openCellPoint₂ l f ∈ levi A l := by
  have h := quotientPointsSubgroup_leviDefiningHopfIdeal l (CommAlgCat.of k A)
  change openCellPoint₂ l f ∈ levi (CommAlgCat.of k A) l
  rw [← h, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  exact fun x hx => mem_of_quotient_point _ x hx

theorem openCellPoint₃_mem (f : OpenCellRing l →ₐ[k] A) :
    openCellPoint₃ l f ∈ unipotent A l := by
  rw [← BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  exact fun x hx => mem_of_quotient_point _ x hx

/-- **The open cell is a monomorphism.** Two `k`-algebra maps out of the open cell ring which
agree after `openCellMap λ` are equal. -/
theorem openCellMap_comp_injective {f g : OpenCellRing l →ₐ[k] A}
    (h : f.comp (openCellMap l) = g.comp (openCellMap l)) : f = g := by
  have e : openCellPoint₁ l f * openCellPoint₂ l f * openCellPoint₃ l f =
      openCellPoint₁ l g * openCellPoint₂ l g * openCellPoint₃ l g := by
    rw [← toConv_comp_openCellMap, ← toConv_comp_openCellMap, h]
  obtain ⟨h1, h2, h3⟩ := mul_injective_openCell l (openCellPoint₁_mem l f)
    (openCellPoint₁_mem l g) (openCellPoint₂_mem l f) (openCellPoint₂_mem l g)
    (openCellPoint₃_mem l f) (openCellPoint₃_mem l g) e
  have q1 := Ideal.Quotient.algHom_ext k (congrArg ofConv h1)
  have q2 := Ideal.Quotient.algHom_ext k (congrArg ofConv h2)
  have q3 := Ideal.Quotient.algHom_ext k (congrArg ofConv h3)
  rw [algHom_tensor3_eq f, algHom_tensor3_eq g, q1, q2, q3]

end AlgMag.Reductive
