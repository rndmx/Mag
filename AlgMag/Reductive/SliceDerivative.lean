/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularSliceLattice
import AlgMag.Reductive.PointDerivationsSlice
import AlgMag.Reductive.PointDerivationsBridge

/-!
# The tangent map of the slice map at `(e, e, t₀)` is bijective (C2(d), part (a))

Generic part: left translation `L_s = (s ⊗ id) ∘ Δ` (`leftTranslationAlgHom`) with
`Q ∘ L_s = s * Q` (`toConv_comp_leftTranslationAlgHom`), compatibility with bialgebra maps,
and `pointDer_eq_of_tensor`.
-/

suppress_compilation

open Magnetism TauCeti WithConv TrivSqZeroExt
open scoped TensorProduct

namespace AlgMag.Reductive

section LeftTranslation

variable {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]

/-- Pullback by left translation by a `k`-point: `L_s = (s ⊗ id) ∘ Δ`. -/
def leftTranslationAlgHom (s : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (AlgHom.mapValue (Algebra.ofId k A) s * toConv (AlgHom.id k A)).ofConv

/-- `Q ∘ L_s = s * Q` in the convolution monoid. -/
theorem toConv_comp_leftTranslationAlgHom {C : Type*} [CommRing C] [Algebra k C]
    (Q : A →ₐ[k] C) (s : WithConv (A →ₐ[k] k)) :
    toConv (Q.comp (leftTranslationAlgHom s)) = AlgHom.mapValue (Algebra.ofId k C) s * toConv Q := by
  rw [leftTranslationAlgHom, AlgHom.comp_convMul_distrib, toConv_ofConv, AlgHom.mapValue_apply,
    AlgHom.mapValue_apply, ofConv_toConv, ofConv_toConv, ← AlgHom.comp_assoc, Algebra.comp_ofId,
    AlgHom.comp_id]

lemma mapValue_ofId_self (s : WithConv (A →ₐ[k] k)) : AlgHom.mapValue (Algebra.ofId k k) s = s := by
  rw [AlgHom.mapValue_apply]
  apply ofConv_injective
  ext a
  rfl

/-- A point composed with a left translation: `e₀ ∘ L_s = s * e₀`. -/
lemma toConv_point_comp_leftTranslationAlgHom (e₀ s : WithConv (A →ₐ[k] k)) :
    toConv (e₀.ofConv.comp (leftTranslationAlgHom s)) = s * e₀ := by
  rw [toConv_comp_leftTranslationAlgHom, mapValue_ofId_self, toConv_ofConv]

/-- `L_{t⁻¹} ∘ L_t = id`. -/
lemma leftTranslationAlgHom_inv_comp (t : WithConv (A →ₐ[k] k)) :
    (leftTranslationAlgHom t⁻¹).comp (leftTranslationAlgHom t) = AlgHom.id k A := by
  apply toConv_injective
  rw [toConv_comp_leftTranslationAlgHom, leftTranslationAlgHom, toConv_ofConv, ← mul_assoc,
    ← map_mul, mul_inv_cancel, map_one, one_mul]

lemma leftTranslationAlgHom_surjective (t : WithConv (A →ₐ[k] k)) :
    Function.Surjective (leftTranslationAlgHom t⁻¹) := fun a =>
  ⟨leftTranslationAlgHom t a, by
    rw [← AlgHom.comp_apply, leftTranslationAlgHom_inv_comp, AlgHom.id_apply]⟩

variable {B : Type*} [CommRing B] [HopfAlgebra k B]

/-- Left translation commutes with a bialgebra map: `φ ∘ L_{t ∘ φ} = L_t ∘ φ`. -/
theorem comp_leftTranslationAlgHom_mapDomain (φ : A →ₐc[k] B) (t : WithConv (B →ₐ[k] k)) :
    (φ : A →ₐ[k] B).comp (leftTranslationAlgHom (BialgHom.mapDomain φ t)) =
      (leftTranslationAlgHom t).comp (φ : A →ₐ[k] B) := by
  apply toConv_injective
  rw [toConv_comp_leftTranslationAlgHom]
  have e1 : toConv ((leftTranslationAlgHom t).comp (φ : A →ₐ[k] B)) =
      BialgHom.mapDomain (A := B) φ (toConv (leftTranslationAlgHom t)) := rfl
  rw [e1, leftTranslationAlgHom, toConv_ofConv, map_mul]
  congr 1

end LeftTranslation

section TensorExt

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- Point derivations of `A ⊗ B` are determined by their restrictions to `A` and `B`. -/
lemma pointDer_eq_of_tensor {ε : A ⊗[k] B →ₐ[k] k} {D D' : pointDer ε}
    (hA : ∀ a, D.1 (a ⊗ₜ 1) = D'.1 (a ⊗ₜ 1)) (hB : ∀ b, D.1 (1 ⊗ₜ b) = D'.1 (1 ⊗ₜ b)) :
    D = D' := by
  apply Subtype.ext
  apply TensorProduct.ext'
  intro a b
  have e : a ⊗ₜ[k] b = (a ⊗ₜ[k] (1 : B)) * ((1 : A) ⊗ₜ[k] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e, pointDer_leibniz D, pointDer_leibniz D', hA, hB]

end TensorExt

section ApplyLemmas

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [Bialgebra k H]

local notation "Cv" => Bialgebra.CounitAlgebra k H k

lemma pointDerVanishingCongr_val {A : Type*} [CommRing A] [Algebra k A]
    {ε₁ ε₂ : A →ₐ[k] k} (h : ε₁ = ε₂) (I : Ideal A) (D : pointDerVanishing ε₁ I) :
    (pointDerVanishingCongr h I D).1.1 = D.1.1 := by
  subst h; rfl

variable {Q : Type u} [CommRing Q] [Bialgebra k Q]

lemma pointDerBialgEquiv_apply (f : H →ₐc[k] Q) (hf : Function.Surjective f)
    (E : pointDer (_root_.Bialgebra.counitAlgHom k Q)) (h : H) :
    ((pointDerBialgEquiv f hf E : vanishingDer k H _) : Derivation k H Cv) h =
      (Bialgebra.CounitAlgebra.algEquivSelf k H k).symm (E.1 (f h)) := by
  simp only [pointDerBialgEquiv, LinearEquiv.trans_apply]
  change (Bialgebra.CounitAlgebra.algEquivSelf k H k).symm
    ((pointDerVanishingCongr _ _ _).1.1 h) = _
  rw [pointDerVanishingCongr_val]
  rfl

end ApplyLemmas

section Slice

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [IsAlgClosed k] [Algebra.FiniteType k H]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)
variable (τ : MonoidAlgebra k X →ₐ[k] k)

local notation "Cv" => Bialgebra.CounitAlgebra k H k
local notation "es" => Bialgebra.CounitAlgebra.algEquivSelf k H k

/-- `τ(x)`. -/
def tval (x : X) : k := τ (MonoidAlgebra.single x 1)

lemma tval_mul (x y : X) : tval τ (x * y) = tval τ x * tval τ y := by
  rw [tval, tval, tval, ← map_mul, MonoidAlgebra.single_mul_single, one_mul]

lemma tval_one : tval τ 1 = 1 := by
  rw [tval, ← MonoidAlgebra.one_def, map_one]

lemma tval_ne_zero (x : X) : tval τ x ≠ 0 := by
  intro h
  have := tval_mul τ x x⁻¹
  rw [mul_inv_cancel, tval_one, h, zero_mul] at this
  exact one_ne_zero this

variable (H) in
/-- The dual-number torus point `x ↦ τ(x) (1 + ε l(x))`. -/
def torusDualPt (l : Additive X →+ k) : MonoidAlgebra k X →ₐ[k] DualNumber Cv :=
  MonoidAlgebra.lift k (DualNumber Cv) X
    { toFun := fun x => ((tval τ x : k), (tval τ x * l (.ofMul x) : k))
      map_one' := by
        ext
        · show tval τ 1 = (1 : k)
          exact tval_one τ
        · show tval τ 1 * l (.ofMul 1) = (0 : k)
          rw [ofMul_one, map_zero, mul_zero]
      map_mul' := fun x y => by
        ext
        · show tval τ (x * y) = tval τ x * tval τ y
          exact tval_mul τ x y
        · show tval τ (x * y) * l (.ofMul (x * y)) =
            tval τ x * (tval τ y * l (.ofMul y)) + tval τ x * l (.ofMul x) * tval τ y
          rw [tval_mul, ofMul_mul, map_add]
          ring }

variable (H) in
lemma fst_torusDualPt_single (l : Additive X →+ k) (x : X) :
    fst (torusDualPt H τ l (MonoidAlgebra.single x 1)) = (tval τ x : k) := by
  simp only [torusDualPt, MonoidAlgebra.lift_single, one_smul]
  rfl

variable (H) in
lemma snd_torusDualPt_single (l : Additive X →+ k) (x : X) :
    snd (torusDualPt H τ l (MonoidAlgebra.single x 1)) = (tval τ x * l (.ofMul x) : k) := by
  simp only [torusDualPt, MonoidAlgebra.lift_single, one_smul]
  rfl

/-- The counit of `O(U^±)`, as a point (same as `sliceCounit` of EtaleSliceAssembly). -/
def srcCounit (ψ : X →* Multiplicative ℤ) : H ⧸ (sliceIdeal π N ψ).toIdeal →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (_root_.Bialgebra.counitAlgHom k H)
    (fun x hx => (sliceIdeal π N ψ).counit_eq_zero (HopfIdeal.mem_toIdeal.1 hx))

lemma srcCounit_eq (ψ : X →* Multiplicative ℤ) :
    srcCounit π N ψ = _root_.Bialgebra.counitAlgHom k (H ⧸ (sliceIdeal π N ψ).toIdeal) := by
  apply Ideal.Quotient.algHom_ext
  have h := counitAlgHom_comp_bialgHom
    (_root_.Bialgebra.Quotient.mkBialgHom (R := k) (sliceIdeal π N ψ).toIdeal)
  ext a
  have h' := congrArg (fun f => f a) h
  simp only [AlgHom.comp_apply] at h' ⊢
  change (_root_.Bialgebra.counitAlgHom k H) a = _
  exact h'.symm

/-- The base point `(e, e, τ)` of the slice (same as `sliceBasePt` of EtaleSliceAssembly). -/
def srcBasePt : sliceSource π N ψ →ₐ[k] k :=
  Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.productMap (srcCounit π N ψ⁻¹) (srcCounit π N ψ)) τ

variable (Xd : lieSlice π N ψ⁻¹) (Yd : lieSlice π N ψ) (l : Additive X →+ k)

lemma slicePoint_minus (a : H) :
    slicePoint π N ψ Xd Yd (torusDualPt H τ l)
      (((Ideal.Quotient.mk (sliceIdeal π N ψ⁻¹).toIdeal a ⊗ₜ[k]
        (1 : H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗ₜ[k] (1 : MonoidAlgebra k X) :
          ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k]
            MonoidAlgebra k X)) = (tanPt (Xd : Derivation k H Cv)).ofConv a := by
  change slicePointRaw π N ψ Xd Yd (torusDualPt H τ l) _ = _
  simp only [slicePointRaw, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one,
    Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  try rfl

lemma slicePoint_plus (a : H) :
    slicePoint π N ψ Xd Yd (torusDualPt H τ l)
      ((((1 : H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗ₜ[k]
        Ideal.Quotient.mk (sliceIdeal π N ψ).toIdeal a) ⊗ₜ[k] (1 : MonoidAlgebra k X) :
          ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k]
            MonoidAlgebra k X)) = (tanPt (Yd : Derivation k H Cv)).ofConv a := by
  change slicePointRaw π N ψ Xd Yd (torusDualPt H τ l) _ = _
  simp only [slicePointRaw, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one,
    one_mul, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  try rfl

lemma slicePoint_torus (c : MonoidAlgebra k X) :
    slicePoint π N ψ Xd Yd (torusDualPt H τ l)
      (((1 : (H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗ₜ[k] c :
          ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k]
            MonoidAlgebra k X)) = torusDualPt H τ l c := by
  change slicePointRaw π N ψ Xd Yd (torusDualPt H τ l) _ = _
  rw [Algebra.TensorProduct.one_def]
  simp only [slicePointRaw, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]

lemma fst_slicePoint (b : sliceSource π N ψ) :
    fst (slicePoint π N ψ Xd Yd (torusDualPt H τ l) b) = (srcBasePt π N ψ τ b : k) := by
  have h : ((fstHom k Cv Cv).comp (slicePoint π N ψ Xd Yd (torusDualPt H τ l)) :
        ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X →ₐ[k] Cv) =
      (((es).symm : k →ₐ[k] Cv).comp (srcBasePt π N ψ τ) : ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X →ₐ[k] Cv) := by
    ext a
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change fst (slicePoint π N ψ Xd Yd (torusDualPt H τ l) (((Ideal.Quotient.mk (sliceIdeal π N ψ⁻¹).toIdeal a ⊗ₜ[k]
        (1 : H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗ₜ[k] (1 : MonoidAlgebra k X) : ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X))) = _
      rw [slicePoint_minus, tanPt, derivationMulEquivTangentKer_apply_fst,
        Bialgebra.CounitAlgebra.algebraMap_apply]
      change (_root_.Bialgebra.counitAlgHom k H) a = _
      (simp [srcBasePt, srcCounit]) <;> rfl
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change fst (slicePoint π N ψ Xd Yd (torusDualPt H τ l) ((((1 : H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal)
        ⊗ₜ[k] Ideal.Quotient.mk (sliceIdeal π N ψ).toIdeal a) ⊗ₜ[k] (1 : MonoidAlgebra k X) :
          ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X))) = _
      rw [slicePoint_plus, tanPt, derivationMulEquivTangentKer_apply_fst,
        Bialgebra.CounitAlgebra.algebraMap_apply]
      change (_root_.Bialgebra.counitAlgHom k H) a = _
      (simp [srcBasePt, srcCounit]) <;> rfl
    · change fst (slicePoint π N ψ Xd Yd (torusDualPt H τ l) ((((1 : (H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal)
        ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗ₜ[k] MonoidAlgebra.single a 1) : ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X))) = _
      rw [slicePoint_torus, fst_torusDualPt_single]
      (simp [srcBasePt, tval]) <;> rfl
  exact congrArg (fun f => f b) h

/-- The dual-number lift of `(Xd, Yd, l)` as a point derivation at `srcBasePt τ`. -/
def sliceSndDer : pointDer (srcBasePt π N ψ τ) :=
  ⟨{ toFun := fun b => es (snd (slicePoint π N ψ Xd Yd (torusDualPt H τ l) b))
     map_add' := fun b b' => by rw [map_add, snd_add, map_add]
     map_smul' := fun c b => by
       rw [map_smul, snd_smul, map_smul]; rfl },
   fun a b => by
    change es (snd (slicePoint π N ψ Xd Yd (torusDualPt H τ l) (a * b))) =
      srcBasePt π N ψ τ a * es (snd (slicePoint π N ψ Xd Yd (torusDualPt H τ l) b)) +
      srcBasePt π N ψ τ b * es (snd (slicePoint π N ψ Xd Yd (torusDualPt H τ l) a))
    rw [← fst_slicePoint π N ψ τ Xd Yd l a, ← fst_slicePoint π N ψ τ Xd Yd l b, map_mul,
      snd_mul]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_add,
      map_mul]
    change fst _ * snd _ + snd _ * fst _ = fst _ * snd _ + fst _ * snd _
    ring⟩

lemma sliceSndDer_apply (b : sliceSource π N ψ) :
    (sliceSndDer π N ψ τ Xd Yd l).1 b = es (snd (slicePoint π N ψ Xd Yd (torusDualPt H τ l) b)) :=
  rfl

/-- The inclusion of `O(U⁻)` into the slice ring. -/
def inclMinus : H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal →ₐ[k] sliceSource π N ψ :=
  (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft :
    H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal →ₐ[k] ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X)

/-- The inclusion of `O(U⁺)` into the slice ring. -/
def inclPlus : H ⧸ (sliceIdeal π N ψ).toIdeal →ₐ[k] sliceSource π N ψ :=
  (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight :
    H ⧸ (sliceIdeal π N ψ).toIdeal →ₐ[k] ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X)

lemma srcBasePt_comp_inclMinus :
    (srcBasePt π N ψ τ).comp (inclMinus π N ψ) =
      _root_.Bialgebra.counitAlgHom k (H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) := by
  rw [← srcCounit_eq]
  apply AlgHom.ext
  intro q
  change Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.productMap (srcCounit π N ψ⁻¹) (srcCounit π N ψ)) τ
      ((q ⊗ₜ[k] (1 : H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗ₜ[k] (1 : MonoidAlgebra k X)) = _
  simp

lemma srcBasePt_comp_inclPlus :
    (srcBasePt π N ψ τ).comp (inclPlus π N ψ) =
      _root_.Bialgebra.counitAlgHom k (H ⧸ (sliceIdeal π N ψ).toIdeal) := by
  rw [← srcCounit_eq]
  apply AlgHom.ext
  intro q
  change Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.productMap (srcCounit π N ψ⁻¹) (srcCounit π N ψ)) τ
      (((1 : H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗ₜ[k] q) ⊗ₜ[k] (1 : MonoidAlgebra k X)) = _
  simp

/-- The `Lie U⁻` component of a point derivation at `(e, e, τ)`. -/
def minusPart (D : pointDer (srcBasePt π N ψ τ)) : lieSlice π N ψ⁻¹ :=
  pointDerSliceEquiv π N ψ⁻¹
    (LinearEquiv.ofEq _ _ (by rw [srcBasePt_comp_inclMinus]) (pointDerComp (inclMinus π N ψ) _ D))

/-- The `Lie U⁺` component of a point derivation at `(e, e, τ)`. -/
def plusPart (D : pointDer (srcBasePt π N ψ τ)) : lieSlice π N ψ :=
  pointDerSliceEquiv π N ψ
    (LinearEquiv.ofEq _ _ (by rw [srcBasePt_comp_inclPlus]) (pointDerComp (inclPlus π N ψ) _ D))

lemma minusPart_apply (D : pointDer (srcBasePt π N ψ τ)) (a : H) :
    ((minusPart π N ψ τ D : lieSlice π N ψ⁻¹) : Derivation k H Cv) a =
      (es).symm (D.1 (inclMinus π N ψ (Ideal.Quotient.mk _ a))) := by
  simp only [minusPart, pointDerSliceEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact pointDerBialgEquiv_apply _ _ _ a

lemma plusPart_apply (D : pointDer (srcBasePt π N ψ τ)) (a : H) :
    ((plusPart π N ψ τ D : lieSlice π N ψ) : Derivation k H Cv) a =
      (es).symm (D.1 (inclPlus π N ψ (Ideal.Quotient.mk _ a))) := by
  simp only [plusPart, pointDerSliceEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact pointDerBialgEquiv_apply _ _ _ a

lemma snd_tanPt' (d : Derivation k H Cv) (x : H) : snd ((tanPt d).ofConv x) = d x := by
  rw [tanPt, derivationMulEquivTangentKer_apply_snd]; rfl

/-- **Source side (U± factors).** A point derivation at `(e, e, τ)` whose torus part is that of
`torusDualPt l` is the dual-number derivation of `slicePoint (D⁻, D⁺, torusDualPt l)`. -/
theorem eq_sliceSndDer_of_torus (D : pointDer (srcBasePt π N ψ τ)) (l : Additive X →+ k)
    (hl : ∀ c : MonoidAlgebra k X,
      D.1 ((((1 : (H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗ₜ[k] c :
        ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X))) = es (snd (torusDualPt H τ l c))) :
    D = sliceSndDer π N ψ τ (minusPart π N ψ τ D) (plusPart π N ψ τ D) l := by
  apply pointDer_eq_of_tensor (A := (H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k]
    (H ⧸ (sliceIdeal π N ψ).toIdeal)) (B := MonoidAlgebra k X)
  · intro q
    have hin : pointDerComp (Algebra.TensorProduct.includeLeft :
          (H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal) →ₐ[k] ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X) _ D =
        pointDerComp (Algebra.TensorProduct.includeLeft :
          (H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal) →ₐ[k] ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X) _
          (sliceSndDer π N ψ τ (minusPart π N ψ τ D) (plusPart π N ψ τ D) l) := by
      apply pointDer_eq_of_tensor
      · intro q1
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q1
        change D.1 (inclMinus π N ψ (Ideal.Quotient.mk _ a)) =
          es (snd (slicePoint π N ψ (minusPart π N ψ τ D) (plusPart π N ψ τ D) (torusDualPt H τ l)
            (((Ideal.Quotient.mk (sliceIdeal π N ψ⁻¹).toIdeal a ⊗ₜ[k]
              (1 : H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗ₜ[k] (1 : MonoidAlgebra k X) : ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X))))
        rw [slicePoint_minus, snd_tanPt', minusPart_apply]
        rfl
      · intro q2
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q2
        change D.1 (inclPlus π N ψ (Ideal.Quotient.mk _ a)) =
          es (snd (slicePoint π N ψ (minusPart π N ψ τ D) (plusPart π N ψ τ D) (torusDualPt H τ l)
            ((((1 : H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗ₜ[k]
              Ideal.Quotient.mk (sliceIdeal π N ψ).toIdeal a) ⊗ₜ[k] (1 : MonoidAlgebra k X) : ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X))))
        rw [slicePoint_plus, snd_tanPt', plusPart_apply]
        rfl
    exact congrArg (fun E => E.1 q) hin
  · intro c
    change D.1 _ = es (snd (slicePoint π N ψ (minusPart π N ψ τ D) (plusPart π N ψ τ D)
      (torusDualPt H τ l) _))
    rw [hl, slicePoint_torus]

end Slice

end AlgMag.Reductive
