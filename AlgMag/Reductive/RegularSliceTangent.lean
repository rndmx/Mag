/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularSlice
import AlgMag.Reductive.RegularSliceDifferential
import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint

/-!
# The tangent map of the slice map at `(e, e, t)` (C2(d), part (a))

`C = CounitAlgebra k H k`, `V = Derivation k H C = Lie G`, `D = C[ε]`. A tangent vector `d`
gives the dual-number point `tanPt d = e + ε d`; constant points embed by `ι`.

* `conj_tanPt`: `t⁻¹ (e + εZ) t (e + εH) (e + εZ)⁻¹ = e + ε (Ad(t⁻¹) Z - Z + H)`;
* `slicePoint X Y pt`: the dual-number point `(e + εX, e + εY, pt)` of `U⁻ × U⁺ × T`;
* `sliceMap_tangent`: composing it with `μ^*` and translating by `t⁻¹` gives
  `e + ε · sliceTangentMap (Ad(t⁻¹)) Um Up L₀ (X, Y, H)`.
-/

suppress_compilation

open Magnetism TauCeti WithConv TrivSqZeroExt
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]

local notation "Cv" => Bialgebra.CounitAlgebra k H k

/-- `e + ε d`. -/
def tanPt (d : Derivation k H Cv) : WithConv (H →ₐ[k] DualNumber Cv) :=
  ((derivationMulEquivTangentKer k H k (Multiplicative.ofAdd d)) :
    WithConv (H →ₐ[k] DualNumber Cv))

/-- Constant dual-number points. -/
def constPt : WithConv (H →ₐ[k] Cv) →* WithConv (H →ₐ[k] DualNumber Cv) :=
  AlgHom.mapValue (inlAlgHom k Cv Cv)

lemma tanPt_add (d d' : Derivation k H Cv) : tanPt (d + d') = tanPt d * tanPt d' := by
  rw [tanPt, tanPt, tanPt, ofAdd_add, map_mul]; rfl

lemma tanPt_neg (d : Derivation k H Cv) : tanPt (-d) = (tanPt d)⁻¹ := by
  rw [tanPt, tanPt, ofAdd_neg, map_inv]; rfl

lemma tanPt_sub (d d' : Derivation k H Cv) : tanPt (d - d') = tanPt d * (tanPt d')⁻¹ := by
  rw [sub_eq_add_neg, tanPt_add, tanPt_neg]

/-- `g (e + εZ) g⁻¹ = e + ε Ad(g) Z`. -/
lemma constPt_conj_tanPt (g : WithConv (H →ₐ[k] Cv)) (Z : Derivation k H Cv) :
    constPt g * tanPt Z * (constPt g)⁻¹ = tanPt (Derivation.adDerivation k g Z) := by
  have hker : constPt g * tanPt Z * (constPt g)⁻¹ ∈ tangentKer k H k :=
    (MonoidHom.normal_ker _).conj_mem _
      (derivationMulEquivTangentKer k H k (Multiplicative.ofAdd Z)).2 _
  have h := (derivationMulEquivTangentKer k H k).apply_symm_apply ⟨_, hker⟩
  have hs : (derivationMulEquivTangentKer k H k).symm ⟨_, hker⟩ =
      Multiplicative.ofAdd (Derivation.adDerivation k g Z) := by
    apply Multiplicative.toAdd.injective
    ext a
    rw [derivationMulEquivTangentKer_symm_apply]
    exact Derivation.snd_conjugate_tangentPoint Z g a
  rw [hs] at h
  exact (congrArg Subtype.val h).symm

/-- **The group computation.** `t⁻¹ ((e+εZ) (t (e+εH)) (e+εZ)⁻¹) = e + ε (Ad(t⁻¹)Z - Z + H)`. -/
theorem conj_tanPt (g : WithConv (H →ₐ[k] Cv)) (Z Hd : Derivation k H Cv) :
    (constPt g)⁻¹ * (tanPt Z * (constPt g * tanPt Hd) * (tanPt Z)⁻¹) =
      tanPt (Derivation.adDerivation k g⁻¹ Z - Z + Hd) := by
  have h1 := constPt_conj_tanPt g⁻¹ Z
  rw [map_inv, inv_inv] at h1
  rw [tanPt_add, tanPt_sub, ← h1]
  -- both sides are words in the commutative tangent kernel and `constPt g`
  have hc : tanPt Hd * (tanPt Z)⁻¹ = (tanPt Z)⁻¹ * tanPt Hd := by
    rw [← tanPt_neg, ← tanPt_add, ← tanPt_add, add_comm]
  calc (constPt g)⁻¹ * (tanPt Z * (constPt g * tanPt Hd) * (tanPt Z)⁻¹)
      = (constPt g)⁻¹ * tanPt Z * constPt g * (tanPt Hd * (tanPt Z)⁻¹) := by
        simp only [mul_assoc]
    _ = (constPt g)⁻¹ * tanPt Z * constPt g * ((tanPt Z)⁻¹ * tanPt Hd) := by rw [hc]
    _ = _ := by simp only [mul_assoc]

variable (π : H →ₐc[k] MonoidAlgebra k X)
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

lemma tanPt_eq_zero_of_mem {I : HopfIdeal k H} {d : Derivation k H Cv}
    (hd : d ∈ I.lieSubalgebra (B := k)) {a : H} (ha : a ∈ I.toIdeal) :
    (tanPt d).ofConv a = 0 := by
  rw [HopfIdeal.mem_lieSubalgebra_iff] at hd
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [tanPt, derivationMulEquivTangentKer_apply_fst, fst_zero,
      Bialgebra.CounitAlgebra.algebraMap_apply, I.counit_eq_zero (HopfIdeal.mem_toIdeal.1 ha),
      map_zero] <;> rfl
  · rw [tanPt, derivationMulEquivTangentKer_apply_snd, snd_zero]
    exact hd a ha

variable [IsAlgClosed k] [Algebra.FiniteType k H]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)

/-- `Lie U⁻`, `Lie U⁺` as submodules of `Lie G`. -/
abbrev lieSlice (ψ : X →* Multiplicative ℤ) : Submodule k (Derivation k H Cv) :=
  ((sliceIdeal π N ψ).lieSubalgebra (B := k)).toSubmodule

/-- The dual-number point `(e + εX, e + εY, pt)` on the underlying tensor product. -/
def slicePointRaw (Xd : lieSlice π N ψ⁻¹) (Yd : lieSlice π N ψ)
    (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv) :
    ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k]
      MonoidAlgebra k X →ₐ[k] DualNumber Cv :=
  Algebra.TensorProduct.productMap
    (Algebra.TensorProduct.productMap
      (Ideal.Quotient.liftₐ _ (tanPt (Xd : Derivation k H Cv)).ofConv
        fun a ha => tanPt_eq_zero_of_mem Xd.2 ha)
      (Ideal.Quotient.liftₐ _ (tanPt (Yd : Derivation k H Cv)).ofConv
        fun a ha => tanPt_eq_zero_of_mem Yd.2 ha))
    pt

/-- The dual-number point `(e + εX, e + εY, pt)` of `U⁻ × U⁺ × T`. -/
def slicePoint (Xd : lieSlice π N ψ⁻¹) (Yd : lieSlice π N ψ)
    (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv) : sliceSource π N ψ →ₐ[k] DualNumber Cv :=
  slicePointRaw π N ψ Xd Yd pt

variable (hT : compIdeal π N ≤ RingHom.ker π.toAlgHom)

/-- **The tangent map of `μ` at `(e, e, t)`.** For `t = g` and a dual-number torus point
`pt` over `t` with tangent `H` (`pt ∘ π = t (e + εH)`), the image of `(e+εX, e+εY, pt)` under
`μ`, translated by `t⁻¹`, is `e + ε ((Ad(t⁻¹) - 1)(X + Y) + H)`. -/
theorem sliceMap_tangent (g : WithConv (H →ₐ[k] Cv)) (L₀ : Submodule k (Derivation k H Cv))
    (p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × L₀)
    (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
    (hpt : toConv (pt.comp π.toAlgHom) = constPt g * tanPt (p.2 : Derivation k H Cv)) :
    (constPt g)⁻¹ * toConv ((slicePoint π N ψ p.1.1 p.1.2 pt).comp
        ((sliceMap π N ψ hT).comp (compMk π N : H →ₐ[k] compAlg π N))) =
      tanPt (sliceTangentMap (Derivation.adRepresentation k g⁻¹)
        (lieSlice π N ψ⁻¹) (lieSlice π N ψ) L₀ p) := by
  set P := slicePoint π N ψ p.1.1 p.1.2 pt
  have hm : AlgHom.mapValue P (slicePtMinus π N ψ) = tanPt (p.1.1 : Derivation k H Cv) := by
    apply WithConv.ofConv_injective; refine AlgHom.ext fun a => ?_
    change slicePointRaw π N ψ p.1.1 p.1.2 pt
      ((Ideal.Quotient.mk (sliceIdeal π N ψ⁻¹).toIdeal a ⊗ₜ[k] 1) ⊗ₜ[k] 1) = (tanPt _).ofConv a
    simp only [slicePointRaw, Algebra.TensorProduct.one_def, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one,
      one_mul, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    try rfl
  have hp : AlgHom.mapValue P (slicePtPlus π N ψ) = tanPt (p.1.2 : Derivation k H Cv) := by
    apply WithConv.ofConv_injective; refine AlgHom.ext fun a => ?_
    change slicePointRaw π N ψ p.1.1 p.1.2 pt
      ((1 ⊗ₜ[k] Ideal.Quotient.mk (sliceIdeal π N ψ).toIdeal a) ⊗ₜ[k] 1) = (tanPt _).ofConv a
    simp only [slicePointRaw, Algebra.TensorProduct.one_def, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one,
      one_mul, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    try rfl
  have ht : AlgHom.mapValue P (slicePtTorus π N ψ) = toConv (pt.comp π.toAlgHom) := by
    apply WithConv.ofConv_injective; refine AlgHom.ext fun a => ?_
    change slicePointRaw π N ψ p.1.1 p.1.2 pt ((1 : (H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k]
      (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗ₜ[k] π.toAlgHom a) = pt (π.toAlgHom a)
    simp only [slicePointRaw, Algebra.TensorProduct.one_def, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one,
      one_mul, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    try rfl
  have hcomp : toConv (P.comp ((sliceMap π N ψ hT).comp (compMk π N : H →ₐ[k] compAlg π N))) =
      AlgHom.mapValue P (sliceConj π N ψ) := by
    rw [sliceMap_comp_compMk]
    rfl
  rw [hcomp, sliceConj, conjFormula, map_mul, map_mul, map_inv, map_mul, hm, hp, ht, hpt,
    ← tanPt_add, conj_tanPt, sliceTangentMap_apply]
  rfl

end AlgMag.Reductive
