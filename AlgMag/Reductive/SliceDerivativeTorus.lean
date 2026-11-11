/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.SliceDerivative
import AlgMag.Reductive.LieTorusZero

/-!
# The torus factor of the slice source (C2(d), part (a))

For a `k`-point `τ` of `T = D(X)` (the torus component of `sliceBasePt π N ψ τ`, see
`sliceBasePt_torus`) and an additive map `l : Additive X →+ k`, the dual-number point
`torusDualPt H τ l : x ↦ τ(x) (1 + ε l(x))` of `SliceDerivative.lean`:

* `torusDer H τ l : pointDer τ`, `D (single x 1) = τ(x) l(x)` (`torusDer_single`);
* `exists_torusDualPt_of_pointDer`: every point derivation of `k[X]` at `τ` is of this form;
* `torusTangent π l : Lie G`, the derivation `h ↦ l'(π h)` (`l'(single x 1) = l(x)`),
  `torusTangent_mem_rootSpace : torusTangent π l ∈ rootSpace π 0`;
* `constPt_mul_tanPt_torusTangent`: `g (e + ε torusTangent π l) = torusDualPt H τ l ∘ π`
  for `g` the point `τ ∘ π` of `G` seen in `Cv` (the `hpt` hypothesis of `sliceMap_tangent`).
-/

suppress_compilation

open Magnetism TauCeti WithConv TrivSqZeroExt
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]

section Ext

omit [CommGroup X] [DecidableEq X] in
/-- Linear maps out of `k[X]` agree when they agree on the `single x 1`. -/
lemma linearMap_ext_single {M : Type*} [AddCommGroup M] [Module k M]
    {f g : MonoidAlgebra k X →ₗ[k] M}
    (h : ∀ x : X, f (MonoidAlgebra.single x 1) = g (MonoidAlgebra.single x 1)) : f = g :=
  MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring (h x)

omit [DecidableEq X] in
/-- Algebra maps out of `k[X]` agree when they agree on the `single x 1`. -/
lemma algHom_ext_single {B : Type*} [Semiring B] [Algebra k B]
    {f g : MonoidAlgebra k X →ₐ[k] B}
    (h : ∀ x : X, f (MonoidAlgebra.single x 1) = g (MonoidAlgebra.single x 1)) : f = g :=
  MonoidAlgebra.algHom_ext h (Subsingleton.elim _ _)

end Ext

-- the instance hypotheses of `torusDualPt` (SliceDerivative.lean)
variable [IsAlgClosed k] [Algebra.FiniteType k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "Cv" => Bialgebra.CounitAlgebra k H k
local notation "es" => Bialgebra.CounitAlgebra.algEquivSelf k H k

section PointDer

variable (τ : MonoidAlgebra k X →ₐ[k] k) (l : Additive X →+ k)

variable (H) in
/-- The first component of the dual torus point is `τ`. -/
lemma fst_torusDualPt (c : MonoidAlgebra k X) : es (fst (torusDualPt H τ l c)) = τ c := by
  have h : ((es : Cv →ₐ[k] k).comp ((fstHom k Cv Cv).comp (torusDualPt H τ l))) = τ := by
    apply algHom_ext_single
    intro x
    simp only [AlgHom.comp_apply, fstHom_apply, AlgEquiv.coe_toAlgHom]
    rw [fst_torusDualPt_single]
    rfl
  exact congrArg (fun f : MonoidAlgebra k X →ₐ[k] k => f c) h

variable (H) in
/-- **The point derivation of the dual torus point**: `c ↦ snd (torusDualPt H τ l c)`. -/
def torusDer : pointDer τ :=
  ⟨{ toFun := fun c => es (snd (torusDualPt H τ l c))
     map_add' := fun a b => by rw [map_add, snd_add, map_add]
     map_smul' := fun r a => by
       rw [map_smul, snd_smul, map_smul]
       rfl },
    fun a b => by
      change es (snd (torusDualPt H τ l (a * b))) =
        τ a * es (snd (torusDualPt H τ l b)) + τ b * es (snd (torusDualPt H τ l a))
      rw [map_mul, snd_mul, map_add, ← fst_torusDualPt H τ l a, ← fst_torusDualPt H τ l b]
      simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_mul]
      ring⟩

variable (H) in
lemma torusDer_apply (c : MonoidAlgebra k X) :
    (torusDer H τ l).1 c = es (snd (torusDualPt H τ l c)) := rfl

variable (H) in
lemma torusDer_single (x : X) :
    (torusDer H τ l).1 (MonoidAlgebra.single x 1) = tval τ x * l (.ofMul x) := by
  rw [torusDer_apply, snd_torusDualPt_single]
  rfl

/-- The additive map attached to a point derivation at `τ`: `x ↦ τ(x)⁻¹ D(single x 1)`. -/
def pointDerToAdd (E : pointDer τ) : Additive X →+ k where
  toFun a := (tval τ a.toMul)⁻¹ * E.1 (MonoidAlgebra.single a.toMul 1)
  map_zero' := by
    change (tval τ 1)⁻¹ * E.1 (MonoidAlgebra.single 1 1) = 0
    rw [← MonoidAlgebra.one_def, pointDer_one, mul_zero]
  map_add' a b := by
    change (tval τ (a.toMul * b.toMul))⁻¹ * E.1 (MonoidAlgebra.single (a.toMul * b.toMul) 1) =
      (tval τ a.toMul)⁻¹ * E.1 (MonoidAlgebra.single a.toMul 1) +
        (tval τ b.toMul)⁻¹ * E.1 (MonoidAlgebra.single b.toMul 1)
    have ha := tval_ne_zero τ a.toMul
    have hb := tval_ne_zero τ b.toMul
    have key : MonoidAlgebra.single (a.toMul * b.toMul) (1 : k) =
        MonoidAlgebra.single a.toMul 1 * MonoidAlgebra.single b.toMul 1 := by
      rw [MonoidAlgebra.single_mul_single, one_mul]
    rw [key, pointDer_leibniz, tval_mul]
    change (tval τ a.toMul * tval τ b.toMul)⁻¹ *
        (tval τ a.toMul * E.1 (MonoidAlgebra.single b.toMul 1) +
          tval τ b.toMul * E.1 (MonoidAlgebra.single a.toMul 1)) = _
    field_simp
    ring

lemma pointDerToAdd_apply (E : pointDer τ) (x : X) :
    pointDerToAdd τ E (.ofMul x) = (tval τ x)⁻¹ * E.1 (MonoidAlgebra.single x 1) := rfl

variable (H) in
/-- A point derivation at `τ` is the derivation of the dual torus point of `pointDerToAdd`. -/
lemma torusDer_pointDerToAdd (E : pointDer τ) : torusDer H τ (pointDerToAdd τ E) = E := by
  apply Subtype.ext
  apply linearMap_ext_single
  intro x
  rw [torusDer_single, pointDerToAdd_apply, ← mul_assoc, mul_inv_cancel₀ (tval_ne_zero τ x),
    one_mul]

variable (H) in
lemma pointDerToAdd_torusDer : pointDerToAdd τ (torusDer H τ l) = l := by
  ext x
  change (tval τ x)⁻¹ * (torusDer H τ l).1 (MonoidAlgebra.single x 1) = l (.ofMul x)
  rw [torusDer_single, ← mul_assoc, inv_mul_cancel₀ (tval_ne_zero τ _), one_mul]

variable (H) in
/-- **Point derivations of `k[X]` at `τ` come from dual torus points.** -/
theorem exists_torusDualPt_of_pointDer (E : pointDer τ) :
    ∃ l : Additive X →+ k, ∀ c, E.1 c = es (snd (torusDualPt H τ l c)) :=
  ⟨pointDerToAdd τ E, fun c => by rw [← torusDer_apply, torusDer_pointDerToAdd]⟩

variable (H) in
/-- `Der_τ(k[X], k) ≃ Hom(X, k)`. -/
def torusDerEquiv : (Additive X →+ k) ≃ₗ[k] pointDer τ where
  toFun l := torusDer H τ l
  invFun E := pointDerToAdd τ E
  map_add' l l' := by
    apply Subtype.ext
    apply linearMap_ext_single
    intro x
    change (torusDer H τ (l + l')).1 _ = (torusDer H τ l).1 _ + (torusDer H τ l').1 _
    rw [torusDer_single, torusDer_single, torusDer_single, AddMonoidHom.add_apply, mul_add]
  map_smul' r l := by
    apply Subtype.ext
    apply linearMap_ext_single
    intro x
    change (torusDer H τ (r • l)).1 _ = r * (torusDer H τ l).1 _
    rw [torusDer_single, torusDer_single, AddMonoidHom.smul_apply, smul_eq_mul]
    ring
  left_inv l := pointDerToAdd_torusDer H τ l
  right_inv E := torusDer_pointDerToAdd H τ E

end PointDer

section Tangent

variable (π : H →ₐc[k] MonoidAlgebra k X) (l : Additive X →+ k)

local notation "εT" => Bialgebra.counitAlgHom k (MonoidAlgebra k X)

/-- The tangent vector `h ↦ l'(π h)` (`l'(single x 1) = l(x)`), an element of `Lie G`. -/
def torusTangent : Derivation k H Cv :=
  Derivation.mk' (((es).symm.toLinearMap ∘ₗ (torusDer H εT l).1) ∘ₗ π.toLinearMap) fun a b => by
    change (es).symm ((torusDer H εT l).1 (π (a * b))) =
      a • (es).symm ((torusDer H εT l).1 (π b)) + b • (es).symm ((torusDer H εT l).1 (π a))
    rw [map_mul, pointDer_leibniz, Algebra.smul_def, Algebra.smul_def,
      Bialgebra.CounitAlgebra.algebraMap_apply, Bialgebra.CounitAlgebra.algebraMap_apply]
    simp only [Bialgebra.counitAlgHom_apply, CoalgHomClass.counit_comp_apply, map_add, map_mul]
    rfl

lemma torusTangent_apply (h : H) :
    torusTangent π l h = (es).symm ((torusDer H εT l).1 (π h)) := rfl

/-- **The torus tangent lies in `𝔤_0 = Lie T`.** -/
theorem torusTangent_mem_rootSpace [Algebra.Smooth k H] (D : SplitReductiveData π) :
    torusTangent π l ∈ rootSpace π 0 := by
  rw [rootSpace_zero_eq_lieTorus π D]
  intro x hx
  rw [torusTangent_apply]
  have hx' : π x = 0 := RingHom.mem_ker.1 hx
  rw [hx', map_zero, map_zero]

/-- The constant torus point `inl ∘ τ` and the unit dual torus point multiply to the dual
torus point. -/
lemma toConv_torusDualPt (τ : MonoidAlgebra k X →ₐ[k] k) :
    toConv ((inlAlgHom k Cv Cv).comp (((es).symm : k →ₐ[k] Cv).comp τ)) *
        toConv (torusDualPt H εT l) = toConv (torusDualPt H τ l) := by
  apply ofConv_injective
  apply algHom_ext_single
  intro x
  rw [AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv]
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, MonoidAlgebra.comul_single,
    CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
  have hi : ∀ r : Cv, inlAlgHom k Cv Cv r = inl r := fun _ => rfl
  rw [hi]
  ext
  · rw [fst_mul, fst_inl, fst_torusDualPt_single, fst_torusDualPt_single]
    change τ (MonoidAlgebra.single x 1) *
        (Coalgebra.counit (R := k) (MonoidAlgebra.single x (1 : k)) : k) =
      τ (MonoidAlgebra.single x 1)
    rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply, mul_one]
  · rw [snd_mul, fst_inl, snd_inl, snd_torusDualPt_single, snd_torusDualPt_single,
      fst_torusDualPt_single]
    simp only [smul_zero, add_zero]
    change τ (MonoidAlgebra.single x 1) *
        ((Coalgebra.counit (R := k) (MonoidAlgebra.single x (1 : k)) : k) * l (.ofMul x)) =
      τ (MonoidAlgebra.single x 1) * l (.ofMul x)
    rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply, one_mul]

lemma tanPt_torusTangent :
    tanPt (torusTangent π l) = toConv ((torusDualPt H εT l).comp π.toAlgHom) := by
  apply ofConv_injective
  ext h
  · rw [tanPt, derivationMulEquivTangentKer_apply_fst, Bialgebra.CounitAlgebra.algebraMap_apply,
      ofConv_toConv, AlgHom.comp_apply]
    have := fst_torusDualPt H εT l (π.toAlgHom h)
    rw [Bialgebra.counitAlgHom_apply] at this
    apply (es).injective
    rw [this]
    change (Coalgebra.counit (R := k) h : k) = (Coalgebra.counit (R := k) (π h) : k)
    exact (CoalgHomClass.counit_comp_apply π h).symm
  · rw [tanPt, derivationMulEquivTangentKer_apply_snd, ofConv_toConv, AlgHom.comp_apply]
    change torusTangent π l h = _
    rw [torusTangent_apply, torusDer_apply]
    exact (es).symm_apply_apply _

/-- **The `hpt` hypothesis of `sliceMap_tangent` for the dual torus point.** For `g` the point
`τ ∘ π` of `G` with values in `Cv`, `g · (e + ε torusTangent π l) = torusDualPt H τ l ∘ π`. -/
theorem constPt_mul_tanPt_torusTangent (τ : MonoidAlgebra k X →ₐ[k] k)
    (g : WithConv (H →ₐ[k] Cv)) (hg : ∀ x, es (g.ofConv x) = τ (π x)) :
    constPt g * tanPt (torusTangent π l) = toConv ((torusDualPt H τ l).comp π.toAlgHom) := by
  have hc : constPt g =
      toConv (((inlAlgHom k Cv Cv).comp (((es).symm : k →ₐ[k] Cv).comp τ)).comp π.toAlgHom) := by
    rw [constPt, AlgHom.mapValue_apply]
    congr 1
    refine AlgHom.ext fun x => ?_
    simp only [AlgHom.comp_apply]
    congr 1
    exact ((es).symm_apply_apply _).symm.trans (congrArg (es).symm (hg x))
  have hP : torusDualPt H τ l =
      ofConv (toConv ((inlAlgHom k Cv Cv).comp (((es).symm : k →ₐ[k] Cv).comp τ)) *
        toConv (torusDualPt H εT l)) := by
    rw [toConv_torusDualPt, ofConv_toConv]
  rw [hc, tanPt_torusTangent]
  apply ofConv_injective
  rw [ofConv_toConv, hP]
  exact (AlgHom.convMul_comp_bialgHom_distrib _ _ π).symm

variable {π} in
/-- The descent of a derivation vanishing on `ker π` to a linear map `k[X] → k`. -/
def rootSpaceZeroLin (hπ : Function.Surjective π) (d : Derivation k H Cv)
    (hd : ∀ x ∈ RingHom.ker π.toAlgHom, d x = 0) : MonoidAlgebra k X →ₗ[k] k :=
  ((LinearMap.ker π.toLinearMap).liftQ ((es).toLinearMap ∘ₗ (d : H →ₗ[k] Cv)) (fun x hx => by
      have hx' : x ∈ RingHom.ker π.toAlgHom := RingHom.mem_ker.2 (LinearMap.mem_ker.1 hx)
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe, hd x hx', map_zero])) ∘ₗ
    (π.toLinearMap.quotKerEquivOfSurjective hπ).symm.toLinearMap

omit [DecidableEq X] [IsAlgClosed k] [Algebra.FiniteType k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)] in
lemma rootSpaceZeroLin_apply (hπ : Function.Surjective π) (d : Derivation k H Cv)
    (hd : ∀ x ∈ RingHom.ker π.toAlgHom, d x = 0) (h : H) :
    rootSpaceZeroLin hπ d hd (π h) = es (d h) := by
  have e : (π.toLinearMap.quotKerEquivOfSurjective hπ).symm (π h) =
      Submodule.Quotient.mk h := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [rootSpaceZeroLin, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
  rfl

variable {π} in
/-- An element of `𝔤_0 = Lie T` (a derivation vanishing on `ker π`) descends to a point
derivation of `k[X]` at the counit. -/
def rootSpaceZeroDer (hπ : Function.Surjective π) (d : Derivation k H Cv)
    (hd : ∀ x ∈ RingHom.ker π.toAlgHom, d x = 0) : pointDer εT :=
  ⟨rootSpaceZeroLin hπ d hd, fun u v => by
    obtain ⟨a, rfl⟩ := hπ u
    obtain ⟨b, rfl⟩ := hπ v
    rw [← map_mul, rootSpaceZeroLin_apply, rootSpaceZeroLin_apply, rootSpaceZeroLin_apply,
      Derivation.leibniz, map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
      Bialgebra.CounitAlgebra.algebraMap_apply, Bialgebra.CounitAlgebra.algebraMap_apply,
      Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
    rfl⟩

lemma rootSpaceZeroDer_apply (hπ : Function.Surjective π) (d : Derivation k H Cv)
    (hd : ∀ x ∈ RingHom.ker π.toAlgHom, d x = 0) (h : H) :
    (rootSpaceZeroDer hπ d hd).1 (π h) = es (d h) :=
  rootSpaceZeroLin_apply π hπ d hd h

/-- **Every element of `𝔤_0 = Lie T` is a torus tangent** (`π` surjective). -/
theorem exists_torusTangent_eq [Algebra.Smooth k H] (hπ : Function.Surjective π)
    (D : SplitReductiveData π) (d : Derivation k H Cv) (hd : d ∈ rootSpace π 0) :
    ∃ l : Additive X →+ k, torusTangent π l = d := by
  rw [rootSpace_zero_eq_lieTorus π D] at hd
  refine ⟨pointDerToAdd εT (rootSpaceZeroDer hπ d hd), Derivation.ext fun h => ?_⟩
  rw [torusTangent_apply, torusDer_pointDerToAdd, rootSpaceZeroDer_apply]
  exact (es).symm_apply_apply _

/-- **The torus component of `hpar`**: for every `d ∈ 𝔤_0` there is a dual torus point over `τ`
with `torusDualPt H τ l ∘ π = g (e + ε d)`. -/
theorem exists_torusDualPt_hpt [Algebra.Smooth k H] (hπ : Function.Surjective π)
    (D : SplitReductiveData π) (τ : MonoidAlgebra k X →ₐ[k] k) (g : WithConv (H →ₐ[k] Cv))
    (hg : ∀ x, es (g.ofConv x) = τ (π x)) (d : Derivation k H Cv) (hd : d ∈ rootSpace π 0) :
    ∃ l : Additive X →+ k,
      toConv ((torusDualPt H τ l).comp π.toAlgHom) = constPt g * tanPt d := by
  obtain ⟨l, rfl⟩ := exists_torusTangent_eq π hπ D d hd
  exact ⟨l, (constPt_mul_tanPt_torusTangent π l τ g hg).symm⟩

end Tangent

end AlgMag.Reductive
