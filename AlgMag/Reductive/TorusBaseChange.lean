/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ParabolicConnected
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.BaseChange

/-!
# Base change of the torus grading and of torus attractors

Let `G = Spec H` be an affine group over a field `k` with an action of `D(X)` given by `π`, and
let `K` be a field extension of `k`. The base-changed action `π_K` on `G_K = Spec (K ⊗[k] H)`
has weight spaces `K ⊗ H_χ`, so the attractor ideals base change:
`J_N(G_K) = K ⊗ J_N(G)`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u v w

section Conjugation

variable (k : Type u) (K : Type v) {H : Type w} [CommRing k] [CommRing K] [Algebra k K]
variable [CommRing H] [HopfAlgebra k H]

/-- The comparison `H ⊗[k] H → (K ⊗[k] H) ⊗[K] (K ⊗[k] H)`, `x ⊗ y ↦ (1 ⊗ x) ⊗ (1 ⊗ y)`. -/
def tensorSquareIncl : H ⊗[k] H →ₐ[k] (K ⊗[k] H) ⊗[K] (K ⊗[k] H) :=
  Algebra.TensorProduct.productMap
    ((Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := K ⊗[k] H)
      (B := K ⊗[k] H)).restrictScalars k |>.comp Algebra.TensorProduct.includeRight)
    ((Algebra.TensorProduct.includeRight (R := K) (A := K ⊗[k] H)
      (B := K ⊗[k] H)).restrictScalars k |>.comp Algebra.TensorProduct.includeRight)

@[simp] lemma tensorSquareIncl_tmul (x y : H) :
    tensorSquareIncl k K (x ⊗ₜ[k] y) = ((1 : K) ⊗ₜ[k] x) ⊗ₜ[K] ((1 : K) ⊗ₜ[k] y) := by
  simp [tensorSquareIncl]

/-- **Conjugation commutes with base change**: on `1 ⊗ h`, the conjugation coaction of `G_K` is
the image of the conjugation coaction of `G`. -/
theorem conjugationAlgHom_baseChange (h : H) :
    HopfAlgebra.conjugationAlgHom (R := K) (H := K ⊗[k] H) ((1 : K) ⊗ₜ[k] h) =
      tensorSquareIncl k K (HopfAlgebra.conjugationAlgHom (R := k) (H := H) h) := by
  let e := AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H)
    (R := (K ⊗[k] H) ⊗[K] (K ⊗[k] H))
  have hL : e.symm (toConv (Bialgebra.TensorProduct.includeLeft (R := K) (H₁ := K ⊗[k] H)
      (H₂ := K ⊗[k] H)).toAlgHom) =
      AlgHom.mapValue (tensorSquareIncl k K)
        (toConv (Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := H) (H₂ := H)).toAlgHom) := by
    apply WithConv.ext
    ext a
    simp [e, Algebra.TensorProduct.one_def]
  have hR : e.symm (toConv (Bialgebra.TensorProduct.includeRight (R := K) (H₁ := K ⊗[k] H)
      (H₂ := K ⊗[k] H)).toAlgHom) =
      AlgHom.mapValue (tensorSquareIncl k K)
        (toConv (Bialgebra.TensorProduct.includeRight (R := k) (H₁ := H) (H₂ := H)).toAlgHom) := by
    apply WithConv.ext
    ext a
    simp [e, Algebra.TensorProduct.one_def]
  have key : e.symm (toConv (HopfAlgebra.conjugationAlgHom (R := K) (H := K ⊗[k] H))) =
      AlgHom.mapValue (tensorSquareIncl k K)
        (toConv (HopfAlgebra.conjugationAlgHom (R := k) (H := H))) := by
    rw [HopfAlgebra.toConv_conjugationAlgHom, HopfAlgebra.toConv_conjugationAlgHom]
    have hinv : ∀ x, e.symm x⁻¹ = (e.symm x)⁻¹ := fun x => by
      apply WithConv.ext
      ext a
      rw [AlgHom.baseChangePointsMulEquiv_symm_inv_apply,
        AlgHom.baseChangePointsMulEquiv_symm_apply]
      simp [algHom_inv_apply]
    simp only [map_mul, map_inv, hinv, hL, hR]
  have := congrArg (fun f => f.ofConv h) key
  simpa [e] using this

end Conjugation

section Torus

variable {k : Type u} (K : Type v) {H : Type w} [Field k] [Field K] [Algebra k K]
variable [CommRing H] [HopfAlgebra k H] {X : Type*} [CommGroup X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- The base change `π_K : K ⊗[k] H → K[X]` of the torus action. -/
def torusBaseChange : K ⊗[k] H →ₐc[K] MonoidAlgebra K X :=
  (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k K (G := X) :
      K ⊗[k] MonoidAlgebra k X →ₐc[K] MonoidAlgebra K X).comp
    (Bialgebra.TensorProduct.map (BialgHom.id K K) π)

@[simp] lemma torusBaseChange_tmul (s : K) (h : H) :
    torusBaseChange K π (s ⊗ₜ[k] h) =
      s • MonoidAlgebra.mapAlgHom X (Algebra.ofId k K) (π h) := by
  simp [torusBaseChange]

/-- The comparison `k[X] ⊗[k] H → K[X] ⊗[K] (K ⊗[k] H)`. -/
def torusCoactIncl : MonoidAlgebra k X ⊗[k] H →ₐ[k] MonoidAlgebra K X ⊗[K] (K ⊗[k] H) :=
  Algebra.TensorProduct.productMap
    ((Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := MonoidAlgebra K X)
      (B := K ⊗[k] H)).restrictScalars k |>.comp
        ((MonoidAlgebra.mapAlgHom X (Algebra.ofId k K)).restrictScalars k))
    ((Algebra.TensorProduct.includeRight (R := K) (A := MonoidAlgebra K X)
      (B := K ⊗[k] H)).restrictScalars k |>.comp Algebra.TensorProduct.includeRight)

lemma torusCoactLeft_baseChange (h : H) :
    torusCoactLeft (torusBaseChange K π) ((1 : K) ⊗ₜ[k] h) =
      torusCoactIncl (k := k) (H := H) (X := X) K (torusCoactLeft π h) := by
  simp only [torusCoactLeft, AlgHom.comp_apply]
  rw [conjugationAlgHom_baseChange]
  induction HopfAlgebra.conjugationAlgHom (R := k) (H := H) h using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x y =>
    simp [torusCoactIncl, Algebra.TensorProduct.one_def]

/-- **Weight vectors base change**: if `h ∈ H_χ` then `1 ⊗ h ∈ (K ⊗ H)_χ`. -/
theorem one_tmul_mem_torusGrading {χ : Additive X} {h : H} (hh : h ∈ torusGrading π χ) :
    (1 : K) ⊗ₜ[k] h ∈ torusGrading (torusBaseChange K π) χ := by
  rw [mem_torusGrading] at hh ⊢
  have hl : torusCoactLeft π h = MonoidAlgebra.single (Additive.toMul χ) 1 ⊗ₜ[k] h := by
    have := congrArg (TensorProduct.comm k H (MonoidAlgebra k X)) hh
    simpa [torusCoact] using this
  simp only [torusCoact, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    AlgHom.toLinearMap_apply]
  rw [torusCoactLeft_baseChange, hl]
  simp [torusCoactIncl]

variable [DecidableEq X]

/-- The homogeneous projections commute with `h ↦ 1 ⊗ h`. -/
lemma proj_one_tmul (χ : Additive X) (h : H) :
    GradedRing.proj (torusGrading (torusBaseChange K π)) χ ((1 : K) ⊗ₜ[k] h) =
      (1 : K) ⊗ₜ[k] GradedRing.proj (torusGrading π) χ h :=
  (map_proj_of_graded (torusGrading π) (torusGrading (torusBaseChange K π))
    (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H).toRingHom
    (fun _ _ hx => one_tmul_mem_torusGrading K π hx) χ h).symm

/-- The homogeneous components of an element of `K ⊗ H` lie in `K ⊗ H_χ`. -/
lemma proj_mem_baseChange (χ : Additive X) (y : K ⊗[k] H) :
    GradedRing.proj (torusGrading (torusBaseChange K π)) χ y ∈
      (torusGrading π χ).baseChange K := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul s h =>
    have hs : s ⊗ₜ[k] h = s • ((1 : K) ⊗ₜ[k] h) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hs]
    change GradedAlgebra.proj (torusGrading (torusBaseChange K π)) χ (s • ((1 : K) ⊗ₜ[k] h)) ∈ _
    rw [LinearMap.map_smul]
    change s • GradedRing.proj (torusGrading (torusBaseChange K π)) χ ((1 : K) ⊗ₜ[k] h) ∈ _
    rw [proj_one_tmul]
    exact Submodule.smul_mem _ s (Submodule.tmul_mem_baseChange_of_mem _
      (by rw [GradedRing.proj_apply]; exact SetLike.coe_mem _))

/-- **The torus grading base changes**: `(K ⊗[k] H)_χ = K ⊗ H_χ`. -/
theorem torusGrading_baseChange (χ : Additive X) :
    torusGrading (torusBaseChange K π) χ = (torusGrading π χ).baseChange K := by
  apply le_antisymm
  · intro y hy
    have : GradedRing.proj (torusGrading (torusBaseChange K π)) χ y = y := by
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same _ hy]
    rw [← this]
    exact proj_mem_baseChange K π χ y
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨h, hh, rfl⟩
    exact one_tmul_mem_torusGrading K π hh

/-- **Attractors base change**: `J_N(G_K) = K ⊗ J_N(G)`, i.e. the attractor ideal of `G_K` is
generated by the attractor ideal of `G`. -/
theorem magnetIdeal_baseChange (N : Magnet (Additive X)) :
    magnetIdeal (torusGrading (torusBaseChange K π)) N =
      (magnetIdeal (torusGrading π) N).map
        (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H) := by
  apply le_antisymm
  · rw [magnetIdeal, Ideal.span_le]
    intro y hy
    obtain ⟨χ, hχ, hy⟩ := Set.mem_iUnion₂.mp hy
    rw [SetLike.mem_coe, torusGrading_baseChange, Submodule.baseChange_eq_span] at hy
    refine Submodule.span_induction (fun z hz => ?_) (zero_mem _) (fun _ _ _ _ => add_mem)
      (fun s z _ hz => ?_) hy
    · obtain ⟨h, hh, rfl⟩ := hz
      exact Ideal.mem_map_of_mem _ (mem_magnetIdeal_of_notMem hχ hh)
    · rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hz
  · rw [Ideal.map_le_iff_le_comap, magnetIdeal, Ideal.span_le]
    intro h hh
    obtain ⟨χ, hχ, hh⟩ := Set.mem_iUnion₂.mp hh
    exact mem_magnetIdeal_of_notMem hχ (one_tmul_mem_torusGrading K π hh)

/-- The `k`-derivation `x ↦ ℓ (D (1 ⊗ x))` of `H` at the unit obtained from a `K`-derivation `D`
of `K ⊗[k] H` at the unit and a `k`-linear form `ℓ` on `K`. -/
def restrictDerivation
    (D : Derivation K (K ⊗[k] H) (Bialgebra.CounitAlgebra K (K ⊗[k] H) K)) (ℓ : K →ₗ[k] k) :
    Derivation k H (Bialgebra.CounitAlgebra k H k) :=
  let v : H → K := fun x =>
    Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[k] H) K (D ((1 : K) ⊗ₜ[k] x))
  have hv_add : ∀ x y, v (x + y) = v x + v y := fun x y => by
    simp only [v, TensorProduct.tmul_add, map_add]
  have hv_smul : ∀ (c : k) x, v (c • x) = algebraMap k K c * v x := fun c x => by
    simp only [v]
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (A := K) c, D.map_smul, map_smul,
      smul_eq_mul]
  have hv_mul : ∀ x y, v (x * y) =
      algebraMap k K (Coalgebra.counit x) * v y + algebraMap k K (Coalgebra.counit y) * v x :=
    fun x y => by
      have hxy : (1 : K) ⊗ₜ[k] (x * y) = ((1 : K) ⊗ₜ[k] x) * ((1 : K) ⊗ₜ[k] y) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [v]
      rw [hxy, Derivation.leibniz, map_add, Bialgebra.CounitAlgebra.algEquivSelf_smul,
        Bialgebra.CounitAlgebra.algEquivSelf_smul]
      simp [TensorProduct.counit_tmul, Algebra.algebraMap_eq_smul_one]
  Derivation.mk'
    { toFun := fun x => (Bialgebra.CounitAlgebra.algEquivSelf k H k).symm (ℓ (v x))
      map_add' := fun x y => by rw [hv_add, map_add, map_add]
      map_smul' := fun c x => by
        rw [hv_smul, ← smul_eq_mul, algebraMap_smul, map_smul, map_smul]
        rfl }
    (fun x y => by
      apply (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add,
        Bialgebra.CounitAlgebra.algEquivSelf_smul, AlgEquiv.apply_symm_apply]
      rw [hv_mul, map_add, ← smul_eq_mul (a := algebraMap k K _), algebraMap_smul, map_smul,
        ← smul_eq_mul (a := algebraMap k K _), algebraMap_smul, map_smul]
      simp [smul_eq_mul])
/-- **Tangent weights descend**: a tangent weight of `G_K` is a tangent weight of `G`. -/
theorem tangentWeights_baseChange_subset :
    tangentWeights (torusBaseChange K π) K ⊆ tangentWeights π k := by
  rintro χ ⟨D, y, hy, hD⟩
  rw [torusGrading_baseChange, Submodule.baseChange_eq_span] at hy
  have : ∃ h ∈ torusGrading π χ, D ((1 : K) ⊗ₜ[k] h) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hD
    refine Submodule.span_induction (fun z hz => ?_) (map_zero D) (fun _ _ _ _ ha hb => ?_)
      (fun s z _ hz => ?_) hy
    · obtain ⟨h, hh, rfl⟩ := hz
      exact hcon h hh
    · rw [map_add, ha, hb, add_zero]
    · rw [D.map_smul, hz, smul_zero]
  obtain ⟨h, hh, hDh⟩ := this
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual k K,
      ℓ (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[k] H) K (D ((1 : K) ⊗ₜ[k] h))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hDh ((Module.forall_dual_apply_eq_zero_iff k
      (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[k] H) K (D ((1 : K) ⊗ₜ[k] h)))).mp hcon)
  refine ⟨restrictDerivation K D ℓ, h, hh, fun h0 => hℓ ?_⟩
  exact h0

end Torus

end AlgMag.Reductive
