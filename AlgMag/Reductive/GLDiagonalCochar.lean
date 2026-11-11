/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Representability
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding

/-!
# The diagonal cocharacter `diag(t^{w_i})` of `GL_N`

* `diagAlgHom w`, `diagCochar w : O(GL_N) →ₐc[k] k[t, t⁻¹]` (proved): the cocharacter
  `t ↦ diag(t^{w_1}, …, t^{w_N})`, with `diagCochar_X : X_ij ↦ δ_ij t^{w_i}`.
* `conjugate_X` (proved): conjugation by `diag(t^w)` sends `X_ij` to `t^{w_i} X_ij t^{−w_j}`.
* `mem_parabolic_diag_iff` (proved): points of `P(diag t^w)` are those with `g_ij = 0` for `w i < w j`.
* `parabolicDefiningHopfIdeal_diagCochar` (proved):
  `P(diag t^w) = weightParabolicDefiningHopfIdeal k w`.
-/

open TauCeti TauCeti.Cocharacter TauCeti.GeneralLinear
open scoped TensorProduct

namespace AlgMag.Reductive.GLDiagonalCochar

universe u

variable (k : Type u) [CommRing k] {N : ℕ}

/-- The diagonal matrix `diag(T^{w_i})` over `k[T, T⁻¹]`. -/
noncomputable def diagMat (w : Fin N → ℤ) : Matrix (Fin N) (Fin N) (LaurentPolynomial k) :=
  Matrix.diagonal fun i => LaurentPolynomial.T (w i)

theorem isUnit_det_diagMat (w : Fin N → ℤ) : IsUnit (diagMat k w).det := by
  rw [diagMat, Matrix.det_diagonal]
  exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
    (fun i _ => LaurentPolynomial.isUnit_T (w i))

theorem comul_T (n : ℤ) :
    Coalgebra.comul (R := k) (LaurentPolynomial.T n : LaurentPolynomial k) =
      LaurentPolynomial.T n ⊗ₜ LaurentPolynomial.T n := by
  show Coalgebra.comul (R := k) (AddMonoidAlgebra.single n (1 : k)) = _
  rw [AddMonoidAlgebra.comul_single]
  simp

theorem counit_T (n : ℤ) :
    Coalgebra.counit (R := k) (LaurentPolynomial.T n : LaurentPolynomial k) = 1 := by
  show Coalgebra.counit (R := k) (AddMonoidAlgebra.single n (1 : k)) = _
  rw [AddMonoidAlgebra.counit_single]
  rfl

/-- The algebra morphism underlying the diagonal cocharacter. -/
noncomputable def diagAlgHom (w : Fin N → ℤ) :
    coordinateHopfAlgebra k N →ₐ[k] LaurentPolynomial k :=
  (generalLinearToPoint (R := k) N
    (Matrix.GeneralLinearGroup.mk'' (diagMat k w) (isUnit_det_diagMat k w))).ofConv

@[simp]
theorem diagAlgHom_X (w : Fin N → ℤ) (i j : Fin N) :
    diagAlgHom k w (coordinateHopfAlgebraAlgEquiv k N
        (coordinateRingMap k N (MvPolynomial.X (i, j)))) = diagMat k w i j := by
  simp only [diagAlgHom, generalLinearToPoint_apply, Matrix.GeneralLinearGroup.val_mk'']

theorem diagAlgHom_counit (w : Fin N → ℤ) :
    (Bialgebra.counitAlgHom k (LaurentPolynomial k)).comp (diagAlgHom k w) =
      Bialgebra.counitAlgHom k (coordinateHopfAlgebra k N) := by
  apply coordinateHopfAlgebra_algHom_ext k N
  intro i j
  simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, diagAlgHom_X,
    coordinateHopfAlgebra_counit_X, diagMat, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem diagAlgHom_comul (w : Fin N → ℤ) :
    (Algebra.TensorProduct.map (diagAlgHom k w) (diagAlgHom k w)).comp
        (Bialgebra.comulAlgHom k (coordinateHopfAlgebra k N)) =
      (Bialgebra.comulAlgHom k (LaurentPolynomial k)).comp (diagAlgHom k w) := by
  apply coordinateHopfAlgebra_algHom_ext k N
  intro i j
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    coordinateHopfAlgebra_comul_X, map_sum, Algebra.TensorProduct.map_tmul, diagAlgHom_X]
  simp only [diagMat, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- **The diagonal cocharacter** `t ↦ diag(t^{w_1}, …, t^{w_N})` of `GL_N`. -/
noncomputable def diagCochar (w : Fin N → ℤ) :
    coordinateHopfAlgebra k N →ₐc[k] LaurentPolynomial k :=
  BialgHom.ofAlgHom (diagAlgHom k w) (diagAlgHom_counit k w) (diagAlgHom_comul k w)

@[simp]
theorem diagCochar_X (w : Fin N → ℤ) (i j : Fin N) :
    diagCochar k w (coordinateHopfAlgebraAlgEquiv k N
        (coordinateRingMap k N (MvPolynomial.X (i, j)))) =
      if i = j then LaurentPolynomial.T (w i) else 0 := by
  simp [diagCochar, BialgHom.ofAlgHom_apply, diagMat, Matrix.diagonal_apply]

/-! ### Conjugation by `diag(t^w)`: `X_ij ↦ t^{w_i − w_j} X_ij` -/

section Conj

variable {k} {A : Type u} [CommRing A] [Algebra k A] (w : Fin N → ℤ)

/-- The matrix of the generic point of `diag(t^w)`. -/
theorem genericPoint_matrix (i j : Fin N) :
    pointToGeneralLinear N (genericPoint A (diagCochar k w)) i j =
      if i = j then LaurentPolynomial.T (w i) else 0 := by
  rw [pointToGeneralLinear_apply, genericPoint_eq_pointsHom,
    pointsHom_apply, BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
  simp only [AlgHom.comp_apply]
  erw [diagCochar_X k w i j]
  split_ifs
  · rw [laurentEval_T, LaurentPolynomial.genericUnit_zpow_val]
  · simp

theorem genericPoint_coe :
    ((pointToGeneralLinear N (genericPoint A (diagCochar k w)) : GL (Fin N) _) :
      Matrix (Fin N) (Fin N) (LaurentPolynomial A)) =
      Matrix.diagonal fun i => LaurentPolynomial.T (w i) := by
  ext i j
  rw [genericPoint_matrix, Matrix.diagonal_apply]

theorem genericPoint_inv_coe :
    (((pointToGeneralLinear N (genericPoint A (diagCochar k w)))⁻¹ : GL (Fin N) _) :
      Matrix (Fin N) (Fin N) (LaurentPolynomial A)) =
      Matrix.diagonal fun i => LaurentPolynomial.T (-w i) := by
  rw [Matrix.coe_units_inv, genericPoint_coe]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

theorem constPoint_matrix (g : WithConv (coordinateHopfAlgebra k N →ₐ[k] A)) (i j : Fin N) :
    pointToGeneralLinear N (constPoint A g) i j =
      algebraMap A (LaurentPolynomial A) (pointToGeneralLinear N g i j) := by
  rw [pointToGeneralLinear_apply, pointToGeneralLinear_apply, constPoint_apply,
    WithConv.ofConv_toConv, AlgHom.comp_apply]
  rfl

/-- **Conjugation by `diag(t^w)`**: the `(i,j)` coordinate becomes `t^{w_i} g_ij t^{−w_j}`. -/
theorem conjugate_X (g : WithConv (coordinateHopfAlgebra k N →ₐ[k] A)) (i j : Fin N) :
    (conjugate A (diagCochar k w) g).ofConv (coordinateHopfAlgebraAlgEquiv k N
        (coordinateRingMap k N (MvPolynomial.X (i, j)))) =
      LaurentPolynomial.T (w i) * algebraMap A (LaurentPolynomial A)
        (pointToGeneralLinear N g i j) * LaurentPolynomial.T (-w j) := by
  rw [← pointToGeneralLinear_apply, conjugate_apply, pointToGeneralLinear_mul,
    pointToGeneralLinear_mul, show pointToGeneralLinear N (genericPoint A (diagCochar k w))⁻¹ =
      (pointToGeneralLinear N (genericPoint A (diagCochar k w)))⁻¹ from
      map_inv (pointsMulEquiv (R := k) (A := LaurentPolynomial A) N) _]
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, genericPoint_inv_coe,
    genericPoint_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have := constPoint_matrix (A := A) g i j
  simp only [pointToGeneralLinear_apply] at this ⊢
  rw [this]

theorem conj_form (a : A) (i j : Fin N) :
    LaurentPolynomial.T (w i) * algebraMap A (LaurentPolynomial A) a * LaurentPolynomial.T (-w j) =
      LaurentPolynomial.C a * LaurentPolynomial.T (w i - w j) := by
  rw [LaurentPolynomial.algebraMap_apply, mul_comm (LaurentPolynomial.T (w i)), mul_assoc,
    ← LaurentPolynomial.T_add, ← sub_eq_add_neg]
  simp

/-- The polynomial Laurent polynomials, as a `k`-subalgebra. -/
noncomputable abbrev polSub : Subalgebra k (LaurentPolynomial A) :=
  ((Polynomial.toLaurentAlg (R := A)).restrictScalars k).range

theorem mem_polSub (a : A) (i j : Fin N) (h : w i < w j → a = 0) :
    LaurentPolynomial.T (w i) * algebraMap A (LaurentPolynomial A) a * LaurentPolynomial.T (-w j)
      ∈ polSub (k := k) (A := A) := by
  rw [conj_form]
  by_cases hij : w i < w j
  · rw [h hij]; simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, w i - w j = n := ⟨(w i - w j).toNat, by omega⟩
    refine ⟨Polynomial.monomial n a, ?_⟩
    simp [hn, Polynomial.toLaurent_C_mul_T]

theorem coeff_conj_form (a : A) (i j : Fin N) :
    (LaurentPolynomial.C a * LaurentPolynomial.T (w i - w j)).coeff (w i - w j) = a := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
  exact Finsupp.single_eq_same

/-- **Points of the dynamic parabolic of `diag(t^w)`**: `g_ij = 0` whenever `w i < w j`. -/
theorem mem_parabolic_diag_iff (g : WithConv (coordinateHopfAlgebra k N →ₐ[k] A)) :
    g ∈ parabolic A (diagCochar k w) ↔
      ∀ i j, w i < w j → pointToGeneralLinear N g i j = 0 := by
  rw [mem_parabolic_iff_forall_coeff_conjugate_eq_zero]
  constructor
  · intro h i j hij
    have := h (coordinateHopfAlgebraAlgEquiv k N (coordinateRingMap k N (MvPolynomial.X (i, j))))
      (w i - w j) (by omega)
    rwa [conjugate_X, conj_form, coeff_conj_form] at this
  · intro h
    have hW : pointsMulEquiv N g ∈ weightParabolicPoints k w A := by
      rw [mem_weightParabolicPoints_iff]
      intro i j hij
      rw [pointsMulEquiv_apply]
      exact h i j hij
    have hinv : ∀ i j, w i < w j → pointToGeneralLinear N g⁻¹ i j = 0 := by
      have hW' := inv_mem hW
      rw [← map_inv, mem_weightParabolicPoints_iff] at hW'
      intro i j hij
      simpa [pointsMulEquiv_apply] using hW' i j hij
    let ψ := (conjugate A (diagCochar k w) g).ofConv
    have hle : Algebra.adjoin k
        (Set.range (fun ij : Fin N × Fin N =>
          coordinateHopfAlgebraAlgEquiv k N (coordinateRingMap k N (MvPolynomial.X ij))) ∪
        Set.range (fun ij : Fin N × Fin N =>
          HopfAlgebra.antipode k (A := coordinateHopfAlgebra k N)
            (coordinateHopfAlgebraAlgEquiv k N (coordinateRingMap k N (MvPolynomial.X ij))))) ≤
        (polSub (k := k) (A := A)).comap ψ := by
      rw [Algebra.adjoin_le_iff]
      rintro x (⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subalgebra.mem_comap]
        change (conjugate A (diagCochar k w) g).ofConv _ ∈ _
        rw [conjugate_X w g i j]
        exact mem_polSub w _ i j (h i j)
      · rw [SetLike.mem_coe, Subalgebra.mem_comap]
        change (conjugate A (diagCochar k w) g).ofConv _ ∈ _
        have e := coe_inv_pointsMulEquiv_apply (R := k) (n := N)
          (conjugate A (diagCochar k w) g) i j
        rw [← e, ← map_inv, ← map_inv, pointsMulEquiv_apply,
          pointToGeneralLinear_apply, conjugate_X]
        exact mem_polSub w _ i j (hinv i j)
    rw [adjoin_coordinateHopfAlgebra_X_union_antipode_X] at hle
    intro x n hn
    obtain ⟨q, hq⟩ := hle (Algebra.mem_top (x := x))
    have hq' : q.toLaurent = ψ x := hq
    exact (TauCeti.exists_toLaurent_eq_iff.mp ⟨q, hq'⟩) n hn

end Conj

/-- **`P(diag t^w) = weight parabolic`**: the dynamic parabolic of `t ↦ diag(t^{w_i})` is cut out
by `X_ij = 0` for `w i < w j`. -/
theorem parabolicDefiningHopfIdeal_diagCochar (w : Fin N → ℤ) :
    parabolicDefiningHopfIdeal (diagCochar k w) = weightParabolicDefiningHopfIdeal k w := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq (H := coordinateHopfAlgebra k N)
  intro A
  ext g
  rw [← pointsMulEquiv_mem_weightParabolicPoints_iff, mem_weightParabolicPoints_iff]
  erw [quotientPointsSubgroup_parabolicDefiningHopfIdeal (H := (coordinateHopfAlgebra k N : Type u))
    (A := (A : Type u))]
  exact mem_parabolic_diag_iff w g

/-! ### Weight bases give diagonal cocharacters -/

section WeightBasis

variable {k} {H : Type u} [CommRing H] [HopfAlgebra k H]
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M]

theorem map_matrixCoefficient (ν : H →ₗ[k] LaurentPolynomial k) (φ : M →ₗ[k] k) (m : M) :
    ν (Comodule.matrixCoefficient (R := k) (C := H) φ m) =
      TensorProduct.lid k _ (TensorProduct.map φ ν
        (Comodule.coact (R := k) (C := H) (M := M) m)) := by
  rw [Comodule.matrixCoefficient_def]
  induction Comodule.coact (R := k) (C := H) (M := M) m using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **A `ν`-weight basis makes `ν` diagonal**: if `b` is a basis of a comodule `M` with
`(id ⊗ ν)(coact (b j)) = b j ⊗ t^{w j}`, then `ν ∘ ρ_b = diag(t^w)`, where `ρ_b` is the
coordinate morphism `O(GL_N) → O(G)` of `b`. -/
theorem comp_coordinateBialgHom_eq_diagCochar {N : ℕ} (b : Module.Basis (Fin N) k M)
    (ν : H →ₐc[k] LaurentPolynomial k) (w : Fin N → ℤ)
    (hw : ∀ j, TensorProduct.map LinearMap.id ν.toLinearMap
        (Comodule.coact (R := k) (C := H) (M := M) (b j)) = b j ⊗ₜ LaurentPolynomial.T (w j)) :
    ν.comp (Comodule.coordinateBialgHom b) = diagCochar k w := by
  apply BialgHom.coe_toAlgHom_injective
  apply coordinateHopfAlgebra_algHom_ext k N
  intro i j
  show ν (Comodule.coordinateBialgHom b _) = diagCochar k w _
  rw [Comodule.coordinateBialgHom_X]
  erw [diagCochar_X k w i j]
  rw [Comodule.coefficientMatrix_apply]
  have e := map_matrixCoefficient ν.toLinearMap (b.coord i) (b j)
  rw [show ν.toLinearMap (Comodule.matrixCoefficient (b.coord i) (b j)) =
    ν (Comodule.matrixCoefficient (b.coord i) (b j)) from rfl] at e
  rw [e, show TensorProduct.map (b.coord i) ν.toLinearMap =
      (TensorProduct.map (b.coord i) LinearMap.id) ∘ₗ (TensorProduct.map LinearMap.id ν.toLinearMap)
      by rw [← TensorProduct.map_comp]; rfl, LinearMap.comp_apply, hw]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **Existence of a `ν`-weight basis** of a finite-dimensional comodule over a field. -/
theorem exists_weightBasis {K : Type u} [Field K] {H : Type u} [CommRing H] [HopfAlgebra K H]
    {M : Type u} [AddCommGroup M] [Module K M] [Comodule K H M] [FiniteDimensional K M]
    (ν : H →ₐc[K] LaurentPolynomial K) :
    ∃ (N : ℕ) (b : Module.Basis (Fin N) K M) (w : Fin N → ℤ), ∀ j,
      TensorProduct.map LinearMap.id ν.toLinearMap
        (Comodule.coact (R := K) (C := H) (M := M) (b j)) = b j ⊗ₜ LaurentPolynomial.T (w j) := by
  let _ : DecidableEq (Multiplicative ℤ) := Classical.decEq _
  let e := AddMonoidAlgebra.toMultiplicativeBialgEquiv K K ℤ
  let π : H →ₗc[K] MonoidAlgebra K (Multiplicative ℤ) :=
    ((e : LaurentPolynomial K →ₐc[K] _).comp ν).toCoalgHom
  have hI := DiagonalizableGroup.isInternal_weightSpace M π
  let v := fun x => Module.Basis.ofVectorSpace K (DiagonalizableGroup.weightSpace M π x)
  let bb := hI.collectedBasis v
  have : Finite (Σ x, Module.Basis.ofVectorSpaceIndex K
      (DiagonalizableGroup.weightSpace M π x)) := Module.Finite.finite_basis bb
  let _ := Fintype.ofFinite (Σ x, Module.Basis.ofVectorSpaceIndex K
      (DiagonalizableGroup.weightSpace M π x))
  let eq := Fintype.equivFin (Σ x, Module.Basis.ofVectorSpaceIndex K
      (DiagonalizableGroup.weightSpace M π x))
  refine ⟨_, bb.reindex eq, fun j => Multiplicative.toAdd (eq.symm j).1, fun j => ?_⟩
  have hmem : (bb.reindex eq) j ∈ DiagonalizableGroup.weightSpace M π (eq.symm j).1 := by
    rw [Module.Basis.reindex_apply, hI.collectedBasis_coe]
    exact (v _ _).2
  rw [DiagonalizableGroup.mem_weightSpace] at hmem
  have h2 := congrArg (TensorProduct.map LinearMap.id
    ((e.symm : MonoidAlgebra K (Multiplicative ℤ) →ₐc[K] LaurentPolynomial K).toLinearMap)) hmem
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, TensorProduct.map_tmul] at h2
  convert h2 using 2
  · congr 1
    apply LinearMap.ext
    intro x
    exact (e.symm_apply_apply (ν x)).symm
  all_goals try rfl
  all_goals
    show _ = e.symm (MonoidAlgebra.single _ 1)
    rw [AddMonoidAlgebra.toMultiplicativeBialgEquiv_symm_single]
    rfl

/-- **Step (1)**: a closed immersion `G ↪ GL_N` in which `ν` is diagonal: a faithful finite
subcomodule of `O(G)` with a `ν`-weight basis. -/
theorem exists_weightBasis_embedding {K : Type u} [Field K] {H : Type u} [CommRing H]
    [HopfAlgebra K H] [Algebra.FiniteType K H] (ν : H →ₐc[K] LaurentPolynomial K) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module K M) (_ : Comodule K H M) (N : ℕ)
      (b : Module.Basis (Fin N) K M) (w : Fin N → ℤ),
      Function.Surjective (Comodule.coordinateBialgHom (H := H) b) ∧ ∀ j,
      TensorProduct.map LinearMap.id ν.toLinearMap
        (Comodule.coact (R := K) (C := H) (M := M) (b j)) = b j ⊗ₜ LaurentPolynomial.T (w j) := by
  let _ : Ring H := Algebra.semiringToRing K
  obtain ⟨M, hMfinite, hMcoeff⟩ :=
    Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top (k := K) (C := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  let _ : Module.Finite K M := hMfinite
  obtain ⟨N, b, w, hw⟩ := exists_weightBasis (M := M) ν
  refine ⟨M, _, _, _, N, b, w, ?_, hw⟩
  have hs : Function.Surjective (Comodule.coordinateBialgHom (H := H) b).toAlgHom := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← hMcoeff]
    exact Comodule.matrixCoefficientSubalgebra_le_coordinateBialgHom_range b
  exact hs

end WeightBasis

end AlgMag.Reductive.GLDiagonalCochar
