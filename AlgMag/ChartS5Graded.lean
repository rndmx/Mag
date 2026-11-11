/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartAlgebraize
import AlgMag.ChartGraded
import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Commutative algebra for the Artin approximation step of the chart lemma

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

For an algebra `R` over `P₀`, the graded ring `QR w R = P ⊗_{P₀} R`, its functoriality in `R`,
Noetherianity of `P̂₀` and `Q`, and the filtered system of the rings `Rs s ⊗ …` over the finitely
generated subalgebras of a `P₀`-algebra `Rh`, with the quotients by finitely many fixed equations.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

universe u

open DirectSum MvPolynomial TensorProduct AlgMag.ChartAlg

namespace AlgMag.ChartS5

section Basic

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {ι : Type*} [Finite ι] (w : ι → M)
  (R : Type*) [CommRing R] [Algebra (P0 w ℤ) R]

/-- `Q_R := P ⊗_{P₀} R`. -/
abbrev QR : Type _ := MvPolynomial ι ℤ ⊗[P0 w ℤ] R

/-- The degree `d` projection of `Q_R`. -/
noncomputable def qProjR (d : M) : QR w R →ₗ[P0 w ℤ] QR w R :=
  LinearMap.rTensor _ (piP w d)

variable {R}

lemma qProjR_tmul (d : M) (p : MvPolynomial ι ℤ) (y : R) :
    qProjR w R d (p ⊗ₜ[P0 w ℤ] y) = piP w d p ⊗ₜ y := rfl

lemma qProjR_idem (d : M) (q : QR w R) : qProjR w R d (qProjR w R d q) = qProjR w R d q := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul p y => rw [qProjR_tmul, qProjR_tmul, piP_piP]
  | add u v hu hv => simp only [map_add, hu, hv]

lemma sum_qProjR (q : QR w R) :
    ∃ S₀ : Finset M, ∀ S, S₀ ⊆ S → ∑ d ∈ S, qProjR w R d q = q := by
  classical
  induction q using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun S _ => by simp⟩
  | tmul p y =>
    obtain ⟨S₀, h⟩ := sum_piP (w := w) p
    refine ⟨S₀, fun S hS => ?_⟩
    conv_rhs => rw [← h S hS]
    rw [TensorProduct.sum_tmul]
    rfl
  | add u v hu hv =>
    obtain ⟨S, hS⟩ := hu
    obtain ⟨T, hT⟩ := hv
    refine ⟨S ∪ T, fun U hU => ?_⟩
    simp only [map_add, Finset.sum_add_distrib]
    rw [hS U (Finset.union_subset_left hU), hT U (Finset.union_subset_right hU)]

lemma piP_ne {d e : M} (h : d ≠ e) (p : MvPolynomial ι ℤ) : piP w d (piP w e p) = 0 :=
  (weightedHomogeneousComponent_isWeightedHomogeneous e p).weightedHomogeneousComponent_ne d h

lemma qProjR_ne {d e : M} (h : d ≠ e) (q : QR w R) : qProjR w R d (qProjR w R e q) = 0 := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul p y => rw [qProjR_tmul, qProjR_tmul, piP_ne w h, TensorProduct.zero_tmul]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

omit [Finite ι] in
lemma piP_mul' (d e : M) (p q : MvPolynomial ι ℤ) :
    piP w (d + e) (p * piP w e q) = piP w d p * piP w e q := by
  classical
  have hq : IsWeightedHomogeneous w (piP w e q) e :=
    weightedHomogeneousComponent_isWeightedHomogeneous e q
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    have hm : IsWeightedHomogeneous w (monomial a c) (Finsupp.weight w a) :=
      isWeightedHomogeneous_monomial w a c rfl
    have hmq := hm.mul hq
    change weightedHomogeneousComponent w (d + e) _ = weightedHomogeneousComponent w d _ * _
    by_cases h : Finsupp.weight w a = d
    · subst h
      rw [hmq.weightedHomogeneousComponent_same, hm.weightedHomogeneousComponent_same]
    · rw [hmq.weightedHomogeneousComponent_ne (d + e) (fun e' => h (add_right_cancel e'.symm)),
        hm.weightedHomogeneousComponent_ne d (Ne.symm h), zero_mul]
  | add p q' hp hq' =>
    rw [add_mul, (piP w (d + e)).map_add, (piP w d).map_add, add_mul, hp, hq']

lemma qProjR_mul (d e : M) (a b : QR w R) :
    qProjR w R (d + e) (a * qProjR w R e b) = qProjR w R d a * qProjR w R e b := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a a' h h' => rw [add_mul, map_add, map_add, add_mul, h, h']
  | tmul p y =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | add b b' h h' => simp only [map_add, mul_add, h, h']
    | tmul q z =>
      rw [qProjR_tmul, qProjR_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, qProjR_tmul, piP_mul']

lemma qProjR_one : qProjR w R 0 (1 : QR w R) = 1 := by
  change piP w 0 (1 : MvPolynomial ι ℤ) ⊗ₜ[P0 w ℤ] (1 : R) = 1 ⊗ₜ 1
  congr 1
  exact (isWeightedHomogeneous_one ℤ w).weightedHomogeneousComponent_same

variable (R) in
/-- The degree `d` part of `Q_R`. -/
def qGrade (d : M) : AddSubgroup (QR w R) where
  carrier := {q | qProjR w R d q = q}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [map_neg, ha]

lemma mem_qGrade {d : M} {q : QR w R} : q ∈ qGrade w R d ↔ qProjR w R d q = q := Iff.rfl

lemma qProjR_mem (d : M) (q : QR w R) : qProjR w R d q ∈ qGrade w R d := qProjR_idem w d q

lemma qProjR_coe (d : M) (x : ⨁ e, qGrade w R e) :
    qProjR w R d (DirectSum.coeAddMonoidHom (qGrade w R) x) = (x d : QR w R) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of e t =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : e = d
    · subst h
      rw [DirectSum.of_eq_same]
      exact t.2
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      have : (t : QR w R) = qProjR w R e t := t.2.symm
      rw [this, qProjR_ne w (Ne.symm h)]
      simp
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv, DirectSum.add_apply, AddMemClass.coe_add]

theorem qGrade_internal : DirectSum.IsInternal (qGrade w R) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    ext d
    have := qProjR_coe w d x
    rw [hx, map_zero] at this
    simpa using this.symm
  · intro q
    obtain ⟨S, hS⟩ := sum_qProjR w q
    refine ⟨∑ d ∈ S, DirectSum.of (fun d => qGrade w R d) d ⟨_, qProjR_mem w d q⟩, ?_⟩
    rw [map_sum]
    conv_rhs => rw [← hS S (Finset.Subset.refl _)]
    exact Finset.sum_congr rfl fun e _ => by rw [DirectSum.coeAddMonoidHom_of]

noncomputable instance instGradedRingQGrade : GradedRing (qGrade w R) :=
  letI : Decomposition (qGrade w R) := (qGrade_internal w).chooseDecomposition
  letI : SetLike.GradedMonoid (qGrade w R) :=
    { one_mem := qProjR_one w
      mul_mem := by
        intro i j a b ha hb
        change qProjR w R (i + j) (a * b) = a * b
        have e := qProjR_mul w i j a b
        rw [show qProjR w R j b = b from hb, show qProjR w R i a = a from ha] at e
        exact e }
  { }

/-- Functoriality of `Q_R` in `R`. -/
noncomputable def QRmap {R' : Type*} [CommRing R'] [Algebra (P0 w ℤ) R'] (g : R →ₐ[P0 w ℤ] R') :
    QR w R →ₐ[P0 w ℤ] QR w R' :=
  Algebra.TensorProduct.map (AlgHom.id _ _) g

variable {R' R'' : Type*} [CommRing R'] [Algebra (P0 w ℤ) R'] [CommRing R'']
  [Algebra (P0 w ℤ) R'']

@[simp] lemma QRmap_tmul (g : R →ₐ[P0 w ℤ] R') (p : MvPolynomial ι ℤ) (y : R) :
    QRmap w g (p ⊗ₜ[P0 w ℤ] y) = p ⊗ₜ g y := rfl

lemma QRmap_qProjR (g : R →ₐ[P0 w ℤ] R') (d : M) (q : QR w R) :
    QRmap w g (qProjR w R d q) = qProjR w R' d (QRmap w g q) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul p y => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

lemma QRmap_mem (g : R →ₐ[P0 w ℤ] R') {d : M} {q : QR w R} (hq : q ∈ qGrade w R d) :
    QRmap w g q ∈ qGrade w R' d := by
  rw [mem_qGrade, ← QRmap_qProjR, show qProjR w R d q = q from hq]

lemma QRmap_comp (g : R →ₐ[P0 w ℤ] R') (g' : R' →ₐ[P0 w ℤ] R'') (q : QR w R) :
    QRmap w g' (QRmap w g q) = QRmap w (g'.comp g) q := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul p y => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

lemma QRmap_id (q : QR w R) : QRmap w (AlgHom.id (P0 w ℤ) R) q = q := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul p y => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

end Basic

section Compare

variable {C M ι : Type*} [CommRing C] [AddCommGroup M] [DecidableEq M] [Finite ι]
  {w : ι → M} {x : ι → C} {m : Ideal C}

/-- `Qring` is `QR` of `P̂₀`. -/
theorem Qring_eq (w : ι → M) (x : ι → C) (m : Ideal C) :
    Qring w x m = QR w (P0hat w x m) := rfl

theorem qProj_eq (d : M) (q : Qring w x m) :
    (qProj d q : Qring w x m) = qProjR w (P0hat w x m) d q := rfl

instance isNoetherianRing_P0 (w : ι → M) : IsNoetherianRing (P0 w ℤ) :=
  haveI := P0_finiteType w ℤ
  Algebra.FiniteType.isNoetherianRing ℤ _

theorem isNoetherianRing_P0hat (w : ι → M) (x : ι → C) (m : Ideal C) :
    IsNoetherianRing (P0hat w x m) := inferInstance

theorem finiteType_P (w : ι → M) : Algebra.FiniteType (P0 w ℤ) (MvPolynomial ι ℤ) :=
  have := Fintype.ofFinite ι
  Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _

theorem isNoetherianRing_QR (w : ι → M) (R : Type*) [CommRing R] [Algebra (P0 w ℤ) R]
    [IsNoetherianRing R] : IsNoetherianRing (QR w R) := by
  have := finiteType_P w
  have h1 : Algebra.FiniteType R (R ⊗[P0 w ℤ] MvPolynomial ι ℤ) := inferInstance
  have h2 : IsNoetherianRing (R ⊗[P0 w ℤ] MvPolynomial ι ℤ) :=
    Algebra.FiniteType.isNoetherianRing R _
  exact isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm (P0 w ℤ) R (MvPolynomial ι ℤ)).toRingEquiv

theorem isNoetherianRing_Qring (w : ι → M) (x : ι → C) (m : Ideal C) :
    IsNoetherianRing (Qring w x m) :=
  haveI := isNoetherianRing_P0hat w x m
  isNoetherianRing_QR w (P0hat w x m)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `Q_R` is of finite type over `R`, for the right algebra structure. -/
theorem finiteType_QR (w : ι → M) (R : Type*) [CommRing R] [Algebra (P0 w ℤ) R] :
    Algebra.FiniteType R (QR w R) := by
  have := finiteType_P w
  have h1 : Algebra.FiniteType R (R ⊗[P0 w ℤ] MvPolynomial ι ℤ) := inferInstance
  exact h1.equiv
    { (Algebra.TensorProduct.comm (P0 w ℤ) R (MvPolynomial ι ℤ)) with
      commutes' := fun r => by
        change (Algebra.TensorProduct.comm (P0 w ℤ) R (MvPolynomial ι ℤ)) (r ⊗ₜ 1) = 1 ⊗ₜ r
        simp }

/-- `Q_R` is of finite type over `ℤ` when `R` is of finite type over `P₀`. -/
theorem finiteType_QR_int (w : ι → M) (R : Type*) [CommRing R] [Algebra (P0 w ℤ) R]
    [Algebra.FiniteType (P0 w ℤ) R] : Algebra.FiniteType ℤ (QR w R) := by
  have := Fintype.ofFinite ι
  have h1 : Algebra.FiniteType (MvPolynomial ι ℤ) (QR w R) := inferInstance
  exact Algebra.FiniteType.trans (S := MvPolynomial ι ℤ) inferInstance h1

end Compare

section Abstract

/-- Tensoring commutes with a directed union: an element of `P ⊗ G i` dying in `P ⊗ H`, where `H` is
the directed union of the `G i`, dies at a finite stage. -/
theorem lTensor_kill_of_directed {A P H J : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [AddCommGroup H] [Module A H] [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    {G : J → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module A (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[A] G j) [DirectedSystem G (f · · ·)]
    (g : ∀ i, G i →ₗ[A] H) (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hinj : ∀ i, Function.Injective (g i)) (hsurj : ∀ r : H, ∃ i y, g i y = r)
    {i : J} (q : P ⊗[A] G i) (h : LinearMap.lTensor P (g i) q = 0) :
    ∃ (j : J) (hij : i ≤ j), LinearMap.lTensor P (f i j hij) q = 0 := by
  classical
  let φ : Module.DirectLimit G f →ₗ[A] H := Module.DirectLimit.lift _ _ G f g hg
  have hφof : ∀ i (y : G i), φ (Module.DirectLimit.of _ _ G f i y) = g i y := fun i y =>
    Module.DirectLimit.lift_of _ _ _
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of z
    rw [hφof] at hz
    rw [(hinj i) (hz.trans (map_zero _).symm), map_zero]
  have hφsurj : Function.Surjective φ := fun r => by
    obtain ⟨i, y, hy⟩ := hsurj r
    exact ⟨_, (hφof i y).trans hy⟩
  let e : Module.DirectLimit G f ≃ₗ[A] H := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let E := TensorProduct.directLimitRight f P
  let F : ∀ i j : J, i ≤ j → P ⊗[A] G i →ₗ[A] P ⊗[A] G j :=
    fun i j h => LinearMap.lTensor P (f i j h)
  haveI : DirectedSystem (fun i => P ⊗[A] G i) (F · · ·) :=
    inferInstanceAs (DirectedSystem (fun i => P ⊗[A] G i)
      (fun i j h => LinearMap.lTensor P (f i j h)))
  have hcomp : ∀ (i : J) (y : P ⊗[A] G i),
      LinearEquiv.lTensor P e (E.symm
        (Module.DirectLimit.of A J (fun i => P ⊗[A] G i) F i y)) =
        LinearMap.lTensor P (g i) y := by
    intro i y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p t =>
      have h1 : E.symm (Module.DirectLimit.of A J (fun i => P ⊗[A] G i) F i (p ⊗ₜ t)) =
          p ⊗ₜ Module.DirectLimit.of _ _ G f i t :=
        TensorProduct.directLimitRight_symm_of_tmul f P p t
      rw [h1, LinearEquiv.lTensor_tmul, LinearMap.lTensor_tmul]
      exact congrArg (p ⊗ₜ[A] ·) (hφof i t)
    | add u v hu hv => simp only [map_add, hu, hv]
  have hz : Module.DirectLimit.of A J (fun i => P ⊗[A] G i) F i q = 0 := by
    have h0 := (hcomp i q).trans h
    have h1 := (LinearEquiv.lTensor P e).injective (h0.trans (map_zero _).symm)
    exact E.symm.injective (h1.trans (map_zero _).symm)
  obtain ⟨t, hst, ht⟩ := Module.DirectLimit.of.zero_exact hz
  exact ⟨t, hst, ht⟩

end Abstract

section Filtered

variable {M : Type*} [AddCommGroup M] [DecidableEq M] {ι : Type u} [Finite ι] (w : ι → M)
  {Rh : Type u} [CommRing Rh] [Algebra (P0 w ℤ) Rh]

/-- The finitely generated `P₀`-subalgebra of `Rh` generated by `s`. -/
noncomputable abbrev Rs (s : Finset Rh) : Subalgebra (P0 w ℤ) Rh := Algebra.adjoin (P0 w ℤ) (s : Set Rh)

/-- The inclusion `Rs s → Rs t`. -/
noncomputable def RsLE {s t : Finset Rh} (h : s ⊆ t) : Rs w s →ₐ[P0 w ℤ] Rs w t :=
  Subalgebra.inclusion (Algebra.adjoin_mono (by exact_mod_cast h))

/-- The inclusion `Rs s → Rh`. -/
noncomputable def RsI (s : Finset Rh) : Rs w s →ₐ[P0 w ℤ] Rh := (Rs w s).val

lemma RsI_comp_RsLE {s t : Finset Rh} (h : s ⊆ t) : (RsI w t).comp (RsLE w h) = RsI w s := rfl

lemma RsLE_comp {s t u : Finset Rh} (h : s ⊆ t) (h' : t ⊆ u) :
    (RsLE w h').comp (RsLE w h) = RsLE w (h.trans h') := rfl

lemma RsLE_refl (s : Finset Rh) : RsLE w (Finset.Subset.refl s) = AlgHom.id _ _ := rfl

lemma QRmap_RsI_RsLE {s t : Finset Rh} (h : s ⊆ t) (q : QR w (Rs w s)) :
    QRmap w (RsI w t) (QRmap w (RsLE w h) q) = QRmap w (RsI w s) q := by
  rw [QRmap_comp, RsI_comp_RsLE]

lemma QRmap_RsLE_RsLE {s t u : Finset Rh} (h : s ⊆ t) (h' : t ⊆ u) (q : QR w (Rs w s)) :
    QRmap w (RsLE w h') (QRmap w (RsLE w h) q) = QRmap w (RsLE w (h.trans h')) q := by
  rw [QRmap_comp, RsLE_comp]

theorem exists_QR_lift_mono (s₀ : Finset Rh) (q : QR w Rh) :
    ∃ (t : Finset Rh) (hst : s₀ ⊆ t) (q' : QR w (Rs w t)), QRmap w (RsI w t) q' = q := by
  classical
  induction q using TensorProduct.induction_on with
  | zero => exact ⟨s₀, Finset.Subset.refl _, 0, map_zero _⟩
  | tmul p y =>
    refine ⟨insert y s₀, Finset.subset_insert _ _,
      p ⊗ₜ ⟨y, Algebra.subset_adjoin (by simp)⟩, rfl⟩
  | add a b ha hb =>
    obtain ⟨t, ht, a', rfl⟩ := ha
    obtain ⟨t', ht', b', rfl⟩ := hb
    refine ⟨t ∪ t', ht.trans Finset.subset_union_left,
      QRmap w (RsLE w (Finset.subset_union_left : t ⊆ t ∪ t')) a' +
        QRmap w (RsLE w (Finset.subset_union_right : t' ⊆ t ∪ t')) b', ?_⟩
    rw [map_add, QRmap_RsI_RsLE, QRmap_RsI_RsLE]

theorem exists_QR_lift (q : QR w Rh) :
    ∃ (s : Finset Rh) (q' : QR w (Rs w s)), QRmap w (RsI w s) q' = q := by
  obtain ⟨t, -, q', h⟩ := exists_QR_lift_mono w ∅ q
  exact ⟨t, q', h⟩

/-- Finite families lift to one `t` containing a given `s₀`. -/
theorem exists_QR_lift_family {κ : Type*} [Finite κ] (s₀ : Finset Rh) (q : κ → QR w Rh) :
    ∃ (t : Finset Rh) (hst : s₀ ⊆ t) (q' : κ → QR w (Rs w t)),
      ∀ k, QRmap w (RsI w t) (q' k) = q k := by
  classical
  have := Fintype.ofFinite κ
  choose t ht q' hq' using fun k => exists_QR_lift_mono w s₀ (q k)
  have hle : ∀ k, t k ⊆ s₀ ∪ Finset.univ.biUnion t := fun k =>
    (Finset.subset_biUnion_of_mem t (Finset.mem_univ k)).trans Finset.subset_union_right
  exact ⟨s₀ ∪ Finset.univ.biUnion t, Finset.subset_union_left,
    fun k => QRmap w (RsLE w (hle k)) (q' k), fun k => by rw [QRmap_RsI_RsLE, hq']⟩

lemma QRmap_eq_lTensor {R R' : Type*} [CommRing R] [Algebra (P0 w ℤ) R] [CommRing R']
    [Algebra (P0 w ℤ) R'] (g : R →ₐ[P0 w ℤ] R') (y : QR w R) :
    QRmap w g y = LinearMap.lTensor (MvPolynomial ι ℤ) g.toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul p t => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

theorem exists_QR_kill {s : Finset Rh} (q' : QR w (Rs w s)) (h : QRmap w (RsI w s) q' = 0) :
    ∃ (t : Finset Rh) (hst : s ⊆ t), QRmap w (RsLE w hst) q' = 0 := by
  classical
  letI : DirectedSystem (fun s : Finset Rh => (Rs w s : Type u))
      (fun s t (h : s ≤ t) => (RsLE w h).toLinearMap) :=
    { map_self := fun _ _ => rfl
      map_map := fun _ _ _ _ _ _ => rfl }
  obtain ⟨t, hst, ht⟩ := lTensor_kill_of_directed (J := Finset Rh) (G := fun s => (Rs w s : Type u))
    (P := MvPolynomial ι ℤ) (A := P0 w ℤ)
    (fun s t (h : s ≤ t) => (RsLE w h).toLinearMap) (fun s => (RsI w s).toLinearMap)
    (fun _ _ _ _ => rfl) (fun _ => Subtype.val_injective)
    (fun r => ⟨{r}, ⟨r, Algebra.subset_adjoin (by simp)⟩, rfl⟩) q'
    ((QRmap_eq_lTensor w _ _).symm.trans h)
  exact ⟨t, hst, (QRmap_eq_lTensor w _ _).trans ht⟩

end Filtered

end AlgMag.ChartS5
