/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.AffineComparison
import AlgMag.Sec15PureMagnets
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Projective space with a diagonal action: attractors

Mayeux, *Algebraic magnetism invariants of a double scalar action on the projective plane*,
arXiv:2509.04274v3, §§3-5. This generalizes `AlgMag.p1` (Remark 3.25 of *Algebraic Magnetism*) from
`ℙ¹` and rank one summands of `D²` to `ℙ(ι)` and rank one summands of `D^ι`.

The projective plane of the paper is the case `ι = Fin 3`, `M = ℤ²`, weights `(1,0), (0,1), (0,0)`;
see `AlgMag.DoubleScalar`.

For `#ι ≥ 3` an idempotent of trace one need not have rank one (the identity of `𝔽₂³`), so the
vanishing of the two by two minors belongs to the definition, unlike in `AlgMag.IsLine`.

## Main results

* `AlgMag.DoubleScalar.pn`, `AlgMag.DoubleScalar.pnAction`: `ℙ(ι)`, and the action of `D(M)` with weights `w`.
* `AlgMag.DoubleScalar.mem_image_iff`: the points of `X^N` are the lines having a rank one projector
  whose `(i, j)` entry vanishes when `w i - w j ∉ N`.
* `AlgMag.DoubleScalar.toPoint_injective`: `X^N → X` is a monomorphism.
-/

open CategoryTheory Opposite Matrix

set_option linter.unusedSectionVars false

namespace AlgMag.DoubleScalar

section Algebra

variable {ι : Type} [Fintype ι] [DecidableEq ι] {D D' : Type} [CommRing D] [CommRing D']

/-- A rank one projector of `D^ι`: an idempotent of trace one whose two by two minors vanish. -/
structure IsRankOneProj (P : Matrix ι ι D) : Prop where
  idem : P * P = P
  trace_eq : P.trace = 1
  minor : ∀ i j k l, P i j * P k l = P i l * P k j

/-- The image of a matrix. -/
def rng (P : Matrix ι ι D) : Submodule D (ι → D) := LinearMap.range P.mulVecLin

/-- A rank one direct summand of `D^ι`: a `D`-point of the projective space `ℙ(ι)`. -/
def IsLineN (K : Submodule D (ι → D)) : Prop := ∃ P : Matrix ι ι D, IsRankOneProj P ∧ K = rng P

lemma col_mem_rng (P : Matrix ι ι D) (j : ι) : (fun i => P i j) ∈ rng P := by
  refine ⟨Pi.single j 1, ?_⟩
  funext i
  simp

lemma rng_eq_span (P : Matrix ι ι D) : rng P = Submodule.span D (Set.range fun j i => P i j) := by
  rw [rng, Matrix.range_mulVecLin]
  rfl

lemma mem_rng_iff {P : Matrix ι ι D} (hP : P * P = P) {v : ι → D} :
    v ∈ rng P ↔ P *ᵥ v = v := by
  constructor
  · rintro ⟨u, rfl⟩
    change P *ᵥ (P *ᵥ u) = P *ᵥ u
    rw [Matrix.mulVec_mulVec, hP]
  · intro h
    exact ⟨v, h⟩

lemma rng_mul_le (A B : Matrix ι ι D) : rng (A * B) ≤ rng A := by
  rintro _ ⟨u, rfl⟩
  refine ⟨B *ᵥ u, ?_⟩
  change A *ᵥ (B *ᵥ u) = (A * B) *ᵥ u
  rw [Matrix.mulVec_mulVec]

/-- Two idempotents with the same image: `P Q = Q`. -/
lemma mul_eq_of_rng_le {P Q : Matrix ι ι D} (hP : P * P = P) (h : rng Q ≤ rng P) : P * Q = Q := by
  ext i j
  have := (mem_rng_iff hP).mp (h (col_mem_rng Q j))
  have := congrFun this i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

lemma rng_eq_of_mul {P Q : Matrix ι ι D} (h1 : P * Q = Q) (h2 : Q * P = P) : rng P = rng Q :=
  le_antisymm (by rw [← h2]; exact rng_mul_le _ _) (by rw [← h1]; exact rng_mul_le _ _)

/-- Two vectors of a line are proportional. -/
lemma IsRankOneProj.cross {P : Matrix ι ι D} (hP : IsRankOneProj P) {c d : ι → D}
    (hc : P *ᵥ c = c) (hd : P *ᵥ d = d) (i k : ι) : c i * d k = c k * d i := by
  have ci : ∀ i, c i = ∑ a, P i a * c a := fun i => by
    conv_lhs => rw [← hc]
    rfl
  have di : ∀ i, d i = ∑ a, P i a * d a := fun i => by
    conv_lhs => rw [← hd]
    rfl
  rw [ci i, di k, ci k, di i, Finset.sum_mul_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have := hP.minor i a k b
  linear_combination (c a * d b) * this

/-- Base change of submodules of `D^ι`. -/
def bcv (φ : D →+* D') (K : Submodule D (ι → D)) : Submodule D' (ι → D') :=
  Submodule.span D' ((fun v i => φ (v i)) '' (K : Set (ι → D)))

lemma bcv_span (φ : D →+* D') (S : Set (ι → D)) :
    bcv φ (Submodule.span D S) = Submodule.span D' ((fun v i => φ (v i)) '' S) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      have : (fun i => φ ((0 : ι → D) i)) = 0 := by funext i; simp
      change (fun i => φ ((0 : ι → D) i)) ∈ Submodule.span D' _
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => φ ((x + y) i)) = (fun i => φ (x i)) + (fun i => φ (y i)) := by
        funext i; simp
      change (fun i => φ ((x + y) i)) ∈ Submodule.span D' _
      rw [this]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have : (fun i => φ ((r • x) i)) = φ r • (fun i => φ (x i)) := by funext i; simp
      change (fun i => φ ((r • x) i)) ∈ Submodule.span D' _
      rw [this]
      exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Submodule.subset_span ⟨z, Submodule.subset_span hz, rfl⟩

lemma bcv_rng (φ : D →+* D') (P : Matrix ι ι D) : bcv φ (rng P) = rng (P.map φ) := by
  rw [rng_eq_span, bcv_span, rng_eq_span, ← Set.range_comp]
  rfl

lemma bcv_id (K : Submodule D (ι → D)) : bcv (RingHom.id D) K = K := by
  simp [bcv]

lemma bcv_comp {D'' : Type} [CommRing D''] (φ : D →+* D') (ψ : D' →+* D'')
    (K : Submodule D (ι → D)) : bcv (ψ.comp φ) K = bcv ψ (bcv φ K) := by
  rw [show bcv φ K = Submodule.span D' ((fun v i => φ (v i)) '' (K : Set (ι → D))) from rfl, bcv_span,
    Set.image_image]
  rfl

lemma IsRankOneProj.map {P : Matrix ι ι D} (hP : IsRankOneProj P) (φ : D →+* D') :
    IsRankOneProj (P.map φ) where
  idem := by rw [← Matrix.map_mul, hP.idem]
  trace_eq := by
    have := congrArg φ hP.trace_eq
    rw [map_one, Matrix.trace, map_sum] at this
    simpa [Matrix.trace] using this
  minor i j k l := by
    simp only [Matrix.map_apply, ← map_mul, hP.minor i j k l]

lemma IsLineN.bcv {K : Submodule D (ι → D)} (hK : IsLineN K) (φ : D →+* D') :
    IsLineN (bcv φ K) := by
  obtain ⟨P, hP, rfl⟩ := hK
  exact ⟨P.map φ, hP.map φ, bcv_rng φ P⟩

/-- A weighted conjugate of a projector, by a family `c` multiplicative along the support of `P`. -/
lemma isRankOneProj_of_twist {P : Matrix ι ι D} (hP : IsRankOneProj P) (c : ι → ι → D)
    (hd : ∀ i, c i i = 1)
    (hm : ∀ i j k, P i j * P j k * (c i j * c j k) = P i j * P j k * c i k)
    (hmm : ∀ i j k l, P i j * P k l * (c i j * c k l) = P i l * P k j * (c i l * c k j)) :
    IsRankOneProj (Matrix.of fun i j => P i j * c i j) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i k
    simp only [Matrix.mul_apply, Matrix.of_apply]
    have e := congrFun (congrFun hP.idem i) k
    simp only [Matrix.mul_apply] at e
    calc ∑ j, P i j * c i j * (P j k * c j k) = ∑ j, P i j * P j k * c i k :=
          Finset.sum_congr rfl fun j _ => by linear_combination hm i j k
      _ = P i k * c i k := by rw [← Finset.sum_mul, e]
  · have := hP.trace_eq
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply] at this ⊢
    simp only [hd, mul_one]
    exact this
  · intro i j k l
    simp only [Matrix.of_apply]
    linear_combination hmm i j k l

/-- The diagonal automorphism of `D^ι`. -/
def dgl (u : ι → D) : (ι → D) →ₗ[D] (ι → D) where
  toFun v i := u i * v i
  map_add' x y := by funext i; simp [mul_add]
  map_smul' r x := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The image of `P` under a diagonal automorphism. -/
lemma map_dgl_rng {u v : ι → D} (huv : ∀ i, u i * v i = 1) (P : Matrix ι ι D) :
    (rng P).map (dgl u) = rng (Matrix.of fun i j => P i j * (u i * v j)) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨dgl u x, ?_⟩
    funext i
    change ∑ j, P i j * (u i * v j) * (u j * x j) = u i * ∑ j, P i j * x j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (P i j * u i * x j) * huv j
  · rintro _ ⟨x, rfl⟩
    refine ⟨P *ᵥ dgl v x, ⟨dgl v x, rfl⟩, ?_⟩
    funext i
    change u i * ∑ j, P i j * (v j * x j) = ∑ j, P i j * (u i * v j) * x j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

lemma isRankOneProj_conj {P : Matrix ι ι D} (hP : IsRankOneProj P) {u v : ι → D}
    (huv : ∀ i, u i * v i = 1) :
    IsRankOneProj (Matrix.of fun i j => P i j * (u i * v j)) := by
  refine isRankOneProj_of_twist hP _ huv ?_ ?_
  · intro i j k
    linear_combination (P i j * P j k * u i * v k) * huv j
  · intro i j k l
    have := hP.minor i j k l
    linear_combination (u i * v j * u k * v l) * this

lemma IsLineN.map_dgl {K : Submodule D (ι → D)} (hK : IsLineN K) {u v : ι → D}
    (huv : ∀ i, u i * v i = 1) : IsLineN (K.map (dgl u)) := by
  obtain ⟨P, hP, rfl⟩ := hK
  exact ⟨_, isRankOneProj_conj hP huv, map_dgl_rng huv P⟩

lemma bcv_map_dgl (φ : D →+* D') (u : ι → D) (K : Submodule D (ι → D)) :
    bcv φ (K.map (dgl u)) = (bcv φ K).map (dgl fun i => φ (u i)) := by
  rw [bcv, bcv, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun y _ => ?_
  funext i
  simp [dgl]

/-- Coefficient extraction: the core of the attractor computation, the analogue of
`AlgMag.coeff_core`. -/
theorem coeff_core {M : Type} [AddCommGroup M] (w : ι → M) (N : AddSubmonoid M)
    {P : Matrix ι ι D} (hP : IsRankOneProj P) {A : Matrix ι ι (AddMonoidAlgebra D M)}
    (hA : IsRankOneProj A) (hsupp : ∀ i j n, n ∉ N → (A i j).coeff n = 0)
    (hT : IsRankOneProj
      (Matrix.of fun i j => (AddMonoidAlgebra.single (w i - w j) (P i j) : AddMonoidAlgebra D M)))
    (h : rng A = rng
      (Matrix.of fun i j => (AddMonoidAlgebra.single (w i - w j) (P i j) : AddMonoidAlgebra D M))) :
    ∃ P' : Matrix ι ι D, IsRankOneProj P' ∧ rng P' = rng P ∧ ∀ i j, w i - w j ∉ N → P' i j = 0 := by
  classical
  set T : Matrix ι ι (AddMonoidAlgebra D M) :=
    Matrix.of fun i j => (AddMonoidAlgebra.single (w i - w j) (P i j) : AddMonoidAlgebra D M) with hTd
  have e1 : T * A = A := mul_eq_of_rng_le hT.idem h.le
  have e2 : A * T = T := mul_eq_of_rng_le hA.idem h.ge
  let P' : Matrix ι ι D := Matrix.of fun i j => (A i j).coeff (w i - w j)
  have m1 : P * P' = P' := by
    ext i k
    have := congrArg (fun x => x.coeff (w i - w k)) (congrFun (congrFun e1 i) k)
    simp only [Matrix.mul_apply, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
      Finset.sum_apply] at this
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
    have ex : w i - w k = (w i - w j) + (w j - w k) := by abel
    change P i j * (A j k).coeff (w j - w k) =
      ((AddMonoidAlgebra.single (w i - w j) (P i j) : AddMonoidAlgebra D M) * A j k).coeff (w i - w k)
    rw [ex, AddMonoidAlgebra.coeff_single_mul_add]
  have m2 : P' * P = P := by
    ext i k
    have := congrArg (fun x => x.coeff (w i - w k)) (congrFun (congrFun e2 i) k)
    simp only [Matrix.mul_apply, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
      Finset.sum_apply] at this
    have r : (T i k).coeff (w i - w k) = P i k := by
      change (AddMonoidAlgebra.single (w i - w k) (P i k) : AddMonoidAlgebra D M).coeff _ = _
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    rw [r] at this
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
    have ex : w i - w k = (w i - w j) + (w j - w k) := by abel
    change (A i j).coeff (w i - w j) * P j k =
      (A i j * (AddMonoidAlgebra.single (w j - w k) (P j k) : AddMonoidAlgebra D M)).coeff (w i - w k)
    rw [ex, AddMonoidAlgebra.coeff_mul_single_add]
  have hfix : ∀ j, P *ᵥ (fun i => P' i j) = fun i => P' i j := by
    intro j
    funext i
    have := congrFun (congrFun m1 i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  refine ⟨P', ⟨?_, ?_, ?_⟩, rng_eq_of_mul m2 m1, fun i j hij => hsupp i j _ hij⟩
  · calc P' * P' = P' * (P * P') := by rw [m1]
      _ = (P' * P) * P' := (Matrix.mul_assoc _ _ _).symm
      _ = P' := by rw [m2, m1]
  · have := congrArg (fun x => x.coeff (0 : M)) hA.trace_eq
    simp only [Matrix.trace, Matrix.diag_apply, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
      Finset.sum_apply] at this
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at this
    rw [Matrix.trace]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    change (A i i).coeff (w i - w i) = _
    rw [sub_self]
  · intro i j k l
    have := hP.cross (hfix j) (hfix l) i k
    linear_combination this

end Algebra

section Functor

variable (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R]

/-- The projective space `ℙ(ι)` on affine `R`-schemes: `ℙ(ι)(D)` is the set of rank one direct
summands of `D^ι`. For `ι = Fin 3` this is `ℙ²` (§3), the generalization of `AlgMag.p1`. -/
def pn : (Aff R)ᵒᵖ ⥤ Type where
  obj U := {K : Submodule (unop (unop U) : CommAlgCat.{0} R) (ι → (unop (unop U) : CommAlgCat.{0} R)) //
    IsLineN K}
  map {U V} g := ↾ fun K => ⟨bcv (g.unop.unop.hom : _ →ₐ[R] _).toRingHom K.1, K.2.bcv _⟩
  map_id U := by
    ext K x
    exact SetLike.ext_iff.mp (bcv_id K.1) x
  map_comp {U V W} f g := by
    ext K x
    exact SetLike.ext_iff.mp (bcv_comp (f.unop.unop.hom : _ →ₐ[R] _).toRingHom
      (g.unop.unop.hom : _ →ₐ[R] _).toRingHom K.1) x

variable {ι R}
variable {M : Type} [AddCommGroup M] (w : ι → M)

lemma apt_inv {D : Type} [CommRing D] (h : Multiplicative M →* D) (m : M) :
    h (Multiplicative.ofAdd m) * h (Multiplicative.ofAdd (-m)) = 1 := by
  rw [← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one]

lemma apt_sub {D : Type} [CommRing D] (h : Multiplicative M →* D) (m m' : M) :
    h (Multiplicative.ofAdd (m - m')) = h (Multiplicative.ofAdd m) * h (Multiplicative.ofAdd (-m')) := by
  rw [← map_mul, ← ofAdd_add, sub_eq_add_neg]

variable (R) in
/-- **§3.** The action of `D(M)` on `ℙ(ι)` with weights `w`: `h • [v] = [(h(w i) v i)_i]`. The double
scalar action is the case `M = ℤ²`, `ι = Fin 3`, `w = ((1,0), (0,1), (0,0))`. -/
noncomputable def pnAction : AAction (affO R) M (pn ι R) where
  smul {U} h K := ⟨K.1.map (dgl fun i =>
      (show (unop (unop U) : CommAlgCat.{0} R) from h (Multiplicative.ofAdd (w i)))),
    K.2.map_dgl (v := fun i => (show (unop (unop U) : CommAlgCat.{0} R) from
      h (Multiplicative.ofAdd (-w i)))) fun i => apt_inv
        (show Multiplicative M →* (unop (unop U) : CommAlgCat.{0} R) from h) (w i)⟩
  one_smul {U} K := by
    refine Subtype.ext ?_
    let D : CommAlgCat.{0} R := unop (unop U)
    have : (dgl fun i => (show D from (1 : Multiplicative M →* D) (Multiplicative.ofAdd (w i)))) =
        LinearMap.id := by
      ext x i
      simp [dgl]
    exact (congrArg (fun f => Submodule.map f K.1) this).trans (Submodule.map_id _)
  mul_smul {U} g h K := by
    refine Subtype.ext ?_
    let D : CommAlgCat.{0} R := unop (unop U)
    let g' : Multiplicative M →* D := g
    let h' : Multiplicative M →* D := h
    have : (dgl fun i => (show D from (g' * h') (Multiplicative.ofAdd (w i)))) =
        (dgl fun i => (show D from g' (Multiplicative.ofAdd (w i)))).comp
          (dgl fun i => (show D from h' (Multiplicative.ofAdd (w i)))) := by
      ext x i
      simp [dgl, mul_assoc]
    exact (congrArg (fun f => Submodule.map f K.1) this).trans (Submodule.map_comp _ _ _)
  map_smul {U V} f h K := by
    refine Subtype.ext ?_
    let D : CommAlgCat.{0} R := unop (unop U)
    let D' : CommAlgCat.{0} R := unop (unop V)
    let φ : D →+* D' := (f.unop.unop.hom : D →ₐ[R] D').toRingHom
    let h' : Multiplicative M →* D := h
    exact bcv_map_dgl φ (fun i => h' (Multiplicative.ofAdd (w i))) K.1

open Classical in
/-- The coordinate `a(e)` of `a ∈ 𝔸(N)`, zero if `e ∉ N`. -/
noncomputable def xv (N : AddSubmonoid M) (e : M) {T' : Aff R} (a : APt (affO R) N (op T')) :
    (unop T' : CommAlgCat.{0} R) :=
  if h : e ∈ N then (show (unop T' : CommAlgCat.{0} R) from a (Multiplicative.ofAdd (⟨e, h⟩ : N))) else 0

lemma xv_res (N : AddSubmonoid M) (e : M) {T' T'' : Aff R} (s : T'' ⟶ T')
    (a : APt (affO R) N (op T')) : xv N e (APt.res s.op a) = s.unop.hom (xv N e a) := by
  unfold xv
  split_ifs with h
  · rfl
  · exact (map_zero _).symm

lemma xv_one (N : AddSubmonoid M) {e : M} (h : e ∈ N) {T' : Aff R} :
    xv N e (1 : APt (affO R) N (op T')) = 1 := by
  unfold xv
  rw [dite_eq_left h]
  rfl

lemma xv_zero (N : AddSubmonoid M) {T' : Aff R} (a : APt (affO R) N (op T')) :
    xv N (0 : M) a = 1 := by
  unfold xv
  rw [dite_eq_left N.zero_mem]
  exact a.map_one

lemma xv_mul (N : AddSubmonoid M) (e : M) {T' : Aff R} (g : APt (affO R) M (op T'))
    (a : APt (affO R) N (op T')) :
    xv N e (APt.toMagnet N g * a) =
      (show (unop T' : CommAlgCat.{0} R) from g (Multiplicative.ofAdd e)) * xv N e a := by
  unfold xv
  split_ifs with h
  · rfl
  · exact (mul_zero _).symm

lemma xv_add (N : AddSubmonoid M) {e f : M} (he : e ∈ N) (hf : f ∈ N) {T' : Aff R}
    (a : APt (affO R) N (op T')) : xv N e a * xv N f a = xv N (e + f) a := by
  unfold xv
  rw [dite_eq_left he, dite_eq_left hf, dite_eq_left (N.add_mem he hf)]
  exact (a.map_mul (Multiplicative.ofAdd (⟨e, he⟩ : N)) (Multiplicative.ofAdd (⟨f, hf⟩ : N))).symm

lemma mul_assoc_right_comm_aux {E : Type} [CommRing E] (p x y : E) : p * (y * x) = p * x * y := by
  ring

/-- The twisted projector `(t(P i j) a(w i - w j))`. -/
lemma isRankOneProj_xv {D : CommAlgCat.{0} R} (N : AddSubmonoid M) {P : Matrix ι ι D}
    (hP : IsRankOneProj P) (hs : ∀ i j, w i - w j ∉ N → P i j = 0) {T' : Aff R}
    (t : T' ⟶ op D) (a : APt (affO R) N (op T')) :
    IsRankOneProj (Matrix.of fun i j => (t.unop.hom : D →ₐ[R] _) (P i j) * xv N (w i - w j) a) := by
  let φ : D →ₐ[R] (unop T' : CommAlgCat.{0} R) := t.unop.hom
  have hQ : IsRankOneProj (P.map φ.toRingHom) := hP.map _
  have hs' : ∀ i j, w i - w j ∉ N → φ (P i j) = 0 := fun i j h => by rw [hs i j h, map_zero]
  refine isRankOneProj_of_twist (P := P.map φ.toRingHom) hQ (fun i j => xv N (w i - w j) a) ?_ ?_ ?_
  · intro i
    simp only [sub_self]
    exact xv_zero N a
  · intro i j k
    change φ (P i j) * φ (P j k) * _ = φ (P i j) * φ (P j k) * _
    by_cases h1 : w i - w j ∈ N
    · by_cases h2 : w j - w k ∈ N
      · have e : (w i - w j) + (w j - w k) = w i - w k := by abel
        rw [xv_add N h1 h2, e]
      · rw [hs' j k h2]; ring
    · rw [hs' i j h1]; ring
  · intro i j k l
    have hmin : φ (P i j) * φ (P k l) = φ (P i l) * φ (P k j) := by
      rw [← map_mul, ← map_mul, hP.minor i j k l]
    change φ (P i j) * φ (P k l) * _ = φ (P i l) * φ (P k j) * _
    by_cases h1 : w i - w j ∈ N
    · by_cases h2 : w k - w l ∈ N
      · by_cases h3 : w i - w l ∈ N
        · by_cases h4 : w k - w j ∈ N
          · have e : (w i - w j) + (w k - w l) = (w i - w l) + (w k - w j) := by abel
            rw [xv_add N h1 h2, xv_add N h3 h4, e, hmin]
          · have h0 : φ (P i l) * φ (P k j) = 0 := by rw [hs' k j h4, mul_zero]
            rw [hmin, h0]; ring
        · have h0 : φ (P i l) * φ (P k j) = 0 := by rw [hs' i l h3, zero_mul]
          rw [hmin, h0]; ring
      · have h0 : φ (P i j) * φ (P k l) = 0 := by rw [hs' k l h2, mul_zero]
        rw [← hmin, h0]; ring
    · have h0 : φ (P i j) * φ (P k l) = 0 := by rw [hs' i j h1, zero_mul]
      rw [← hmin, h0]; ring

/-- The point of `X^N` attached to a rank one projector supported on `N`. -/
noncomputable def liftPt {D : CommAlgCat.{0} R} (N : AddSubmonoid M) {P : Matrix ι ι D}
    (hP : IsRankOneProj P) (hs : ∀ i j, w i - w j ∉ N → P i j = 0) :
    AttractorPt (pnAction R w) N (op D) where
  app {T'} t a := ⟨rng (Matrix.of fun i j => (t.unop.hom : D →ₐ[R] _) (P i j) * xv N (w i - w j) a),
    _, isRankOneProj_xv w N hP hs t a, rfl⟩
  naturality {T' T''} s t a := by
    refine Subtype.ext ?_
    refine Eq.trans ?_ (bcv_rng (s.unop.hom : _ →ₐ[R] _).toRingHom _).symm
    refine congrArg rng (Matrix.ext fun i j => ?_)
    rw [Matrix.of_apply, Matrix.map_apply, Matrix.of_apply, xv_res]
    exact (map_mul (s.unop.hom : _ →ₐ[R] _).toRingHom _ _).symm
  equivariant {T'} t g a := by
    refine Subtype.ext ?_
    refine Eq.trans ?_ (map_dgl_rng (v := fun i => (show (unop T' : CommAlgCat.{0} R) from
      g (Multiplicative.ofAdd (-w i)))) (fun i => apt_inv
        (show Multiplicative M →* (unop T' : CommAlgCat.{0} R) from g) (w i)) _).symm
    refine congrArg rng (Matrix.ext fun i j => ?_)
    rw [Matrix.of_apply, Matrix.of_apply, xv_mul]
    have e := apt_sub (show Multiplicative M →* (unop T' : CommAlgCat.{0} R) from g) (w i) (w j)
    generalize (show Multiplicative M →* (unop T' : CommAlgCat.{0} R) from g)
      (Multiplicative.ofAdd (w i - w j)) = A at e
    change (t.unop.hom : D →ₐ[R] _) (P i j) * (A * xv N (w i - w j) a) = _
    rw [e]
    exact mul_assoc_right_comm_aux _ _ _

lemma liftPt_toPoint {D : CommAlgCat.{0} R} (N : AddSubmonoid M) {P : Matrix ι ι D}
    (hP : IsRankOneProj P) (hs : ∀ i j, w i - w j ∉ N → P i j = 0) :
    ((liftPt w N hP hs).toPoint).1 = rng P := by
  change rng _ = rng P
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  by_cases h : w i - w j ∈ N
  · rw [xv_one N h, mul_one]
    rfl
  · rw [hs i j h, map_zero, zero_mul]

/-- The value of a point of `X^N` on the universal point of `𝔸(N)`, pushed to `D[M]`, is the
twist of its unit value. This is the equivariance of the point. -/
theorem univ_rng {D : CommAlgCat.{0} R} {N : AddSubmonoid M}
    (φ : AttractorPt (pnAction R w) N (op D)) {P : Matrix ι ι D}
    (hK : φ.toPoint.1 = rng P) {Q : Matrix ι ι (AddMonoidAlgebra (D : Type) N)}
    (hQ : (φ.app (affHom (constAlg (R := R) N (D : Type))) (AddMonoidAlgebra.of (D : Type) N)).1 = rng Q) :
    rng (Q.map (AddMonoidAlgebra.mapDomainAlgHom (D : Type) (D : Type) N.subtype).toRingHom) =
      rng (Matrix.of fun i j =>
        (AddMonoidAlgebra.single (w i - w j) (P i j) : AddMonoidAlgebra (D : Type) M)) := by
  classical
  let DD : Type := D
  let EN := AddMonoidAlgebra DD N
  let EZ := AddMonoidAlgebra DD M
  let tN : op (CommAlgCat.of R EN) ⟶ op D := affHom (constAlg (R := R) N DD)
  let aN : APt (affO R) N (op (op (CommAlgCat.of R EN))) := AddMonoidAlgebra.of DD N
  let τ₀ := AddMonoidAlgebra.mapDomainAlgHom DD DD N.subtype
  let τ : EN →ₐ[R] EZ := τ₀.restrictScalars R
  let tτ : op (CommAlgCat.of R EZ) ⟶ op (CommAlgCat.of R EN) := affHom τ
  let ι₀ : DD →ₐ[R] EZ := constAlg (R := R) M DD
  let tZ : op (CommAlgCat.of R EZ) ⟶ op D := affHom ι₀
  have htt : tτ ≫ tN = tZ := by
    refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext (AlgHom.ext fun x => ?_))
    change τ₀ (AddMonoidAlgebra.single 0 x) = AddMonoidAlgebra.single 0 x
    simp [τ₀]
  let hU : APt (affO R) M (op (op (CommAlgCat.of R EZ))) := AddMonoidAlgebra.of DD M
  have e1 : φ.app tZ (APt.res tτ.op aN) = (pn ι R).map tτ.op (φ.app tN aN) := by
    rw [← htt]
    exact φ.naturality tτ tN aN
  have e2 : APt.res tτ.op aN = APt.toMagnet N hU * 1 := by
    refine MonoidHom.ext fun n => ?_
    refine Eq.trans ?_ (mul_one _).symm
    change τ₀ (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) =
      AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M) 1
    simp [τ₀]
  have e3 := φ.equivariant tZ hU 1
  have e4 : φ.app tZ 1 = (pn ι R).map tZ.op φ.toPoint := by
    have := φ.naturality tZ (𝟙 _) 1
    rw [Category.comp_id, show APt.res tZ.op (1 : APt (affO R) N (op (op D))) = 1 from by ext p; simp] at this
    exact this
  have l1 : (((pn ι R).map tτ.op (φ.app tN aN)).1 : Submodule EZ (ι → EZ)) =
      rng (Q.map τ.toRingHom) := by
    change bcv τ.toRingHom (φ.app tN aN).1 = _
    rw [show (φ.app tN aN).1 = rng Q from hQ]
    exact bcv_rng τ.toRingHom Q
  have l2 : (((pn ι R).map tZ.op φ.toPoint).1 : Submodule EZ (ι → EZ)) = rng (P.map ι₀.toRingHom) := by
    change bcv ι₀.toRingHom φ.toPoint.1 = _
    rw [hK]
    exact bcv_rng ι₀.toRingHom P
  have e5 : rng (Q.map τ.toRingHom) = (rng (P.map ι₀.toRingHom)).map
      (dgl fun i => (show EZ from hU (Multiplicative.ofAdd (w i)))) := by
    rw [← l1, ← l2, ← e1, e2, e3, e4]
    rfl
  have huv : ∀ i, (show EZ from hU (Multiplicative.ofAdd (w i))) *
      (show EZ from hU (Multiplicative.ofAdd (-w i))) = 1 := fun i =>
    apt_inv (show Multiplicative M →* EZ from hU) (w i)
  rw [map_dgl_rng huv] at e5
  refine e5.trans (congrArg rng (Matrix.ext fun i j => ?_))
  change (AddMonoidAlgebra.single (0 : M) (P i j) : EZ) *
      (AddMonoidAlgebra.single (w i) (1 : DD) * AddMonoidAlgebra.single (-w j) (1 : DD)) = _
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single]
  simp [Matrix.of_apply, sub_eq_add_neg]

lemma coeff_mapSub {D : Type} [CommRing D] (N : AddSubmonoid M) (f : AddMonoidAlgebra D N) {n : M}
    (hn : n ∉ N) : (AddMonoidAlgebra.mapDomainAlgHom D D N.subtype f).coeff n = 0 := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy, add_zero]
  | single m r =>
    have : AddMonoidAlgebra.mapDomainAlgHom D D N.subtype (AddMonoidAlgebra.single m r) =
        AddMonoidAlgebra.single (m : M) r := by simp
    rw [this, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne]
    intro e
    exact hn (e ▸ m.2)

/-- The twist of a rank one projector in `D[M]`. -/
lemma isRankOneProj_single {D : Type} [CommRing D] {P : Matrix ι ι D} (hP : IsRankOneProj P) :
    IsRankOneProj (Matrix.of fun i j =>
      (AddMonoidAlgebra.single (w i - w j) (P i j) : AddMonoidAlgebra D M)) := by
  classical
  let ι₀ : D →+* AddMonoidAlgebra D M := AddMonoidAlgebra.singleZeroRingHom
  have := isRankOneProj_conj (hP.map ι₀)
    (u := fun i => AddMonoidAlgebra.single (w i) (1 : D))
    (v := fun i => AddMonoidAlgebra.single (-w i) (1 : D)) (fun i => by
      rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, AddMonoidAlgebra.one_def, mul_one])
  have e : (Matrix.of fun i j =>
      (AddMonoidAlgebra.single (w i - w j) (P i j) : AddMonoidAlgebra D M)) =
      Matrix.of fun i j => (P.map ι₀) i j * (AddMonoidAlgebra.single (w i) (1 : D) *
        AddMonoidAlgebra.single (-w j) (1 : D)) := by
    refine Matrix.ext fun i j => ?_
    change _ = (AddMonoidAlgebra.single (0 : M) (P i j)) * _
    rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single]
    simp [Matrix.of_apply, sub_eq_add_neg]
  rw [e]
  exact this

/-- **The key step.** A point of `X^N` over `D` has a rank one projector with the same image, whose
`(i, j)` entry vanishes when `w i - w j ∉ N`. This is the analogue of
`AlgMag.exists_proj_of_attractor`, and the chart computation of the paper written globally: in the
column `j` of the projector, the coordinate `i` has the weight `w i - w j` of Lemma 4.2. -/
theorem exists_proj_of_attractor {D : CommAlgCat.{0} R} {N : AddSubmonoid M}
    (φ : AttractorPt (pnAction R w) N (op D)) {P : Matrix ι ι D} (hP : IsRankOneProj P)
    (hK : φ.toPoint.1 = rng P) :
    ∃ P' : Matrix ι ι D, IsRankOneProj P' ∧ rng P' = rng P ∧ ∀ i j, w i - w j ∉ N → P' i j = 0 := by
  obtain ⟨Q, hQ, hQK⟩ :=
    (φ.app (affHom (constAlg (R := R) N (D : Type))) (AddMonoidAlgebra.of (D : Type) N)).2
  have h := univ_rng w φ hK hQK
  refine coeff_core (D := (D : Type)) w N hP (hQ.map _) (fun i j n hn => ?_) (isRankOneProj_single w hP) h
  exact coeff_mapSub N (Q i j) hn

/-- **The attractor, on points.** `K ∈ X^N(D)` iff `K` has a rank one projector whose `(i, j)` entry
vanishes when `w i - w j ∉ N`. -/
theorem mem_image_iff {D : CommAlgCat.{0} R} {N : AddSubmonoid M} (K : (pn ι R).obj (op (op D))) :
    K ∈ attractorImage (pnAction R w) N (op D) ↔
      ∃ P : Matrix ι ι D, IsRankOneProj P ∧ K.1 = rng P ∧ ∀ i j, w i - w j ∉ N → P i j = 0 := by
  constructor
  · rintro ⟨φ, rfl⟩
    obtain ⟨P, hP, hK⟩ := φ.toPoint.2
    obtain ⟨P', hP', e, hs⟩ := exists_proj_of_attractor w φ hP hK
    exact ⟨P', hP', hK.trans e.symm, hs⟩
  · rintro ⟨P, hP, hK, hs⟩
    exact ⟨liftPt w N hP hs, Subtype.ext ((liftPt_toPoint w N hP hs).trans hK.symm)⟩

end Functor

end AlgMag.DoubleScalar
