/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.DoubleScalarLine
import AlgMag.Sec3Functorial
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Projective space with a diagonal action: charts and pure magnets

Mayeux, *Algebraic magnetism invariants of a double scalar action on the projective plane*,
arXiv:2509.04274v3, §§4, 5, for `ℙ(ι)` with arbitrary weights. This is Remark 5.1 (i) for `ℙ(ι)`.

## Main results

* `AlgMag.DoubleScalar.toPoint_injective`: `X^N → X` is a monomorphism.
* `AlgMag.DoubleScalar.InChart`: the linear subspace `𝔸^S` of the chart `v_s = 1`.
* `AlgMag.DoubleScalar.mem_image_iff_zunion`: `X^N` is the Zariski union of the `(𝔸^s)^N`: on each chart,
  the coordinates of weight in `N`.
* `AlgMag.DoubleScalar.image_eq_iff`: `X^N = X^L` iff `N ∩ Φ = L ∩ Φ`.
* `AlgMag.DoubleScalar.pureMagnets_bijOn`: pure magnets correspond to additively stable subsets of `Φ`.
* `AlgMag.DoubleScalar.chart_disjoint`, `AlgMag.DoubleScalar.chart_glue`: when charts are disjoint, and how they glue.
* `AlgMag.DoubleScalar.exists_component`: components of `X^N` over a connected base.
-/

open CategoryTheory Opposite Matrix

set_option linter.unusedSectionVars false

namespace AlgMag.DoubleScalar

section Mono

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]
variable {M : Type} [AddCommGroup M] (w : ι → M)

/-- **Corollary 3.30 for `ℙ(ι)`.** `X^N → X` is a monomorphism. -/
theorem toPoint_injective {D : CommAlgCat.{0} R} {N : AddSubmonoid M}
    {φ ψ : AttractorPt (pnAction R w) N (op D)} (h : φ.toPoint = ψ.toPoint) : φ = ψ := by
  classical
  obtain ⟨P, hP, hK⟩ := φ.toPoint.2
  have hK' : ψ.toPoint.1 = rng P := by rw [← h]; exact hK
  obtain ⟨A, hA, hAK⟩ :=
    (φ.app (affHom (constAlg (R := R) N (D : Type))) (AddMonoidAlgebra.of (D : Type) N)).2
  obtain ⟨B, hB, hBK⟩ :=
    (ψ.app (affHom (constAlg (R := R) N (D : Type))) (AddMonoidAlgebra.of (D : Type) N)).2
  let τ := (AddMonoidAlgebra.mapDomainAlgHom (D : Type) (D : Type) N.subtype).toRingHom
  have r1 := univ_rng w φ hK hAK
  have r2 := univ_rng w ψ hK' hBK
  have key : ∀ (z : AddMonoidAlgebra (D : Type) N) (n : N), (τ z).coeff (n : M) = z.coeff n := by
    intro z n
    induction z using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        Finsupp.add_apply, hx, hy]
    | single m r =>
      have : τ (AddMonoidAlgebra.single m r) = AddMonoidAlgebra.single (m : M) r := by
        simp [τ]
      rw [this, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single]
      by_cases hmn : m = n
      · subst hmn; simp
      · rw [Finsupp.single_eq_of_ne, Finsupp.single_eq_of_ne]
        · exact fun e => hmn e.symm
        · exact fun e => hmn (Subtype.ext e.symm)
  have hinj : Function.Injective τ := by
    intro x y hxy
    apply AddMonoidAlgebra.coeff_injective
    refine Finsupp.ext fun n => ?_
    have := congrArg (fun z => z.coeff (n : M)) hxy
    simpa only [key] using this
  have mapinj : Function.Injective (fun X : Matrix ι ι (AddMonoidAlgebra (D : Type) N) => X.map τ) :=
    fun X Y e => Matrix.ext fun i j => hinj (congrFun (congrFun e i) j)
  have e1 : A * B = B := by
    apply mapinj
    change (A * B).map τ = B.map τ
    rw [Matrix.map_mul]
    exact mul_eq_of_rng_le (hA.map τ).idem (r2.le.trans r1.ge)
  have e2 : B * A = A := by
    apply mapinj
    change (B * A).map τ = A.map τ
    rw [Matrix.map_mul]
    exact mul_eq_of_rng_le (hB.map τ).idem (r1.le.trans r2.ge)
  have eAB : rng B = rng A := rng_eq_of_mul e2 e1
  have val : ∀ (χ : AttractorPt (pnAction R w) N (op D)) {T' : Aff R} (t : T' ⟶ op D)
      (a : APt (affO R) N (op T')), χ.app t a = (pn ι R).map
        (CommAlgCat.ofHom (evalAlg (R := R) (N := N) (C := (D : Type)) (D := (unop T' : CommAlgCat.{0} R))
          (t.unop.hom : (D : Type) →ₐ[R] _)
          (show Multiplicative N →* (unop T' : CommAlgCat.{0} R) from a))).op.op
        (χ.app (affHom (constAlg (R := R) N (D : Type))) (AddMonoidAlgebra.of (D : Type) N)) := by
    intro χ T' t a
    let e := evalAlg (R := R) (N := N) (C := (D : Type)) (D := (unop T' : CommAlgCat.{0} R))
          (t.unop.hom : (D : Type) →ₐ[R] _)
          (show Multiplicative N →* (unop T' : CommAlgCat.{0} R) from a)
    let s : T' ⟶ op (CommAlgCat.of R (AddMonoidAlgebra (D : Type) N)) := (CommAlgCat.ofHom e).op
    have hs : s ≫ affHom (constAlg (R := R) N (D : Type)) = t := by
      refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext (AlgHom.ext fun x => ?_))
      change e (AddMonoidAlgebra.single 0 x) = _
      rw [evalAlg_single]
      have : (show Multiplicative N →* (unop T' : CommAlgCat.{0} R) from a)
        (Multiplicative.ofAdd (0 : N)) = 1 := map_one _
      rw [this, mul_one]
    have ha : APt.res s.op (AddMonoidAlgebra.of (D : Type) N :
        APt (affO R) N (op (op (CommAlgCat.of R (AddMonoidAlgebra (D : Type) N))))) = a := by
      refine MonoidHom.ext fun n => ?_
      change e (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) = _
      rw [evalAlg_single, map_one, one_mul]
      rfl
    have := χ.naturality s (affHom (constAlg (R := R) N (D : Type))) (AddMonoidAlgebra.of (D : Type) N)
    rw [hs, ha] at this
    exact this
  refine AttractorPt.ext ?_
  funext T' t a
  rw [val φ t a, val ψ t a]
  congr 1
  exact Subtype.ext (hAK.trans (eAB.symm.trans hBK.symm))

end Mono

section Chart

variable {ι : Type} [Fintype ι] [DecidableEq ι] {D D' : Type} [CommRing D] [CommRing D']

/-- The vector `v` is in the linear subspace `𝔸^S` of the chart `v_s = 1`. -/
structure IsChartVec (s : ι) (S : Finset ι) (v : ι → D) : Prop where
  one : v s = 1
  zero : ∀ j, j ≠ s → j ∉ S → v j = 0

/-- The submodule `K` of `D^ι` is a point of `𝔸^S` in the chart `{v_s = 1}` of `ℙ(ι)`. With `S = ∅` this is
the fixed point `s`, and `#S = 1, 2` give the `𝔸¹, 𝔸²` of the paper in the chart `s`. -/
def InChart (s : ι) (S : Finset ι) (K : Submodule D (ι → D)) : Prop :=
  ∃ v : ι → D, IsChartVec s S v ∧ K = Submodule.span D {v}

/-- The projector `v ⊗ δ_s` on a vector with `v_s = 1`. -/
def chartProj (s : ι) (v : ι → D) : Matrix ι ι D := Matrix.of fun i j => if j = s then v i else 0

lemma isRankOneProj_chartProj (s : ι) {v : ι → D} (hv : v s = 1) :
    IsRankOneProj (chartProj s v) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i k
    simp only [chartProj, Matrix.mul_apply, Matrix.of_apply]
    by_cases hk : k = s
    · simp [hk, hv]
    · simp [hk]
  · simp [Matrix.trace, chartProj, hv]
  · intro i j k l
    simp only [chartProj, Matrix.of_apply]
    by_cases hj : j = s <;> by_cases hl : l = s <;> simp [hj, hl, mul_comm]

lemma rng_chartProj (s : ι) {v : ι → D} (hv : v s = 1) :
    rng (chartProj s v) = Submodule.span D {v} := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    refine Submodule.mem_span_singleton.mpr ⟨u s, ?_⟩
    funext i
    change u s * v i = ∑ j, (if j = s then v i else 0) * u j
    simp [mul_comm]
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    have := col_mem_rng (chartProj s v) s
    simpa [chartProj] using this

lemma col_fixed {P : Matrix ι ι D} (hP : P * P = P) (j : ι) :
    P *ᵥ (fun i => P i j) = fun i => P i j := by
  funext k
  have := congrFun (congrFun hP k) j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/-- A line containing `v` with `v_s = 1` is spanned by `v`. -/
lemma rng_eq_span_of_fixed {P : Matrix ι ι D} (hP : IsRankOneProj P) {s : ι} {v : ι → D}
    (hv : v s = 1) (hfix : P *ᵥ v = v) : rng P = Submodule.span D {v} := by
  apply le_antisymm
  · rw [rng_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.mem_span_singleton.mpr ⟨P s j, ?_⟩
    funext i
    have := hP.cross (col_fixed hP.idem j) hfix i s
    rw [hv, mul_one] at this
    change P s j * v i = P i j
    exact this.symm
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨v, hfix⟩

/-- A rank one projector with the image of another one. -/
lemma isRankOneProj_of_mul {P Q : Matrix ι ι D} (hP : IsRankOneProj P) (h1 : P * Q = Q)
    (h2 : Q * P = P) (ht : Q.trace = 1) : IsRankOneProj Q := by
  refine ⟨?_, ht, ?_⟩
  · calc Q * Q = Q * (P * Q) := by rw [h1]
      _ = (Q * P) * Q := (Matrix.mul_assoc _ _ _).symm
      _ = Q := by rw [h2, h1]
  · intro i j k l
    have hfix : ∀ j, P *ᵥ (fun i => Q i j) = fun i => Q i j := by
      intro j
      funext i
      have := congrFun (congrFun h1 i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have := hP.cross (hfix j) (hfix l) i k
    linear_combination this

/-- Gluing a projector from vectors of a line: the formula behind the sheaf property of `X^N`.
If `∑ h_a u_a(s_a) = 1` with `u_a ∈ K`, then `∑ h_a u_a ⊗ δ_{s_a}` is a projector on `K`. -/
noncomputable def glueProj {α : Type} [Fintype α] (s : α → ι) (u : α → ι → D) (h : α → D) :
    Matrix ι ι D :=
  Matrix.of fun i j => ∑ a, if s a = j then h a * u a i else 0

/-- If the `u_a` lie in the line of the rank one projector `P` and `∑ h_a u_a(s_a) = 1`, then `glueProj s u h` is a
rank one projector with the same line as `P`. -/
theorem glueProj_spec {α : Type} [Fintype α] {P : Matrix ι ι D} (hP : IsRankOneProj P)
    (s : α → ι) (u : α → ι → D) (h : α → D) (hu : ∀ a, P *ᵥ u a = u a)
    (hsum : ∑ a, h a * u a (s a) = 1) :
    IsRankOneProj (glueProj s u h) ∧ rng (glueProj s u h) = rng P := by
  have hc : ∀ j, P *ᵥ (fun i => glueProj s u h i j) = fun i => glueProj s u h i j := by
    intro j
    funext i
    simp only [glueProj, Matrix.of_apply]
    change ∑ k, P i k * ∑ a, _ = _
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : s a = j
    · simp only [ha, ite_true]
      have := congrFun (hu a) i
      change ∑ k, P i k * u a k = u a i at this
      calc ∑ k, P i k * (h a * u a k) = h a * ∑ k, P i k * u a k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [this]
    · simp [ha]
  have h1 : P * glueProj s u h = glueProj s u h := by
    ext i j
    have := congrFun (hc j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h2 : glueProj s u h * P = P := by
    ext i k
    have hk := col_fixed hP.idem k
    simp only [Matrix.mul_apply, glueProj, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ a, ∑ j, (if s a = j then h a * u a i else 0) * P j k = h a * u a (s a) * P i k := by
      intro a
      rw [Finset.sum_eq_single (s a)]
      · simp only [ite_true]
        have := hP.cross (hu a) hk i (s a)
        linear_combination (h a) * this
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    simp only [this]
    rw [← Finset.sum_mul, hsum, one_mul]
  refine ⟨isRankOneProj_of_mul hP h1 h2 ?_, rng_eq_of_mul h2 h1⟩
  simp only [Matrix.trace, Matrix.diag_apply, glueProj, Matrix.of_apply]
  rw [Finset.sum_comm, ← hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (s a)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- **Zariski union of charts.** `K` is, Zariski locally on `Spec D`, in one of the charts
`𝔸^{S a}` of `{v_{s a} = 1}`. This is the union of subfunctors in the Zariski sheaf `ℙ(ι)`; as the charts of
different components meet in the empty scheme (`chart_disjoint`), on these it is their disjoint sum. -/
def ZUnion {α : Type} [Fintype α] (s : α → ι) (S : α → Finset ι) (K : Submodule D (ι → D)) : Prop :=
  ∃ f : α → D, Ideal.span (Set.range f) = ⊤ ∧ ∀ a, InChart (s a) (S a)
    (bcv (algebraMap D (Localization.Away (f a))) K)

/-- Locally in a chart: clearing denominators. -/
theorem exists_vectors_of_away {P : Matrix ι ι D} (hP : IsRankOneProj P) {f : D} {s : ι}
    {S : Finset ι} (h : InChart s S (bcv (algebraMap D (Localization.Away f)) (rng P))) :
    ∃ n : ℕ, (∀ j t, j ≠ s → j ∉ S → f ^ n * P j t = 0) ∧
      f ^ n ∈ Ideal.span (Set.range fun t => P s t) := by
  classical
  obtain ⟨v, hv, hK⟩ := h
  let A := Localization.Away f
  let φ := algebraMap D A
  have hQ : IsRankOneProj (P.map φ) := hP.map φ
  rw [bcv_rng] at hK
  have hfix : (P.map φ) *ᵥ v = v := by
    refine (mem_rng_iff hQ.idem).mp ?_
    rw [hK]
    exact Submodule.mem_span_singleton_self v
  have hcol : ∀ t i, φ (P i t) = φ (P s t) * v i := by
    intro t i
    have := hQ.cross (col_fixed hQ.idem t) hfix i s
    rw [hv.one, mul_one] at this
    simpa using this
  have hzero : ∀ j t, j ≠ s → j ∉ S → ∃ n : ℕ, f ^ n * P j t = 0 := by
    intro j t hj hjS
    have : φ (P j t) = 0 := by rw [hcol t j, hv.zero j hj hjS, mul_zero]
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) A _).mp this
    exact ⟨n, hc⟩
  have hunit : Ideal.map φ (Ideal.span (Set.range fun t => P s t)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e := congrFun hfix s
    rw [hv.one] at e
    rw [← e]
    refine Ideal.sum_mem _ fun t _ => ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨t, rfl⟩))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, f ^ m ∈ Ideal.span (Set.range fun t => P s t) := by
    by_contra hcon
    have hd : Disjoint ((Submonoid.powers f : Submonoid D) : Set D)
        ((Ideal.span (Set.range fun t => P s t) : Ideal D) : Set D) := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨n, rfl⟩ hn
      exact hcon ⟨n, hn⟩
    exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers f) A _).mpr hd hunit
  choose! n hn using hzero
  let N := m + ∑ j, ∑ t, n j t
  refine ⟨N, ?_, ?_⟩
  · intro j t hj hjS
    have hle : n j t ≤ N := by
      have h1 : n j t ≤ ∑ t, n j t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      have h2 : ∑ t, n j t ≤ ∑ j, ∑ t, n j t :=
        Finset.single_le_sum (f := fun j => ∑ t, n j t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add]
    linear_combination (f ^ d) * hn j t hj hjS
  · rw [show N = m + ∑ j, ∑ t, n j t from rfl, pow_add]
    exact Ideal.mul_mem_right _ _ hm

/-- A line which is locally in charts has a projector whose columns are in the charts. -/
theorem exists_proj_of_zunion {α : Type} [Fintype α] {s : α → ι} {S : α → Finset ι}
    {P : Matrix ι ι D} (hP : IsRankOneProj P) (h : ZUnion s S (rng P)) :
    ∃ Q : Matrix ι ι D, IsRankOneProj Q ∧ rng Q = rng P ∧
      ∀ i j, Q i j ≠ 0 → ∃ a, s a = j ∧ (i = j ∨ i ∈ S a) := by
  classical
  obtain ⟨f, hf, hc⟩ := h
  choose n hn1 hn2 using fun a => exists_vectors_of_away hP (hc a)
  -- the vectors `f_a^n P_{·t}`
  let u : α × ι → ι → D := fun p i => f p.1 ^ n p.1 * P i p.2
  have hu : ∀ p, P *ᵥ u p = u p := by
    intro p
    funext i
    have := congrFun (congrFun hP.idem i) p.2
    simp only [Matrix.mul_apply] at this
    change ∑ k, P i k * (f p.1 ^ n p.1 * P k p.2) = f p.1 ^ n p.1 * P i p.2
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- they generate
  have htop : Ideal.span (Set.range fun p : α × ι => u p (s p.1)) = ⊤ := by
    let J := Ideal.span (Set.range fun p : α × ι => u p (s p.1))
    have h1 : ∀ a, f a ^ (n a + n a) ∈ J := by
      intro a
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hn2 a)
      rw [pow_add]
      nth_rewrite 2 [← hc]
      rw [Finset.mul_sum]
      refine Ideal.sum_mem _ fun t _ => ?_
      have : f a ^ n a * (c t * P (s a) t) = c t * u (a, t) (s a) := by
        change _ = c t * (f a ^ n a * P (s a) t)
        ring
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨(a, t), rfl⟩)
    let m := ∑ a, (n a + n a)
    have h2 : ∀ a, f a ^ m ∈ J := by
      intro a
      have hle : n a + n a ≤ m :=
        Finset.single_le_sum (f := fun a => n a + n a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add]
      exact Ideal.mul_mem_right _ _ (h1 a)
    have h3 := Ideal.span_pow_eq_top (Set.range f) hf m
    rw [eq_top_iff, ← h3]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact h2 a
  obtain ⟨h, hh⟩ : ∃ h : α × ι → D, ∑ p, h p * u p (s p.1) = 1 := by
    have : (1 : D) ∈ Ideal.span (Set.range fun p : α × ι => u p (s p.1)) := by
      rw [htop]; trivial
    exact Ideal.mem_span_range_iff_exists_fun.mp this
  obtain ⟨hQ, hQr⟩ := glueProj_spec hP (fun p => s p.1) u h hu hh
  refine ⟨_, hQ, hQr, fun i j hij => ?_⟩
  by_contra hcon
  push Not at hcon
  apply hij
  simp only [glueProj, Matrix.of_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : s p.1 = j
  · rw [ite_eq_left hp]
    have h1 := hcon p.1 hp
    have : u p i = 0 := hn1 p.1 i p.2 (by rw [hp]; exact h1.1) h1.2
    rw [this, mul_zero]
  · rw [ite_eq_right hp]

/-- A projector is locally in the charts of its columns. -/
theorem zunion_of_proj {α : Type} [Fintype α] {s : α → ι} {S : α → Finset ι}
    {Q : Matrix ι ι D} (hQ : IsRankOneProj Q) (hcov : Function.Bijective s)
    (hsupp : ∀ a i, i ≠ s a → i ∉ S a → Q i (s a) = 0) : ZUnion s S (rng Q) := by
  classical
  refine ⟨fun a => Q (s a) (s a), ?_, fun a => ?_⟩
  · rw [Ideal.eq_top_iff_one]
    have := hQ.trace_eq
    rw [Matrix.trace] at this
    rw [← this]
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨a, rfl⟩ := hcov.2 i
    exact Ideal.subset_span ⟨a, rfl⟩
  · let A := Localization.Away (Q (s a) (s a))
    let φ := algebraMap D A
    obtain ⟨g, hg⟩ : ∃ g : A, φ (Q (s a) (s a)) * g = 1 :=
      (IsLocalization.Away.algebraMap_isUnit (Q (s a) (s a)) : IsUnit (φ _)).exists_right_inv
    let v : ι → A := fun i => g * φ (Q i (s a))
    have hQ' := hQ.map φ
    refine ⟨v, ⟨?_, fun j hj hjS => ?_⟩, ?_⟩
    · change g * φ (Q (s a) (s a)) = 1
      rw [mul_comm]; exact hg
    · change g * φ (Q j (s a)) = 0
      rw [hsupp a j hj hjS, map_zero, mul_zero]
    · rw [bcv_rng]
      refine rng_eq_span_of_fixed hQ' (s := s a) ?_ ?_
      · change g * φ (Q (s a) (s a)) = 1
        rw [mul_comm]; exact hg
      · have hc := col_fixed hQ'.idem (s a)
        funext i
        have := congrFun hc i
        change ∑ k, φ (Q i k) * (g * φ (Q k (s a))) = g * φ (Q i (s a))
        change ∑ k, φ (Q i k) * φ (Q k (s a)) = φ (Q i (s a)) at this
        rw [← this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- **The charts of different components are disjoint.** If `K` is both in the chart `𝔸^S` of `s` and in the
chart `𝔸^{S'}` of `t ≠ s` over a nonzero ring, then `t ∈ S` and `s ∈ S'`. -/
theorem chart_disjoint [Nontrivial D] {s t : ι} (hst : s ≠ t) {S S' : Finset ι}
    {K : Submodule D (ι → D)} (hK : IsLineN K) (h1 : InChart s S K) (h2 : InChart t S' K) :
    t ∈ S ∧ s ∈ S' := by
  obtain ⟨P, hP, rfl⟩ := hK
  obtain ⟨v, hv, e1⟩ := h1
  obtain ⟨v', hv', e2⟩ := h2
  have f1 : P *ᵥ v = v := (mem_rng_iff hP.idem).mp (e1 ▸ Submodule.mem_span_singleton_self v)
  have f2 : P *ᵥ v' = v' := (mem_rng_iff hP.idem).mp (e2 ▸ Submodule.mem_span_singleton_self v')
  have := hP.cross f1 f2 s t
  rw [hv.one, hv'.one, one_mul] at this
  have h : v t * v' s = 1 := this.symm
  constructor
  · by_contra hn
    rw [hv.zero t hst.symm hn, zero_mul] at h
    exact zero_ne_one h
  · by_contra hn
    rw [hv'.zero s hst hn, mul_zero] at h
    exact zero_ne_one h

/-- **§5, gluing.** `𝔸^{S} ∖ {v_t = 0}` in the chart `s` is the part of the chart `t` where the coordinate
`v_s` is invertible: this is the printed equality `𝔸¹ ∖ {z} = 𝔸¹ ∖ {y}`, by
`[0 : βu : 1] = [0 : 1 : u⁻¹β⁻¹]`. -/
theorem chart_glue {s t : ι} (hst : s ≠ t) {S S' : Finset ι} (hS : ∀ j ∈ S, j ≠ t → j ∈ S') (hs' : s ∈ S')
    {v : ι → D} (hv : IsChartVec s S v) {g : D} (hg : v t * g = 1) :
    IsChartVec t S' (fun i => g * v i) ∧ g * v s = g ∧
      Submodule.span D {fun i => g * v i} = Submodule.span D {v} := by
  refine ⟨⟨by rw [mul_comm]; exact hg, fun j hj hjS => ?_⟩, by rw [hv.one, mul_one], ?_⟩
  · by_cases hjs : j = s
    · subst hjs; exact absurd hs' hjS
    · have : j ∉ S := fun h => hjS (hS j h hj)
      change g * v j = 0
      rw [hv.zero j hjs this, mul_zero]
  · apply le_antisymm
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.mem_span_singleton.mpr ⟨g, rfl⟩)
    · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
      refine Submodule.mem_span_singleton.mpr ⟨v t, ?_⟩
      funext i
      change v t * (g * v i) = v i
      linear_combination (v i) * hg

end Chart

end AlgMag.DoubleScalar
