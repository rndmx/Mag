/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.DoubleScalarCharts

/-!
# Projective space with a diagonal action: pure magnets

Mayeux, *Algebraic magnetism invariants of a double scalar action on the projective plane*,
arXiv:2509.04274v3, §4, for `ℙ(ι)` with arbitrary weights `w`. Here `Om w` is the set of the weights
`w j - w s`, `j ≠ s`, of the charts, the analogue of `Φ`.

## Main results

* `AlgMag.DoubleScalar.mem_image_iff_zunion`: `X^N` is the Zariski union of the charts `(𝔸^s)^N`.
* `AlgMag.DoubleScalar.mem_of_tangent`: the tangent vector test, which replaces the printed step in the
  proof of Proposition 4.1.
* `AlgMag.DoubleScalar.image_eq_iff`: `X^N = X^L` iff `N ∩ Φ = L ∩ Φ`.
* `AlgMag.DoubleScalar.image_eq_iff_charts`: `X^N = X^L` iff the attractors agree on each chart.
* `AlgMag.DoubleScalar.pureMagnets_bijOn`: Proposition 4.1 for `ℙ(ι)`.
* `AlgMag.DoubleScalar.exists_component`: components of `X^N` over a connected base.
* `AlgMag.DoubleScalar.component_rel_face`: faces have the same components.
* `AlgMag.DoubleScalar.toPoint_ofFace`: the face morphism `X^N → X^F` on points.
-/

open CategoryTheory Opposite Matrix

set_option linter.unusedSectionVars false

namespace AlgMag.DoubleScalar

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]
variable {M : Type} [AddCommGroup M] (w : ι → M)

/-- The weights of the charts: the analogue of `Φ`, in the notation of §3. -/
def Om : Set M := {m | ∃ i j : ι, i ≠ j ∧ m = w i - w j}

open Classical in
/-- The coordinates of the chart `s` whose weight is in `N`: `(𝔸^s)^N = 𝔸^{chartS w N s}` by Lemma 4.2. -/
noncomputable def chartS (N : AddSubmonoid M) (s : ι) : Finset ι :=
  Finset.univ.filter fun j => j ≠ s ∧ w j - w s ∈ N

lemma mem_chartS {N : AddSubmonoid M} {s j : ι} : j ∈ chartS w N s ↔ j ≠ s ∧ w j - w s ∈ N := by
  simp [chartS]

/-- **§4, §5: the method of the paper.** `X^N` is the Zariski union of the attractors `(𝔸^s)^N` of the charts,
each one being given by the coordinates of weight in `N` (Lemma 4.2). -/
theorem mem_image_iff_zunion {D : CommAlgCat.{0} R} {N : AddSubmonoid M}
    (K : (pn ι R).obj (op (op D))) :
    K ∈ attractorImage (pnAction R w) N (op D) ↔ ZUnion (id : ι → ι) (chartS w N) K.1 := by
  rw [mem_image_iff]
  constructor
  · rintro ⟨P, hP, hK, hs⟩
    rw [hK]
    refine zunion_of_proj hP Function.bijective_id fun a i hi hS => hs i a fun hN => hS ?_
    exact (mem_chartS w).mpr ⟨hi, hN⟩
  · intro h
    obtain ⟨P, hP, hK⟩ := K.2
    rw [hK] at h
    obtain ⟨Q, hQ, e, hs⟩ := exists_proj_of_zunion hP h
    refine ⟨Q, hQ, hK.trans e.symm, fun i j hij => ?_⟩
    by_contra hn
    obtain ⟨a, rfl, h1 | h1⟩ := hs i j hn
    · subst h1
      simp at hij
    · exact hij ((mem_chartS w).mp h1).2

lemma image_eq_of_inter {N L : AddSubmonoid M} (h : (N : Set M) ∩ Om w = (L : Set M) ∩ Om w) :
    attractorImage (pnAction R w) N = attractorImage (pnAction R w) L := by
  have key : ∀ {N L : AddSubmonoid M}, (N : Set M) ∩ Om w = (L : Set M) ∩ Om w →
      ∀ (T : Aff R), attractorImage (pnAction R w) N T ⊆ attractorImage (pnAction R w) L T := by
    intro N L h T K hK
    obtain ⟨P, hP, e, hs⟩ := (mem_image_iff (D := unop T) w K).mp hK
    refine (mem_image_iff (D := unop T) w K).mpr ⟨P, hP, e, fun i j hij => hs i j fun hn => hij ?_⟩
    by_cases hne : i = j
    · subst hne
      simp
    · have : w i - w j ∈ (N : Set M) ∩ Om w := ⟨hn, i, j, hne, rfl⟩
      rw [h] at this
      exact this.1
  funext T
  exact Set.Subset.antisymm (key h T) (key h.symm T)

/-- `X^N = X^{[N ∩ Φ⟩}`. -/
theorem image_eq_closure (N : AddSubmonoid M) :
    attractorImage (pnAction R w) N =
      attractorImage (pnAction R w) (AddSubmonoid.closure ((N : Set M) ∩ Om w)) := by
  refine image_eq_of_inter w (Set.Subset.antisymm ?_ ?_)
  · exact fun x hx => ⟨AddSubmonoid.subset_closure hx, hx.2⟩
  · rintro x ⟨hx, hO⟩
    exact ⟨(AddSubmonoid.closure_le.mpr Set.inter_subset_left) hx, hO⟩

/-- The tangent vector `e_s + ε e_j` at the fixed point `s`. -/
noncomputable def tangentVec (R : Type) [CommRing R] (s j : ι) : ι → DualNumber R := fun i =>
  if i = s then 1 else if i = j then DualNumber.eps else 0

lemma tangentVec_self (s j : ι) : tangentVec R s j s = 1 := by simp [tangentVec]

lemma tangentVec_of_ne {s j : ι} (hj : j ≠ s) : tangentVec R s j j = DualNumber.eps := by
  simp [tangentVec, hj]

lemma tangentVec_other {s j i : ι} (h1 : i ≠ s) (h2 : i ≠ j) : tangentVec R s j i = 0 := by
  simp [tangentVec, h1, h2]

/-- The tangent vector as a point of `ℙ(ι)` over the dual numbers. -/
noncomputable def tangentLine (R : Type) [CommRing R] (s j : ι) :
    (pn ι R).obj (op (op (CommAlgCat.of R (DualNumber R)))) :=
  ⟨Submodule.span (DualNumber R) {tangentVec R s j}, chartProj s (tangentVec R s j),
    isRankOneProj_chartProj s (tangentVec_self s j), (rng_chartProj s (tangentVec_self s j)).symm⟩

/-- If `w j - w s ∈ N`, the tangent vector at `s` in the direction `j` is in `X^N`. -/
theorem tangent_mem {N : AddSubmonoid M} {s j : ι} (h : w j - w s ∈ N) :
    tangentLine R s j ∈ attractorImage (pnAction R w) N (op (CommAlgCat.of R (DualNumber R))) := by
  refine (mem_image_iff (D := CommAlgCat.of R (DualNumber R)) w _).mpr
    ⟨chartProj s (tangentVec R s j), isRankOneProj_chartProj s (tangentVec_self s j),
      (rng_chartProj s (tangentVec_self s j)).symm, fun i k hik => ?_⟩
  change (if k = s then tangentVec R s j i else 0) = 0
  by_cases hk : k = s
  · subst hk
    rw [ite_eq_left rfl]
    by_cases hi : i = k
    · subst hi; simp at hik
    · by_cases hij : i = j
      · subst hij; exact absurd h hik
      · exact tangentVec_other hi hij
  · rw [ite_eq_right hk]

/-- **The test replacing the printed step of Proposition 4.1.** If the tangent vector at the fixed point `s` in
the direction `j ≠ s` lies in `X^L`, then `w j - w s ∈ L`. Test objects must be non reduced: over a field, the
attractor of `ℙ¹` for `ℕ` and for `ℤ` have the same points. -/
theorem mem_of_tangent [Nontrivial R] {L : AddSubmonoid M} {s j : ι} (hj : j ≠ s)
    (h : tangentLine R s j ∈ attractorImage (pnAction R w) L (op (CommAlgCat.of R (DualNumber R)))) :
    w j - w s ∈ L := by
  classical
  by_contra hL
  obtain ⟨P, hP, hK, hs⟩ := (mem_image_iff (D := CommAlgCat.of R (DualNumber R)) w _).mp h
  let v := tangentVec R s j
  have hv : v s = 1 := tangentVec_self s j
  have hK' : Submodule.span (DualNumber R) {v} = rng P := hK
  have hfix : P *ᵥ v = v := (mem_rng_iff hP.idem).mp (hK' ▸ Submodule.mem_span_singleton_self v)
  have h1 : P j s = P s s * DualNumber.eps := by
    have := hP.cross (col_fixed hP.idem s) hfix j s
    rw [hv, mul_one, show v j = DualNumber.eps from tangentVec_of_ne hj] at this
    exact this
  have h0 : P j s = 0 := hs j s hL
  have h2 : P s s + P s j * DualNumber.eps = 1 := by
    have := congrFun hfix s
    rw [hv] at this
    change ∑ k, P s k * v k = 1 at this
    rw [← this, Finset.sum_eq_add_of_mem s j (Finset.mem_univ _) (Finset.mem_univ _) hj.symm]
    · rw [hv, mul_one, show v j = DualNumber.eps from tangentVec_of_ne hj]
    · intro c _ hc
      rw [show v c = 0 from tangentVec_other hc.1 hc.2, mul_zero]
  have h3 : (DualNumber.eps : DualNumber R) = 0 := by
    have e : (P s s + P s j * DualNumber.eps) * DualNumber.eps = P s s * DualNumber.eps := by
      rw [add_mul, mul_assoc, DualNumber.eps_mul_eps, mul_zero, add_zero]
    rw [h2, one_mul, ← h1, h0] at e
    exact e
  exact (one_ne_zero (α := R)) (by simpa using congrArg TrivSqZeroExt.snd h3)

/-- `X^N = X^L` iff `N ∩ Φ = L ∩ Φ`. -/
theorem image_eq_iff [Nontrivial R] {N L : AddSubmonoid M} :
    attractorImage (pnAction R w) N = attractorImage (pnAction R w) L ↔
      (N : Set M) ∩ Om w = (L : Set M) ∩ Om w := by
  refine ⟨fun e => ?_, image_eq_of_inter w⟩
  have key : ∀ {N L : AddSubmonoid M}, attractorImage (pnAction R w) N =
      attractorImage (pnAction R w) L → (N : Set M) ∩ Om w ⊆ (L : Set M) ∩ Om w := by
    rintro N L e _ ⟨hx, i, j, hij, rfl⟩
    refine ⟨?_, i, j, hij, rfl⟩
    refine mem_of_tangent (R := R) w hij ?_
    rw [← e]
    exact tangent_mem w hx
  exact Set.Subset.antisymm (key e) (key e.symm)

/-- **The two printed steps of Proposition 4.1.** `X^N = X^L` iff the attractors agree on every chart
`{v_s = 1}`, in the form of Lemma 4.2. The direct implication is the step "*Since `X^N = X^L`, we have
`(𝔸²)^N = (𝔸²)^L`*" of the printed proof of surjectivity; the printed text gives no reason for it. -/
theorem image_eq_iff_charts [Nontrivial R] {N L : AddSubmonoid M} :
    attractorImage (pnAction R w) N = attractorImage (pnAction R w) L ↔
      ∀ s, chartS w N s = chartS w L s := by
  rw [image_eq_iff]
  constructor
  · intro e s
    ext j
    simp only [mem_chartS]
    refine and_congr_right fun hj => ?_
    have m : w j - w s ∈ Om w := ⟨j, s, hj, rfl⟩
    have a : w j - w s ∈ (N : Set M) ∩ Om w ↔ w j - w s ∈ (L : Set M) ∩ Om w := by rw [e]
    exact ⟨fun h => (a.mp ⟨h, m⟩).1, fun h => (a.mpr ⟨h, m⟩).1⟩
  · intro e
    have key : ∀ {N L : AddSubmonoid M}, (∀ s, chartS w N s = chartS w L s) →
        (N : Set M) ∩ Om w ⊆ (L : Set M) ∩ Om w := by
      rintro N L e _ ⟨hx, i, j, hij, rfl⟩
      refine ⟨?_, i, j, hij, rfl⟩
      have : i ∈ chartS w N j := (mem_chartS w).mpr ⟨hij, hx⟩
      rw [e j] at this
      exact ((mem_chartS w).mp this).2
    exact Set.Subset.antisymm (key e) (key fun s => (e s).symm)

/-- `E ⊆ Φ` is additively stable: `[E⟩ ∩ Φ = E` (§4). -/
def AddStableIn (E : Set M) : Prop :=
  E ⊆ Om w ∧ ((AddSubmonoid.closure E : AddSubmonoid M) : Set M) ∩ Om w = E

/-- A magnet is pure iff it is generated by its elements in `Φ`. -/
theorem isPure_iff [Nontrivial R] {N : AddSubmonoid M} :
    IsPure (attractorImage (pnAction R w)) N ↔ N = AddSubmonoid.closure ((N : Set M) ∩ Om w) := by
  constructor
  · exact fun h => IsPure.eq_closure_inter (image_eq_closure w) h
  · intro h L e
    rw [h]
    refine AddSubmonoid.closure_le.mpr ?_
    have := (image_eq_iff w).mp e
    rw [this]
    exact Set.inter_subset_left

/-- **Proposition 4.1 for `ℙ(ι)`.** `N ↦ N ∩ Φ` is a bijection from the pure magnets to the additively stable
subsets of `Φ`. The nonzero base is needed: over the zero ring all attractors agree. -/
theorem pureMagnets_bijOn [Nontrivial R] :
    Set.BijOn (fun N : AddSubmonoid M => (N : Set M) ∩ Om w)
      (pureMagnets (attractorImage (pnAction R w))) {E | AddStableIn w E} := by
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    refine ⟨Set.inter_subset_right, ?_⟩
    change _ ∩ _ = _
    rw [← (isPure_iff w).mp hN]
  · intro N hN L hL e
    rw [(isPure_iff w).mp hN, (isPure_iff w).mp hL]
    exact congrArg _ e
  · intro E hE
    have hE' : ((AddSubmonoid.closure E : AddSubmonoid M) : Set M) ∩ Om w = E := hE.2
    refine ⟨AddSubmonoid.closure E, ?_, hE'⟩
    refine (isPure_iff w).mpr ?_
    change _ = AddSubmonoid.closure (_ ∩ _)
    rw [hE']

/-- The inverse bijection of Proposition 4.1: a stable set is sent to the monoid it generates. -/
theorem isPure_closure [Nontrivial R] {E : Set M} (hE : AddStableIn w E) :
    IsPure (attractorImage (pnAction R w)) (AddSubmonoid.closure E) := by
  refine (isPure_iff w).mpr ?_
  rw [hE.2]

/-! ### Components -/

/-- Two fixed points are in the same component of `X^N`: `±(w i - w j) ∈ N`. -/
def CompRel (N : AddSubmonoid M) (i j : ι) : Prop := w i - w j ∈ N ∧ w j - w i ∈ N

lemma CompRel.refl (N : AddSubmonoid M) (i : ι) : CompRel w N i i := by simp [CompRel]

variable {w} in
lemma CompRel.symm {N : AddSubmonoid M} {i j : ι} (h : CompRel w N i j) : CompRel w N j i :=
  ⟨h.2, h.1⟩

variable {w} in
lemma CompRel.trans {N : AddSubmonoid M} {i j k : ι} (h : CompRel w N i j) (h' : CompRel w N j k) :
    CompRel w N i k := by
  refine ⟨?_, ?_⟩
  · have := N.add_mem h.1 h'.1
    rwa [show w i - w j + (w j - w k) = w i - w k by abel] at this
  · have := N.add_mem h'.2 h.2
    rwa [show w k - w j + (w j - w i) = w k - w i by abel] at this

/-- **§5.** For a face `F` of `N`, the components of `X^N` and `X^F` are indexed alike: this is the observed
bijection on connected components for `[±(0,1)⟩ ⊂ [±(0,1), (1,0)⟩`. -/
theorem component_rel_face {F N : AddSubmonoid M} (hF : IsFace F N) (i j : ι) :
    CompRel w F i j ↔ CompRel w N i j := by
  constructor
  · exact fun h => ⟨hF.le h.1, hF.le h.2⟩
  · intro h
    have h0 : w i - w j + (w j - w i) ∈ F := by
      rw [show w i - w j + (w j - w i) = 0 by abel]
      exact F.zero_mem
    exact hF.mem_of_add_mem h.1 h.2 h0

/-- Off a component, the product of two diagonal entries vanishes. -/
lemma diag_mul_diag_eq_zero {D : Type} [CommRing D] {N : AddSubmonoid M} {P : Matrix ι ι D}
    (hP : IsRankOneProj P) (hs : ∀ i j, w i - w j ∉ N → P i j = 0) {i j : ι} (h : ¬ CompRel w N i j) :
    P i i * P j j = 0 := by
  rw [show P i i * P j j = P i j * P j i from hP.minor i i j j]
  by_cases h1 : w i - w j ∈ N
  · rw [hs j i fun h2 => h ⟨h1, h2⟩, mul_zero]
  · rw [hs i j h1, zero_mul]

open Classical in
/-- **§5: components.** Over a connected ring, a point of `X^N` lives in one component: the diagonal of a
projector supported on `N` vanishes off one class of `CompRel`. For the magnets with `N ∩ -N ∩ Φ = ∅` this says
that `X^N` has one component for each fixed point, as in "the attractor has three components". -/
theorem exists_component [Nonempty ι] {D : Type} [CommRing D] (hD : ∀ e : D, e * e = e → e = 0 ∨ e = 1)
    {N : AddSubmonoid M} {P : Matrix ι ι D} (hP : IsRankOneProj P)
    (hs : ∀ i j, w i - w j ∉ N → P i j = 0) :
    ∃ s, (∑ i with CompRel w N i s, P i i) = 1 ∧ ∀ k, ¬ CompRel w N k s → P k k = 0 := by
  classical
  have htr : ∑ i, P i i = 1 := hP.trace_eq
  have hzero : ∀ s, (∑ i with ¬ CompRel w N i s, P i i) * (∑ i with CompRel w N i s, P i i) = 0 := by
    intro s
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    exact diag_mul_diag_eq_zero w hP hs fun h => hi' (h.trans hj')
  have hsum : ∀ s, (∑ i with CompRel w N i s, P i i) + (∑ i with ¬ CompRel w N i s, P i i) = 1 := by
    intro s
    rw [Finset.sum_filter_add_sum_filter_not, htr]
  have hid : ∀ s, (∑ i with CompRel w N i s, P i i) * (∑ i with CompRel w N i s, P i i) =
      ∑ i with CompRel w N i s, P i i := by
    intro s
    have := hzero s
    have h2 := hsum s
    linear_combination (∑ i with CompRel w N i s, P i i) * h2 - this
  by_cases hall : ∃ s, (∑ i with CompRel w N i s, P i i) = 1
  · obtain ⟨s, hs1⟩ := hall
    refine ⟨s, hs1, fun k hk => ?_⟩
    have : P k k * (∑ i with CompRel w N i s, P i i) = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := (Finset.mem_filter.mp hj).2
      exact diag_mul_diag_eq_zero w hP hs fun h => hk (h.trans hj')
    rwa [hs1, mul_one] at this
  · exfalso
    push Not at hall
    have hz : ∀ s, P s s = 0 := by
      intro s
      have h0 : (∑ i with CompRel w N i s, P i i) = 0 :=
        (hD _ (hid s)).resolve_right (hall s)
      have : P s s * (∑ i with CompRel w N i s, P i i) = P s s := by
        have h2 := hsum s
        have hm : P s s * (∑ i with ¬ CompRel w N i s, P i i) = 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_eq_zero fun j hj => ?_
          have hj' := (Finset.mem_filter.mp hj).2
          exact diag_mul_diag_eq_zero w hP hs fun h => hj' h.symm
        linear_combination (P s s) * h2 - hm
      rw [h0, mul_zero] at this
      exact this.symm
    have h1 : (1 : D) = 0 := by
      rw [← htr]
      exact Finset.sum_eq_zero fun s _ => hz s
    obtain ⟨s⟩ := ‹Nonempty ι›
    apply hall s
    have : ∀ x : D, x = 0 := fun x => by rw [← mul_one x, h1, mul_zero]
    rw [this (∑ i with CompRel w N i s, P i i), this 1]

/-! ### The face morphism on points -/

/-- **Fact 3.15 on points.** The limit: the face morphism sends the line of a projector supported on `N` to the
line of its part supported on `F`. -/
theorem toPoint_ofFace {D : CommAlgCat.{0} R} {N F : AddSubmonoid M} (hF : IsFace F N)
    {P : Matrix ι ι D} (hP : IsRankOneProj P) (hs : ∀ i j, w i - w j ∉ N → P i j = 0) :
    (AttractorPt.toPoint (AttractorPt.ofFace hF (liftPt w N hP hs))).1 =
      rng (Matrix.of fun i j => xv (R := R) (T' := op D) F (w i - w j) 1 * P i j) := by
  change rng _ = _
  refine congrArg rng (Matrix.ext fun i j => ?_)
  rw [Matrix.of_apply, Matrix.of_apply, mul_comm]
  congr 1
  unfold xv
  by_cases h : w i - w j ∈ N
  · by_cases h' : w i - w j ∈ F
    · rw [dite_eq_left h, dite_eq_left h']
      change (APt.faceExt hF 1) _ = (1 : APt (affO R) F (op (op D))) _
      exact APt.faceExt_pos hF (n := Multiplicative.ofAdd (⟨w i - w j, h⟩ : N)) _ h'
    · rw [dite_eq_left h, dite_eq_right h']
      change (APt.faceExt hF 1) _ = 0
      exact APt.faceExt_neg hF _ h'
  · have : w i - w j ∉ F := fun h' => h (hF.le h')
    rw [dite_eq_right h, dite_eq_right this]

end AlgMag.DoubleScalar
