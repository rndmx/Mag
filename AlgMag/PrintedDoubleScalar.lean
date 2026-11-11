/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.DoubleScalar

/-!
# Double scalar action: printed routes

A. Mayeux, arXiv:2509.04274v3.

* `chart_attr_iff_lem42`: the attractor of a chart, from **Lemma 4.2** (`lem42`), through the equivariant
  identification of the chart `{v_s = 1}` with the linear representation `𝔸^{ι ∖ s}`.
* `prop41_injOn_printed`: **Proposition 4.1, injectivity**, as printed: Lemma 4.2 on each chart, then purity.
* `three_le_card_filter_printed`, `prop65_printed`: **Proposition 6.5**, by the printed opposite pairs.

The surjectivity of Proposition 4.1 keeps the tangent vector test: its printed step
"`(𝔸²)^N = (𝔸²)^L`" is unjustified (see `AlgMag.DoubleScalar`).
-/

open CategoryTheory Opposite

set_option linter.unusedSectionVars false

namespace AlgMag.DoubleScalar

section Chart

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]
variable {M : Type} [AddCommGroup M] [DecidableEq M] (w : ι → M)

/-- The weights of the linear coordinates of the chart `s`. -/
def chartW (s : ι) (j : {j : ι // j ≠ s}) : M := w j.1 - w s

/-- The chart `{v_s = 1}` in the linear representation `𝔸^{ι ∖ s}`. -/
noncomputable def chartToLin (s : ι) :
    EquivariantHom (chartAct (R := R) w s) (linAction R (wtGr R (chartW w s))) where
  hom :=
    { app := fun U => ↾ fun v =>
        Finsupp.linearCombination R (fun j : {j : ι // j ≠ s} => v.1 j.1)
      naturality := fun U V f => by
        ext v
        refine Finsupp.lhom_ext' fun j => LinearMap.ext_ring ?_
        change Finsupp.linearCombination R (fun j : {j : ι // j ≠ s} => (f.unop.unop.hom : _ →ₐ[R] _) (v.1 j.1))
            (Finsupp.single j 1) =
          (f.unop.unop.hom : _ →ₐ[R] _) (Finsupp.linearCombination R (fun j : {j : ι // j ≠ s} => v.1 j.1)
            (Finsupp.single j 1))
        simp [Finsupp.linearCombination_single] }
  map_smul := by
    intro U h v
    refine Finsupp.lhom_ext' fun j => LinearMap.ext_ring ?_
    let D : CommAlgCat.{0} R := unop (unop U)
    refine Eq.trans ?_ (linSmul_of_mem (D := D) R (wtGr R (chartW w s)) _ _
      (single_mem_wtGr R (chartW w s) j 1)).symm
    change Finsupp.linearCombination R (fun j : {j : ι // j ≠ s} => ((chartAct (R := R) w s).smul h v).1 j.1)
        (Finsupp.single j 1) = (show Multiplicative M →* D from h) (Multiplicative.ofAdd (chartW w s j)) *
        Finsupp.linearCombination R (fun j : {j : ι // j ≠ s} => v.1 j.1) (Finsupp.single j 1)
    simp only [Finsupp.linearCombination_single, one_smul]
    rfl

/-- The linear representation `𝔸^{ι ∖ s}` as the chart `{v_s = 1}`. -/
noncomputable def linToChart (s : ι) :
    EquivariantHom (linAction R (wtGr R (chartW w s))) (chartAct (R := R) w s) where
  hom :=
    { app := fun U => ↾ fun x =>
        ⟨fun i => if h : i = s then 1 else
          (show _ →ₗ[R] (unop (unop U) : CommAlgCat.{0} R) from x) (Finsupp.single ⟨i, h⟩ 1), by simp⟩
      naturality := fun U V f => by
        ext x
        refine Subtype.ext (funext fun i => ?_)
        by_cases h : i = s
        · subst h
          change (dite _ _ _ : (unop (unop V) : CommAlgCat.{0} R)) = (f.unop.unop.hom : _ →ₐ[R] _) (dite _ _ _)
          simp
        · change (dite _ _ _ : (unop (unop V) : CommAlgCat.{0} R)) = (f.unop.unop.hom : _ →ₐ[R] _) (dite _ _ _)
          simp only [h, dite_false]
          rfl }
  map_smul := by
    intro U g x
    refine Subtype.ext (funext fun i => ?_)
    let D : CommAlgCat.{0} R := unop (unop U)
    by_cases h : i = s
    · subst h
      change (dite _ _ _ : D) = _ * dite _ _ _
      simp
      exact (map_one (show Multiplicative M →* D from g)).symm
    · change (dite _ _ _ : D) = _ * dite _ _ _
      simp only [h, dite_false]
      exact linSmul_of_mem (D := D) R (wtGr R (chartW w s)) _ _
        (single_mem_wtGr R (chartW w s) ⟨i, h⟩ 1)

/-- The chart, then the linear representation, then the chart. -/
lemma linToChart_chartToLin (s : ι) {U : (Aff R)ᵒᵖ} (v : (chartV R s).obj U) :
    (linToChart (R := R) w s).hom.app U ((chartToLin (R := R) w s).hom.app U v) = v := by
  refine Subtype.ext (funext fun i => ?_)
  by_cases h : i = s
  · subst h
    change (dite _ _ _ : (unop (unop U) : CommAlgCat.{0} R)) = _
    simp [v.2]
  · change (dite _ _ _ : (unop (unop U) : CommAlgCat.{0} R)) = _
    simp only [h, dite_false]
    change Finsupp.linearCombination R (fun j : {j : ι // j ≠ s} => v.1 j.1) (Finsupp.single ⟨i, h⟩ 1) = _
    simp [Finsupp.linearCombination_single]

/-- **Lemma 4.2 on the chart `s`**, deduced from Lemma 4.2 for `𝔸^{ι ∖ s}` as printed. -/
theorem chart_attr_iff_lem42 {s : ι} {D : CommAlgCat.{0} R} {N : AddSubmonoid M}
    (v : (chartV R s).obj (op (op D))) :
    v ∈ attractorImage (chartAct w s) N (op D) ↔ IsChartVec s (chartS w N s) v.1 := by
  have hval : ∀ (j : {j : ι // j ≠ s}),
      (show _ →ₗ[R] D from (chartToLin (R := R) w s).hom.app (op (op D)) v) (Finsupp.single j 1) = v.1 j.1 := by
    intro j
    change Finsupp.linearCombination R (fun j : {j : ι // j ≠ s} => v.1 j.1) (Finsupp.single j 1) = _
    simp [Finsupp.linearCombination_single]
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨φ.toPoint.2, fun j hj hjS => ?_⟩
    have hN : chartW w s ⟨j, hj⟩ ∉ N := fun h => hjS ((mem_chartS w).mpr ⟨hj, h⟩)
    have := (lem42 (R := R) (chartW w s) N D (AttractorPt.push (chartToLin (R := R) w s) φ)).2 ⟨j, hj⟩ hN
    exact (hval ⟨j, hj⟩).symm.trans this
  · intro hv
    let u : {j : ι // j ≠ s} → D := fun j => v.1 j.1
    have hu : ∀ j, chartW w s j ∉ N → u j = 0 := fun j hj =>
      hv.zero j.1 j.2 fun h => hj ((mem_chartS w).mp h).2
    let ψ := (lem42 (R := R) (chartW w s) N D).symm ⟨u, hu⟩
    have hψ : ∀ j, (show _ →ₗ[R] D from ψ.toPoint) (Finsupp.single j 1) = u j := fun j =>
      congrFun (congrArg Subtype.val ((lem42 (R := R) (chartW w s) N D).apply_symm_apply ⟨u, hu⟩)) j
    refine ⟨AttractorPt.push (linToChart (R := R) w s) ψ, ?_⟩
    have hx : ψ.toPoint = (chartToLin (R := R) w s).hom.app (op (op D)) v :=
      Finsupp.lhom_ext' fun j => LinearMap.ext_ring ((hψ j).trans (hval j).symm)
    change (linToChart (R := R) w s).hom.app _ ψ.toPoint = v
    rw [hx]
    exact linToChart_chartToLin w s v

/-- The step of the printed proof: `N ∩ Φ = L ∩ Φ` gives, by Lemma 4.2, the equality of the attractors on
each chart. -/
theorem chart_eq_of_inter {N L : AddSubmonoid M} (h : (N : Set M) ∩ Om w = (L : Set M) ∩ Om w) (s : ι) :
    attractorImage (chartAct (R := R) w s) N = attractorImage (chartAct w s) L := by
  have e : chartS w N s = chartS w L s := by
    ext j
    simp only [mem_chartS]
    refine and_congr_right fun hj => ?_
    have m : w j - w s ∈ Om w := ⟨j, s, hj, rfl⟩
    have a : w j - w s ∈ (N : Set M) ∩ Om w ↔ w j - w s ∈ (L : Set M) ∩ Om w := by rw [h]
    exact ⟨fun h => (a.mp ⟨h, m⟩).1, fun h => (a.mpr ⟨h, m⟩).1⟩
  funext T
  ext v
  rw [chart_attr_iff_lem42 (D := unop T) w v, chart_attr_iff_lem42 (D := unop T) w v, e]

/-- **Proposition 4.1, injectivity**, as printed: "Lemma 4.2 implies that `(𝔸²_s)^N = (𝔸²_s)^{N'}` for all `s`.
In other words, on each chart, the attractors are equal. This implies that `N = N'` since `N` and `N'` are
pure." -/
theorem pnInjOn_printed [Nontrivial R] :
    Set.InjOn (fun N : AddSubmonoid M => (N : Set M) ∩ Om w) (pureMagnets (attractorImage (pnAction R w))) := by
  intro N hN L hL e
  have hX : attractorImage (pnAction R w) N = attractorImage (pnAction R w) L :=
    (image_eq_iff_chart_attr w).mpr (chart_eq_of_inter w e)
  exact le_antisymm (hN L hX) (hL N hX.symm)

end Chart

/-- **Proposition 4.1, injectivity** for the double scalar action, printed proof. -/
theorem prop41_injOn_printed {R : Type} [CommRing R] [Nontrivial R] :
    Set.InjOn (fun N : AddSubmonoid (ℤ × ℤ) => (N : Set (ℤ × ℤ)) ∩ (Phi : Set (ℤ × ℤ)))
      (pureMagnets (attractorImage (dsAct R))) := by
  have := pnInjOn_printed (R := R) wP
  simp only [om_eq] at this
  exact this

/-- Among any four elements of `Φ`, two are opposite (proof of Proposition 6.5). -/
theorem exists_opposite : ∀ F ∈ Phi.powerset, 4 ≤ F.card → ∃ a ∈ F, -a ∈ F := by
  decide

/-- The case `#E ≤ 2` of **Proposition 6.5**, as printed: otherwise there are at least four elements of `Φ`
with `f < 0`, two of them opposite, which is absurd. -/
theorem three_le_card_filter_printed (p q : ℤ) :
    3 ≤ (Phi.filter (fun v => 0 ≤ p * v.1 + q * v.2)).card := by
  by_contra hlt
  have hc := Finset.card_filter_add_card_filter_not (s := Phi) (fun v : ℤ × ℤ => 0 ≤ p * v.1 + q * v.2)
  have h6 : Phi.card = 6 := by decide
  obtain ⟨a, ha, hb⟩ := exists_opposite (Phi.filter (fun v : ℤ × ℤ => ¬ 0 ≤ p * v.1 + q * v.2))
    (Finset.mem_powerset.mpr (Finset.filter_subset _ _)) (by omega)
  have h1 := (Finset.mem_filter.mp ha).2
  have h2 := (Finset.mem_filter.mp hb).2
  simp only [Prod.fst_neg, Prod.snd_neg] at h2
  have e : p * -a.1 + q * -a.2 = -(p * a.1 + q * a.2) := by ring
  rw [e] at h2
  omega

/-- **Proposition 6.5**, printed proof. -/
theorem prop65_printed {R : Type} [CommRing R] [Nontrivial R] {E : Finset (ℤ × ℤ)} (hE : E ⊆ Phi)
    (hst : Closed E) :
    IsLambdafiable (attractorImage (dsAct R)) (AddSubmonoid.closure (E : Set (ℤ × ℤ))) ↔ 3 ≤ E.card := by
  refine ⟨?_, (prop65 hE hst).mpr⟩
  rintro ⟨f, hf⟩
  have hS := addStable_of_closed hE hst
  rw [image_eq_iff wP, om_eq, hS] at hf
  have hg : f = linForm (f (1, 0)) (f (0, 1)) := AddMonoidHom.ext fun v => addHom_prod f v
  rw [hg, comap_inter] at hf
  have := three_le_card_filter_printed (f (1, 0)) (f (0, 1))
  rwa [Finset.coe_injective hf] at this

end AlgMag.DoubleScalar

#print axioms AlgMag.DoubleScalar.prop41_injOn_printed
#print axioms AlgMag.DoubleScalar.prop65_printed
