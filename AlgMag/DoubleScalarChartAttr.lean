/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.DoubleScalarPure
import AlgMag.Sec3Remaining

/-!
# Projective space with a diagonal action: attractors of the charts

Mayeux, *Algebraic magnetism invariants of a double scalar action on the projective plane*,
arXiv:2509.04274v3, §§3, 4.

The chart `{v_s = 1}` of `ℙ(ι)` as a functor with a linear action of weights `w j - w s` (§3), and its attractors
by Lemma 4.2. Then the step of the proof of Proposition 4.1 which is not justified as printed.

## Main results

* `AlgMag.DoubleScalar.chartV`, `AlgMag.DoubleScalar.chartAct`, `AlgMag.DoubleScalar.toLine`: the chart, its action,
  and its equivariant monomorphism to `ℙ(ι)`.
* `AlgMag.DoubleScalar.lem42`: Lemma 4.2, from `AlgMag.ex12`.
* `AlgMag.DoubleScalar.chart_attr_iff`: Lemma 4.2 on the chart.
* `AlgMag.DoubleScalar.image_eq_iff_chart_attr`: `X^N = X^L` iff the attractors agree on all charts.
* `AlgMag.DoubleScalar.gm_image_ne`, `AlgMag.DoubleScalar.a1_image_eq`: for a stable open `U ⊂ X`, `X^N = X^L` does
  not imply `U^N = U^L` in general.
-/

open CategoryTheory Opposite Matrix

set_option linter.unusedSectionVars false

namespace AlgMag.DoubleScalar

/-- **Lemma 4.2.** Let `D(M)` act linearly on `V = 𝔸^ι`, the coordinates having weights `m`. Then `V^N` is the sum
of the `V_n`, `n ∈ N`: the map `v ↦ (v_i)` identifies `V^N(C)` with the vectors supported on the coordinates of
weight in `N`. The printed proof cites Example 1.2 of *Algebraic Magnetism*, which is `AlgMag.ex12`; see
`AlgMag.VB.ex12_general` over an arbitrary scheme. -/
noncomputable def lem42 {R : Type} [CommRing R] {M κ : Type} [AddCommMonoid M] [DecidableEq M]
    (m : κ → M) (N : AddSubmonoid M) (C : Type) [CommRing C] [Algebra R C] :
    AttractorPt (linAction R (wtGr R m)) N (op (CommAlgCat.of R C)) ≃
      {v : κ → C // ∀ i, m i ∉ N → v i = 0} :=
  ex12 R N C m

variable {ι : Type} [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R]
variable {M : Type} [AddCommGroup M] (w : ι → M)

/-- **§3.** The chart `v_s = 1` of `ℙ(ι)`, isomorphic to `𝔸^{ι ∖ s}`. -/
def chartV (s : ι) : (Aff R)ᵒᵖ ⥤ Type where
  obj U := {v : ι → (unop (unop U) : CommAlgCat.{0} R) // v s = 1}
  map {U V} g := ↾ fun v => ⟨fun i => (g.unop.unop.hom : _ →ₐ[R] _) (v.1 i), by
    change (g.unop.unop.hom : _ →ₐ[R] _) (v.1 s) = 1
    rw [v.2]; exact map_one _⟩
  map_id U := by
    ext v i
    rfl
  map_comp {U V W} f g := by
    ext v i
    rfl

variable {R}

/-- **§3.** The linear action on the chart `s`: the coordinate `j` has weight `w j - w s`. -/
noncomputable def chartAct (s : ι) : AAction (affO R) M (chartV R s) where
  smul {U} h v := ⟨fun i => (show Multiplicative M →* (unop (unop U) : CommAlgCat.{0} R) from h)
      (Multiplicative.ofAdd (w i - w s)) * v.1 i, by
    change (show Multiplicative M →* (unop (unop U) : CommAlgCat.{0} R) from h)
      (Multiplicative.ofAdd (w s - w s)) * v.1 s = 1
    rw [v.2, sub_self, ofAdd_zero, map_one, mul_one]⟩
  one_smul {U} v := Subtype.ext (funext fun i => one_mul _)
  mul_smul {U} g h v := Subtype.ext (funext fun i => mul_assoc _ _ _)
  map_smul {U V} f h v := Subtype.ext (funext fun i => map_mul (f.unop.unop.hom : _ →ₐ[R] _) _ _)

/-- The line of a point of the chart. -/
noncomputable def toLine {s : ι} {U : (Aff R)ᵒᵖ} (v : (chartV R s).obj U) : (pn ι R).obj U :=
  ⟨Submodule.span _ {v.1}, chartProj s v.1, isRankOneProj_chartProj s v.2,
    (rng_chartProj s v.2).symm⟩

/-- The map from the chart to `ℙ(ι)` is a monomorphism: this is its image `{v_s = 1}`. -/
theorem toLine_injective {s : ι} {U : (Aff R)ᵒᵖ} {v v' : (chartV R s).obj U}
    (h : toLine v = toLine v') : v = v' := by
  refine Subtype.ext ?_
  have h' : Submodule.span _ {v.1} = Submodule.span _ {v'.1} := congrArg Subtype.val h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h' ▸ Submodule.mem_span_singleton_self v.1)
  have h1 : c = 1 := by
    have := congrFun hc s
    rw [Pi.smul_apply, v.2, v'.2, smul_eq_mul, mul_one] at this
    exact this
  rw [← hc, h1, one_smul]

/-- **§3, the printed formulas for the weights.** For instance
`(λ, β) · [x : 1 : z] = [λx : β : z] = [λβ⁻¹x : 1 : β⁻¹z]`: the map from the chart to `ℙ(ι)` is equivariant. -/
theorem toLine_smul {s : ι} {U : (Aff R)ᵒᵖ} (h : APt (affO R) M U) (v : (chartV R s).obj U) :
    (pnAction R w).smul h (toLine v) = toLine ((chartAct w s).smul h v) := by
  refine Subtype.ext ?_
  let D : CommAlgCat.{0} R := unop (unop U)
  let h' : Multiplicative M →* D := h
  change Submodule.map (dgl fun i => h' (Multiplicative.ofAdd (w i))) (Submodule.span D {v.1}) =
    Submodule.span D {fun i => h' (Multiplicative.ofAdd (w i - w s)) * v.1 i}
  rw [Submodule.map_span, Set.image_singleton]
  have e : ∀ i, h' (Multiplicative.ofAdd (w i - w s)) * h' (Multiplicative.ofAdd (w s)) =
      h' (Multiplicative.ofAdd (w i)) := fun i => by
    rw [← map_mul, ← ofAdd_add, sub_add_cancel]
  have e2 : (dgl fun i => h' (Multiplicative.ofAdd (w i))) v.1 =
      h' (Multiplicative.ofAdd (w s)) • fun i => h' (Multiplicative.ofAdd (w i - w s)) * v.1 i := by
    funext i
    change h' (Multiplicative.ofAdd (w i)) * v.1 i =
      h' (Multiplicative.ofAdd (w s)) * (h' (Multiplicative.ofAdd (w i - w s)) * v.1 i)
    rw [← e i]
    ring
  rw [e2]
  have hu := apt_inv h' (w s)
  apply le_antisymm
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr
      (Submodule.mem_span_singleton.mpr ⟨h' (Multiplicative.ofAdd (-w s)), ?_⟩)
    rw [smul_smul, mul_comm, hu, one_smul]

/-- A vector of the chart supported on `N` gives a point of the attractor of the chart. -/
noncomputable def chartLift {s : ι} {D : CommAlgCat.{0} R} (N : AddSubmonoid M) (v : ι → D) (hv : v s = 1) :
    AttractorPt (chartAct w s) N (op D) where
  app {T'} t a := ⟨fun i => (t.unop.hom : D →ₐ[R] _) (v i) * xv N (w i - w s) a, by
    change (t.unop.hom : D →ₐ[R] _) (v s) * xv N (w s - w s) a = 1
    rw [hv, map_one, sub_self, xv_zero, mul_one]⟩
  naturality {T' T''} s' t a := by
    refine Subtype.ext (funext fun i => ?_)
    change _ * xv N (w i - w s) (APt.res s'.op a) = _
    rw [xv_res]
    exact (map_mul (s'.unop.hom : _ →ₐ[R] _) _ _).symm
  equivariant {T'} t g a := by
    refine Subtype.ext (funext fun i => ?_)
    change _ * xv N (w i - w s) (APt.toMagnet N g * a) = _
    rw [xv_mul]
    exact mul_left_comm _ _ _

/-- **Lemma 4.2 on the chart `s`.** The attractor `(𝔸^s)^N` is the set of the vectors of the chart supported on
the coordinates of weight in `N`. -/
theorem chart_attr_iff {s : ι} {D : CommAlgCat.{0} R} {N : AddSubmonoid M}
    (v : (chartV R s).obj (op (op D))) :
    v ∈ attractorImage (chartAct w s) N (op D) ↔ IsChartVec s (chartS w N s) v.1 := by
  classical
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨φ.toPoint.2, fun j hj hjS => ?_⟩
    have hN : w j - w s ∉ N := fun h => hjS ((mem_chartS w).mpr ⟨hj, h⟩)
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
    have e1 : φ.app tZ (APt.res tτ.op aN) = (chartV R s).map tτ.op (φ.app tN aN) := by
      rw [← htt]
      exact φ.naturality tτ tN aN
    have e2 : APt.res tτ.op aN = APt.toMagnet N hU * 1 := by
      refine MonoidHom.ext fun n => ?_
      refine Eq.trans ?_ (mul_one _).symm
      change τ₀ (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) =
        AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M) 1
      simp [τ₀]
    have e3 := φ.equivariant tZ hU 1
    have e4 : φ.app tZ 1 = (chartV R s).map tZ.op φ.toPoint := by
      have := φ.naturality tZ (𝟙 _) 1
      rw [Category.comp_id, show APt.res tZ.op (1 : APt (affO R) N (op (op D))) = 1 from by ext p; simp] at this
      exact this
    have e5 : (chartV R s).map tτ.op (φ.app tN aN) =
        (chartAct w s).smul hU ((chartV R s).map tZ.op φ.toPoint) := by
      rw [← e1, e2, e3, e4]
    have e6 := congrFun (congrArg Subtype.val e5) j
    have e7 : τ₀ ((φ.app tN aN).1 j) = AddMonoidAlgebra.single (w j - w s) (φ.toPoint.1 j) := by
      refine e6.trans ?_
      change AddMonoidAlgebra.single (w j - w s) (1 : DD) *
        AddMonoidAlgebra.single (0 : M) (φ.toPoint.1 j) = _
      rw [AddMonoidAlgebra.single_mul_single]
      simp
    have e8 := congrArg (fun x : EZ => x.coeff (w j - w s)) e7
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at e8
    rw [← e8]
    exact coeff_mapSub N _ hN
  · intro hv
    refine ⟨chartLift w N v.1 v.2, Subtype.ext (funext fun i => ?_)⟩
    change v.1 i * xv N (w i - w s) (1 : APt (affO R) N (op (op D))) = v.1 i
    by_cases hi : i = s
    · subst hi
      rw [sub_self, xv_zero, mul_one]
    · by_cases hN : w i - w s ∈ N
      · rw [xv_one N hN, mul_one]
      · rw [hv.zero i hi fun h => hN ((mem_chartS w).mp h).2, zero_mul]

/-- `(𝔸^s)^N ⊂ X^N`. -/
theorem toLine_mem_image {s : ι} {D : CommAlgCat.{0} R} {N : AddSubmonoid M}
    {v : (chartV R s).obj (op (op D))} (h : v ∈ attractorImage (chartAct w s) N (op D)) :
    toLine v ∈ attractorImage (pnAction R w) N (op D) := by
  have hv := (chart_attr_iff w v).mp h
  refine (mem_image_iff w _).mpr ⟨chartProj s v.1, isRankOneProj_chartProj s v.2,
    (rng_chartProj s v.2).symm, fun i j hij => ?_⟩
  change (if j = s then v.1 i else 0) = 0
  by_cases hj : j = s
  · subst hj
    rw [ite_eq_left rfl]
    by_cases hi : i = j
    · subst hi; simp at hij
    · exact hv.zero i hi fun h => hij ((mem_chartS w).mp h).2
  · rw [ite_eq_right hj]

/-- **The printed step of Proposition 4.1, with a proof.** `X^N = X^L` iff `(𝔸^s)^N = (𝔸^s)^L` for all `s`.

The direct implication is the sentence "*Since `X^N = X^L`, we have `(𝔸²)^N = (𝔸²)^L` for all `s`*" in the proof
of surjectivity. It is not formal: `AlgMag.DoubleScalar.gm_image_ne` and `AlgMag.DoubleScalar.a1_image_eq` show that
it fails for general stable opens. The proof here goes through `AlgMag.DoubleScalar.mem_of_tangent`: it tests on the
tangent vectors at the fixed point of the chart. -/
theorem image_eq_iff_chart_attr [Nontrivial R] {N L : AddSubmonoid M} :
    attractorImage (pnAction R w) N = attractorImage (pnAction R w) L ↔
      ∀ s, attractorImage (chartAct (R := R) w s) N = attractorImage (chartAct w s) L := by
  rw [image_eq_iff_charts]
  constructor
  · intro h s
    funext T
    ext v
    have a := chart_attr_iff (s := s) (D := unop T) (N := N) w v
    have b := chart_attr_iff (s := s) (D := unop T) (N := L) w v
    rw [h s] at a
    exact a.trans b.symm
  · intro h s
    have key : ∀ {N L : AddSubmonoid M},
        attractorImage (chartAct (R := R) w s) N = attractorImage (chartAct w s) L →
        chartS w N s ⊆ chartS w L s := by
      intro N L h j hj
      obtain ⟨hne, hjN⟩ := (mem_chartS w).mp hj
      let D : CommAlgCat.{0} R := CommAlgCat.of R (DualNumber R)
      let v : (chartV R s).obj (op (op D)) := ⟨tangentVec R s j, tangentVec_self s j⟩
      have hv : v ∈ attractorImage (chartAct w s) N (op D) := by
        refine (chart_attr_iff w v).mpr ⟨v.2, fun i hi hiS => ?_⟩
        have hij : i ≠ j := fun e => hiS (e ▸ hj)
        exact tangentVec_other hi hij
      rw [h] at hv
      have := (chart_attr_iff w v).mp hv
      by_contra hn
      have h0 := this.zero j hne hn
      have h1 : v.1 j = DualNumber.eps := tangentVec_of_ne hne
      rw [h1] at h0
      exact (one_ne_zero (α := R)) (by simpa using congrArg TrivSqZeroExt.snd h0)
    exact Finset.Subset.antisymm (key (h s)) (key (h s).symm)

/-! ### The printed step is not formal -/

section Counter

variable (R)

/-- The affine line. -/
def a1F : (Aff R)ᵒᵖ ⥤ Type where
  obj U := (unop (unop U) : CommAlgCat.{0} R)
  map {U V} g := ↾ fun v => (g.unop.unop.hom : _ →ₐ[R] _) v

/-- `𝔾_m = 𝔸¹ ∖ 0`, stable open in `𝔸¹`. -/
def gmF : (Aff R)ᵒᵖ ⥤ Type where
  obj U := (unop (unop U) : CommAlgCat.{0} R)ˣ
  map {U V} g := ↾ fun v => Units.map ((g.unop.unop.hom : _ →ₐ[R] _) : _ →* _) v

/-- The action of `D(ℤ)` on `𝔸¹` of weight one. -/
noncomputable def a1Act : AAction (affO R) ℤ (a1F R) where
  smul {U} h v := (show Multiplicative ℤ →* (unop (unop U) : CommAlgCat.{0} R) from h)
    (Multiplicative.ofAdd 1) * (show (unop (unop U) : CommAlgCat.{0} R) from v)
  one_smul {U} v := one_mul (M := (unop (unop U) : CommAlgCat.{0} R)) _
  mul_smul {U} g h v := mul_assoc (G := (unop (unop U) : CommAlgCat.{0} R)) _ _ _
  map_smul {U V} f h v := map_mul (f.unop.unop.hom : _ →ₐ[R] _) _ _

lemma gm_unit {D : Type} [CommRing D] (h : Multiplicative ℤ →* D) :
    h (Multiplicative.ofAdd 1) * h (Multiplicative.ofAdd (-1)) = 1 := apt_inv h 1

/-- The action of `D(ℤ)` on `𝔾_m` induced by `a1Act`. -/
noncomputable def gmAct : AAction (affO R) ℤ (gmF R) where
  smul {U} h v := ⟨(show Multiplicative ℤ →* (unop (unop U) : CommAlgCat.{0} R) from h)
      (Multiplicative.ofAdd 1) * v.1,
    (show Multiplicative ℤ →* (unop (unop U) : CommAlgCat.{0} R) from h)
      (Multiplicative.ofAdd (-1)) * v.2, by
      have e := gm_unit (show Multiplicative ℤ →* (unop (unop U) : CommAlgCat.{0} R) from h)
      calc _ = (show Multiplicative ℤ →* (unop (unop U) : CommAlgCat.{0} R) from h)
            (Multiplicative.ofAdd 1) * (show Multiplicative ℤ →* (unop (unop U) : CommAlgCat.{0} R) from h)
            (Multiplicative.ofAdd (-1)) * (v.1 * v.2) := by ring
        _ = 1 := by rw [e, v.3, one_mul], by
      have e := gm_unit (show Multiplicative ℤ →* (unop (unop U) : CommAlgCat.{0} R) from h)
      calc _ = (show Multiplicative ℤ →* (unop (unop U) : CommAlgCat.{0} R) from h)
            (Multiplicative.ofAdd 1) * (show Multiplicative ℤ →* (unop (unop U) : CommAlgCat.{0} R) from h)
            (Multiplicative.ofAdd (-1)) * (v.2 * v.1) := by ring
        _ = 1 := by rw [e, v.4, one_mul]⟩
  one_smul {U} v := Units.ext (one_mul _)
  mul_smul {U} g h v := Units.ext (mul_assoc _ _ _)
  map_smul {U V} f h v := Units.ext (map_mul (f.unop.unop.hom : _ →ₐ[R] _) _ _)

/-- For `X = 𝔸¹` of weight one, `X^ℕ = X^ℤ = X`. -/
theorem a1_image_eq : attractorImage (a1Act R) posN = attractorImage (a1Act R) ⊤ := by
  have key : ∀ (N : AddSubmonoid ℤ), (1 : ℤ) ∈ N → ∀ (T : Aff R) (x : (a1F R).obj (op T)),
      x ∈ attractorImage (a1Act R) N T := by
    intro N hN T x
    let D : CommAlgCat.{0} R := unop T
    refine ⟨{ app := fun {T'} t a => (t.unop.hom : D →ₐ[R] _) (show D from x) * xv N 1 a
              naturality := fun {T' T''} s t a => ?_
              equivariant := fun {T'} t h a => ?_ }, ?_⟩
    · change _ * xv N 1 (APt.res s.op a) = _
      rw [xv_res]
      exact (map_mul (s.unop.hom : _ →ₐ[R] _) _ _).symm
    · change _ * xv N 1 (APt.toMagnet N h * a) = _
      rw [xv_mul]
      exact mul_left_comm (G := (unop T' : CommAlgCat.{0} R)) _ _ _
    · change (show D from x) * xv N 1 (1 : APt (affO R) N (op (op D))) = _
      rw [xv_one N hN, mul_one]
  funext T
  ext x
  exact ⟨fun _ => key _ (AddSubmonoid.mem_top _) T x, fun _ => key _ (by simp [mem_posN]) T x⟩

/-- For the stable open `U = 𝔾_m ⊂ 𝔸¹`, `U^ℕ ≠ U^ℤ`: over a nonzero ring, `U^ℤ = U` has a point and `U^ℕ` has none.
With `a1_image_eq`, this shows that `X^N = X^L` does not imply `U^N = U^L` for a stable open `U ⊂ X`. -/
theorem gm_image_ne [Nontrivial R] : attractorImage (gmAct R) posN ≠ attractorImage (gmAct R) ⊤ := by
  classical
  intro e
  let D : CommAlgCat.{0} R := CommAlgCat.of R R
  let e1 : (gmF R).obj (op (op D)) := (1 : (D : Type)ˣ)
  have h1 : e1 ∈ attractorImage (gmAct R) ⊤ (op D) :=
    ⟨(attractorTopEquiv (gmAct R) (op D)).symm e1, (attractorTopEquiv (gmAct R) (op D)).apply_symm_apply e1⟩
  rw [← e] at h1
  obtain ⟨φ, -⟩ := h1
  let B := AddMonoidAlgebra R ℤ
  let t : op (CommAlgCat.of R B) ⟶ op D := affHom (constAlg ℤ R)
  let hB : Multiplicative ℤ →* B := AddMonoidAlgebra.of R ℤ
  let hu : APt (affO R) ℤ (op (op (CommAlgCat.of R B))) := hB
  let a0 : APt (affO R) posN (op (op (CommAlgCat.of R B))) := zeroPt B
  have h0 : APt.toMagnet posN hu * a0 = a0 := by
    refine MonoidHom.ext fun n => ?_
    have : ∀ n : posN, hB (Multiplicative.ofAdd (n : ℤ)) * zeroPt B (Multiplicative.ofAdd n) =
        zeroPt B (Multiplicative.ofAdd n) := by
      intro n
      rw [zeroPt_of]
      by_cases hn : n = 0
      · subst hn
        simp
      · simp [hn]
    exact this _
  have h2 := φ.equivariant t hu a0
  rw [h0] at h2
  let y : Bˣ := φ.app t a0
  have h3 : y.1 = hB (Multiplicative.ofAdd 1) * y.1 := congrArg Units.val h2
  have h4 : hB (Multiplicative.ofAdd 1) = 1 := by
    have := congrArg (· * y.2) h3
    simp only [mul_assoc, y.3, mul_one] at this
    exact this.symm
  have h5 := congrArg (fun x : B => x.coeff (0 : ℤ)) h4
  change (AddMonoidAlgebra.single (1 : ℤ) (1 : R) : B).coeff 0 = (1 : B).coeff 0 at h5
  rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by norm_num)] at h5
  exact zero_ne_one h5

end Counter

end AlgMag.DoubleScalar
