/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSMain
import AlgMag.ChartDeligne
import AlgMag.ChartEffectiveBridge

/-!
# Theorem 4.1, uniqueness, for equivariant points of any algebraic space

Uniqueness in the chart-lemma proof without separatedness. The analogue of `ChartMain.thm41_unique` for any two points is
false for `X` not separated. Two *equivariant* points agreeing on all `V(mⁿ)` are equal. The agreement
locus `A` is open, contains `V(m)`, and is stable. The ideal `K` of the complement has `K + m = 1`; taking
a power and the component of degree `0` gives an element of `K` of the form `1 - s`, `s ∈ m₀`, invertible
by completeness.

The topological stability is not enough for the component step when `D(M)` is not reduced: an element of
`K` has coaction nilpotent modulo `K`, whence the power.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQS

open ChartMain

set_option linter.unusedSectionVars false

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `f` flat after composing with an open immersion is flat. -/
lemma flat_of_comp_open {A A' A'' : Scheme.{u}} (f : A ⟶ A') (j : A' ⟶ A'') [IsOpenImmersion j]
    (h : Flat (f ≫ j)) : Flat f := by
  rw [Flat.iff_flat_stalkMap] at h ⊢
  intro x
  have h1 := h x
  rw [Scheme.Hom.stalkMap_comp] at h1
  have e : f.stalkMap x = inv (j.stalkMap (f x)) ≫ (j.stalkMap (f x) ≫ f.stalkMap x) := by simp
  rw [e, CommRingCat.hom_comp]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (inv (j.stalkMap (f x))))) h1

/-- `p`, `q` coincide on `D(f)`. -/
def AgreeOn {T : BigFppfOver B S hS} (p q : X.obj (op T)) (f : Γ((SCH).obj T, ⊤)) : Prop :=
  X.map (Chart.immι T ((SCH).obj T |>.basicOpen f).ι).op p =
    X.map (Chart.immι T ((SCH).obj T |>.basicOpen f).ι).op q

/-- Agreement after a family of flat open maps gives agreement on any `D(f)` in their images. -/
theorem agreeOn_of_family (hX : IsAlgebraicSpace B S hS X) {T : BigFppfOver B S hS} {ι : Type u}
    (P : ι → BigFppfOver B S hS) (e : ∀ a, P a ⟶ T) (hf : ∀ a, Flat ((SCH).map (e a)))
    (ho : ∀ a, IsOpenMap ((SCH).map (e a)))
    (p q : X.obj (op T)) (h : ∀ a, X.map (e a).op p = X.map (e a).op q) (f : Γ((SCH).obj T, ⊤))
    (hr : ∀ y ∈ ((SCH).obj T).basicOpen f, ∃ a, y ∈ Set.range ((SCH).map (e a))) : AgreeOn p q f := by
  let D := ((SCH).obj T).basicOpen f
  let E : ∀ a, ((SCH).obj (P a)).Opens := fun a => (SCH).map (e a) ⁻¹ᵁ D
  let i : ∀ a, Chart.immObj (P a) (E a).ι ⟶ P a := fun a => Chart.immι (P a) (E a).ι
  let jD := Chart.immι T D.ι
  haveI hjo : IsOpenImmersion ((SCH).map jD) := inferInstanceAs (IsOpenImmersion D.ι)
  have hrj : Set.range ((SCH).map jD) = D := Scheme.Opens.range_ι _
  haveI hiop : ∀ a, IsOpenImmersion ((SCH).map (i a)) := fun a => inferInstanceAs (IsOpenImmersion (E a).ι)
  have hie : ∀ a z, (SCH).map (i a ≫ e a) z ∈ D := fun a z => by
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact (show ((SCH).map (i a) z : (SCH).obj (P a)) ∈ E a from (z : E a).2)
  have hex : ∀ a, ∃ c, c ≫ jD = i a ≫ e a := fun a => exists_factor_open jD (i a ≫ e a) (by
    rw [hrj]
    rintro _ ⟨z, rfl⟩
    exact hie a z)
  choose c hc using hex
  have hmc : ∀ a, (SCH).map (c a) ≫ (SCH).map jD = (SCH).map (i a) ≫ (SCH).map (e a) := fun a => by
    rw [← Functor.map_comp, hc, Functor.map_comp]
  refine eq_of_family hX (fun a => Chart.immObj (P a) (E a).ι) c (fun a => ?_)
    (fun a => ?_) (fun y => ?_) _ _ (fun a => ?_)
  · refine flat_of_comp_open _ ((SCH).map jD) ?_
    rw [hmc]
    have := hf a
    infer_instance
  · intro U hU
    have hop : IsOpenMap ((SCH).map (i a) ≫ (SCH).map (e a)) := by
      have h1 : IsOpenMap ((SCH).map (i a)) := ((SCH).map (i a)).isOpenEmbedding.isOpenMap
      rw [Scheme.Hom.comp_base]
      simpa using (ho a).comp h1
    have h2 := hop U hU
    rw [← hmc] at h2
    have hemb := ((SCH).map jD).isOpenEmbedding
    have : (SCH).map (c a) '' U = ((SCH).map jD) ⁻¹' (((SCH).map (c a) ≫ (SCH).map jD) '' U) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, by simp⟩
      · rintro ⟨z, hz, hy⟩
        refine ⟨z, hz, hemb.injective ?_⟩
        simpa using hy
    rw [this]
    exact h2.preimage ((SCH).map jD).continuous
  · have hy : (SCH).map jD y ∈ D := (Set.ext_iff.1 hrj _).1 ⟨y, rfl⟩
    obtain ⟨a, z, hz⟩ := hr _ hy
    have hzE : z ∈ E a := by
      change (SCH).map (e a) z ∈ D
      rw [hz]
      exact hy
    let w : (SCH).obj (Chart.immObj (P a) (E a).ι) := (⟨z, hzE⟩ : E a)
    refine ⟨a, w, ?_⟩
    apply ((SCH).map jD).isOpenEmbedding.injective
    have := congr($(hmc a) w)
    simp only [Scheme.Hom.comp_apply] at this
    exact this.trans hz
  · change X.map (c a).op (X.map jD.op p) = X.map (c a).op (X.map jD.op q)
    simp only [← Functor.map_comp_apply, ← op_comp, hc]
    simp only [op_comp, Functor.map_comp_apply, h]

/-- A family of `D(f')` on which `p, q` agree, covering `D(f)`. -/
theorem agreeOn_of_cover (hX : IsAlgebraicSpace B S hS X) {T : BigFppfOver B S hS}
    (p q : X.obj (op T)) (f : Γ((SCH).obj T, ⊤))
    (hr : ∀ y ∈ ((SCH).obj T).basicOpen f, ∃ f', AgreeOn p q f' ∧ y ∈ ((SCH).obj T).basicOpen f') :
    AgreeOn p q f := by
  refine agreeOn_of_family hX (ι := {f' : Γ((SCH).obj T, ⊤) // AgreeOn p q f'})
    (fun a => Chart.immObj T (((SCH).obj T).basicOpen a.1).ι)
    (fun a => Chart.immι T (((SCH).obj T).basicOpen a.1).ι)
    (fun a => inferInstanceAs (Flat (((SCH).obj T).basicOpen a.1).ι))
    (fun a => (((SCH).obj T).basicOpen a.1).ι.isOpenEmbedding.isOpenMap) p q (fun a => a.2) f
    fun y hy => ?_
  obtain ⟨f', hf', hyf⟩ := hr y hy
  exact ⟨⟨f', hf'⟩, ⟨⟨y, hyf⟩, rfl⟩⟩

/-- `r ∈ y` under a map of affine schemes. -/
lemma mem_asIdeal_map {A A' : Scheme.{u}} [IsAffine A] [IsAffine A'] (g : A ⟶ A') (z : A)
    (r : Γ(A', ⊤)) : r ∈ (A'.isoSpec.hom (g z)).asIdeal ↔ g.appTop.hom r ∈ (A.isoSpec.hom z).asIdeal := by
  have h1 := mem_basicOpen_iff (g z) r
  have h2 := mem_basicOpen_iff z (g.appTop.hom r)
  have e : A.basicOpen (g.appTop.hom r) = g ⁻¹ᵁ A'.basicOpen r := (Scheme.preimage_basicOpen g r).symm
  have h3 : z ∈ A.basicOpen (g.appTop.hom r) ↔ g z ∈ A'.basicOpen r := by rw [e]; rfl
  rw [← not_iff_not, ← h1, ← h2, h3]

/-- In a complete pair, `1 - s` is a unit for `s` of degree `0` in `m`. -/
lemma isUnit_one_sub {N C : Type*} [AddCommGroup N] [DecidableEq N] [CommRing C]
    (𝒞 : N → AddSubgroup C) [GradedRing 𝒞] {m : Ideal C} (hP : ChartGraded.IsCompletePair 𝒞 m)
    {s : C} (hs0 : s ∈ 𝒞 0) (hsm : s ∈ m) : IsUnit (1 - s) := by
  have hpow : ∀ n : ℕ, s ^ n ∈ 𝒞 0 := fun n => by
    have := SetLike.pow_mem_graded n hs0
    simpa using this
  let y : ℕ → C := fun n => ∑ i ∈ Finset.range n, s ^ i
  have hy : ∀ n, y n ∈ 𝒞 0 := fun n => sum_mem fun i _ => hpow i
  obtain ⟨c, hc0, hc⟩ := hP.exists_lim 0 y hy (fun n => by
    simp only [y, Finset.sum_range_succ, add_sub_cancel_left]
    exact Ideal.pow_mem_pow hsm n)
  have hone : (1 : C) ∈ 𝒞 0 := SetLike.GradedOne.one_mem
  have hmul : c * (1 - s) ∈ 𝒞 0 := by
    have := SetLike.GradedMul.mul_mem hc0 (sub_mem hone hs0)
    simpa using this
  have h0 : c * (1 - s) - 1 = 0 := hP.sep 0 _ (sub_mem hmul hone) fun n => by
    have e : c * (1 - s) - 1 = (c - y n) * (1 - s) - s ^ n := by
      have g : (1 - s) * y n = 1 - s ^ n := mul_neg_geom_sum s n
      linear_combination g
    rw [e]
    exact sub_mem (Ideal.mul_mem_right _ _ (hc n)) (Ideal.pow_mem_pow hsm n)
  exact IsUnit.of_mul_eq_one c (by rw [mul_comm]; linear_combination h0)

set_option maxHeartbeats 2000000 in
/-- The chart step of `eq_of_agree_pow`, without the Jacobson radical: points agreeing on all `V(a^k)`
agree étale locally at each point of `V(a)`. -/
theorem exists_etale_agree (hX : IsAlgebraicSpace B S hS X) (W : BigFppfOver B S hS)
    [IsAffine ((SCH).obj W)] [IsNoetherianRing Γ((SCH).obj W, ⊤)] (a : Ideal Γ((SCH).obj W, ⊤))
    (p q : X.obj (op W))
    (h : ∀ k : ℕ, X.map (Chart.immι W (Chart.closedι ((SCH).obj W) (a ^ k))).op p =
      X.map (Chart.immι W (Chart.closedι ((SCH).obj W) (a ^ k))).op q)
    (y : (SCH).obj W) (hy : ∀ r ∈ a, y ∉ ((SCH).obj W).basicOpen r) :
    ∃ (P : BigFppfOver B S hS) (e : P ⟶ W), Etale ((SCH).map e) ∧ y ∈ Set.range ((SCH).map e) ∧
        X.map e.op p = X.map e.op q := by
  let p' : yoneda.obj W ⟶ X := yonedaEquiv.symm p
  let q' : yoneda.obj W ⟶ X := yonedaEquiv.symm q
  have hVk : ∀ k : ℕ, yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) (a ^ k))) ≫ p' =
      yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) (a ^ k))) ≫ q' := by
    intro k
    apply yonedaEquiv.injective
    simpa [p', q', yonedaEquiv_apply] using h k
  obtain ⟨P, V, hPa, e, v, hv, s, t, hVa, heE, ⟨y₁, hy₁⟩, hs, ht, hst⟩ :=
    exists_chart_agree hX a p' q' hVk y hy
  let f := ((SCH).map e).appTop.hom
  have hft : f.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra Γ((SCH).obj W, ⊤) Γ((SCH).obj P, ⊤) := f.toAlgebra
  haveI : Algebra.FiniteType Γ((SCH).obj W, ⊤) Γ((SCH).obj P, ⊤) := hft
  haveI hNP : IsNoetherianRing Γ((SCH).obj P, ⊤) :=
    Algebra.FiniteType.isNoetherianRing Γ((SCH).obj W, ⊤) _
  let σ : Γ((SCH).obj V, ⊤) →+* Γ((SCH).obj P, ⊤) := ((SCH).map s).appTop.hom
  let τ : Γ((SCH).obj V, ⊤) →+* Γ((SCH).obj P, ⊤) := ((SCH).map t).appTop.hom
  let I : Ideal Γ((SCH).obj P, ⊤) := Ideal.span (Set.range fun b => σ b - τ b)
  let aP : Ideal Γ((SCH).obj P, ⊤) := a.map f
  have hIk : ∀ i ∈ I, ∀ k : ℕ, i ∈ aP ^ k := by
    intro i hi k
    refine (Ideal.span_le.2 ?_ : I ≤ _) hi
    rintro _ ⟨b, rfl⟩
    have hk : aP ^ k = (a ^ k).map f := (Ideal.map_pow _ _ _).symm
    rw [hk]
    refine Chart.closedι_appTop_eq_zero _ _ ?_
    have h' := congrArg (fun φ => ((SCH).map φ).appTop.hom b) (hst k)
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at h'
    change (Chart.closedι ((SCH).obj P) _).appTop.hom (σ b - τ b) = 0
    rw [map_sub, sub_eq_zero]
    exact h'
  obtain ⟨r, hr, hri⟩ := exists_one_sub_mul_eq_zero aP I hIk
  let D := ((SCH).obj P).basicOpen (1 - r)
  haveI hDa : IsAffine D.toScheme := (isAffineOpen_top _).basicOpen _
  let jD := Chart.immι P D.ι
  have hzz : ∀ b, D.ι.appTop.hom (σ b - τ b) = 0 := fun b =>
    ι_appTop_eq_zero_of_mul _ _ (hri _ (Ideal.subset_span ⟨b, rfl⟩))
  have hstD : jD ≫ s = jD ≫ t := by
    haveI : IsAffine ((SCH).obj V) := hVa
    refine ChartMain.siteExt (ChartMain.toAffine_ext (RingHom.ext fun b => ?_))
    have h0 := hzz b
    rw [map_sub, sub_eq_zero] at h0
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact h0
  have hyD : y₁ ∈ D := by
    refine (mem_basicOpen_iff y₁ _).2 fun hm => ?_
    have hrp : r ∈ (((SCH).obj P).isoSpec.hom y₁).asIdeal := by
      refine (Ideal.map_le_iff_le_comap.2 fun x hx => ?_ : aP ≤ _) hr
      by_contra hc
      have hb := (mem_basicOpen_iff y₁ (f x)).2 hc
      have e' : ((SCH).obj P).basicOpen (f x) = (SCH).map e ⁻¹ᵁ ((SCH).obj W).basicOpen x :=
        (Scheme.preimage_basicOpen _ x).symm
      rw [e'] at hb
      refine hy x hx ?_
      rw [← hy₁]
      exact hb
    have := Ideal.add_mem _ hm hrp
    rw [sub_add_cancel] at this
    exact (((SCH).obj P).isoSpec.hom y₁).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨Chart.immObj P D.ι, jD ≫ e, ?_, ⟨(⟨y₁, hyD⟩ : D), hy₁⟩, ?_⟩
  · change Etale (D.ι ≫ (SCH).map e)
    infer_instance
  · have hps : yoneda.map (jD ≫ s) ≫ v = yoneda.map (jD ≫ e) ≫ p' := by
      simp only [yoneda.map_comp, Category.assoc, hs]
    have hpt : yoneda.map (jD ≫ t) ≫ v = yoneda.map (jD ≫ e) ≫ q' := by
      simp only [yoneda.map_comp, Category.assoc, ht]
    rw [hstD] at hps
    have := congrArg yonedaEquiv (hps.symm.trans hpt)
    simpa [p', q', yonedaEquiv_apply] using this

section Main

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M] {T : BigFppfOver B S hS}
  [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (actT : AAction (fppfO B S hS) M (yoneda.obj T)) (actX : AAction (fppfO B S hS) M X)

/-- The action is injective on points. -/
lemma smul_injective {W : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj W, ⊤))
    {a b : X.obj (op W)} (e : actX.smul (F := X) (U := op W) h a = actX.smul (F := X) (U := op W) h b) :
    a = b := by
  let h' : Multiplicative M →* Γ((SCH).obj W, ⊤) := h.comp invMonoidHom
  have hm : h' * h = 1 := MonoidHom.ext fun x => by
    change h (x⁻¹) * h x = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  have key : ∀ c : X.obj (op W), actX.smul (F := X) (U := op W) h' (actX.smul (F := X) (U := op W) h c) = c := fun c => by
    refine (actX.mul_smul (U := op W) h' h c).symm.trans ?_
    exact (congrArg (fun k => actX.smul (F := X) (U := op W) k c) hm).trans (actX.one_smul c)
  rw [← key a, e, key b]

/-- The projection `Spec Γ(T)[M] → T` is flat and open. -/
lemma pr_flat_open [IsNoetherianRing Γ((SCH).obj T, ⊤)] :
    Flat ((SCH).map (spToT T (ι1 T (M := M)) contains1)) ∧
      IsOpenMap ((SCH).map (spToT T (ι1 T (M := M)) contains1)) := by
  let pr := spToT T (ι1 T (M := M)) contains1
  let ρ : Γ((SCH).obj T, ⊤) →+* Γ((SCH).obj (spObj T (ι1 T (M := M)) contains1), ⊤) :=
    ((SCH).map pr).appTop.hom
  have hρ : ρ = (spSec T (ι1 T (M := M)) contains1).comp (ι1 T) :=
    RingHom.ext fun x => spToT_appTop T _ _ x
  have hfl : ρ.Flat := by
    have f1 : (ι1 T (M := M)).Flat := by
      have h0 : Module.Flat (RT T) (AddMonoidAlgebra (RT T) M) := inferInstance
      exact (RingHom.flat_algebraMap_iff (R := RT T) (S := AddMonoidAlgebra (RT T) M)).2 h0
    have f2 := RingHom.Flat.of_bijective (spSec_bijective T (ι1 T (M := M)) contains1)
    rw [hρ]
    exact RingHom.Flat.comp f1 f2
  have hF : Flat ((SCH).map pr) := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).2 hfl
  have hfp : ρ.FinitePresentation := by
    have f1 : (ι1 T (M := M)).FinitePresentation := by
      haveI : Algebra.FiniteType (RT T) (AddMonoidAlgebra (RT T) M) := inferInstance
      haveI : IsNoetherianRing (RT T) := ‹IsNoetherianRing Γ((SCH).obj T, ⊤)›
      have : Algebra.FinitePresentation (RT T) (AddMonoidAlgebra (RT T) M) :=
        Algebra.FinitePresentation.of_finiteType.1 inferInstance
      exact RingHom.finitePresentation_algebraMap.2 this
    have f2 : (spSec T (ι1 T (M := M)) contains1).FinitePresentation :=
      RingHom.FinitePresentation.of_surjective _ (spSec_bijective T _ _).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (spSec_bijective T _ _).1]; exact Submodule.fg_bot)
    rw [hρ]
    exact RingHom.FinitePresentation.comp f2 f1
  have hL : LocallyOfFinitePresentation ((SCH).map pr) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).2 hfp
  exact ⟨hF, ((SCH).map pr).isOpenMap⟩

/-- A coefficient of an element of `K[M]` lies in `K`. -/
lemma coeff_mem_of_mem_map {R N : Type*} [CommRing R] [AddCommMonoid N] (K : Ideal R)
    {x : AddMonoidAlgebra R N} (hx : x ∈ K.map ((AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R N)))
    (d : N) : x.coeff d ∈ K := by
  have hle : K.map ((AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R N)) ≤
      RingHom.ker (AddMonoidAlgebra.mapRingHom N (Ideal.Quotient.mk K)) := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    change AddMonoidAlgebra.mapRingHom N (Ideal.Quotient.mk K) (AddMonoidAlgebra.single 0 c) = 0
    rw [AddMonoidAlgebra.mapRingHom_single, Ideal.Quotient.eq_zero_iff_mem.2 hc]
    simp
  have h0 := congrArg (fun z => z.coeff d) (hle hx)
  simp only [AddMonoidAlgebra.coeff_mapRingHom] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using h0)

set_option maxHeartbeats 2000000 in
/-- On the open `D(c f)` of `Spec Γ(T)[M]`, `c` the coaction, equivariant `p`, `q` agreeing on `D(f)` have
equal pullbacks along the projection. -/
lemma agree_coact (p q : X.obj (op T))
    (hp : ∀ {W : BigFppfOver B S hS} (t : W ⟶ T) (h : Multiplicative M →* Γ((SCH).obj W, ⊤)),
      X.map (smulAt actT h t).op p = actX.smul (F := X) (U := op W) h (X.map t.op p))
    (hq : ∀ {W : BigFppfOver B S hS} (t : W ⟶ T) (h : Multiplicative M →* Γ((SCH).obj W, ⊤)),
      X.map (smulAt actT h t).op q = actX.smul (F := X) (U := op W) h (X.map t.op q))
    (f : Γ((SCH).obj T, ⊤)) (hf : AgreeOn p q f) :
    let Tm := spObj T (ι1 T (M := M)) contains1
    let i := Chart.immι Tm (((SCH).obj Tm).basicOpen (((SCH).map (univMap actT)).appTop.hom f)).ι
    X.map (i ≫ spToT T (ι1 T (M := M)) contains1).op p =
      X.map (i ≫ spToT T (ι1 T (M := M)) contains1).op q := by
  intro Tm i
  let pr := spToT T (ι1 T (M := M)) contains1
  let jf := Chart.immι T (((SCH).obj T).basicOpen f).ι
  haveI : IsOpenImmersion ((SCH).map jf) := inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))
  have hr : Set.range ((SCH).map jf) = ((SCH).obj T).basicOpen f := Scheme.Opens.range_ι _
  obtain ⟨c, hc⟩ := exists_factor_open jf (i ≫ univMap actT) (by
    rw [hr]
    rintro _ ⟨y, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    have hm : ((SCH).map i y : (SCH).obj Tm) ∈
        ((SCH).map (univMap actT)) ⁻¹ᵁ ((SCH).obj T).basicOpen f := by
      rw [Scheme.preimage_basicOpen]
      exact (y : ((SCH).obj Tm).basicOpen _).2
    exact hm)
  let h0 : Multiplicative M →* Γ((SCH).obj (Chart.immObj Tm (((SCH).obj Tm).basicOpen (((SCH).map (univMap actT)).appTop.hom f)).ι), ⊤) :=
    secPt ((SCH).map i).appTop.hom (univPt1 (U := T))
  have e₀ : i ≫ univMap actT = smulAt actT h0 (i ≫ pr) := comp_smulAt actT i _ _
  apply smul_injective actX h0
  rw [← hp, ← hq, ← e₀, ← hc, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  exact congrArg _ hf

set_option maxHeartbeats 4000000 in
/-- **Theorem 4.1, uniqueness, for `X` any algebraic space.** Two equivariant points of `X` over a
complete pair, agreeing on all `V(mⁿ)`, are equal. -/
theorem thm41_unique_equivariant (hX : IsAlgebraicSpace B S hS X) (m : Ideal Γ((SCH).obj T, ⊤))
    (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m)
    (p q : X.obj (op T))
    (hp : ∀ {W : BigFppfOver B S hS} (t : W ⟶ T) (h : Multiplicative M →* Γ((SCH).obj W, ⊤)),
      X.map (smulAt actT h t).op p = actX.smul (F := X) (U := op W) h (X.map t.op p))
    (hq : ∀ {W : BigFppfOver B S hS} (t : W ⟶ T) (h : Multiplicative M →* Γ((SCH).obj W, ⊤)),
      X.map (smulAt actT h t).op q = actX.smul (F := X) (U := op W) h (X.map t.op q))
    (h : ∀ n, X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n))).op p =
      X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n))).op q) : p = q := by
  letI := gradedRingOfAction actT
  haveI : IsNoetherianRing Γ((SCH).obj T, ⊤) := hP.noeth
  let Y := (SCH).obj T
  have hhi : ∀ y : Y, Y.isoSpec.inv (Y.isoSpec.hom y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
  have hhj : ∀ w : Spec Γ(Y, ⊤), Y.isoSpec.hom (Y.isoSpec.inv w) = w := fun w => by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
  let A : Set Y := {y | ∃ f, AgreeOn p q f ∧ y ∈ Y.basicOpen f}
  let K : Ideal Γ(Y, ⊤) := sInf {I | ∃ y : Y, y ∉ A ∧ I = (Y.isoSpec.hom y).asIdeal}
  have hKmem : ∀ {f}, f ∈ K ↔ ∀ y : Y, y ∉ A → f ∈ (Y.isoSpec.hom y).asIdeal := fun {f} => by
    rw [Submodule.mem_sInf]
    constructor
    · exact fun hf y hy => hf _ ⟨y, hy, rfl⟩
    · rintro hf _ ⟨y, hy, rfl⟩
      exact hf y hy
  have hK1 : ∀ y : Y, K ≤ (Y.isoSpec.hom y).asIdeal → y ∉ A := by
    rintro y hle ⟨f, hAg, hy⟩
    refine (mem_basicOpen_iff y f).1 hy (hle (hKmem.2 fun y' hy' => ?_))
    by_contra hc
    exact hy' ⟨f, hAg, (mem_basicOpen_iff y' f).2 hc⟩
  -- a basic open around a point of an open image
  have hbas : ∀ {P : BigFppfOver B S hS} (e : P ⟶ T), Flat ((SCH).map e) →
      IsOpenMap ((SCH).map e) → X.map e.op p = X.map e.op q →
      ∀ y ∈ Set.range ((SCH).map e), y ∈ A := by
    intro P e hf ho hag y hy
    have hU : IsOpen (Set.range ((SCH).map e)) := ho.isOpen_range
    obtain ⟨f, hfU, hyf⟩ := (isAffineOpen_top Y).exists_basicOpen_le
      (V := ⟨Set.range ((SCH).map e), hU⟩) ⟨y, hy⟩ trivial
    refine ⟨f, ?_, hyf⟩
    exact agreeOn_of_family hX (fun _ : PUnit.{u + 1} => P) (fun _ => e) (fun _ => hf) (fun _ => ho)
      p q (fun _ => hag) f fun y' hy' => ⟨PUnit.unit, hfU hy'⟩
  have hnear : ∀ y : Y, (∀ r ∈ m, y ∉ Y.basicOpen r) → y ∈ A := by
    intro y hy
    obtain ⟨P, e, he, hyr, hag⟩ := exists_etale_agree hX T m p q h y hy
    exact hbas e inferInstance ((SCH).map e).isOpenMap hag y hyr
  obtain ⟨r, hr, f, hf, hrf⟩ : ∃ r ∈ m, ∃ f ∈ K, r + f = 1 := by
    by_contra hcon
    have hne : m ⊔ K ≠ ⊤ := by
      intro htop
      have h1 : (1 : Γ(Y, ⊤)) ∈ m ⊔ K := htop ▸ Submodule.mem_top
      obtain ⟨r, hr, f, hf, hrf⟩ := Submodule.mem_sup.1 h1
      exact hcon ⟨r, hr, f, hf, hrf⟩
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    let y : Y := Y.isoSpec.inv ⟨Q, hQ.isPrime⟩
    have hyQ : (Y.isoSpec.hom y).asIdeal = Q := by
      exact congrArg (fun w : Spec Γ(Y, ⊤) => PrimeSpectrum.asIdeal w) (hhj ⟨Q, hQ.isPrime⟩)
    refine hK1 y (by rw [hyQ]; exact le_trans le_sup_right hle) (hnear y fun x hx hb => ?_)
    refine (mem_basicOpen_iff y x).1 hb ?_
    rw [hyQ]
    exact hle (Ideal.mem_sup_left hx)
  have hfAg : AgreeOn p q f := agreeOn_of_cover hX p q f fun y hy => by
    by_contra hc
    have hyA : y ∉ A := fun ⟨f', h1, h2⟩ => hc ⟨f', h1, h2⟩
    exact (mem_basicOpen_iff y f).1 hy (hKmem.1 hf y hyA)
  -- the action and the projection
  let Tm := spObj T (ι1 T (M := M)) contains1
  let pr := spToT T (ι1 T (M := M)) contains1
  obtain ⟨hprF, hprO⟩ := pr_flat_open (T := T) (M := M)
  let sec : R1 T M ≃+* Γ((SCH).obj Tm, ⊤) := RingEquiv.ofBijective _ (spSec_bijective T (ι1 T (M := M)) contains1)
  have hrad : coact actT f ∈ (K.map (ι1 T (M := M))).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hle, hprime⟩
    by_contra hu
    let Q' : Ideal Γ((SCH).obj Tm, ⊤) := Q.comap (sec.symm : _ →+* _)
    haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hQ' : ∀ c : R1 T M, sec c ∈ Q' ↔ c ∈ Q := fun c => by
      change sec.symm (sec c) ∈ Q ↔ _
      rw [RingEquiv.symm_apply_apply]
    let z : (SCH).obj Tm := ((SCH).obj Tm).isoSpec.inv ⟨Q', inferInstance⟩
    have hzQ : (((SCH).obj Tm).isoSpec.hom z).asIdeal = Q' := by
      have hhj' : ∀ w : Spec Γ((SCH).obj Tm, ⊤),
          ((SCH).obj Tm).isoSpec.hom (((SCH).obj Tm).isoSpec.inv w) = w := fun w => by
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
      exact congrArg (fun w : Spec Γ((SCH).obj Tm, ⊤) => PrimeSpectrum.asIdeal w)
        (hhj' ⟨Q', inferInstance⟩)
    let u' := ((SCH).map (univMap actT)).appTop.hom f
    have hzD : z ∈ ((SCH).obj Tm).basicOpen u' := by
      refine (mem_basicOpen_iff z u').2 ?_
      rw [hzQ, show u' = sec (coact actT f) from (spSec_coact actT f).symm, hQ']
      exact hu
    let i := Chart.immι Tm (((SCH).obj Tm).basicOpen u').ι
    have hag := agree_coact actT actX p q hp hq f hfAg
    haveI hiF : Flat ((SCH).map i) := inferInstanceAs (Flat (((SCH).obj Tm).basicOpen u').ι)
    have hiO : IsOpenMap ((SCH).map i) := (((SCH).obj Tm).basicOpen u').ι.isOpenEmbedding.isOpenMap
    haveI := hprF
    have hyA := hbas (i ≫ pr)
      (by rw [Functor.map_comp]; infer_instance)
      (by rw [Functor.map_comp, Scheme.Hom.comp_base]; simpa using hprO.comp hiO) hag
      ((SCH).map pr z) ⟨(⟨z, hzD⟩ : ((SCH).obj Tm).basicOpen u'), by
        rw [Functor.map_comp]; rfl⟩
    refine hK1 _ (fun c hc => ?_) hyA
    rw [mem_asIdeal_map, hzQ]
    have e : ((SCH).map pr).appTop.hom c = sec (ι1 T c) := spToT_appTop T _ _ c
    rw [e, hQ']
    exact hle (Ideal.mem_map_of_mem _ hc)
  obtain ⟨N, hN⟩ := hrad
  rw [← map_pow] at hN
  have hc0 := coeff_mem_of_mem_map K hN 0
  let r' := 1 - f ^ N
  have hr' : r' ∈ m := by
    have hdv : (f - 1) ∣ f ^ N - 1 ^ N := sub_dvd_pow_sub_pow f 1 N
    obtain ⟨w, hw⟩ := hdv
    have : r' = r * w := by
      have e : f - 1 = -r := by linear_combination hrf
      simp only [r']
      rw [one_pow, e] at hw
      linear_combination -hw
    rw [this]
    exact Ideal.mul_mem_right _ _ hr
  let s := (coact actT r').coeff 0
  have hs0 : s ∈ homog actT (0 : M) := coact_coeff actT r' 0
  have hsm : s ∈ m := by
    have := hP.hom (0 : M) hr'
    rwa [decompose_eq_coeff actT r' 0] at this
  have hsK : 1 - s ∈ K := by
    have e : (coact actT (f ^ N)).coeff (0 : M) = 1 - s := by
      have : f ^ N = 1 - r' := by simp [r']
      rw [this, map_sub, map_one]
      simp [s, AddMonoidAlgebra.one_def]
    rwa [e] at hc0
  have hu := isUnit_one_sub _ hP hs0 hsm
  have hKtop : K = ⊤ := Ideal.eq_top_of_isUnit_mem _ hsK hu
  have hA : ∀ y : Y, y ∈ A := by
    intro y
    by_contra hy
    have h1 : (1 : Γ(Y, ⊤)) ∈ K := hKtop ▸ Submodule.mem_top
    exact (Y.isoSpec.hom y).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hKmem.1 h1 y hy))
  refine eq_of_family hX (ι := {f' : Γ(Y, ⊤) // AgreeOn p q f'})
    (fun a => Chart.immObj T (Y.basicOpen a.1).ι)
    (fun a => Chart.immι T (Y.basicOpen a.1).ι)
    (fun a => inferInstanceAs (Flat (Y.basicOpen a.1).ι))
    (fun a => (Y.basicOpen a.1).ι.isOpenEmbedding.isOpenMap) (fun y => ?_) p q (fun a => a.2)
  obtain ⟨f', hf', hyf⟩ := hA y
  exact ⟨⟨f', hf'⟩, ⟨⟨y, hyf⟩, rfl⟩⟩

end Main

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.thm41_unique_equivariant
