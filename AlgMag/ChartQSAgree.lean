/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartEffectiveMain
import AlgMag.ChartQSCore

/-!
# Agreement through an étale chart, without separatedness

Step 1 of the chart-lemma proof without separatedness. Variant of `Chart.eq_of_agree_basicOpen_of_agree_thickening` for a
principal ideal `(g)`: `s, t : P → V` with `v : V → X` étale, `Γ(P)` flat over a noetherian `C`. If
`v s = v t` in `X` on `D(g)` and `s = t` on every `V(g^k)`, then `v s = v t`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQS

/-- A section of a formally unramified morphism locally of finite type is an open immersion. -/
theorem isOpenImmersion_section {V F : Scheme.{u}} (f : F ⟶ V) [FormallyUnramified f]
    [LocallyOfFiniteType f] (δ : V ⟶ F) (h : δ ≫ f = 𝟙 V) : IsOpenImmersion δ := by
  let k : F ⟶ pullback f f := pullback.lift (f ≫ δ) (𝟙 F) (by simp [h])
  have hk1 : k ≫ pullback.fst f f = f ≫ δ := pullback.lift_fst _ _ _
  have hk2 : k ≫ pullback.snd f f = 𝟙 F := pullback.lift_snd _ _ _
  have hsq : IsPullback δ δ k (pullback.diagonal f) := by
    refine IsPullback.of_isLimit' ⟨?_⟩ ?_
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hk1, pullback.diagonal_fst, Category.comp_id,
          ← Category.assoc, h, Category.id_comp]
      · simp only [Category.assoc, hk2, pullback.diagonal_snd, Category.comp_id]
    · refine PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ f) ?_ ?_ ?_
      · intro c
        have h1 := congrArg (· ≫ pullback.fst f f) c.condition
        have h2 := congrArg (· ≫ pullback.snd f f) c.condition
        simp only [Category.assoc, hk1, hk2, pullback.diagonal_fst, pullback.diagonal_snd,
          Category.comp_id] at h1 h2
        rw [Category.assoc, h1, h2]
      · intro c
        have h1 := congrArg (· ≫ pullback.fst f f) c.condition
        have h2 := congrArg (· ≫ pullback.snd f f) c.condition
        simp only [Category.assoc, hk1, hk2, pullback.diagonal_fst, pullback.diagonal_snd,
          Category.comp_id] at h1 h2
        rw [Category.assoc]
        exact h1
      · intro c m h1 _
        rw [← h1, Category.assoc, h, Category.comp_id]
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip inferInstance

lemma ι_appTop_eq_zero_of_mul {Y : Scheme.{u}} [IsAffine Y] (r x : Γ(Y, ⊤)) (h : r * x = 0) :
    (Y.basicOpen r).ι.appTop x = 0 := by
  have hloc := (isAffineOpen_top Y).isLocalization_basicOpen r
  have h0 : algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen r) x = 0 :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers r) _ x).2
      ⟨⟨r, Submonoid.mem_powers r⟩, h⟩
  have key2 : Y.presheaf.map (homOfLE le_top : Y.basicOpen r ⟶ ⊤).op ≫ (Y.basicOpen r).topIso.inv =
      (Y.basicOpen r).ι.appTop := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact (Y.presheaf.map_comp _ _).symm
  rw [← key2, ConcreteCategory.comp_apply]
  erw [h0]
  exact map_zero _

lemma mem_basicOpen_or {Y : Scheme.{u}} [IsAffine Y] (a b : Γ(Y, ⊤)) (y : Y) :
    y ∈ Y.basicOpen a ∨ y ∈ Y.basicOpen (1 - a * b) := by
  have hbo : ∀ r : Γ(Y, ⊤), y ∈ Y.basicOpen r ↔ r ∉ (Y.isoSpec.hom y).asIdeal := fun r => by
    have := congrArg (fun U : Y.Opens => y ∈ U) (Scheme.toSpecΓ_preimage_basicOpen Y r)
    exact (iff_of_eq this).symm
  rw [hbo, hbo]
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  have hp := (Y.isoSpec.hom y).isPrime
  apply hp.ne_top
  rw [Ideal.eq_top_iff_one]
  have := Ideal.add_mem _ h2 (Ideal.mul_mem_right b _ h1)
  simpa using this

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- Two opens covering an affine `P` separate points of an algebraic space. -/
theorem eq_of_two_opens (hX : IsAlgebraicSpace B S hS X) (P : BigFppfOver B S hS)
    [IsAffine ((SCH).obj P)] (r₁ r₂ : Γ((SCH).obj P, ⊤))
    (hcov : ∀ y : (SCH).obj P, y ∈ ((SCH).obj P).basicOpen r₁ ∨ y ∈ ((SCH).obj P).basicOpen r₂)
    (p q : X.obj (op P))
    (h₁ : X.map (Chart.immι P ((SCH).obj P |>.basicOpen r₁).ι).op p =
      X.map (Chart.immι P ((SCH).obj P |>.basicOpen r₁).ι).op q)
    (h₂ : X.map (Chart.immι P ((SCH).obj P |>.basicOpen r₂).ι).op p =
      X.map (Chart.immι P ((SCH).obj P |>.basicOpen r₂).ι).op q) : p = q := by
  let Z : Fin 2 → BigFppfOver B S hS := Fin.cons (Chart.immObj P ((SCH).obj P |>.basicOpen r₁).ι)
    (fun _ => Chart.immObj P ((SCH).obj P |>.basicOpen r₂).ι)
  let c : ∀ i, Z i ⟶ P := fun i => Fin.cases (motive := fun i => Z i ⟶ P)
    (Chart.immι P _) (fun _ => Chart.immι P _) i
  have hc : Presieve.ofArrows (fun i => (SCH).obj (Z i)) (fun i => (SCH).map (c i)) ∈
      Scheme.fpqcPrecoverage ((SCH).obj P) := by
    refine ChartSplit.ofArrows_two_mem_fpqcPrecoverage _ _ ?_ ?_ ?_
    · rw [Fin.forall_fin_two]
      exact ⟨inferInstanceAs (Flat ((((SCH).obj P).basicOpen r₁).ι)),
        inferInstanceAs (Flat ((((SCH).obj P).basicOpen r₂).ι))⟩
    · rw [Fin.forall_fin_two]
      have a₁ : IsAffine (((SCH).obj P).basicOpen r₁).toScheme :=
        (isAffineOpen_top _).basicOpen r₁
      have a₂ : IsAffine (((SCH).obj P).basicOpen r₂).toScheme :=
        (isAffineOpen_top _).basicOpen r₂
      exact ⟨inferInstanceAs (QuasiCompact ((((SCH).obj P).basicOpen r₁).ι)),
        inferInstanceAs (QuasiCompact ((((SCH).obj P).basicOpen r₂).ι))⟩
    · intro y
      rcases hcov y with hy | hy
      · exact ⟨0, ⟨⟨y, hy⟩, rfl⟩⟩
      · exact ⟨1, ⟨⟨y, hy⟩, rfl⟩⟩
  let x : ∀ i, X.obj (op (Z i)) := fun i => X.map (c i).op p
  have hcompat : ∀ i k ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ Z i) (g₂ : W ⟶ Z k),
      g₁ ≫ c i = g₂ ≫ c k → X.map g₁.op (x i) = X.map g₂.op (x k) := by
    intro i k W g₁ g₂ h
    simp only [x, ← Functor.map_comp_apply, ← op_comp, h]
  obtain ⟨φ, -, hu⟩ := ChartMain.existsUnique_glue hX Z c hc x hcompat
  have hp := hu p fun _ => rfl
  have hq := hu q fun i => by
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨h₁.symm, h₂.symm⟩
  exact hp.trans hq.symm

/-- **Step 1 of the chart-lemma proof without separatedness.** Let `v : V → X` be étale with `V` affine, `s, t : P → V`,
`P` affine with `Γ(P)` flat over a noetherian ring `C`, `g ∈ C`. If `v s = v t` on `D(g)` and `s = t`
on each `V(g^k)`, then `v s = v t`. No separatedness: `s, t` may differ on `D(g)`. -/
theorem eq_of_lift_etale (hX : IsAlgebraicSpace B S hS X) {P V : BigFppfOver B S hS}
    [IsAffine ((SCH).obj P)] [IsAffine ((SCH).obj V)] (v : yoneda.obj V ⟶ X)
    (hv : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) v)
    (s t : P ⟶ V) {C : Type*} [CommRing C] [IsNoetherianRing C] [Algebra C Γ((SCH).obj P, ⊤)]
    [Module.Flat C Γ((SCH).obj P, ⊤)] (g : C)
    (hD : X.map (Chart.immι P ((SCH).obj P |>.basicOpen (algebraMap C Γ((SCH).obj P, ⊤) g)).ι).op
        (v.app (op P) s) =
      X.map (Chart.immι P ((SCH).obj P |>.basicOpen (algebraMap C Γ((SCH).obj P, ⊤) g)).ι).op
        (v.app (op P) t))
    (hth : ∀ k : ℕ, Chart.immι P (Chart.closedι ((SCH).obj P)
        (((Ideal.span {g}) ^ k).map (algebraMap C Γ((SCH).obj P, ⊤)))) ≫ s =
      Chart.immι P (Chart.closedι ((SCH).obj P)
        (((Ideal.span {g}) ^ k).map (algebraMap C Γ((SCH).obj P, ⊤)))) ≫ t) :
    v.app (op P) s = v.app (op P) t := by
  let Y := (SCH).obj P
  let R := Γ(Y, ⊤)
  let γ : Γ(Y, ⊤) := algebraMap C Γ(Y, ⊤) g
  let σ : Γ((SCH).obj V, ⊤) →+* R := ((SCH).map s).appTop.hom
  let τ : Γ((SCH).obj V, ⊤) →+* R := ((SCH).map t).appTop.hom
  let I : Ideal R := Ideal.span (Set.range fun b => σ b - τ b)
  have hIk : ∀ i ∈ I, ∀ k : ℕ, i ∈ ((Ideal.span {g}) ^ k).map (algebraMap C R) := by
    intro i hi k
    refine (Ideal.span_le.2 ?_ : I ≤ _) hi
    rintro _ ⟨b, rfl⟩
    refine Chart.closedι_appTop_eq_zero _ _ ?_
    have h := congrArg (fun φ => ((SCH).map φ).appTop.hom b) (hth k)
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at h
    change (Chart.closedι ((SCH).obj P) _).appTop.hom (σ b - τ b) = 0
    rw [map_sub, sub_eq_zero]
    exact h
  -- the fibre product `F = V ×_X V`, its diagonal `δ`, and the map `m : D(γ) → F`.
  let F := hv.rep.pullback v
  let π₁ : F ⟶ V := hv.rep.fst' v
  let π₂ : F ⟶ V := hv.rep.snd v
  let d : V ⟶ F := hv.rep.lift' (𝟙 V) (𝟙 V) rfl
  have hd₁ : d ≫ π₁ = 𝟙 V := hv.rep.lift'_fst _ _ _
  have hd₂ : d ≫ π₂ = 𝟙 V := hv.rep.lift'_snd _ _ _
  haveI hπ₂ : Etale ((SCH).map π₂) := hv.property_snd v
  have hδ : IsOpenImmersion ((SCH).map d) := by
    refine isOpenImmersion_section ((SCH).map π₂) _ ?_
    rw [← CategoryTheory.Functor.map_comp, hd₂, CategoryTheory.Functor.map_id]
  let U := Y.basicOpen γ
  haveI hUa : IsAffine U.toScheme := (isAffineOpen_top Y).basicOpen γ
  let D := Chart.immObj P U.ι
  let i₀ : D ⟶ P := Chart.immι P U.ι
  have hc : yoneda.map (i₀ ≫ s) ≫ v = yoneda.map (i₀ ≫ t) ≫ v := by
    apply yonedaEquiv.injective
    have e₁ := NatTrans.naturality_apply v i₀.op s
    have e₂ := NatTrans.naturality_apply v i₀.op t
    simp only [yonedaEquiv_apply, FunctorToTypes.comp, yoneda_map_app, Category.comp_id]
    exact e₁.trans (hD.trans e₂.symm)
  let m : D ⟶ F := hv.rep.lift' (i₀ ≫ s) (i₀ ≫ t) hc
  have hm₁ : m ≫ π₁ = i₀ ≫ s := hv.rep.lift'_fst _ _ _
  have hm₂ : m ≫ π₂ = i₀ ≫ t := hv.rep.lift'_snd _ _ _
  -- on any open of `D(γ)` over the diagonal, `s = t`
  let ιU : U.toScheme ⟶ Y := U.ι
  let mm : U.toScheme ⟶ (SCH).obj F := (SCH).map m
  have hms : mm ≫ (SCH).map π₁ = ιU ≫ (SCH).map s := by
    have e := congrArg (fun f => (SCH).map f) hm₁
    simp only [CategoryTheory.Functor.map_comp] at e
    exact e
  have hmt : mm ≫ (SCH).map π₂ = ιU ≫ (SCH).map t := by
    have e := congrArg (fun f => (SCH).map f) hm₂
    simp only [CategoryTheory.Functor.map_comp] at e
    exact e
  let I' : Ideal Γ(U.toScheme, ⊤) := I.map ιU.appTop.hom
  have hzero : ∀ O : U.toScheme.Opens, (∀ x ∈ O, mm x ∈ Set.range ((SCH).map d)) →
      ∀ i ∈ I', O.ι.appTop i = 0 := by
    intro O hO i hi
    have hle : I' ≤ RingHom.ker O.ι.appTop.hom := by
      refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
      rintro _ ⟨b, rfl⟩
      let l : O.toScheme ⟶ (SCH).obj V := IsOpenImmersion.lift ((SCH).map d) (O.ι ≫ mm) (by
        rintro _ ⟨x, rfl⟩
        exact hO _ x.2)
      have hl : l ≫ (SCH).map d = O.ι ≫ mm := IsOpenImmersion.lift_fac _ _ _
      have h₁ : O.ι ≫ ιU ≫ (SCH).map s = l := by
        rw [← hms, ← Category.assoc, ← hl, Category.assoc, ← CategoryTheory.Functor.map_comp, hd₁,
          CategoryTheory.Functor.map_id, Category.comp_id]
      have h₂ : O.ι ≫ ιU ≫ (SCH).map t = l := by
        rw [← hmt, ← Category.assoc, ← hl, Category.assoc, ← CategoryTheory.Functor.map_comp, hd₂,
          CategoryTheory.Functor.map_id, Category.comp_id]
      have h3 := congrArg (fun f => f.appTop.hom b) (h₁.trans h₂.symm)
      simp only [Scheme.Hom.comp_appTop] at h3
      simp only [SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact h3
    exact hle hi
  have hU : ∀ i ∈ I', ∀ x : U.toScheme, mm x ∈ Set.range ((SCH).map d) →
      x ∉ U.toScheme.basicOpen i := by
    intro i hi x hx hb
    let O : U.toScheme.Opens := mm ⁻¹ᵁ ((SCH).map d).opensRange
    have h0 := hzero O (fun y hy => hy) i hi
    have hp : O.ι ⁻¹ᵁ U.toScheme.basicOpen i = O.toScheme.basicOpen (O.ι.appTop i) :=
      Scheme.preimage_basicOpen _ i
    have hxO : (⟨x, hx⟩ : O) ∈ O.ι ⁻¹ᵁ U.toScheme.basicOpen i := hb
    rw [hp, h0, Scheme.basicOpen_zero] at hxO
    exact hxO
  have hV : ∀ x : U.toScheme, (∀ i ∈ I', x ∉ U.toScheme.basicOpen i) →
      mm x ∈ Set.range ((SCH).map d) := by
    intro x hx
    haveI hDa : IsAffine ((SCH).obj D) := hUa
    let I'' : Ideal Γ((SCH).obj D, ⊤) := I'
    let c : _ ⟶ (SCH).obj D := Chart.closedι ((SCH).obj D) I''
    let E := Chart.immObj D c
    let j : E ⟶ D := Chart.immι D c
    have hjI : ∀ b, ((SCH).map (j ≫ i₀ ≫ s)).appTop.hom b = ((SCH).map (j ≫ i₀ ≫ t)).appTop.hom b := by
      intro b
      have hz : (Chart.closedι U.toScheme I').appTop.hom (ιU.appTop.hom (σ b - τ b)) = 0 :=
        ChartMain.closedι_appTop_of_mem I' (Ideal.mem_map_of_mem _
          (Ideal.subset_span ⟨b, rfl⟩))
      rw [map_sub, map_sub, sub_eq_zero] at hz
      simp only [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
        RingHom.comp_apply]
      exact hz
    have hj : j ≫ i₀ ≫ s = j ≫ i₀ ≫ t :=
      ChartMain.siteExt (ChartMain.toAffine_ext (RingHom.ext hjI))
    have hjm : j ≫ m = j ≫ i₀ ≫ s ≫ d := by
      refine hv.rep.hom_ext' ?_ ?_
      · change (j ≫ m) ≫ π₁ = (j ≫ i₀ ≫ s ≫ d) ≫ π₁
        simp only [Category.assoc, hm₁, hd₁, Category.comp_id]
      · change (j ≫ m) ≫ π₂ = (j ≫ i₀ ≫ s ≫ d) ≫ π₂
        simp only [Category.assoc, hm₂, hd₂, Category.comp_id]
        exact hj.symm
    have hrange : x ∈ Set.range (Chart.closedι U.toScheme I') := by
      let h := U.toScheme.isoSpec
      have hp : I' ≤ (h.hom x).asIdeal := fun i hi => by
        by_contra hni
        refine hx i hi ?_
        have := congrArg (fun W : U.toScheme.Opens => x ∈ W)
          (Scheme.toSpecΓ_preimage_basicOpen U.toScheme i)
        exact (iff_of_eq this).1 hni
      have hsj : Function.Surjective (Ideal.Quotient.mk I') := Ideal.Quotient.mk_surjective
      have hr := range_comap_of_surjective _ (Ideal.Quotient.mk I') hsj
      have hmem : h.hom x ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk I') : Set _) := by
        intro i hi
        exact hp (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hi)
      rw [← hr] at hmem
      obtain ⟨y, hy⟩ := hmem
      refine ⟨y, ?_⟩
      have hh : h.inv (h.hom x) = x := by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
      rw [← hh, ← hy]
      rfl
    obtain ⟨y, rfl⟩ := hrange
    have e0 := congrArg (fun f => (SCH).map f) hjm
    simp only [CategoryTheory.Functor.map_comp] at e0
    have e1 : c ≫ mm = (c ≫ ιU ≫ (SCH).map s) ≫ (SCH).map d := by
      simp only [Category.assoc]
      exact e0
    have e := congr($e1 y)
    simp only [Scheme.Hom.comp_apply] at e
    exact ⟨_, e.symm⟩
  obtain ⟨e, he, h1e⟩ := exists_idempotent_of_open ((SCH).map d) mm I' hU
    (fun i hi r hr => hzero _ hr i hi) hV
  letI alg : Algebra R Γ(U.toScheme, ⊤) := ιU.appTop.hom.toAlgebra
  have halg : ∀ r, algebraMap R Γ(U.toScheme, ⊤) r = ιU.appTop.hom r := fun _ => rfl
  haveI hloc₀ := (isAffineOpen_top Y).isLocalization_basicOpen γ
  letI alg' : Algebra R Γ(Y, U) := inferInstanceAs (Algebra Γ(Y, ⊤) Γ(Y, Y.basicOpen γ))
  haveI hloc : IsLocalization.Away (algebraMap C R g) Γ(U.toScheme, ⊤) := by
    let E : Γ(Y, U) ≃+* Γ(U.toScheme, ⊤) := U.topIso.symm.commRingCatIsoToRingEquiv
    have hE : ∀ r, E (algebraMap R Γ(Y, U) r) = algebraMap R Γ(U.toScheme, ⊤) r := fun r => by
      rw [halg]
      have key2 : Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op ≫ U.topIso.inv = U.ι.appTop := by
        rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
        exact (Y.presheaf.map_comp _ _).symm
      exact ConcreteCategory.congr_hom key2 r
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap C R g))
      (AlgEquiv.ofRingEquiv (f := E) hE)
  obtain ⟨w, hw⟩ := exists_mul_eq_zero (R := R) (Rg := Γ(U.toScheme, ⊤)) g I hIk e
    (fun i hi => he _ (Ideal.mem_map_of_mem _ hi)) h1e
  have hzz : ∀ b, (Y.basicOpen (1 - γ * w)).ι.appTop.hom (σ b - τ b) = 0 := fun b =>
    ι_appTop_eq_zero_of_mul _ _ (hw _ (Ideal.subset_span ⟨b, rfl⟩))
  haveI hOa : IsAffine (Y.basicOpen (1 - γ * w)).toScheme := (isAffineOpen_top Y).basicOpen _
  have hst : Chart.immι P (Y.basicOpen (1 - γ * w)).ι ≫ s = Chart.immι P (Y.basicOpen (1 - γ * w)).ι ≫ t := by
    refine ChartMain.siteExt (ChartMain.toAffine_ext (RingHom.ext fun b => ?_))
    have h := hzz b
    rw [map_sub, sub_eq_zero] at h
    simp only [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
    exact h
  refine eq_of_two_opens hX P γ (1 - γ * w) (mem_basicOpen_or _ _) _ _ hD ?_
  have e₁ := NatTrans.naturality_apply v (Chart.immι P (Y.basicOpen (1 - γ * w)).ι).op s
  have e₂ := NatTrans.naturality_apply v (Chart.immι P (Y.basicOpen (1 - γ * w)).ι).op t
  have e₃ : v.app (op (Chart.immObj P (Y.basicOpen (1 - γ * w)).ι))
      (Chart.immι P (Y.basicOpen (1 - γ * w)).ι ≫ s) =
      v.app (op (Chart.immObj P (Y.basicOpen (1 - γ * w)).ι))
      (Chart.immι P (Y.basicOpen (1 - γ * w)).ι ≫ t) := by rw [hst]
  exact e₁.symm.trans (e₃.trans e₂)

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.isOpenImmersion_section
#print axioms AlgMag.ChartQS.eq_of_two_opens
#print axioms AlgMag.ChartQS.eq_of_lift_etale
