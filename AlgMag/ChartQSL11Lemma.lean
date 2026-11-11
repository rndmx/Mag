/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSL11Generic
import AlgMag.ChartQSStratOrbit

/-!
# Lemma 1.1 of the chart-lemma proof for quasi-separated `X`

`lemma11_qs`, `orbit_lfp_qs`, and `lemma11QS_holds`, which discharges `ChartPoint.Lemma11QS`.
The Lean statement `lemma11_qs` adds two hypotheses to the printed lemma: `S` affine and `o` locally of
finite presentation. No quasi-affineness of fibre products (Zariski's Main Theorem) is used: a finite
affine cover and `exists_chart_affine_pull` suffice.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQSL11

open ChartMain AlgMag.ChartPoint

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]

variable [IsAffine S] {o : yoneda.obj (Ob P N) ⟶ X}

/-- **Lemma 1.1, step D**: over a point `g` of the image `Y`, the base change of `o` is an open
immersion, by `IsOpenImmersion.of_flat_of_mono`. -/
theorem orbit_openImmersion_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    (hK : IsField (RT P)) (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    (hoi : ∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P N),
      o.app (op T) a = o.app (op T) b → a = b)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o)
    {T W : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X)
    (hg : g.app (op T) (𝟙 T) ∈ (imS o).obj (op T)) (p : W ⟶ Ob P N) (w : W ⟶ T)
    (sq : IsPullback (yoneda.map p) (yoneda.map w) o g) : IsOpenImmersion ((SCH).map w) := by
  obtain ⟨h, hn, hgood⟩ := exists_good_basicOpen_qs hX hqc hK hoi hlfp
  have hall := goodAt_of_basicOpen_qs hX hqc hK actX hoe hlfp h hn hgood
  haveI hm : Mono ((SCH).map w) := mono_of_pull hoi sq
  haveI hl : LocallyOfFinitePresentation ((SCH).map w) := hlfp.property _ _ _ sq
  have hfl : Flat ((SCH).map w) := Flat.of_stalkMap _ fun v => by
    -- an affine open of `T` around the image of `v`
    obtain ⟨T0, hT0, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := (SCH).map w v) (U := ⊤) trivial
    let Ts := Space.openSiteObject B S hS T T0
    let ι : Ts ⟶ T := Space.openSiteObjectHom B S hS T T0
    haveI : IsAffine ((SCH).obj Ts) := hT0
    let gs : yoneda.obj Ts ⟶ X := yoneda.map ι ≫ g
    have hgs : gs.app (op Ts) (𝟙 Ts) ∈ (imS o).obj (op Ts) := by
      have e0 : gs.app (op Ts) (𝟙 Ts) = X.map ι.op (g.app (op T) (𝟙 T)) := by
        rw [← hom_nat]
        change g.app (op Ts) (𝟙 Ts ≫ ι) = _
        simp
      rw [e0]
      exact (imS o).map _ hg
    obtain ⟨E, e₂, e₁, sqE⟩ := exists_pull_qs hX o gs
    have hι : IsOpenImmersion ((SCH).map ι) := by
      change IsOpenImmersion T0.ι
      infer_instance
    -- `E → W`
    obtain ⟨k, hk1, hk2⟩ := pb_lift sq e₂ (e₁ ≫ ι) (by have := pb_comm sqE; exact this)
    have hcart : IsPullback k e₁ w ι := by
      refine IsPullback.of_map yoneda hk2 (pb_mk (congrArg (fun z => z) hk2) ?_ ?_)
      · intro V a b hab
        have hab' : a ≫ w = b ≫ ι := hab
        have e0 : o.app (op V) (a ≫ p) = gs.app (op V) b := by
          change _ = g.app (op V) (b ≫ ι)
          rw [← hab', hom_nat, hom_nat, pb_comm sq]
        obtain ⟨l, hl1, hl2⟩ := pb_lift sqE _ _ e0
        refine ⟨l, pb_ext sq ?_ ?_, hl2⟩
        · change (l ≫ k) ≫ p = a ≫ p
          rw [Category.assoc, hk1, hl1]
        · change (l ≫ k) ≫ w = a ≫ w
          rw [Category.assoc, hk2, ← Category.assoc, hl2, hab']
      · intro V l l' h1 h2
        have h1' : l ≫ k = l' ≫ k := h1
        refine pb_ext sqE ?_ h2
        rw [← hk1, ← Category.assoc, ← Category.assoc, h1']
    have hS' := hcart.map (SCH)
    have hkO : IsOpenImmersion ((SCH).map k) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hS'.flip hι
    have hpt : ∃ y : (SCH).obj E, (SCH).map k y = v := by
      have hpv : (SCH).map w v = (SCH).map ι (⟨(SCH).map w v, hmem⟩ : T0) := rfl
      obtain ⟨y, h1, -⟩ := Scheme.Pullback.exists_preimage_pullback v _ hpv
      refine ⟨hS'.isoPullback.inv y, ?_⟩
      rw [← h1, ← Scheme.Hom.comp_apply, hS'.isoPullback_inv_fst]
    obtain ⟨y, rfl⟩ := hpt
    have h1 : (((SCH).map e₁).stalkMap y).hom.Flat :=
      hall _ gs hgs e₂ e₁ sqE y rfl
    have h2 : (((SCH).map k ≫ (SCH).map w).stalkMap y).hom.Flat := by
      rw [← Functor.map_comp, hk2, Functor.map_comp, Scheme.Hom.stalkMap_comp]
      exact RingHom.Flat.comp (Flat.stalkMap _ _) h1
    exact flat_stalk_descend _ _ y (Flat.stalkMap _ _) h2
  exact IsOpenImmersion.of_flat_of_mono _

/-- **Lemma 1.1, corrected.** `S` affine, `o` locally of finite presentation (added hypotheses with
respect to the printed lemma). -/
theorem lemma11_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    (hK : IsField (RT P)) (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    (hoi : ∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P N),
      o.app (op T) a = o.app (op T) b → a = b)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o) :
    ∃ (X' : Subfunctor X) (hle : Subfunctor.range o ≤ X'),
      Space.IsOpenSubspace B S hS X' ∧
      (∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (x : X'.toFunctor.obj T),
        ∃ y, X'.ι.app T y = actX.smul h (X'.ι.app T x)) ∧
      ClosedP (Subfunctor.lift o hle) := by
  classical
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  have hcl := Space.isClosedSubspace_schemeTheoreticImageSubfunctor B S hS o hX
  have hrangeY : Subfunctor.range o ≤ imS o :=
    Space.range_le_schemeTheoreticImageSubfunctor B S hS o
  have hle : Subfunctor.range o ≤ orbitOpen o := by
    rintro V _ ⟨a, rfl⟩ V' e -
    refine ⟨e ≫ a, ?_⟩
    exact hom_nat o e a
  -- the closed part of a point
  have hYpt : ∀ {T : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X), ∃ (C : BigFppfOver B S hS)
      (c : C ⟶ T), IsClosedImmersion ((SCH).map c) ∧ g.app (op C) c ∈ (imS o).obj (op C) ∧
      ∀ {V : BigFppfOver B S hS} (e : V ⟶ T), g.app (op V) e ∈ (imS o).obj (op V) →
        ∃ l : V ⟶ C, l ≫ c = e := by
    intro T g
    let hι := hcl.2
    let C := hι.rep.pullback g
    let c : C ⟶ T := hι.rep.snd g
    have sq : IsPullback (hι.rep.fst g) (yoneda.map c) (imS o).ι g := hι.rep.isPullback g
    refine ⟨C, c, hι.property_snd g, ?_, ?_⟩
    · have e : (imS o).ι.app (op C) ((hι.rep.fst g).app (op C) (𝟙 C)) =
          g.app (op C) ((yoneda.map c).app (op C) (𝟙 C)) :=
        congrArg (fun k => k.app (op C) (𝟙 C)) sq.w
      have e2 : (yoneda.map c).app (op C) (𝟙 C) = c := by simp
      rw [e2] at e
      rw [← e]
      exact ((hι.rep.fst g).app (op C) (𝟙 C)).2
    · intro V e he
      let a : yoneda.obj V ⟶ (imS o).toFunctor := yonedaEquiv.symm ⟨g.app (op V) e, he⟩
      have hcomm : a ≫ (imS o).ι = yoneda.map e ≫ g := by
        apply yonedaEquiv.injective
        simp [a, yonedaEquiv]
        rfl
      obtain ⟨l, hl⟩ := Functor.Full.map_surjective (F := yoneda) (sq.lift a (yoneda.map e) hcomm)
      refine ⟨l, Functor.Faithful.map_injective (F := yoneda) ?_⟩
      rw [Functor.map_comp, hl]
      exact sq.lift_snd _ _ _
  have hgmap : ∀ {T V : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X) (e : V ⟶ T) {V' : BigFppfOver B S hS}
      (e' : V' ⟶ V), X.map e'.op (g.app (op V) e) = g.app (op V') (e' ≫ e) :=
    fun g e _ e' => (hom_nat g e' e).symm
  refine ⟨orbitOpen o, hle, ?_, ?_, ?_⟩
  · -- open
    have hopen : Space.IsOpenImmersion B S hS (orbitOpen o).ι := by
      refine MorphismProperty.relative.of_exists fun T g => ?_
      obtain ⟨C, c, hc, hcY, hcl'⟩ := hYpt g
      let gC : yoneda.obj C ⟶ X := yoneda.map c ≫ g
      obtain ⟨WC, pC, wC, sqC⟩ := exists_pull_qs hX o gC
      have hgC : gC.app (op C) (𝟙 C) ∈ (imS o).obj (op C) := by
        change g.app (op C) (𝟙 C ≫ c) ∈ _
        simpa using hcY
      have hwO : IsOpenImmersion ((SCH).map wC) :=
        orbit_openImmersion_qs hX hqc hK actX hoe hoi hlfp gC hgC pC wC sqC
      let Z : Set ((SCH).obj T) := (SCH).map c '' (Set.range ((SCH).map wC))ᶜ
      have hZ : IsClosed Z :=
        ((SCH).map c).isClosedEmbedding.isClosedMap _
          (((SCH).map wC).isOpenEmbedding.isOpen_range.isClosed_compl)
      let T0 : ((SCH).obj T).Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
      have hchar : ∀ {V : BigFppfOver B S hS} (e : V ⟶ T),
          g.app (op V) e ∈ (orbitOpen o).obj (op V) ↔ ∀ y, (SCH).map e y ∈ T0 := by
        intro V e
        constructor
        · intro he y hy
          obtain ⟨cz, hcz, hcy⟩ := hy
          let Q := pullback e c
          let a : Q ⟶ V := pullback.fst e c
          let b : Q ⟶ C := pullback.snd e c
          have hQ : IsPullback a b e c := IsPullback.of_hasPullback _ _
          have hQS := hQ.map (SCH)
          obtain ⟨ζ0, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback y cz hcy.symm
          let ζ := hQS.isoPullback.inv ζ0
          have hζ : (SCH).map b ζ = cz := by
            rw [← h2, ← Scheme.Hom.comp_apply, hQS.isoPullback_inv_snd]
          have hin : X.map a.op (g.app (op V) e) ∈ (imS o).obj (op Q) := by
            rw [hgmap, hQ.w, ← hgmap]
            exact (imS o).map _ hcY
          obtain ⟨r, hr⟩ := he a hin
          have hr' : o.app (op Q) r = gC.app (op Q) b := by
            have : o.app (op Q) r = X.map a.op (g.app (op V) e) := hr
            rw [this, hgmap, hQ.w]
            rfl
          obtain ⟨l, -, hl⟩ := pb_lift sqC r b hr'
          exact hcz ⟨(SCH).map l ζ, by
            rw [← hζ, ← hl, Functor.map_comp, Scheme.Hom.comp_apply]⟩
        · intro he V' e' hY
          rw [hgmap] at hY ⊢
          obtain ⟨l, hl⟩ := hcl' _ hY
          have hrange : Set.range ((SCH).map l) ⊆ Set.range ((SCH).map wC) := by
            rintro _ ⟨u, rfl⟩
            by_contra hu
            refine he ((SCH).map e' u) ⟨(SCH).map l u, hu, ?_⟩
            rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp,
              ← Functor.map_comp, hl]
          let lr := IsOpenImmersion.lift ((SCH).map wC) ((SCH).map l) hrange
          have hlr : lr ≫ (SCH).map wC = (SCH).map l := IsOpenImmersion.lift_fac _ _ _
          let r : V' ⟶ WC := siteHom lr (by
            rw [← site_w wC, ← Category.assoc, hlr, site_w])
          have hr : r ≫ wC = l := site_hom_ext (by rw [Functor.map_comp]; exact hlr)
          refine ⟨r ≫ pC, ?_⟩
          change o.app (op V') (r ≫ pC) = _
          rw [hom_nat, pb_comm sqC, ← hom_nat, hr]
          change g.app (op V') (l ≫ c) = _
          rw [hl]
      let Ts := Space.openSiteObject B S hS T T0
      let ι : Ts ⟶ T := Space.openSiteObjectHom B S hS T T0
      have hιmem : g.app (op Ts) ι ∈ (orbitOpen o).obj (op Ts) :=
        (hchar ι).2 fun y => y.2
      let fst : yoneda.obj Ts ⟶ (orbitOpen o).toFunctor :=
        yonedaEquiv.symm ⟨g.app (op Ts) ι, hιmem⟩
      have hιO : IsOpenImmersion ((SCH).map ι) := by
        change IsOpenImmersion T0.ι
        infer_instance
      have hfst : ∀ {V : BigFppfOver B S hS} (l : V ⟶ Ts),
          (orbitOpen o).ι.app (op V) (fst.app (op V) l) = g.app (op V) (l ≫ ι) := by
        intro V l
        change X.map l.op (g.app (op Ts) ι) = _
        rw [hgmap]
      refine ⟨Ts, fst, ι, IsPullback.of_forall_isPullback_app fun V => ?_, hιO⟩
      rw [Types.isPullback_iff]
      refine ⟨?_, ?_, ?_⟩
      · ext l
        exact hfst l
      · intro l l' hh
        have hm : Mono ι := (SCH).mono_of_mono_map inferInstance
        exact (cancel_mono ι).1 hh.2
      · intro x e hxe
        have hmem : g.app V e ∈ (orbitOpen o).obj V := by
          have : (orbitOpen o).ι.app V x = g.app V e := hxe
          rw [← this]
          intro V' e' h'
          exact x.2 e' h'
        have hrg : Set.range ((SCH).map (e : V.unop ⟶ T)) ⊆ Set.range T0.ι := by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          exact (hchar (V := V.unop) e).1 hmem y
        let lr := IsOpenImmersion.lift T0.ι ((SCH).map (e : V.unop ⟶ T)) hrg
        have hlr : lr ≫ T0.ι = (SCH).map (e : V.unop ⟶ T) := IsOpenImmersion.lift_fac _ _ _
        let l : V.unop ⟶ Ts := siteHom lr (by
          change lr ≫ T0.ι ≫ T.hom.hom = _
          rw [← Category.assoc, hlr, site_w])
        have hl : l ≫ ι = e := site_hom_ext hlr
        refine ⟨l, Subtype.ext ?_, hl⟩
        have h1 := hfst (V := V.unop) l
        rw [hl] at h1
        exact h1.trans hxe.symm
    exact ⟨isAlgebraicSpace_of_relativelyRepresentable B S hS _ hopen.1 hX, hopen⟩
  · -- stable
    intro T h x
    refine ⟨⟨actX.smul h x.1, ?_⟩, rfl⟩
    intro V' e hY
    have hmp := actX.map_smul e.op h x.1
    let he : Multiplicative M →* Γ((SCH).obj V', ⊤) :=
      APt.res (𝒪 := fppfO B S hS) (U := T) (V := op V') e.op h
    have hmp' : X.map e.op (actX.smul h x.1) = actX.smul (U := op V') he (X.map e.op x.1) := hmp
    rw [hmp'] at hY ⊢
    have h0 : X.map e.op x.1 ∈ (imS o).obj (op V') := by
      have := image_stable_qs hX hqc actX hoe hlfp (invPt he) _ hY
      have e2 := (actX.mul_smul (U := op V') (invPt he) he (X.map e.op x.1)).symm
      have e3 : (invPt he * he : Multiplicative M →* Γ((SCH).obj V', ⊤)) = 1 := invPt_mul he
      have e4 : actX.smul (U := op V') (invPt he) (actX.smul (U := op V') he (X.map e.op x.1)) =
          X.map e.op x.1 := by
        refine e2.trans ((congrArg (fun c => actX.smul (U := op V') c (X.map e.op x.1)) e3).trans ?_)
        exact actX.one_smul (U := op V') _
      rw [← e4]
      exact this
    obtain ⟨a, ha⟩ := x.2 e h0
    have ha' : o.app (op V') a = X.map e.op x.1 := ha
    refine ⟨oSmul N he a, ?_⟩
    have := hoe (T := op V') he a
    rw [ha'] at this
    exact this
  · -- closed
    refine MorphismProperty.relative.of_exists fun T g => ?_
    let t : yoneda.obj T ⟶ X := g ≫ (orbitOpen o).ι
    obtain ⟨W, p, w, sq⟩ := exists_pull_qs hX o t
    have hιinj : ∀ {V : BigFppfOver B S hS} (a b : (orbitOpen o).toFunctor.obj (op V)),
        (orbitOpen o).ι.app (op V) a = (orbitOpen o).ι.app (op V) b → a = b :=
      fun _ _ h => Subtype.ext h
    have hlo : ∀ {V : BigFppfOver B S hS} (a : V ⟶ Ob P N),
        (orbitOpen o).ι.app (op V) ((Subfunctor.lift o hle).app (op V) a) = o.app (op V) a :=
      fun a => rfl
    have hsq' : IsPullback (yoneda.map p) (yoneda.map w) (Subfunctor.lift o hle) g := by
      refine pb_mk (hιinj _ _ ?_) ?_ ?_
      · rw [hlo]; exact pb_comm sq
      · intro V a b hab
        exact pb_lift sq a b (by rw [← hlo, hab]; rfl)
      · intro V l l' h1 h2
        exact pb_ext sq h1 h2
    refine ⟨W, yoneda.map p, w, hsq', ?_⟩
    obtain ⟨C, c, hc, hcY, hclift⟩ := hYpt t
    have htX : ∀ {V : BigFppfOver B S hS} (e : V ⟶ T), t.app (op V) e ∈ (imS o).obj (op V) →
        ∃ a : V ⟶ Ob P N, o.app (op V) a = t.app (op V) e := by
      intro V e he
      have ht1 : t.app (op V) e = X.map (𝟙 V).op (t.app (op V) e) := by simp
      have he' : X.map (𝟙 V).op (t.app (op V) e) ∈ (imS o).obj (op V) := by
        rw [← ht1]; exact he
      obtain ⟨a, ha⟩ := (g.app (op V) e).2 (𝟙 V) he'
      exact ⟨a, ha.trans ht1.symm⟩
    obtain ⟨a, ha⟩ := htX c hcY
    obtain ⟨l, -, hl⟩ := pb_lift sq a c ha
    have hwY : t.app (op W) w ∈ (imS o).obj (op W) := by
      rw [← pb_comm sq]
      exact hrangeY _ ⟨p, rfl⟩
    obtain ⟨l', hl'⟩ := hclift w hwY
    haveI hcm : Mono c := (SCH).mono_of_mono_map inferInstance
    haveI hwm : Mono ((SCH).map w) := mono_of_pull hoi sq
    haveI hwm' : Mono w := (SCH).mono_of_mono_map inferInstance
    have h1 : l ≫ l' = 𝟙 C := (cancel_mono c).1 (by simp [hl', hl])
    have h2 : l' ≫ l = 𝟙 W := (cancel_mono w).1 (by simp [hl', hl])
    let iso : W ≅ C := ⟨l', l, h2, h1⟩
    change IsClosedImmersion ((SCH).map w)
    rw [← hl', Functor.map_comp]
    have : IsIso ((SCH).map l') := ((SCH).mapIso iso).isIso_hom
    infer_instance

/-- The orbit map is locally of finite presentation: all charts are of finite type over `ℤ`, and
this descends along an étale cover of the test scheme. -/
theorem orbit_lfp_qs (hX : IsAlgebraicSpace B S hS X)
    (hO : LocallyOfFiniteType (toZ (Ob P N)))
    (hU : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ → LocallyOfFiniteType (toZ U)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o := by
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  obtain ⟨U, φ, hs, he⟩ := hX.exists_atlas
  have hLU := hU U φ he
  haveI : IsLocallyNoetherian ((SCH).obj U) := LocallyOfFiniteType.isLocallyNoetherian (toZ U)
  -- the chart
  obtain ⟨E, pE, wE, sqE⟩ := exists_pull_qs hX o φ
  have hpE : Etale ((SCH).map pE) := he.property _ _ _ sqE.flip
  have hwE : LocallyOfFinitePresentation ((SCH).map wE) := by
    rw [LocallyOfFinitePresentation.iff_locallyOfFiniteType]
    have h1 : LocallyOfFiniteType ((SCH).map wE ≫ toZ U) := by
      rw [comp_toZ, ← comp_toZ pE]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (toZ U)
  haveI : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstance)
  haveI : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ inferInstance
  haveI : (MorphismProperty.inverseImage (@LocallyOfFinitePresentation.{u} :
      MorphismProperty Scheme.{u}) (SCH)).RespectsIso :=
    MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun f g e hf =>
      (MorphismProperty.arrow_mk_iso_iff (@LocallyOfFinitePresentation.{u})
        ((SCH).mapArrow.mapIso e)).1 hf
  refine MorphismProperty.relative.of_exists fun T g => ?_
  obtain ⟨W, p, w, sq⟩ := exists_pull_qs hX o g
  refine ⟨W, yoneda.map p, w, sq, ?_⟩
  let T1 := he.rep.pullback g
  let sn : T1 ⟶ T := he.rep.snd g
  have sq1 : IsPullback (he.rep.fst g) (yoneda.map sn) φ g := he.rep.isPullback g
  obtain ⟨toU, htoU⟩ := yoneda.map_surjective (he.rep.fst g)
  have sq1' : IsPullback (yoneda.map toU) (yoneda.map sn) φ g := by rw [htoU]; exact sq1
  have hsnE : Etale ((SCH).map sn) := he.property _ _ _ sq1'
  have hsnS : Surjective ((SCH).map sn) := hs.property _ _ _ sq1'
  let W1 := pullback w sn
  let a : W1 ⟶ W := pullback.fst w sn
  let b : W1 ⟶ T1 := pullback.snd w sn
  have hA : IsPullback a b w sn := IsPullback.of_hasPullback _ _
  have h0 : o.app (op W1) (a ≫ p) = φ.app (op W1) (b ≫ toU) := by
    rw [hom_nat, pb_comm sq, ← hom_nat, hA.w, hom_nat, ← pb_comm sq1', ← hom_nat]
  obtain ⟨k, hk1, hk2⟩ := pb_lift sqE _ _ h0
  have hsqY : IsPullback (yoneda.map k) (yoneda.map b) (yoneda.map wE) (yoneda.map toU) := by
    refine pb_mk hk2 ?_ ?_
    · intro V x y hxy
      have hxy' : x ≫ wE = y ≫ toU := hxy
      have e6 : o.app (op V) (x ≫ pE) = g.app (op V) (y ≫ sn) := by
        rw [hom_nat, pb_comm sqE, ← hom_nat, hxy', hom_nat, pb_comm sq1', ← hom_nat]
      obtain ⟨l0, hl1, hl2⟩ := pb_lift sq _ _ e6
      refine ⟨hA.lift l0 y hl2, pb_ext sqE ?_ ?_, hA.lift_snd _ _ _⟩
      · rw [Category.assoc, hk1, ← Category.assoc, hA.lift_fst, hl1]
      · rw [Category.assoc, hk2, ← Category.assoc, hA.lift_snd, hxy']
    · intro V l l' h1 h2
      have h1' : l ≫ k = l' ≫ k := h1
      have h2' : l ≫ b = l' ≫ b := h2
      refine hA.hom_ext (pb_ext sq ?_ ?_) h2'
      · rw [Category.assoc, Category.assoc, ← hk1, ← Category.assoc, ← Category.assoc, h1']
      · rw [Category.assoc, Category.assoc, hA.w, ← Category.assoc, ← Category.assoc, h2']
  have hsqS : IsPullback k b wE toU :=
    IsPullback.of_map yoneda hk2 (by simpa using hsqY)
  have hb : LocallyOfFinitePresentation ((SCH).map b) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (hsqS.map (SCH)) hwE
  have hAS := (hA.map (SCH)).flip
  haveI := lfp_descends.{u}
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @LocallyOfFinitePresentation) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    hAS ⟨⟨hsnS, inferInstance⟩, inferInstance⟩ hb

/-- **Lemma 1.1 for quasi-separated `X`**: the hypothesis `ChartPoint.Lemma11QS` of
`exists_orbitInput_qs` holds. -/
theorem lemma11QS_holds : Lemma11QS B S hS := by
  intro X M _ _ P _ N _ hX hqs hK actX o hoe hoi hO hU
  haveI : IsAffine ((SCH).obj (Ob P N)) := inferInstance
  exact lemma11_qs hX (isQuasiCompact_of_affine hX hqs o) hK actX hoe hoi
    (orbit_lfp_qs hX hO hU)

/-- **§1 of the chart-lemma proof for quasi-separated `X`**: no hypothesis. -/
theorem exists_orbitInput_qs' (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hqs : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X) :
    ∃ (Zp : BigFppfOver B S hS) (ιz : p.P ⟶ Zp) (X'' : Subfunctor (XP X Zp))
      (hst : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T)
        (x : X''.toFunctor.obj T),
        ∃ y, X''.ι.app T y = (actProd Zp actX).smul h (X''.ι.app T x))
      (D : OrbitInput (actOfMono (actProd Zp actX) X''.ι hst)) (u : p.P ⟶ D.O),
      Etale ((SCH).map (toTop Zp)) ∧ Mono ιz ∧ Space.IsOpenSubspace B S hS X'' ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)))
        (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)) ∧
      yoneda.map u ≫ D.j ≫ X''.ι = FunctorToTypes.prod.lift p.x (yoneda.map ιz) :=
  exists_orbitInput_qs lemma11QS_holds hSft hX hqs hft actX p

end AlgMag.ChartQSL11

#print axioms AlgMag.ChartQSL11.lemma11QS_holds
#print axioms AlgMag.ChartQSL11.exists_orbitInput_qs'
