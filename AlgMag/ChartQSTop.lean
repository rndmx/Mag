/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesLimitThm68

/-!
# Theorem 6.8 (ii) = Theorem A.2 (ii) from the chart lemma for quasi-separated spaces

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Theorem 6.8 (ii) and proof of
Theorem A.2 (ii). The globalization of `SpacesLimitThm68` without separatedness of `X`.

* `ChartLemmaQS`: the chart lemma, `X` quasi-separated of finite type over `S`, `S` affine of finite
  type over `ℤ`, closed points. The stabilizer condition of `IsChartAt` is not asked: Theorem A.1 gives
  `Z`-FPR. A named hypothesis.
* `exists_atlas_of_chartLemmaQS`: a finite family of charts, an equivariant atlas.
* `atlas_of_limit_qs`: the atlas over a limit of stages (Stacks 084W is not used).
* `exists_atlas_of_fp_qs`, `exists_charts_at_qs`, `exists_family_qs`: as `exists_atlas_of_fp`,
  `exists_charts_at`, `exists_charts`.
* `thm68_ii`, `thm68_ii_qc_final`: Theorem 6.8 (ii) with `ChartLemmaQS` as only premise on charts.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQSTop

open LimThm LimAct LimOrbit LimView

attribute [local instance] Space.pointTopology

noncomputable section

/-- An affine equivariant étale chart through a closed point: `AlgMag.IsChartAt` without the
stabilizer. -/
structure IsChartQSAt {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u}
    [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (actX : AAction (fppfO B S hS) M X) (p : ChartPoint X)
    (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (f : yoneda.obj U ⟶ X) (u : p.P ⟶ U) : Prop where
  affine : IsAffine ((BigFppfOver.toScheme B S hS).obj U)
  equivariant : IsEquivariant actU actX f
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f
  lies_over : yoneda.map u ≫ f = p.x

/-- **The chart lemma for quasi-separated spaces**: `M` f.g. abelian, `S` affine of finite type over
`ℤ`, `X` quasi-separated of finite type over `S` with `D(M)`-action, `p` a closed point. Alper–Hall–Rydh,
Corollary 10.2 (cited as Corollary 20.2 in the printed proof of Theorem A.2 (ii)). -/
def ChartLemmaQS (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] : Prop :=
  AddMonoid.FG M → IsAffine S → LocallyOfFiniteType (terminal.from S) →
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
    (_ : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (_ : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (p : ChartPoint X),
    ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (f : yoneda.obj U ⟶ X) (u : p.P ⟶ U), IsChartQSAt actX p U actU f u

section Stage

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `ChartLemmaQS` and the density of closed points (Stacks 0BA6, decent spaces): an equivariant
atlas, `X` quasi-separated of finite type over `S` affine of finite type over `ℤ`. As
`StronglyFPR.thm11_ft`. -/
theorem exists_atlas_of_chartLemmaQS [AddGroup.FG M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (hchart : ChartLemmaQS B S hS M) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsEquivariantAtlas actV actX v := by
  have hfg : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  have hdec : Space.IsDecentSpace B S hS X :=
    Space.isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hqs
  have hcov : ClosedPointsDetectCovers X :=
    StronglyFPR.closedPointsDetectCovers hX hdec (ChartAssembly.jacobson_of_ft hSft hX hdec hft.1)
      ((Space.isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).1
        (ChartAssembly.qc_of_ft hX hft))
  have hc := fun p : ChartPoint X => hchart hfg inferInstance hSft X hX hqs hft actX p
  choose W actW g u h using hc
  obtain ⟨n, a, hcv⟩ := hcov (ChartPoint X) W g (fun p => (h p).etale)
    (fun p => ⟨p, u p, (h p).lies_over⟩)
  let U : ULift.{u} (Fin n) → BigFppfOver B S hS := fun i => W (a i.down)
  let L : EtaleChartFamily actX (ULift.{u} (Fin n)) U :=
    { act := fun i => actW (a i.down)
      f := fun i => g (a i.down)
      equivariant := fun i => (h _).equivariant
      etale := fun i => (h _).etale
      isAffineHom := fun i => by
        have := (h (a i.down)).affine
        exact isAffineHom_of_isAffine _
      covers := fun T x t => by
        obtain ⟨i, hi⟩ := hcv T x t
        exact ⟨⟨i⟩, hi⟩ }
  obtain ⟨V, j, ⟨hV⟩⟩ := exists_cofan U
  obtain ⟨v, -, hat⟩ := exists_atlas_of_family hX L hV
  exact ⟨V, _, v, hat⟩

/-- An equivariant atlas pulls back along an equivariant affine morphism: the atlas part of
Lemma 6.7 (i). -/
theorem atlas_pullback {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX' : AAction (fppfO B S hS) M X'}
    {actX : AAction (fppfO B S hS) M X} {f : yoneda.obj U ⟶ X'} {g : X ⟶ X'}
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    (hgeq : IsEquivariant actX actX' g) (h : IsEquivariantAtlas actU actX' f) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsEquivariantAtlas actV actX v := by
  have hpb : IsPullback (yoneda.map (hg.rep.snd f)) (hg.rep.fst f) f g :=
    (hg.rep.isPullback f).flip
  obtain ⟨A, W, hW⟩ := h.decomposition
  refine ⟨_, pullbackAction hg.rep f h.equivariant hgeq, hg.rep.fst f, pullbackAction_fst _ _ _, ?_, ?_,
    ⟨A, _, decomposition_pullback hg _ hgeq hW⟩⟩
  · exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb h.surjective
  · exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb h.etale

variable {hZ : B.Contains (⊤_ Scheme.{u})} {L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- As `LimAct.strongAtlas_of_limit`, `Y` not separated: the descended model over a stage is
quasi-separated of finite type, `ChartLemmaQS` applies, and the atlas pulls back. -/
theorem atlas_of_limit_qs [AddGroup.FG M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hchart : ChartLemmaQS B S hS M)
    (P : LimitData B S hS hZ L) (hL : IsAlgebraicSpace B S hS L) (hG : ActGood B S hS M)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ L) (hY : IsAlgebraicSpace B S hS Y)
    (hfp : Space.IsFinitePresentation B S hS p)
    (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T), p.app T (act.smul h x) = p.app T x) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ Y), IsEquivariantAtlas actV act v := by
  obtain ⟨k, W, m, hW, hWfp, mu, mm⟩ := exists_stage P hL hG p hY hfp act hinv
  have hqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.left :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hW (P.hQs k) hWfp.2.2
  obtain ⟨V, actV, v, hv⟩ := exists_atlas_of_chartLemmaQS hSft hW hqs (P.stageFT k W hW hWfp)
    (m.toAct mu mm) hchart
  exact atlas_pullback (m.isAffine_q (P.hπ k)) (m.equivariant mu mm) hv

end Stage

section Global

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `LimThm.AffineAtlas` without the strongly-FPR field. -/
structure AffineAtlasQS (act : AAction (fppfO B S hS) M X) (V : BigFppfOver B S hS) where
  actV : AAction (fppfO B S hS) M (yoneda.obj V)
  v : yoneda.obj V ⟶ X
  equivariant : IsEquivariant actV act v
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) v
  surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) v
  I : Type u
  piece : I → ((SCH).obj V).Opens
  iSup_eq_top : iSup piece = ⊤
  stable : ∀ a, IsStableOpen actV (piece a)
  affine : ∀ a, IsAffine (piece a).toScheme

variable [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- As `LimThm.exists_atlas_of_fp`, `p` not separated. -/
theorem exists_atlas_of_fp_qs
    (hchart : ChartLemmaQS B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {A : BigFppfOver B S hS} (hA : IsAffine ((SCH).obj A))
    (p : Y ⟶ yoneda.obj A) (hfp : Space.IsFinitePresentation B S hS p)
    (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (a : APt (fppfO B S hS) M T) (y : Y.obj T),
      p.app T (act.smul a y) = p.app T y) :
    ∃ V : BigFppfOver B S hS, Nonempty (AffineAtlasQS act V) := by
  have htop : IsAffine (⊤_ Scheme.{u}) := isAffine_top
  have hSft : LocallyOfFiniteType (terminal.from (⊤_ Scheme.{u})) := by
    have : IsIso (terminal.from (⊤_ Scheme.{u})) :=
      ⟨terminal.from _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    infer_instance
  obtain ⟨V', actV', v', hs⟩ := atlas_of_limit_qs (S := ⊤_ Scheme.{u}) (hS := hZ) hSft hchart
    (LimFin.limitDataZ hZ (zObj hZ A hA)) (isAlgebraicSpace_yoneda B _ hZ _) (LimFin.actGoodZ hZ hM)
    (viewBase hZ hA p) (view_isAlgebraicSpace (hZ := hZ) hY)
    (isFinitePresentation_viewBase hZ hA p hfp)
    (viewAct act) (fun a y => viewMap_invariant (hZ := hZ) (fun a y => hinv a y) a y)
  have hv' : IsEquivariant actV' (viewAct act) v' := hs.equivariant
  obtain ⟨I, Vs, hdec⟩ := hs.decomposition
  refine ⟨LimView.chartObj v', ⟨⟨LimView.chartAct actV' hv', LimView.chartMap v',
    LimView.chartMap_equivariant hv',
    LimView.chartMap_etale v' hs.etale, LimView.chartMap_surjective v' hs.surjective,
    I, Vs, hdec.iSup_eq_top,
    fun a => chart_isStableOpen hv' (hdec.stable a), fun a => ?_⟩⟩⟩
  have h1 : IsAffineHom ((Vs a).ι ≫ structMap V') := hdec.isAffineHom a
  have h2 : IsAffine (Vs a).toScheme := by
    have : IsAffine (Scheme.Opens.toScheme (Vs a)) := isAffine_of_isAffineHom ((Vs a).ι ≫ structMap V')
    exact this
  exact h2

include hZ in
/-- As `LimThm.exists_charts_at`, `X` quasi-separated: the charts at one point. -/
theorem exists_charts_at_qs
    (hchart : ChartLemmaQS B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X)
    (x : Space.points B S hS X) :
    ∃ (I : Type u) (U : I → BigFppfOver B S hS) (actU : ∀ a, AAction (fppfO B S hS) M (yoneda.obj (U a)))
      (f : ∀ a, yoneda.obj (U a) ⟶ X) (_ : ∀ a, IsEquivariant (actU a) act (f a)),
      (∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f a)) ∧
      (∀ a, IsAffine ((SCH).obj (U a))) ∧
      ∃ a, x ∈ Set.range (Space.pointsMap B S hS _ (f a)) := by
  have hfg : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  obtain ⟨O, W, hOa, hW, hq, hst, hL, y, rfl⟩ := exists_stable_open hM hX act x
  obtain ⟨V, ⟨a⟩⟩ := exists_atlas_of_fp_qs hZ hchart hM hW.1 (isAffine_openBase hOa) (LimThm.toBase hL)
    (isFinitePresentation_toBase hX hlfp hqs hW hq hL hOa) (restrictAct act hst)
    (fun k z => toBase_invariant hL _ k z)
  have hιeq : IsEquivariant (restrictAct act hst) act W.ι := ι_equivariant act hst
  let c : ∀ i, yoneda.obj (openObj (a.piece i)) ⟶ X := fun i =>
    yoneda.map (openJ (a.piece i)) ≫ a.v ≫ W.ι
  have hE : ∀ i, IsEquivariant (StronglyFPR.openAct (a.stable i)) act (c i) := fun i =>
    isEquivariant_comp (StronglyFPR.openJ_equivariant (a.stable i))
      (isEquivariant_comp a.equivariant hιeq)
  refine ⟨a.I, fun i => openObj (a.piece i), fun i => StronglyFPR.openAct (a.stable i), c, hE,
    fun i => ?_, fun i => a.affine i, ?_⟩
  · have hmap := Space.isMultiplicative_presheaf_etale B S hS
    refine MorphismProperty.comp_mem _ _ _ ?_ (isEtale_comp_ι hW a.etale)
    have : Etale ((SCH).map (openJ (a.piece i))) :=
      inferInstanceAs (Etale (Scheme.Opens.ι (a.piece i)))
    exact (Space.presheaf_yoneda_map_iff B S hS inferInstance _).2 this
  · obtain ⟨z, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS a.v a.surjective y
    have hτ : Space.pointsToScheme B S hS V z ∈ (iSup a.piece) := by
      rw [a.iSup_eq_top]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hτ
    obtain ⟨w, hw⟩ := Space.surjective_pointsToScheme B S hS (openObj (a.piece i))
      (⟨_, hi⟩ : (a.piece i).toScheme)
    have e0 : Space.pointsMap B S hS _ (yoneda.map (openJ (a.piece i))) w = z :=
      Space.injective_pointsToScheme B S hS V
        (by rw [Space.pointsToScheme_pointsMap_yoneda, hw]; rfl)
    refine ⟨i, w, ?_⟩
    change Space.pointsMap B S hS _ (yoneda.map (openJ (a.piece i)) ≫ a.v ≫ W.ι) w = _
    rw [Space.pointsMap_comp_apply, e0, Space.pointsMap_comp_apply]

include hZ in
/-- **Globalization**: `ChartLemmaQS` gives an `EtaleChartFamily` of charts from affine schemes, for
`X` quasi-separated and locally of finite presentation over `S` separated. -/
theorem exists_family_qs [S.IsSeparated]
    (hchart : ChartLemmaQS B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X) :
    ∃ (A : Type u) (U : A → BigFppfOver B S hS), Nonempty (EtaleChartFamily act A U) ∧
      ∀ a, IsAffine ((SCH).obj (U a)) := by
  obtain ⟨U0, g, hs, -⟩ := hX.exists_atlas
  have hp := fun u : (SCH).obj U0 => exists_charts_at_qs hZ hchart hM hX hlfp hqs act
    (Space.pointsMap B S hS _ g ((Space.pointsEquivScheme B S hS U0).symm u))
  choose I U actU f he het haf hhit using hp
  let f' : ∀ p : (Σ u : (SCH).obj U0, I u), yoneda.obj (U p.1 p.2) ⟶ X := fun p => f p.1 p.2
  have het' : ∀ p : (Σ u : (SCH).obj U0, I u), (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f' p) :=
    fun p => het p.1 p.2
  have hit : ∀ x : Space.points B S hS X, ∃ p, x ∈ Set.range (Space.pointsMap B S hS _ (f' p)) := by
    intro x
    obtain ⟨y, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS g hs x
    obtain ⟨i, hi⟩ := hhit (Space.pointsToScheme B S hS U0 y)
    refine ⟨⟨_, i⟩, ?_⟩
    have e : (Space.pointsEquivScheme B S hS U0).symm (Space.pointsToScheme B S hS U0 y) = y :=
      (Space.pointsEquivScheme B S hS U0).symm_apply_apply y
    rwa [e] at hi
  refine ⟨Σ u : (SCH).obj U0, I u, fun p => U p.1 p.2, ⟨⟨fun p => actU p.1 p.2, f',
    fun p => he p.1 p.2, het', fun p => isAffineHom_structMap (haf p.1 p.2),
    covers_of_hit f' het' hit⟩⟩, fun p => haf p.1 p.2⟩

include hZ in
/-- **Theorem 6.8 (ii) = Theorem A.2 (ii)**, from `ChartLemmaQS` alone: `M` f.g., `X` quasi-separated
locally of finite presentation over `S` separated, `M/Z` torsion-free in the form
`IrreducibleFibres`. A chart family from affine schemes, and for each coproduct of it in the site a
`Z`-FPR atlas. -/
theorem thm68_ii [S.IsSeparated]
    (hchart : ChartLemmaQS B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X)
    {Z : AddSubgroup M} (hMZ : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ (A : Type u) (U : A → BigFppfOver B S hS) (L : EtaleChartFamily act A U),
      (∀ a, IsAffine ((SCH).obj (U a))) ∧
      ∀ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V) (hV : IsColimit (Cofan.mk V j)),
        ∃ v : yoneda.obj V ⟶ X, IsZFPRAtlas (coprodAction L.act hV) act v Z := by
  obtain ⟨A, U, ⟨L⟩, haf⟩ := exists_family_qs hZ hchart hM hX hlfp hqs act
  exact ⟨A, U, L, haf, fun V j hV => thm68_ii_of_charts hX L hV hMZ hirr⟩

include hZ in
/-- **Theorem 6.8 (ii), quasi-compact clause**, from `ChartLemmaQS` alone: an `S`-affine `Z`-FPR atlas. -/
theorem thm68_ii_qc_final [S.IsSeparated]
    (hchart : ChartLemmaQS B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (hq : Space.IsQuasiCompactSpace B S hS X)
    (act : AAction (fppfO B S hS) M X)
    {Z : AddSubgroup M} (hMZ : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsZFPRAtlas actV act v Z ∧ IsSAffineAtlas actV act v := by
  obtain ⟨A, U, ⟨L⟩, -⟩ := exists_family_qs hZ hchart hM hX hlfp hqs act
  exact thm68_ii_qc hX L hq hMZ hirr

end Global

end

end AlgMag.ChartQSTop

#print axioms AlgMag.ChartQSTop.exists_atlas_of_chartLemmaQS
#print axioms AlgMag.ChartQSTop.exists_family_qs
#print axioms AlgMag.ChartQSTop.thm68_ii
#print axioms AlgMag.ChartQSTop.thm68_ii_qc_final
