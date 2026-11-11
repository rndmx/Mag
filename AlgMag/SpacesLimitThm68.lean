/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesLimitLocal

/-!
# Theorem 6.8 = Theorem A.2 for an arbitrary base

Mayeux, *Algebraic Magnetism*, Theorem 6.8 and proof of Theorem A.2, and *Existence of strongly-FPR
atlases*, Theorem 1.1, with the chart lemma over `Spec ℤ` (`h5`) as a named hypothesis.

* `exists_stable_open`: each point lies in a stable quasi-compact open over an affine open of `S`.
* `ChartFamily`, `exists_charts`: `S` arbitrary, `X` separated over `S`: equivariant étale strongly-FPR
  charts from affine schemes, jointly covering.
* `thm68_family`: `S` separated: an `EtaleChartFamily`, and an atlas for each coproduct in the site.
* `thm68_qc`: `S` separated, `X` quasi-compact: an `S`-affine atlas.
* `thm11_affine`: `S` affine, `X` separated of finite presentation: strongly-FPR Theorem 1.1.
* `thm68_ii_of_charts`, `thm68_ii_qc`: case (ii), for `X` not separated, given a chart family.

Definition 6.1 asks for `S`-affine pieces. An affine scheme over a non-separated `S` need not be
`S`-affine, so these statements assume `S` separated, and `exists_charts` holds without it.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.LimThm

open LimAct LimOrbit LimView

attribute [local instance] Space.pointTopology

noncomputable section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- Proof of Theorem A.1: a point of `X` lies in the orbit of a quasi-compact open over an affine open
of `S`. -/
theorem exists_stable_open [AddMonoid.FG M] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (act : AAction (fppfO B S hS) M X)
    (x : Space.points B S hS X) :
    ∃ (O : S.Opens) (W : Subfunctor X), IsAffineOpen O ∧ Space.IsOpenSubspace B S hS W ∧
      Space.IsQuasiCompactSpace B S hS W.toFunctor ∧
      (∀ (T : (BigFppfOver B S hS)ᵒᵖ) (k : APt (fppfO B S hS) M T) (y : X.obj T),
        y ∈ W.obj T → act.smul k y ∈ W.obj T) ∧
      LiesOver W O ∧ x ∈ Set.range (Space.pointsMap B S hS W.toFunctor W.ι) := by
  obtain ⟨⟨O, hOa⟩, W, hW, hq, hL, y, rfl⟩ := exists_cover hX
    (fun O : {O : S.Opens // IsAffineOpen O} => O.1) (fun s => by
      obtain ⟨A, hA, hs, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
      exact ⟨⟨A, hA⟩, hs⟩) x
  obtain ⟨W', hW', hle, hq', hst, hL'⟩ := exists_orbit act hM hX hW hq
  refine ⟨O, W', hOa, hW', hq', hst, hL' O hL, Space.pointsMap B S hS _ (Subfunctor.homOfLe hle) y, ?_⟩
  rw [← Space.pointsMap_comp_apply, Subfunctor.homOfLe_ι]

/-! ### Chart families -/

/-- From the points to the `covers` form of `EtaleChartFamily`. -/
theorem covers_of_hit {A : Type*} {U : A → BigFppfOver B S hS} (f : ∀ a, yoneda.obj (U a) ⟶ X)
    (etale : ∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f a))
    (hit : ∀ x : Space.points B S hS X, ∃ a, x ∈ Set.range (Space.pointsMap B S hS _ (f a)))
    (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X) (t : (SCH).obj T) :
    ∃ a, t ∈ Set.range ((SCH).map ((etale a).rep.snd x)) := by
  obtain ⟨y, rfl⟩ := Space.surjective_pointsToScheme B S hS T t
  obtain ⟨a, x0, hx0⟩ := hit (Space.pointsMap B S hS _ x y)
  refine ⟨a, ?_⟩
  have sq := (etale a).rep.isPullback x
  obtain ⟨w, -, rfl⟩ := Space.exists_point_of_isPullback_presheaf B S hS sq x0 y hx0
  rw [Space.pointsToScheme_pointsMap_yoneda]
  exact ⟨Space.pointsToScheme B S hS _ w, rfl⟩

/-- The `covers` form gives the points. -/
theorem hit_of_covers (hX : IsAlgebraicSpace B S hS X) {A : Type*} {U : A → BigFppfOver B S hS}
    (f : ∀ a, yoneda.obj (U a) ⟶ X)
    (etale : ∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f a))
    (covers : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X) (t : (SCH).obj T),
      ∃ a, t ∈ Set.range ((SCH).map ((etale a).rep.snd x)))
    (x : Space.points B S hS X) : ∃ a, x ∈ Set.range (Space.pointsMap B S hS _ (f a)) := by
  obtain ⟨U0, g, hs, -⟩ := hX.exists_atlas
  obtain ⟨y, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS g hs x
  obtain ⟨a, z, hz⟩ := covers U0 g (Space.pointsToScheme B S hS U0 y)
  obtain ⟨w, rfl⟩ := Space.surjective_pointsToScheme B S hS _ z
  have e0 : Space.pointsMap B S hS _ (yoneda.map ((etale a).rep.snd g)) w = y :=
    Space.injective_pointsToScheme B S hS U0 (by rw [Space.pointsToScheme_pointsMap_yoneda, hz])
  have e : yoneda.map ((etale a).rep.fst' g) ≫ f a = yoneda.map ((etale a).rep.snd g) ≫ g := by
    rw [Functor.relativelyRepresentable.map_fst']
    exact (etale a).rep.w g
  refine ⟨a, Space.pointsMap B S hS _ (yoneda.map ((etale a).rep.fst' g)) w, ?_⟩
  rw [← Space.pointsMap_comp_apply, e, Space.pointsMap_comp_apply, e0]

/-- A jointly surjective family of equivariant étale strongly-FPR morphisms from affine schemes. There
is no condition relating the charts to `S`: Definition 6.1 asks for `S`-affine, see `toEtale`. -/
structure ChartFamily (act : AAction (fppfO B S hS) M X) (A : Type u)
    (U : A → BigFppfOver B S hS) where
  actU : ∀ a, AAction (fppfO B S hS) M (yoneda.obj (U a))
  f : ∀ a, yoneda.obj (U a) ⟶ X
  equivariant : ∀ a, IsEquivariant (actU a) act (f a)
  etale : ∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f a)
  strong : ∀ a, IsStronglyFPR (equivariant a)
  affine : ∀ a, IsAffine ((SCH).obj (U a))
  hit : ∀ x : Space.points B S hS X, ∃ a, x ∈ Set.range (Space.pointsMap B S hS _ (f a))

/-- The `covers` field of `EtaleChartFamily`. -/
theorem ChartFamily.covers {act : AAction (fppfO B S hS) M X} {A : Type u}
    {U : A → BigFppfOver B S hS} (L : ChartFamily act A U) (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X) (t : (SCH).obj T) :
    ∃ a, t ∈ Set.range ((SCH).map ((L.etale a).rep.snd x)) :=
  covers_of_hit L.f L.etale L.hit T x t

/-- An `S`-affine chart family is an `EtaleChartFamily`. -/
def ChartFamily.toEtale {act : AAction (fppfO B S hS) M X} {A : Type u}
    {U : A → BigFppfOver B S hS} (L : ChartFamily act A U)
    (h : ∀ a, IsAffineHom (structMap (U a))) : EtaleChartFamily act A U where
  act := L.actU
  f := L.f
  equivariant := L.equivariant
  etale := L.etale
  isAffineHom := h
  covers := L.covers

/-- Finitely many of the charts suffice if `X` is quasi-compact: the proof of Theorem A.2, "the final
claim ... is obvious". -/
theorem exists_finset_hit {A : Type*} {U : A → BigFppfOver B S hS} (f : ∀ a, yoneda.obj (U a) ⟶ X)
    (etale : ∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f a))
    (hit : ∀ x : Space.points B S hS X, ∃ a, x ∈ Set.range (Space.pointsMap B S hS _ (f a)))
    (hC : CompactSpace (Space.points B S hS X)) :
    ∃ s : Finset A, ∀ x : Space.points B S hS X,
      ∃ a : s, x ∈ Set.range (Space.pointsMap B S hS _ (f a.1)) := by
  let R : A → Set (Space.points B S hS X) := fun a => Set.range (Space.pointsMap B S hS _ (f a))
  have hRo : ∀ a, IsOpen (R a) := fun a =>
    (Space.isOpenMap_pointsMap_of_presheafEtale B S hS (f a) (etale a)).isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover R hRo (fun x _ => by
    obtain ⟨a, ha⟩ := hit x
    exact Set.mem_iUnion.2 ⟨a, ha⟩)
  refine ⟨s, fun x => ?_⟩
  obtain ⟨a, has, ha⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨a, has⟩, ha⟩

/-- The site has the coproduct of a finite family. -/
theorem exists_cofan {A : Type u} [Finite A] (U : A → BigFppfOver B S hS) :
    ∃ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V), Nonempty (IsColimit (Cofan.mk V j)) := by
  haveI : HasFiniteCoproducts (BigFppfOver B S hS) := ChartAssembly.hasFiniteCoproducts_site
  have : HasColimit (Discrete.functor U) := inferInstance
  refine ⟨∐ U, Sigma.ι U, ⟨(coproductIsCoproduct U).ofIsoColimit (Cocone.ext (Iso.refl _) (by
    rintro ⟨a⟩; simp))⟩⟩

/-- An affine scheme over a separated scheme is `S`-affine. -/
lemma isAffineHom_structMap [S.IsSeparated] {T : BigFppfOver B S hS} (h : IsAffine ((SCH).obj T)) :
    IsAffineHom (structMap T) := by
  haveI : IsAffineHom (structMap T ≫ terminal.from S) := by
    have : IsAffine ((SCH).obj T) := h
    infer_instance
  exact IsAffineHom.of_comp (structMap T) (terminal.from S)

/-! ### Theorem 6.8 (i) -/

section Main

variable [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- The charts at one point: the pieces of the atlas of a stable open over an affine open of `S`. -/
theorem exists_charts_at
    (h5 : ∀ [AddMonoid.FG M] [DecidableEq M],
      ChartAssembly.Section5FromEffectivity B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X)
    (x : Space.points B S hS X) :
    ∃ (I : Type u) (U : I → BigFppfOver B S hS) (actU : ∀ a, AAction (fppfO B S hS) M (yoneda.obj (U a)))
      (f : ∀ a, yoneda.obj (U a) ⟶ X) (he : ∀ a, IsEquivariant (actU a) act (f a)),
      (∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f a)) ∧
      (∀ a, IsStronglyFPR (he a)) ∧ (∀ a, IsAffine ((SCH).obj (U a))) ∧
      ∃ a, x ∈ Set.range (Space.pointsMap B S hS _ (f a)) := by
  have hfg : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  obtain ⟨O, W, hOa, hW, hq, hst, hL, y, rfl⟩ := exists_stable_open hM hX act x
  have hs : Space.IsSeparated B S hS (toT1 X) :=
    (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS (isTerminal_T1 B S hS) _).1 hsep
  obtain ⟨V, ⟨a⟩⟩ := exists_atlas_of_fp hZ h5 hM hW.1 (isAffine_openBase hOa) (toBase hL)
    (isFinitePresentation_toBase hX hlfp (Space.isQuasiSeparated_of_isSeparated B S hS hs) hW hq hL hOa)
    (isSeparated_toBase hsep hL) (restrictAct act hst)
    (fun k z => toBase_invariant hL _ k z)
  have hιeq : IsEquivariant (restrictAct act hst) act W.ι := ι_equivariant act hst
  let c : ∀ i, yoneda.obj (openObj (a.piece i)) ⟶ X := fun i =>
    yoneda.map (openJ (a.piece i)) ≫ a.v ≫ W.ι
  have hE : ∀ i, IsEquivariant (StronglyFPR.openAct (a.stable i)) act (c i) := fun i =>
    isEquivariant_comp (StronglyFPR.openJ_equivariant (a.stable i))
      (isEquivariant_comp a.equivariant hιeq)
  refine ⟨a.I, fun i => openObj (a.piece i), fun i => StronglyFPR.openAct (a.stable i), c, hE,
    fun i => ?_, fun i => ?_, fun i => a.affine i, ?_⟩
  · have hmap := Space.isMultiplicative_presheaf_etale B S hS
    refine MorphismProperty.comp_mem _ _ _ ?_ (isEtale_comp_ι hW a.etale)
    have : Etale ((SCH).map (openJ (a.piece i))) :=
      inferInstanceAs (Etale (Scheme.Opens.ι (a.piece i)))
    exact (Space.presheaf_yoneda_map_iff B S hS inferInstance _).2 this
  · have hm := StronglyFPR.mono_openJ (V := a.piece i)
    exact isStronglyFPR_mono_comp (StronglyFPR.openJ_equivariant (a.stable i))
      (isEquivariant_comp a.equivariant hιeq)
      (fun T u v h => (cancel_mono (openJ (a.piece i))).mp h)
      (isStronglyFPR_comp_mono a.equivariant hιeq (ι_injective) a.strong)
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
/-- **Theorem 6.8 (i)**, charts, `S` arbitrary, `X` separated over `S` and locally of finite
presentation: charts indexed by `A : Type u`, from affine schemes, each lying over an affine open of
`S` by construction, equivariant, étale, strongly-FPR, jointly covering (`ChartFamily.covers`). The
index set is built from the points of an atlas of `X`, since `|X|` lives in `Type (u + 1)`. -/
theorem exists_charts
    (h5 : ∀ [AddMonoid.FG M] [DecidableEq M],
      ChartAssembly.Section5FromEffectivity B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (A : Type u) (U : A → BigFppfOver B S hS), Nonempty (ChartFamily act A U) := by
  obtain ⟨U0, g, hs, -⟩ := hX.exists_atlas
  have hp := fun u : (SCH).obj U0 => exists_charts_at hZ h5 hM hX hlfp hsep act
    (Space.pointsMap B S hS _ g ((Space.pointsEquivScheme B S hS U0).symm u))
  choose I U actU f he het hst haf hhit using hp
  refine ⟨Σ u : (SCH).obj U0, I u, fun p => U p.1 p.2, ⟨⟨fun p => actU p.1 p.2, fun p => f p.1 p.2,
    fun p => he p.1 p.2, fun p => het p.1 p.2, fun p => hst p.1 p.2, fun p => haf p.1 p.2, fun x => ?_⟩⟩⟩
  obtain ⟨y, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS g hs x
  obtain ⟨i, hi⟩ := hhit (Space.pointsToScheme B S hS U0 y)
  refine ⟨⟨_, i⟩, ?_⟩
  have e : (Space.pointsEquivScheme B S hS U0).symm (Space.pointsToScheme B S hS U0 y) = y :=
    (Space.pointsEquivScheme B S hS U0).symm_apply_apply y
  rwa [e] at hi

include hZ in
/-- **Theorem 6.8 (i)**, `S` separated: an `EtaleChartFamily` of strongly-FPR charts from affine
schemes, and for each coproduct of the charts in the site a strongly-FPR atlas. The coproduct of an
infinite family need not exist in the site, by the size bound of `BigFppfSite`. -/
theorem thm68_family [S.IsSeparated]
    (h5 : ∀ [AddMonoid.FG M] [DecidableEq M],
      ChartAssembly.Section5FromEffectivity B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (A : Type u) (U : A → BigFppfOver B S hS) (L : EtaleChartFamily act A U),
      (∀ a, IsAffine ((SCH).obj (U a))) ∧ (∀ a, IsStronglyFPR (L.equivariant a)) ∧
      ∀ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V) (hV : IsColimit (Cofan.mk V j)),
        ∃ v : yoneda.obj V ⟶ X, IsStronglyFPRAtlas (coprodAction L.act hV) act v ∧
          ∀ Z : AddSubgroup M, IsZFPRAtlas (coprodAction L.act hV) act v Z := by
  obtain ⟨A, U, ⟨L⟩⟩ := exists_charts hZ h5 hM hX hlfp hsep act
  let E := L.toEtale fun a => isAffineHom_structMap (L.affine a)
  refine ⟨A, U, E, L.affine, L.strong, fun V j hV => ?_⟩
  obtain ⟨v, hv, hat⟩ := exists_atlas_of_family hX E hV
  have h : IsStronglyFPRAtlas (coprodAction E.act hV) act v :=
    ⟨hat, fun Z => isZFPR_coprod hV E hv hat.equivariant fun a => L.strong a Z⟩
  exact ⟨v, h, h.isZFPRAtlas⟩

include hZ in
/-- **Theorem 6.8 (i), quasi-compact clause**, `S` separated, `X` quasi-compact: an `S`-affine atlas,
which is `Z`-FPR for all `Z` at once. -/
theorem thm68_qc [S.IsSeparated]
    (h5 : ∀ [AddMonoid.FG M] [DecidableEq M],
      ChartAssembly.Section5FromEffectivity B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (hq : Space.IsQuasiCompactSpace B S hS X)
    (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v ∧
        (∀ Z : AddSubgroup M, IsZFPRAtlas actV act v Z) ∧ IsSAffineAtlas actV act v := by
  obtain ⟨A, U, ⟨L⟩⟩ := exists_charts hZ h5 hM hX hlfp hsep act
  obtain ⟨s, hs⟩ := exists_finset_hit L.f L.etale L.hit
    ((Space.isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).1 hq)
  let U' : s → BigFppfOver B S hS := fun a => U a.1
  let E : EtaleChartFamily act s U' :=
    { act := fun a => L.actU a.1
      f := fun a => L.f a.1
      equivariant := fun a => L.equivariant a.1
      etale := fun a => L.etale a.1
      isAffineHom := fun a => isAffineHom_structMap (L.affine a.1)
      covers := covers_of_hit (fun a : s => L.f a.1) (fun a : s => L.etale a.1) hs }
  obtain ⟨V, j, ⟨hV⟩⟩ := exists_cofan U'
  obtain ⟨v, hv, hat⟩ := exists_atlas_of_family hX E hV
  have h : IsStronglyFPRAtlas (coprodAction E.act hV) act v :=
    ⟨hat, fun Z => isZFPR_coprod hV E hv hat.equivariant fun a => L.strong a.1 Z⟩
  exact ⟨V, _, v, h, h.isZFPRAtlas, hat, s, inferInstance, _,
    coprod_decomposition E.act hV E.isAffineHom⟩

include hZ in
/-- **Strongly-FPR note, Theorem 1.1 (2)**, **Theorem 6.8 (i)** for `S` affine, `X` separated and of
finite presentation over `S`: a single affine scheme. -/
theorem thm11_affine [IsAffine S]
    (h5 : ∀ [AddMonoid.FG M] [DecidableEq M],
      ChartAssembly.Section5FromEffectivity B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v ∧ IsSAffineAtlas actV act v ∧
        IsAffine ((SCH).obj V) := by
  have hA : IsAffine ((SCH).obj (T1 B S hS)) := inferInstanceAs (IsAffine S)
  have hT := isAlgebraicSpace_yoneda B S hS (T1 B S hS)
  have hqT : Space.IsQuasiCompactSpace B S hS (yoneda.obj (T1 B S hS)) :=
    Space.isQuasiCompact_yoneda_of_compact B S hS _ inferInstance
  have hpb := hfp.2.1 (yoneda.obj (T1 B S hS)) hT hqT (𝟙 _)
  have : IsIso (pullback.snd (𝟙 (yoneda.obj (T1 B S hS))) (toT1 X)) :=
    (IsPullback.of_hasPullback (𝟙 (yoneda.obj (T1 B S hS))) (toT1 X)).flip.isIso_fst_of_isIso
  have hq : Space.IsQuasiCompactSpace B S hS X :=
    Space.IsQuasiCompactSpace.of_iso B S hS hpb (asIso (pullback.snd _ _))
  obtain ⟨V, actV, v, h1, -, h3⟩ := thm68_qc hZ h5 hM hX hfp.1 hsep hq act
  refine ⟨V, actV, v, h1, h3, ?_⟩
  have := (hasFiniteAffineDecomposition_iff _).mp h3.2
  exact isAffine_of_isAffineHom (structMap V)

end Main

/-! ### Theorem 6.8 (ii) -/

section II

variable {A : Type u} {U : A → BigFppfOver B S hS} {act : AAction (fppfO B S hS) M X}

/-- **Theorem 6.8 (ii)**, `M/Z` torsion-free in the form `IrreducibleFibres`, `X` quasi-separated and
not necessarily separated, given the charts. The hypothesis `L` is Alper-Hall-Rydh, Corollary 20.2,
cited by the printed proof; here the chart lemma is available for `X` separated only, and then
`thm68_family` gives a stronger conclusion. -/
theorem thm68_ii_of_charts (hX : IsAlgebraicSpace B S hS X) (L : EtaleChartFamily act A U)
    {V : BigFppfOver B S hS} {j : ∀ a, U a ⟶ V} (hV : IsColimit (Cofan.mk V j)) {Z : AddSubgroup M}
    (hM : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ v : yoneda.obj V ⟶ X, IsZFPRAtlas (coprodAction L.act hV) act v Z :=
  isZFPRAtlas_of_family_irreducible hX L hV hM hirr

/-- **Theorem 6.8 (ii), quasi-compact clause**, given the charts. -/
theorem thm68_ii_qc (hX : IsAlgebraicSpace B S hS X) (L : EtaleChartFamily act A U)
    (hq : Space.IsQuasiCompactSpace B S hS X) {Z : AddSubgroup M}
    (hM : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsZFPRAtlas actV act v Z ∧ IsSAffineAtlas actV act v := by
  obtain ⟨s, hs⟩ := exists_finset_hit L.f L.etale (hit_of_covers hX L.f L.etale L.covers)
    ((Space.isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).1 hq)
  let U' : s → BigFppfOver B S hS := fun a => U a.1
  let E : EtaleChartFamily act s U' :=
    { act := fun a => L.act a.1
      f := fun a => L.f a.1
      equivariant := fun a => L.equivariant a.1
      etale := fun a => L.etale a.1
      isAffineHom := fun a => L.isAffineHom a.1
      covers := covers_of_hit (fun a : s => L.f a.1) (fun a : s => L.etale a.1) hs }
  obtain ⟨V, j, ⟨hV⟩⟩ := exists_cofan U'
  obtain ⟨v, hv⟩ := isZFPRAtlas_of_family_irreducible hX E hV hM hirr
  exact ⟨V, _, v, hv, hv.atlas, s, inferInstance, _, coprod_decomposition E.act hV E.isAffineHom⟩

end II

end

end AlgMag.LimThm

#print axioms AlgMag.LimThm.exists_stable_open
#print axioms AlgMag.LimThm.exists_charts
#print axioms AlgMag.LimThm.thm68_family
#print axioms AlgMag.LimThm.thm68_qc
#print axioms AlgMag.LimThm.thm11_affine
#print axioms AlgMag.LimThm.thm68_ii_of_charts
#print axioms AlgMag.LimThm.thm68_ii_qc
