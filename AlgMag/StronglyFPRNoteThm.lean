/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalThm68Single
import AlgMag.FinalAtlasFree
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.FppfMayerVietoris

/-!
# Existence of strongly-FPR atlases: Theorem 1.1 and Corollary 2.4

Mayeux, *Existence of strongly-FPR atlases*, §2.5, following the printed proofs.

* `thm11_2`: **Theorem 1.1 (2)**, `S` quasi-compact and separated, `X → S` quasi-compact: finitely many affine
  opens `S_i`, the stable opens `X_{S_i}` over the site of `S`, the affine case by change of site
  (`LimThm.exists_atlas_of_fp`), Fact 7.1, and the disjoint union.
* `thm11_2_affine`: the clause "`S` affine: a single affine scheme".
* `thm11_1`, `thm11_1_charts`: **Theorem 1.1 (1)**. Definition 6.1 (iv) asks for `S`-affine pieces, so `S` is separated
  in `thm11_1`, with coproducts in the site; `thm11_1_charts` is the output of the printed proof for any `S`.
* `cor24`: **Corollary 2.4**.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.StronglyFPRNote

open LimThm LimOrbit LimView LimAct

attribute [local instance] Space.pointTopology

noncomputable section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The open `X_O` of `X` over the open `O` of `S`. -/
def overOpen (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (O : S.Opens) : Subfunctor X :=
  (imgSub (yoneda.map (openBaseι (B := B) (hS := hS) O))).preimage (toT1 X)

lemma isOpen_img (O : S.Opens) :
    Space.IsOpenSubspace B S hS (imgSub (yoneda.map (openBaseι (B := B) (hS := hS) O))) :=
  img_isOpen (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) _
    (Space.isFlat_yoneda_map B S hS _ inferInstance)
    (Space.isLocallyOfFinitePresentation_yoneda_map B S hS _ inferInstance)

lemma overOpen_isOpen (hX : IsAlgebraicSpace B S hS X) (O : S.Opens) :
    Space.IsOpenSubspace B S hS (overOpen X O) :=
  Space.isOpenSubspace_preimage B S hS _ _ (isAlgebraicSpace_yoneda B S hS _) hX (isOpen_img O)

lemma overOpen_liesOver (O : S.Opens) : LiesOver (overOpen X O) O := by
  rintro T ⟨x, hx⟩ t
  refine img_liesOver (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) _
    (Space.isFlat_yoneda_map B S hS _ inferInstance)
    (Space.isLocallyOfFinitePresentation_yoneda_map B S hS _ inferInstance)
    (fun U r u => ?_) T ⟨_, hx⟩ t
  have hw : (SCH).map r ≫ structMap (openBase (B := B) (hS := hS) O) = structMap U :=
    congrArg (B.inclusion.map) (Over.w r)
  rw [← hw]
  have hb : structMap (openBase (B := B) (hS := hS) O) ((SCH).map r u) ∈ O := by
    rw [← structMap_toT1 (openBaseι (B := B) (hS := hS) O)]
    have hr : Set.range ((SCH).map (openBaseι (B := B) (hS := hS) O)) =
        (show ((SCH).obj (T1 B S hS)).Opens from O : Set _) := StronglyFPR.range_openJ
    have hm : (SCH).map (openBaseι (B := B) (hS := hS) O) ((SCH).map r u) ∈
        Set.range ((SCH).map (openBaseι (B := B) (hS := hS) O)) := ⟨_, rfl⟩
    rw [hr] at hm
    exact hm
  exact hb

lemma mem_overOpen_of_liesOver {O : S.Opens} {T : (BigFppfOver B S hS)ᵒᵖ}
    (h : ∀ t : (SCH).obj (unop T), structMap (unop T) t ∈ O) (x : X.obj T) :
    x ∈ (overOpen X O).obj T := by
  obtain ⟨l, -⟩ := exists_lift_openBase (B := B) (hS := hS) (O := O) (unop T) h
  have := img_mem (yoneda.map (openBaseι (B := B) (hS := hS) O)) (T := T) l
  change (toT1 X).app T x ∈ (imgSub (yoneda.map (openBaseι (B := B) (hS := hS) O))).obj T
  rwa [show (toT1 X).app T x = (yoneda.map (openBaseι (B := B) (hS := hS) O)).app T l from
    t1_ext _ _]

lemma le_overOpen {W : Subfunctor X} {O : S.Opens} (h : LiesOver W O) : W ≤ overOpen X O :=
  fun T x hx => mem_overOpen_of_liesOver (h T ⟨x, hx⟩) x

/-- `X_O = X ×_S O`. -/
lemma isPullback_overOpen (O : S.Opens) :
    IsPullback (LimThm.toBase (overOpen_liesOver (X := X) O)) (overOpen X O).ι
      (yoneda.map (openBaseι (B := B) (hS := hS) O)) (toT1 X) := by
  have comm := toBase_comp (overOpen_liesOver (X := X) O)
  refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm
    (fun s => Subfunctor.lift s.snd ?_) (fun s => ?_) (fun s => Subfunctor.lift_ι _ _) (fun s m _ h2 => ?_)⟩⟩
  · rintro T _ ⟨q, rfl⟩
    have := img_mem (yoneda.map (openBaseι (B := B) (hS := hS) O)) (T := T) (s.fst.app T q)
    change (toT1 X).app T (s.snd.app T q) ∈ (imgSub (yoneda.map (openBaseι (B := B) (hS := hS) O))).obj T
    rwa [show (toT1 X).app T (s.snd.app T q) =
      (yoneda.map (openBaseι (B := B) (hS := hS) O)).app T (s.fst.app T q) from t1_ext _ _]
  · ext T q
    exact openBase_ext _ _
  · rw [← cancel_mono (overOpen X O).ι, h2]
    exact (Subfunctor.lift_ι _ _).symm

lemma overOpen_qc (hq : Space.IsQuasiCompact B S hS (toT1 X)) {O : S.Opens} (hO : IsAffineOpen O) :
    Space.IsQuasiCompactSpace B S hS (overOpen X O).toFunctor := by
  have hA := isAffine_openBase (B := B) (hS := hS) hO
  have h := hq (yoneda.obj (openBase (B := B) (hS := hS) O)) (isAlgebraicSpace_yoneda B S hS _)
    (Space.isQuasiCompact_yoneda_of_compact B S hS _ inferInstance)
    (yoneda.map (openBaseι (B := B) (hS := hS) O))
  exact Space.IsQuasiCompactSpace.of_iso B S hS h (isPullback_overOpen (X := X) O).isoPullback.symm

variable [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- **Theorem 1.1 (2), `S` affine**, applied to `X_O`, in the site of the base: finitely many affine stable charts,
strongly-FPR by Fact 7.1, hitting the points of `X_O`. -/
theorem exists_charts_over (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqc : Space.IsQuasiCompact B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X)
    {O : S.Opens} (hO : IsAffineOpen O) :
    ∃ (I : Type u) (_ : Finite I) (U : I → BigFppfOver B S hS)
      (actU : ∀ a, AAction (fppfO B S hS) M (yoneda.obj (U a)))
      (f : ∀ a, yoneda.obj (U a) ⟶ X) (he : ∀ a, IsEquivariant (actU a) act (f a)),
      (∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f a)) ∧
      (∀ a, IsStronglyFPR (he a)) ∧ (∀ a, IsAffine ((SCH).obj (U a))) ∧
      ∀ y : Space.points B S hS (overOpen X O).toFunctor, ∃ a,
        Space.pointsMap B S hS _ (overOpen X O).ι y ∈ Set.range (Space.pointsMap B S hS _ (f a)) := by
  have hfg : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  set W := overOpen X O with hWdef
  have hW : Space.IsOpenSubspace B S hS W := overOpen_isOpen hX O
  have hq : Space.IsQuasiCompactSpace B S hS W.toFunctor := overOpen_qc hqc hO
  have hL : LiesOver W O := overOpen_liesOver O
  have hst : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (k : APt (fppfO B S hS) M T) (y : X.obj T),
      y ∈ W.obj T → act.smul k y ∈ W.obj T := fun T k y hy =>
    mem_overOpen_of_liesOver (hL T ⟨y, hy⟩) _
  have hs : Space.IsSeparated B S hS (toT1 X) :=
    (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS (isTerminal_T1 B S hS) _).1 hsep
  obtain ⟨V, ⟨a⟩⟩ := exists_atlas_of_fp hZ ChartAssembly.section5FromEffectivity hM hW.1
    (isAffine_openBase hO) (LimThm.toBase hL)
    (isFinitePresentation_toBase hX hlfp (Space.isQuasiSeparated_of_isSeparated B S hS hs) hW hq hL hO)
    (isSeparated_toBase hsep hL) (restrictAct act hst)
    (fun k z => toBase_invariant hL _ k z)
  have hιeq : IsEquivariant (restrictAct act hst) act W.ι := ι_equivariant act hst
  have hmapE := Space.isMultiplicative_presheaf_etale B S hS
  let c' : ∀ i, yoneda.obj (openObj (a.piece i)) ⟶ W.toFunctor := fun i =>
    yoneda.map (openJ (a.piece i)) ≫ a.v
  have hc'E : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (c' i) := fun i => by
    refine MorphismProperty.comp_mem _ _ _ ?_ a.etale
    have : Etale ((SCH).map (openJ (a.piece i))) :=
      inferInstanceAs (Etale (Scheme.Opens.ι (a.piece i)))
    exact (Space.presheaf_yoneda_map_iff B S hS inferInstance _).2 this
  have hit : ∀ y : Space.points B S hS W.toFunctor, ∃ i,
      y ∈ Set.range (Space.pointsMap B S hS _ (c' i)) := by
    intro y
    obtain ⟨z, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS a.v a.surjective y
    have hτ : Space.pointsToScheme B S hS V z ∈ (iSup a.piece) := by
      rw [a.iSup_eq_top]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hτ
    obtain ⟨w, hw⟩ := Space.surjective_pointsToScheme B S hS (openObj (a.piece i))
      (⟨_, hi⟩ : (a.piece i).toScheme)
    have e0 : Space.pointsMap B S hS _ (yoneda.map (openJ (a.piece i))) w = z :=
      Space.injective_pointsToScheme B S hS V
        (by rw [Space.pointsToScheme_pointsMap_yoneda, hw]; rfl)
    refine ⟨i, w, ?_⟩
    change Space.pointsMap B S hS _ (yoneda.map (openJ (a.piece i)) ≫ a.v) w = _
    rw [Space.pointsMap_comp_apply, e0]
  obtain ⟨t, ht⟩ := exists_finset_hit c' hc'E hit
    ((Space.isQuasiCompactSpace_iff_compactSpace_points B S hS _ hW.1).1 hq)
  let c : ∀ i : t, yoneda.obj (openObj (a.piece i.1)) ⟶ X := fun i =>
    yoneda.map (openJ (a.piece i.1)) ≫ a.v ≫ W.ι
  have hE : ∀ i : t, IsEquivariant (StronglyFPR.openAct (a.stable i.1)) act (c i) := fun i =>
    isEquivariant_comp (StronglyFPR.openJ_equivariant (a.stable i.1))
      (isEquivariant_comp a.equivariant hιeq)
  refine ⟨t, inferInstance, fun i => openObj (a.piece i.1), fun i => StronglyFPR.openAct (a.stable i.1),
    c, hE, fun i => ?_, fun i => ?_, fun i => a.affine i.1, fun y => ?_⟩
  · refine MorphismProperty.comp_mem _ _ _ ?_ (isEtale_comp_ι hW a.etale)
    have : Etale ((SCH).map (openJ (a.piece i.1))) :=
      inferInstanceAs (Etale (Scheme.Opens.ι (a.piece i.1)))
    exact (Space.presheaf_yoneda_map_iff B S hS inferInstance _).2 this
  · have hm := StronglyFPR.mono_openJ (V := a.piece i.1)
    exact isStronglyFPR_mono_comp (StronglyFPR.openJ_equivariant (a.stable i.1))
      (isEquivariant_comp a.equivariant hιeq)
      (fun T u v h => (cancel_mono (openJ (a.piece i.1))).mp h)
      (isStronglyFPR_comp_mono a.equivariant hιeq (ι_injective) a.strong)
  · obtain ⟨i, w, rfl⟩ := ht y
    refine ⟨i, w, ?_⟩
    change Space.pointsMap B S hS _ (c' i.1 ≫ W.ι) w = _
    rw [Space.pointsMap_comp_apply]

include hZ in
/-- **Theorem 1.1 (2)**, `S` quasi-compact and separated, `X` separated, locally of finite presentation and
quasi-compact over `S`: an `S`-affine strongly-FPR atlas. Printed proof: finite affine cover `S_i` of `S`, the atlas of
each `X_{S_i}`, Fact 7.1, disjoint union. -/
theorem thm11_2 [S.IsSeparated] [CompactSpace S] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqc : Space.IsQuasiCompact B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v ∧ IsSAffineAtlas actV act v := by
  -- the finite affine cover
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun O : S.affineOpens => ((O : S.Opens) : Set S)) (fun O => O.1.isOpen) (fun x _ => by
      obtain ⟨A, hA, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.2 ⟨⟨A, hA⟩, hx⟩)
  have hch := fun O : s => exists_charts_over hZ hM hX hlfp hqc hsep act O.1.2
  choose I hI U actU f he het hst haf hhit using hch
  let A := Σ O : s, I O
  let U' : A → BigFppfOver B S hS := fun p => U p.1 p.2
  have hitA : ∀ x : Space.points B S hS X, ∃ a : A, x ∈ Set.range (Space.pointsMap B S hS _ (f a.1 a.2)) := by
    intro x
    obtain ⟨⟨O, hO⟩, W, -, -, hL, y, rfl⟩ := exists_cover hX (fun O : s => (O.1 : S.Opens))
      (fun t => by
        obtain ⟨O, hOs, ht⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ t))
        exact ⟨⟨O, hOs⟩, ht⟩) x
    have hle := le_overOpen hL
    obtain ⟨a, ha⟩ := hhit ⟨O, hO⟩ (Space.pointsMap B S hS _ (Subfunctor.homOfLe hle) y)
    refine ⟨⟨⟨O, hO⟩, a⟩, ?_⟩
    rwa [← Space.pointsMap_comp_apply, Subfunctor.homOfLe_ι] at ha
  let E : EtaleChartFamily act A U' :=
    { act := fun a => actU a.1 a.2
      f := fun a => f a.1 a.2
      equivariant := fun a => he a.1 a.2
      etale := fun a => het a.1 a.2
      isAffineHom := fun a => isAffineHom_structMap (haf a.1 a.2)
      covers := covers_of_hit (fun a : A => f a.1 a.2) (fun a : A => het a.1 a.2) hitA }
  obtain ⟨V, j, ⟨hV⟩⟩ := exists_cofan U'
  obtain ⟨v, hv, hat⟩ := exists_atlas_of_family hX E hV
  have h : IsStronglyFPRAtlas (coprodAction E.act hV) act v :=
    ⟨hat, fun Z => isZFPR_coprod hV E hv hat.equivariant fun a => hst a.1 a.2 Z⟩
  exact ⟨V, _, v, h, hat, A, inferInstance, _, coprod_decomposition E.act hV E.isAffineHom⟩

include hZ in
/-- **Theorem 1.1 (2)**, last clause: `S` affine, a single affine scheme. -/
theorem thm11_2_affine [IsAffine S] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqc : Space.IsQuasiCompact B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v ∧ IsSAffineAtlas actV act v ∧
        IsAffine ((SCH).obj V) := by
  obtain ⟨V, actV, v, h1, h3⟩ := thm11_2 hZ hM hX hlfp hqc hsep act
  refine ⟨V, actV, v, h1, h3, ?_⟩
  have := (hasFiniteAffineDecomposition_iff _).mp h3.2
  exact isAffine_of_isAffineHom (structMap V)

include hZ in
/-- **Theorem 1.1 (1)**, output of the printed proof (orbits `D(M)·V`, `LimOrbit.exists_cover`, `LimOrbit.exists_orbit`,
through `LimThm.exists_stable_open`), for any `S`: equivariant étale strongly-FPR morphisms from affine schemes, jointly
surjective, indexed by `Type u`. They are not `S`-affine in general, see `thm11_1`. -/
theorem thm11_1_charts (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (A : Type u) (U : A → BigFppfOver B S hS), Nonempty (ChartFamily act A U) :=
  exists_charts hZ ChartAssembly.section5FromEffectivity hM hX hlfp hsep act

include hZ in
/-- **Theorem 1.1 (1)**, `S` separated (so that Definition 6.1 (iv) holds), with `hco`, coproducts of `Type u`-families
in the site `B`: `AlgMag.Final.thm68_single`, whose proof is the printed one. -/
theorem thm11_1 [S.IsSeparated]
    (hco : ∀ (A : Type u) (U : A → BigFppfOver B S hS),
      ∃ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V), Nonempty (IsColimit (Cofan.mk V j)))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V)) (v : yoneda.obj V ⟶ X),
      IsStronglyFPRAtlas actV act v :=
  let ⟨V, actV, v, h, _⟩ := Final.thm68_single hZ hco hM hX hlfp hsep act
  ⟨V, actV, v, h⟩

include hZ in
/-- **Corollary 2.4**: `S` quasi-compact and separated, `X` separated of finite presentation over `S`: finitely many pure
magnets. Theorem 1.1 (2) and `thm154_ii_lfp`. -/
theorem cor24 [S.IsSeparated] [CompactSpace S] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep' : Space.IsSeparatedOver B S hS X)
    (hfp' : Space.IsFinitePresentation B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X) :
    (pureMagnets (attractorImage act)).Finite := by
  obtain ⟨V, actV, v, h1, h3⟩ := thm11_2 hZ hM hX hfp'.1 hfp'.2.1 hsep' act
  haveI := (hasFiniteAffineDecomposition_iff _).mp h3.2
  have hs : Space.IsSeparated B S hS (toT1 X) :=
    (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS (isTerminal_T1 B S hS) _).1 hsep'
  have hsep : IsSeparatedOver X := by
    have e : AlgMag.toBase X = toT1 X := toT1_ext _ _
    change Space.IsSeparated B S hS (AlgMag.toBase X)
    rw [e]
    exact hs
  let e2 := (isTerminal_T1 B S hS).uniqueUpToIso terminalIsTerminal
  have hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X) :=
    (Space.isFinitePresentation_of_arrowIso B S hS (toT1 X) (terminal.from X) (𝟙 _) e2.hom
      (terminal.hom_ext _ _) hfp').1
  exact (thm154_ii_lfp h1 hX hsep hfp).1

end

end AlgMag.StronglyFPRNote

#print axioms AlgMag.StronglyFPRNote.thm11_2
#print axioms AlgMag.StronglyFPRNote.thm11_2_affine
#print axioms AlgMag.StronglyFPRNote.thm11_1_charts
#print axioms AlgMag.StronglyFPRNote.thm11_1
#print axioms AlgMag.StronglyFPRNote.cor24
