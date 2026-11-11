/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesLimitAction
import AlgMag.ChartStratumImage
import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification

/-!
# Orbits of quasi-compact opens

Mayeux, *Algebraic Magnetism*, proof of Theorem A.1: "Because `G → S` is flat and finitely presented,
the orbit in `X` of an open quasi-compact subspace `W ⊂ X` is open and quasi-compact. We may replace
`X` by one such orbit."

* `AlgMag.LimOrbit.actGood_of_fg`, `flat_actSnd`: `D(M)_S` is flat and finitely presented over `S`.
* `AlgMag.LimOrbit.exists_orbit`: the orbit of a quasi-compact open.
* `AlgMag.LimOrbit.exists_cover`: quasi-compact opens over the members of an open cover of `S`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.LimOrbit

open LimAct

attribute [local instance] Space.pointTopology

noncomputable section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-! ### `D(M)_S` -/

section Rep

variable {M : Type u} [AddCommGroup M]

variable (B S hS) in
/-- `S` as an object of its own site. -/
def T1 : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

variable (B S hS) in
def isTerminal_T1 : IsTerminal (yoneda.obj (T1 B S hS)) :=
  (Over.mkIdTerminal).isTerminalObj yoneda _

lemma t1_ext {V : BigFppfOver B S hS} (a b : V ⟶ T1 B S hS) : a = b :=
  (Over.mkIdTerminal).hom_ext a b

variable (B S hS) in
/-- `D(M)_S`, as an object of the site. -/
def G0 (h : B.Contains (Spec (ZMon M))) : BigFppfOver B S hS := monAffObj M h (T1 B S hS)

variable (B S hS) in
/-- `D(M)_S → S`. -/
def G0π (h : B.Contains (Spec (ZMon M))) : G0 B S hS h ⟶ T1 B S hS := gπ h (T1 B S hS)

variable (B S hS) in
/-- Points of `D(M)_S` are points of `D(M)`. -/
def toApt (h : B.Contains (Spec (ZMon M))) :
    yoneda.obj (G0 B S hS h) ⟶ aptP (fppfO B S hS) M where
  app T := ↾fun t => APt.res t.op (gc h (T1 B S hS))
  naturality T T' f := tex fun t => by
    change APt.res (f.unop ≫ t).op _ = APt.res f (APt.res t.op _)
    exact APt.res_comp t.op f _

instance isIso_toApt (h : B.Contains (Spec (ZMon M))) : IsIso (toApt (M := M) B S hS h) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun T => ?_
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hab' : APt.res (Quiver.Hom.op a) (gc h (T1 B S hS)) =
        APt.res (Quiver.Hom.op b) (gc h (T1 B S hS)) := hab
    apply (SCH).map_injective
    refine MonAff.hom_ext' ?_ fun p => DFunLike.congr_fun hab' p
    have h3 : (SCH).map a ≫ (SCH).map (G0π B S hS h) = (SCH).map b ≫ (SCH).map (G0π B S hS h) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ (t1_ext _ _)
    exact h3
  · refine ⟨gLift h (Over.homMk (unop T).hom (by simp [T1]) : unop T ⟶ T1 B S hS) a, ?_⟩
    exact res_gLift h _ a

/-- `D(M)_S → S` is flat. -/
lemma flat_G0π (h : B.Contains (Spec (ZMon M))) : Flat ((SCH).map (G0π (M := M) B S hS h)) := by
  have := ChartStratum.flat_terminal_zmon.{u} M
  exact inferInstanceAs (Flat (pullback.fst _ _))

/-- `D(M)_S → S` is of finite presentation. -/
lemma fp_G0π [AddMonoid.FG M] (h : B.Contains (Spec (ZMon M))) :
    FinitePresentation ((SCH).map (G0π (M := M) B S hS h)) := by
  have hl := ChartStratum.lfp_terminal_zmon.{u} M
  have ha : IsAffineHom (terminal.from (Spec (ZMon M))) := by
    rw [ChartStratum.terminal_from_zmon]; infer_instance
  have h1 : LocallyOfFinitePresentation ((SCH).map (G0π (M := M) B S hS h)) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ _))
  have q1 : QuasiCompact (terminal.from (Spec (ZMon M))) := inferInstance
  have q2 : QuasiSeparated (terminal.from (Spec (ZMon M))) := inferInstance
  have h2 : QuasiCompact ((SCH).map (G0π (M := M) B S hS h)) :=
    inferInstanceAs (QuasiCompact (pullback.fst _ _))
  have h3 : QuasiSeparated ((SCH).map (G0π (M := M) B S hS h)) :=
    inferInstanceAs (QuasiSeparated (pullback.fst _ _))
  exact ⟨h1, h2, h3⟩

/-- `D(M) × Y → Y` is a base change of `D(M)_S → S`. -/
lemma isPullback_actSnd (h : B.Contains (Spec (ZMon M))) (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsPullback (actGrp (fppfO B S hS) M Y ≫ inv (toApt B S hS h)) (actSnd (fppfO B S hS) M Y)
      (yoneda.map (G0π B S hS h)) ((isTerminal_T1 B S hS).from Y) := by
  have hT := isTerminal_T1 B S hS
  exact ⟨⟨(isTerminal_T1 B S hS).hom_ext _ _⟩, ⟨PullbackCone.IsLimit.mk
      (f := yoneda.map (G0π B S hS h)) (g := (isTerminal_T1 B S hS).from Y)
      (fst := actGrp (fppfO B S hS) M Y ≫ inv (toApt B S hS h)) (snd := actSnd (fppfO B S hS) M Y)
      ((isTerminal_T1 B S hS).hom_ext _ _)
      (fun (s : PullbackCone (yoneda.map (G0π B S hS h)) ((isTerminal_T1 B S hS).from Y)) =>
        actLift (s.fst ≫ toApt B S hS h) s.snd)
      (fun s => by
        rw [← Category.assoc, actLift_grp, Category.assoc, IsIso.hom_inv_id, Category.comp_id])
      (fun s => rfl)
      (fun s m h₁ h₂ => act_hom_ext (by
        rw [actLift_grp, ← h₁, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id])
        (by rw [actLift_snd]; exact h₂))⟩⟩

/-- **`ActGood`** over an arbitrary `S`, for `M` finitely generated. -/
theorem actGood_of_fg [AddMonoid.FG M] (h : B.Contains (Spec (ZMon M))) : ActGood B S hS M :=
  actGood_of_representable (isTerminal_T1 B S hS) (G0π B S hS h) (asIso (toApt B S hS h)).symm
    (Space.isFinitePresentation_yoneda_map B S hS _ (fp_G0π h))

/-- "`G → S` is flat": `D(M) × Y → Y` is flat. -/
theorem flat_actSnd [AddMonoid.FG M] (h : B.Contains (Spec (ZMon M)))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) :
    Space.IsFlat B S hS (actSnd (fppfO B S hS) M Y) :=
  (ChartStratum.flat_lfp_bc (actGood_of_fg h Y hY).1 (isAlgebraicSpace_yoneda B S hS _) hY
    (isAlgebraicSpace_yoneda B S hS _) (isPullback_actSnd h Y)
    (Space.isFlat_yoneda_map B S hS _ (flat_G0π h))
    (Space.isLocallyOfFinitePresentation_yoneda_map B S hS _
      (fp_G0π h).locallyOfFinitePresentation)).1

end Rep

/-! ### The open image of a flat morphism -/

section Image

variable {R X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A subfunctor lies over the open `O` of `S`: the structure morphisms of the objects on which it has
a section factor through `O`. -/
def LiesOver (W : Subfunctor X) (O : S.Opens) : Prop :=
  ∀ (T : (BigFppfOver B S hS)ᵒᵖ), (∃ s, s ∈ W.obj T) → ∀ t : (SCH).obj (unop T),
    structMap (unop T) t ∈ O

/-- The subfunctor cut out by the image of `g` on points. -/
def imgSub (g : R ⟶ X) : Subfunctor X :=
  Space.openSubspaceOfPoints B S hS X (Set.range (Space.pointsMap B S hS R g))

lemma img_mem (g : R ⟶ X) {T : (BigFppfOver B S hS)ᵒᵖ} (r : R.obj T) : g.app T r ∈ (imgSub g).obj T :=
  Space.range_le_openSubspaceOfPoints_range_pointsMap g T ⟨r, rfl⟩

variable (hR : IsAlgebraicSpace B S hS R) (hX : IsAlgebraicSpace B S hS X) (g : R ⟶ X)
  (hf : Space.IsFlat B S hS g) (hl : Space.IsLocallyOfFinitePresentation B S hS g)

include hR hX hf hl

lemma img_isOpen : Space.IsOpenSubspace B S hS (imgSub g) :=
  Space.isOpenSubspace_flatImage B S hS
    (ObjectProperty.homMk g : (⟨R, hR⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) hf hl

lemma img_qc (hq : Space.IsQuasiCompactSpace B S hS R) :
    Space.IsQuasiCompactSpace B S hS (imgSub g).toFunctor := by
  let g' : (⟨R, hR⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩ := ObjectProperty.homMk g
  exact Space.IsQuasiCompactSpace.of_isSurjective B S hS hR (img_isOpen hR hX g hf hl).1
    (Space.isSurjective_flatImageLift B S hS g' hf hl) hq

/-- A section of the image lifts to the source, along a surjective flat lfp map of the site. -/
theorem exists_lift {T : BigFppfOver B S hS} {x : X.obj (op T)} (hx : x ∈ (imgSub g).obj (op T)) :
    ∃ (U : BigFppfOver B S hS) (q : U ⟶ T) (r : R.obj (op U)),
      g.app (op U) r = X.map q.op x ∧ Surjective ((SCH).map q) := by
  let cR : AlgebraicSpaces B S hS := ⟨R, hR⟩
  let cX : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let cT : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let g' : cR ⟶ cX := ObjectProperty.homMk g
  let t : cT ⟶ cX := ObjectProperty.homMk (yonedaEquiv.symm x)
  have hr : Subfunctor.range (yonedaEquiv.symm x) ≤ imgSub g := by
    rintro T' _ ⟨y, rfl⟩
    have : (yonedaEquiv.symm x).app T' y = X.map y.op x := rfl
    rw [this]
    exact (imgSub g).map y.op hx
  let a : cT ⟶ Space.flatImage B S hS g' hf hl := ObjectProperty.homMk (Subfunctor.lift _ hr)
  have ha : a ≫ Space.flatImageι B S hS g' hf hl = t :=
    ObjectProperty.hom_ext _ (Subfunctor.lift_ι _ hr)
  obtain ⟨h1, h2, h3⟩ := Space.surjectiveFlatLfp_pullback_snd_of_fac B S hS g' hf hl t a ha
  obtain ⟨U, q, u, hu, -, -, hqS⟩ := ChartStratum.exists_fppf_lift (pullback g' t).property _ h1 h2 h3
  refine ⟨U, q, yonedaEquiv (u ≫ (pullback.fst g' t).hom), ?_, hqS⟩
  have e : (pullback.fst g' t).hom ≫ g = (pullback.snd g' t).hom ≫ yonedaEquiv.symm x :=
    congrArg (fun k => k.hom) (pullback.condition (f := g') (g := t))
  have e2 : (u ≫ (pullback.fst g' t).hom) ≫ g = yoneda.map q ≫ yonedaEquiv.symm x := by
    rw [Category.assoc, e, ← Category.assoc, hu]
  have e3 := congrArg yonedaEquiv e2
  rw [yonedaEquiv_comp] at e3
  refine e3.trans ?_
  rw [yonedaEquiv_comp]
  simp [yonedaEquiv]

/-- The image lies over `O` when every section of the source does. -/
theorem img_liesOver {O : S.Opens}
    (h : ∀ (U : BigFppfOver B S hS), R.obj (op U) → ∀ u : (SCH).obj U, structMap U u ∈ O) :
    LiesOver (imgSub g) O := by
  rintro T ⟨x, hx⟩ t
  obtain ⟨U, q, r, -, hq⟩ := exists_lift hR hX g hf hl (T := unop T) hx
  obtain ⟨u, rfl⟩ := hq.surj t
  have hw : (SCH).map q ≫ structMap (unop T) = structMap U := congrArg (B.inclusion.map) (Over.w q)
  have := h U r u
  rw [← hw] at this
  exact this

end Image

/-! ### Orbits -/

section Orbit

variable {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (act : AAction (fppfO B S hS) M X)

/-- `(h, x) ↦ (h, h • x)`. -/
def shear : actP (fppfO B S hS) M X ⟶ actP (fppfO B S hS) M X :=
  actLift (actGrp _ M X) (ofAct act)

instance isIso_shear : IsIso (shear act) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun T => ?_
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hab' : (a.1, act.smul a.1 a.2) = (b.1, act.smul b.1 b.2) := hab
    have e1 : a.1 = b.1 := (Prod.mk.inj hab').1
    have e2 : act.smul a.1 a.2 = act.smul b.1 b.2 := (Prod.mk.inj hab').2
    refine Prod.ext e1 ?_
    rw [e1] at e2
    have := congrArg (act.smul (APt.inv b.1)) e2
    rwa [← act.mul_smul, ← act.mul_smul, APt.inv_mul, act.one_smul, act.one_smul] at this
  · refine ⟨(a.1, act.smul (APt.inv a.1) a.2), Prod.ext rfl ?_⟩
    change act.smul a.1 (act.smul (APt.inv a.1) a.2) = a.2
    rw [← act.mul_smul, mul_comm, APt.inv_mul, act.one_smul]

/-- The action map is flat and lfp: it is the projection after an automorphism of `D(M) × X`. -/
lemma ofAct_flat_lfp [AddMonoid.FG M] (h : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) :
    Space.IsFlat B S hS (ofAct act) ∧ Space.IsLocallyOfFinitePresentation B S hS (ofAct act) := by
  have hA := (actGood_of_fg h X hX).1
  have sq : IsPullback (shear act) (ofAct act) (actSnd _ M X) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
  exact ChartStratum.flat_lfp_bc hA hA hX hX sq (flat_actSnd h hX) (actGood_of_fg h X hX).2.1

/-- `D(M) × W → X`, `(h, w) ↦ h • w`. -/
def orbMap (W : Subfunctor X) : actP (fppfO B S hS) M W.toFunctor ⟶ X :=
  actMap _ M W.ι ≫ ofAct act

/-- The orbit of `W`. -/
def orbit (W : Subfunctor X) : Subfunctor X := imgSub (orbMap act W)

variable [AddMonoid.FG M] (h : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
  {W : Subfunctor X} (hW : Space.IsOpenSubspace B S hS W)

include h hX hW

lemma orbMap_flat_lfp :
    Space.IsFlat B S hS (orbMap act W) ∧
      Space.IsLocallyOfFinitePresentation B S hS (orbMap act W) := by
  have hR := (actGood_of_fg h _ hW.1).1
  have hA := (actGood_of_fg h X hX).1
  have hE := Space.isEtale_of_isOpenImmersion B S hS hW.2
  obtain ⟨f1, l1⟩ := ChartStratum.flat_lfp_bc hR hW.1 hA hX
    (isPullback_actMap (𝒪 := fppfO B S hS) (M := M) W.ι).flip
    (Space.isFlat_of_isEtale B S hS hE) (Space.isLocallyOfFinitePresentation_of_isEtale B S hS hE)
  obtain ⟨f2, l2⟩ := ofAct_flat_lfp act h hX
  exact ⟨Space.isFlat_comp B S hS hR hA hX _ _ f1 f2,
    Space.isLocallyOfFinitePresentation_comp B S hS hR hA hX _ _ l1 l2⟩

theorem orbit_isOpen : Space.IsOpenSubspace B S hS (orbit act W) :=
  have hf := orbMap_flat_lfp act h hX hW
  img_isOpen (actGood_of_fg h _ hW.1).1 hX _ hf.1 hf.2

theorem le_orbit : W ≤ orbit act W := by
  intro T x hx
  have := img_mem (orbMap act W) (T := T) ((1, ⟨x, hx⟩) : APt _ M T × W.toFunctor.obj T)
  have e : (orbMap act W).app T ((1, ⟨x, hx⟩) : APt _ M T × W.toFunctor.obj T) = x :=
    act.one_smul x
  rwa [e] at this

/-- The orbit of a quasi-compact open is quasi-compact: `D(M) × W` is of finite presentation over
`W`. -/
theorem orbit_qc (hq : Space.IsQuasiCompactSpace B S hS W.toFunctor) :
    Space.IsQuasiCompactSpace B S hS (orbit act W).toFunctor := by
  have hf := orbMap_flat_lfp act h hX hW
  have hG := actGood_of_fg (hS := hS) h _ hW.1
  have hQ := hG.2.2.1
  have : IsIso (pullback.snd (𝟙 W.toFunctor) (actSnd (fppfO B S hS) M W.toFunctor)) :=
    (IsPullback.of_hasPullback (𝟙 W.toFunctor) (actSnd (fppfO B S hS) M W.toFunctor)).flip.isIso_fst_of_isIso
  have hRq : Space.IsQuasiCompactSpace B S hS (actP (fppfO B S hS) M W.toFunctor) :=
    Space.IsQuasiCompactSpace.of_iso B S hS (hQ _ hW.1 hq (𝟙 _)) (asIso (pullback.snd _ _))
  exact img_qc hG.1 hX _ hf.1 hf.2 hRq

/-- The orbit is stable under `D(M)`. -/
theorem smul_mem_orbit {T : (BigFppfOver B S hS)ᵒᵖ} (k : APt (fppfO B S hS) M T) {x : X.obj T}
    (hx : x ∈ (orbit act W).obj T) : act.smul k x ∈ (orbit act W).obj T := by
  have hf := orbMap_flat_lfp act h hX hW
  obtain ⟨U, q, r, e, hq⟩ := exists_lift (actGood_of_fg h _ hW.1).1 hX _ hf.1 hf.2 (T := unop T) hx
  refine ChartStratum.mem_of_surjective _ q hq _ ?_
  rw [act.map_smul, ← e]
  have e' : act.smul (APt.res q.op k) ((orbMap act W).app (op U) r) =
      (orbMap act W).app (op U) (APt.res q.op k * r.1, r.2) :=
    (act.mul_smul _ _ _).symm
  rw [e']
  exact img_mem (orbMap act W) _

/-- The action does not change the structure morphism: the orbit lies over what `W` lies over. -/
theorem orbit_liesOver {O : S.Opens} (hO : LiesOver W O) : LiesOver (orbit act W) O := by
  have hf := orbMap_flat_lfp act h hX hW
  refine img_liesOver (actGood_of_fg h _ hW.1).1 hX _ hf.1 hf.2 fun U r u => ?_
  exact hO (op U) ⟨_, r.2.2⟩ u

/-- **Proof of Theorem A.1**: "the orbit in `X` of an open quasi-compact subspace `W ⊂ X` is open and
quasi-compact". -/
theorem exists_orbit (hq : Space.IsQuasiCompactSpace B S hS W.toFunctor) :
    ∃ W' : Subfunctor X, Space.IsOpenSubspace B S hS W' ∧ W ≤ W' ∧
      Space.IsQuasiCompactSpace B S hS W'.toFunctor ∧
      (∀ (T : (BigFppfOver B S hS)ᵒᵖ) (k : APt (fppfO B S hS) M T) (x : X.obj T),
        x ∈ W'.obj T → act.smul k x ∈ W'.obj T) ∧
      ∀ O : S.Opens, LiesOver W O → LiesOver W' O :=
  ⟨orbit act W, orbit_isOpen act h hX hW, le_orbit act h hX hW, orbit_qc act h hX hW hq,
    fun _ k _ hx => smul_mem_orbit act h hX hW k hx, fun _ hO => orbit_liesOver act h hX hW hO⟩

end Orbit

/-! ### Covers -/

/-- Every point of `X` lies in a quasi-compact open subspace over a member of a given open cover of
`S`. (Affineness of the members is not needed.) -/
theorem exists_cover {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {ι : Type*} (𝒰 : ι → S.Opens) (h𝒰 : ∀ s : S, ∃ i, s ∈ 𝒰 i) (x : Space.points B S hS X) :
    ∃ (i : ι) (W : Subfunctor X), Space.IsOpenSubspace B S hS W ∧
      Space.IsQuasiCompactSpace B S hS W.toFunctor ∧ LiesOver W (𝒰 i) ∧
      x ∈ Set.range (Space.pointsMap B S hS W.toFunctor W.ι) := by
  obtain ⟨U, f, hs, he⟩ := hX.exists_atlas
  obtain ⟨y, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS f hs x
  set v := Space.pointsToScheme B S hS U y with hv
  obtain ⟨i, hi⟩ := h𝒰 (structMap U v)
  obtain ⟨A, hA, hvA, hAO⟩ := exists_isAffineOpen_mem_and_subset
    (x := v) (U := (structMap U) ⁻¹ᵁ 𝒰 i) hi
  let V := Space.opensObject B S hS U A
  let j : V ⟶ U := Space.opensObjectι B S hS U A
  have hO : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hE : Space.IsEtale B S hS f := (Space.isEtale_iff_presheaf_of_yoneda B S hS f).2 he
  have hjF : Flat ((SCH).map j) := inferInstanceAs (Flat A.ι)
  have hjL : LocallyOfFinitePresentation ((SCH).map j) :=
    inferInstanceAs (LocallyOfFinitePresentation A.ι)
  let c : yoneda.obj V ⟶ X := yoneda.map j ≫ f
  have hcF : Space.IsFlat B S hS c := Space.isFlat_comp B S hS hO hU hX _ _
    (Space.isFlat_yoneda_map B S hS j hjF) (Space.isFlat_of_isEtale B S hS hE)
  have hcL : Space.IsLocallyOfFinitePresentation B S hS c :=
    Space.isLocallyOfFinitePresentation_comp B S hS hO hU hX _ _
      (Space.isLocallyOfFinitePresentation_yoneda_map B S hS j hjL)
      (Space.isLocallyOfFinitePresentation_of_isEtale B S hS hE)
  have hCompact : CompactSpace ((SCH).obj V) := by
    have : IsAffine A.toScheme := hA
    exact inferInstanceAs (CompactSpace A.toScheme)
  refine ⟨i, imgSub c, img_isOpen hO hX c hcF hcL,
    img_qc hO hX c hcF hcL (Space.isQuasiCompactSpace_yoneda_obj B S hS hCompact),
    img_liesOver hO hX c hcF hcL fun W' r u => ?_, ?_⟩
  · have hw : (SCH).map r ≫ structMap V = structMap W' := congrArg (B.inclusion.map) (Over.w r)
    rw [← hw]
    exact hAO ((SCH).map r u).2
  · obtain ⟨w, hw⟩ := Space.surjective_pointsToScheme B S hS V (⟨v, hvA⟩ : A.toScheme)
    have hjw : Space.pointsMap B S hS (yoneda.obj V) (yoneda.map j) w = y :=
      Space.injective_pointsToScheme B S hS U
        (by rw [Space.pointsToScheme_pointsMap, hw]; rfl)
    have hrange : Space.pointsMap B S hS (yoneda.obj V) c w ∈
        Set.range (Space.pointsMap B S hS (yoneda.obj V) c) := ⟨w, rfl⟩
    have key : Set.range (Space.pointsMap B S hS (imgSub c).toFunctor (imgSub c).ι) =
        Set.range (Space.pointsMap B S hS (yoneda.obj V) c) :=
      Space.range_pointsMap_ι_openSubspaceOfPoints B S hS _
    rw [key]
    have : Space.pointsMap B S hS (yoneda.obj V) c w = Space.pointsMap B S hS _ f y := by
      rw [Space.pointsMap_comp_apply, hjw]
    rwa [this] at hrange

end

end AlgMag.LimOrbit

#print axioms AlgMag.LimOrbit.actGood_of_fg
#print axioms AlgMag.LimOrbit.flat_actSnd
#print axioms AlgMag.LimOrbit.exists_orbit
#print axioms AlgMag.LimOrbit.exists_cover
