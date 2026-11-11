/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumFlat
import StacksFrontier.AlgebraicGeometry.Spaces.FlatImageOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace

/-!
# The open orbit of an étale chart (affine stratum lemma, step 3)

For an étale chart `c : W → X` the map `D(M) × W → X`, `(a, t) ↦ a • c t`, is flat and locally of
finite presentation. Its image is a `D(M)`-stable open subspace, and each of its points lifts to
`D(M) × W` along a surjective, flat, locally finitely presented map of the site.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A point of `D(⊤)` as a point of `D(M)`. -/
noncomputable def topPt {T : (BigFppfOver B S hS)ᵒᵖ}
    (a : APt (fppfO B S hS) (⊤ : AddSubgroup M).toAddSubmonoid T) : APt (fppfO B S hS) M T where
  toFun w := a (Multiplicative.ofAdd ⟨Multiplicative.toAdd w, trivial⟩)
  map_one' := map_one a
  map_mul' x y := by rw [← map_mul a]; rfl

/-- A point of `D(M)` as a point of `D(⊤)`. -/
noncomputable def ptTop {T : (BigFppfOver B S hS)ᵒᵖ} (a : APt (fppfO B S hS) M T) :
    APt (fppfO B S hS) (⊤ : AddSubgroup M).toAddSubmonoid T :=
  APt.toMagnet (⊤ : AddSubgroup M).toAddSubmonoid a

@[simp] lemma topPt_ptTop {T : (BigFppfOver B S hS)ᵒᵖ} (a : APt (fppfO B S hS) M T) :
    topPt (ptTop a) = a := MonoidHom.ext fun _ => rfl

lemma topPt_one {T : (BigFppfOver B S hS)ᵒᵖ} :
    topPt (1 : APt (fppfO B S hS) (⊤ : AddSubgroup M).toAddSubmonoid T) = 1 :=
  MonoidHom.ext fun _ => rfl

lemma topPt_mul {T : (BigFppfOver B S hS)ᵒᵖ}
    (g h : APt (fppfO B S hS) (⊤ : AddSubgroup M).toAddSubmonoid T) :
    topPt (g * h) = topPt g * topPt h := MonoidHom.ext fun _ => rfl

lemma topPt_res {T T' : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ T')
    (h : APt (fppfO B S hS) (⊤ : AddSubgroup M).toAddSubmonoid T) :
    topPt (APt.res f h) = APt.res f (topPt h) := MonoidHom.ext fun _ => rfl

/-- `D(M)` acting through `D(⊤)`. -/
noncomputable def topAct (act : AAction (fppfO B S hS) M X) :
    AAction (fppfO B S hS) (⊤ : AddSubgroup M).toAddSubmonoid X where
  smul a x := act.smul (topPt a) x
  one_smul x := by rw [topPt_one]; exact act.one_smul x
  mul_smul g h x := by rw [topPt_mul]; exact act.mul_smul (topPt g) (topPt h) x
  map_smul f h x := by rw [topPt_res]; exact act.map_smul f (topPt h) x

/-- A base change of a flat morphism locally of finite presentation. -/
theorem flat_lfp_bc {P A C D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hA : IsAlgebraicSpace B S hS A)
    (hC : IsAlgebraicSpace B S hS C) (hD : IsAlgebraicSpace B S hS D)
    {t : P ⟶ A} {l : P ⟶ C} {r : A ⟶ D} {b : C ⟶ D} (sq : IsPullback t l r b)
    (hf : Space.IsFlat B S hS r) (hl : Space.IsLocallyOfFinitePresentation B S hS r) :
    Space.IsFlat B S hS l ∧ Space.IsLocallyOfFinitePresentation B S hS l := by
  let cP : AlgebraicSpaces B S hS := ⟨P, hP⟩
  let cA : AlgebraicSpaces B S hS := ⟨A, hA⟩
  let cC : AlgebraicSpaces B S hS := ⟨C, hC⟩
  let cD : AlgebraicSpaces B S hS := ⟨D, hD⟩
  let t' : cP ⟶ cA := ObjectProperty.homMk t
  let l' : cP ⟶ cC := ObjectProperty.homMk l
  let r' : cA ⟶ cD := ObjectProperty.homMk r
  let b' : cC ⟶ cD := ObjectProperty.homMk b
  have sq' : IsPullback t' l' r' b' :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  exact ⟨(Space.isFlat_isStableUnderBaseChange B S hS).of_isPullback sq' hf,
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq' hl⟩

variable {W : BigFppfOver B S hS} (act : AAction (fppfO B S hS) M X) (c : yoneda.obj W ⟶ X)

/-- `D(⊤) × W → D(⊤) × X`. -/
noncomputable def relLift : relP (yoneda.obj W) (⊤ : AddSubgroup M) ⟶ relP X (⊤ : AddSubgroup M) where
  app T := ↾ fun r => (r.1, c.app T r.2)
  naturality T T' f := by
    ext1
    refine DFunLike.ext _ _ fun r => ?_
    refine Prod.ext rfl ?_
    exact ConcreteCategory.congr_hom (c.naturality f) r.2

lemma relLift_isPullback :
    IsPullback (relLift (M := M) c) relSrc relSrc c := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · rintro x y ⟨e1, e2⟩
    have e1' : (x.1, c.app T x.2) = (y.1, c.app T y.2) := e1
    exact Prod.ext (Prod.mk.inj e1').1 e2
  · intro x₂ x₃ e
    refine ⟨(x₂.1, x₃), ?_, rfl⟩
    exact Prod.ext rfl e.symm

/-- The orbit map `(a, t) ↦ a • c t`. -/
noncomputable def orbMap : relP (yoneda.obj W) (⊤ : AddSubgroup M) ⟶ X :=
  relLift c ≫ relTgt (topAct act)

lemma orbMap_app {T : (BigFppfOver B S hS)ᵒᵖ}
    (r : (relP (yoneda.obj W) (⊤ : AddSubgroup M)).obj T) :
    (orbMap act c).app T r = act.smul (topPt r.1) (c.app T r.2) := rfl

variable [AddGroup.FG M]

instance : AddMonoid.FG (⊤ : AddSubgroup M).toAddSubmonoid := fg_toAddSubmonoid _

/-- **Affine stratum lemma, step 3**: the orbit map of an étale chart is flat and locally of finite
presentation. -/
theorem orbMap_flat_lfp (hX : IsAlgebraicSpace B S hS X) (hc : Space.IsEtale B S hS c) :
    Space.IsFlat B S hS (orbMap act c) ∧
      Space.IsLocallyOfFinitePresentation B S hS (orbMap act c) := by
  have hW := isAlgebraicSpace_yoneda B S hS W
  have hRW := relP_isAlgebraicSpace (Z := (⊤ : AddSubgroup M)) hW
  have hRX := relP_isAlgebraicSpace (Z := (⊤ : AddSubgroup M)) hX
  obtain ⟨f1, l1⟩ := flat_lfp_bc hRW hW hRX hX (relLift_isPullback (M := M) c).flip
    (Space.isFlat_of_isEtale B S hS hc) (Space.isLocallyOfFinitePresentation_of_isEtale B S hS hc)
  obtain ⟨f2, l2, -, -⟩ := relJ_flat_lfp (topAct act) hX
  rw [relJ_target] at f2 l2
  exact ⟨Space.isFlat_comp B S hS hRW hRX hX _ _ f1 f2,
    Space.isLocallyOfFinitePresentation_comp B S hS hRW hRX hX _ _ l1 l2⟩

/-- The open image of the orbit map. -/
noncomputable def orbSub : Subfunctor X :=
  Space.openSubspaceOfPoints B S hS X
    (Set.range (Space.pointsMap B S hS (relP (yoneda.obj W) (⊤ : AddSubgroup M)) (orbMap act c)))

theorem orbSub_isOpen (hX : IsAlgebraicSpace B S hS X) (hc : Space.IsEtale B S hS c) :
    Space.IsOpenSubspace B S hS (orbSub act c) := by
  have hRW := relP_isAlgebraicSpace (Z := (⊤ : AddSubgroup M)) (isAlgebraicSpace_yoneda B S hS W)
  obtain ⟨f, l⟩ := orbMap_flat_lfp act c hX hc
  let g : (⟨_, hRW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩ := ObjectProperty.homMk (orbMap act c)
  exact Space.isOpenSubspace_flatImage B S hS g f l

/-- Values of the orbit map lie in the orbit. -/
lemma orbMap_mem {T : (BigFppfOver B S hS)ᵒᵖ}
    (r : (relP (yoneda.obj W) (⊤ : AddSubgroup M)).obj T) :
    (orbMap act c).app T r ∈ (orbSub act c).obj T :=
  Space.range_le_openSubspaceOfPoints_range_pointsMap (orbMap act c) T ⟨r, rfl⟩

/-- Membership in a set of points can be checked after a surjective base change. -/
lemma mem_of_surjective {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : Set (Space.points B S hS Y))
    {T U : BigFppfOver B S hS} (q : U ⟶ T)
    (hq : Surjective ((BigFppfOver.toScheme B S hS).map q)) (y : Y.obj (op T))
    (hy : Y.map q.op y ∈ (Space.openSubspaceOfPoints B S hS Y A).obj (op U)) :
    y ∈ (Space.openSubspaceOfPoints B S hS Y A).obj (op T) := by
  rw [Space.mem_openSubspaceOfPoints_iff] at hy ⊢
  rintro _ ⟨z, rfl⟩
  obtain ⟨z', rfl⟩ := Space.isSurjective_yoneda_map B S hS q hq z
  have e : yonedaEquiv.symm (Y.map q.op y) = yoneda.map q ≫ yonedaEquiv.symm y :=
    yonedaEquiv_symm_map q.op y
  refine hy ⟨z', ?_⟩
  rw [e]
  exact congrFun (Space.pointsMap_comp B S hS _ _ _) z'

/-- Every point of a surjective, flat, lfp map onto a represented presheaf lifts along a map of the
site with the same properties. -/
theorem exists_fppf_lift {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
    (hP : IsAlgebraicSpace B S hS P) (s : P ⟶ yoneda.obj T)
    (hs : Space.IsSurjective B S hS s) (hf : Space.IsFlat B S hS s)
    (hl : Space.IsLocallyOfFinitePresentation B S hS s) :
    ∃ (U : BigFppfOver B S hS) (q : U ⟶ T) (u : yoneda.obj U ⟶ P), u ≫ s = yoneda.map q ∧
      Flat ((BigFppfOver.toScheme B S hS).map q) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map q) := by
  obtain ⟨U, u, hus, hue⟩ := hP.exists_atlas
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hT := isAlgebraicSpace_yoneda B S hS T
  have huE : Space.IsEtale B S hS u := (Space.isEtale_iff_presheaf_of_yoneda B S hS u).2 hue
  have hF := Space.isFlat_comp B S hS hU hP hT u s (Space.isFlat_of_isEtale B S hS huE) hf
  have hL := Space.isLocallyOfFinitePresentation_comp B S hS hU hP hT u s
    (Space.isLocallyOfFinitePresentation_of_isEtale B S hS huE) hl
  have hSu : Space.IsSurjective B S hS (u ≫ s) := by
    have h1 := (Space.surjective_iff_surjective_pointsMap B S hS P hP U u).1 hus
    rw [Space.IsSurjective, Space.pointsMap_comp]
    exact hs.comp h1
  let q : U ⟶ T := yoneda.preimage (u ≫ s)
  have hq : yoneda.map q = u ≫ s := yoneda.map_preimage _
  have idE : ∀ V : BigFppfOver B S hS, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
        (𝟙 (yoneda.obj V)) := fun V => by
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro A C g fst snd sq
    have : IsIso (yoneda.map snd) := sq.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
    exact (inferInstance : Etale ((BigFppfOver.toScheme B S hS).map snd))
  refine ⟨U, q, u, hq.symm, ?_, ?_, ?_⟩
  · refine hF U T (𝟙 _) (𝟙 _) q (idE U) (idE T) ?_
    rw [hq]; simp
  · refine hL U T (𝟙 _) (𝟙 _) q (idE U) (idE T) ?_
    rw [hq]; simp
  · refine (MorphismProperty.relative_map_iff (F := yoneda) (P := MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))).mp
      ((Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS q).mpr ?_)
    rw [hq]; exact hSu

/-- **Affine stratum lemma, step 3**: a point of the open orbit lifts to `D(M) × W` along an fppf map. -/
theorem exists_lift_of_mem_orbSub (hX : IsAlgebraicSpace B S hS X) (hc : Space.IsEtale B S hS c)
    {T : BigFppfOver B S hS} {x : X.obj (op T)} (hx : x ∈ (orbSub act c).obj (op T)) :
    ∃ (U : BigFppfOver B S hS) (q : U ⟶ T)
      (r : (relP (yoneda.obj W) (⊤ : AddSubgroup M)).obj (op U)),
      (orbMap act c).app (op U) r = X.map q.op x ∧
      Flat ((BigFppfOver.toScheme B S hS).map q) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map q) := by
  have hRW := relP_isAlgebraicSpace (Z := (⊤ : AddSubgroup M)) (isAlgebraicSpace_yoneda B S hS W)
  obtain ⟨f, l⟩ := orbMap_flat_lfp act c hX hc
  let cR : AlgebraicSpaces B S hS := ⟨_, hRW⟩
  let cX : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let cT : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let g : cR ⟶ cX := ObjectProperty.homMk (orbMap act c)
  let t : cT ⟶ cX := ObjectProperty.homMk (yonedaEquiv.symm x)
  have hr : Subfunctor.range (yonedaEquiv.symm x) ≤ orbSub act c := by
    rintro T' _ ⟨y, rfl⟩
    have : (yonedaEquiv.symm x).app T' y = X.map y.op x := rfl
    rw [this]
    exact (orbSub act c).map y.op hx
  let a : cT ⟶ Space.flatImage B S hS g f l := ObjectProperty.homMk (Subfunctor.lift _ hr)
  have ha : a ≫ Space.flatImageι B S hS g f l = t :=
    ObjectProperty.hom_ext _ (Subfunctor.lift_ι _ hr)
  obtain ⟨h1, h2, h3⟩ := Space.surjectiveFlatLfp_pullback_snd_of_fac B S hS g f l t a ha
  obtain ⟨U, q, u, hu, hqF, hqL, hqS⟩ := exists_fppf_lift (pullback g t).property _ h1 h2 h3
  refine ⟨U, q, yonedaEquiv (u ≫ (pullback.fst g t).hom), ?_, hqF, hqL, hqS⟩
  have e : (pullback.fst g t).hom ≫ orbMap act c = (pullback.snd g t).hom ≫ yonedaEquiv.symm x :=
    congrArg (fun k => k.hom) (pullback.condition (f := g) (g := t))
  have e2 : (u ≫ (pullback.fst g t).hom) ≫ orbMap act c = yoneda.map q ≫ yonedaEquiv.symm x := by
    rw [Category.assoc, e, ← Category.assoc, hu]
  have e3 := congrArg yonedaEquiv e2
  rw [yonedaEquiv_comp] at e3
  refine e3.trans ?_
  rw [yonedaEquiv_comp]
  simp [yonedaEquiv]

/-- **Affine stratum lemma, step 3**: the open orbit is stable under `D(M)`. -/
theorem smul_mem_orbSub (hX : IsAlgebraicSpace B S hS X) (hc : Space.IsEtale B S hS c)
    {T : BigFppfOver B S hS} (h : APt (fppfO B S hS) M (op T)) {x : X.obj (op T)}
    (hx : x ∈ (orbSub act c).obj (op T)) : act.smul h x ∈ (orbSub act c).obj (op T) := by
  obtain ⟨U, q, r, e, -, -, hS'⟩ := exists_lift_of_mem_orbSub act c hX hc hx
  refine mem_of_surjective _ q hS' _ ?_
  rw [act.map_smul, ← e, orbMap_app]
  have : act.smul (APt.res q.op h) (act.smul (topPt r.1) (c.app _ r.2)) =
      (orbMap act c).app (op U) (ptTop (APt.res q.op h * topPt r.1), r.2) := by
    change _ = act.smul (topPt (ptTop _)) _
    rw [topPt_ptTop, act.mul_smul]
    rfl
  rw [this]
  exact orbMap_mem act c _

end AlgMag.ChartStratum
