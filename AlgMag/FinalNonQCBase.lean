/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCFact
import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibre
import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison

/-!
# Passing to the site of an object of the site

For `T₀` an object of the big fppf site of `S`, `Res X T₀` is `X` as a presheaf on the site of `T₀`. It carries the action, and its
attractor points over `T` are those of `X` over `T` viewed over `S`. This is the reduction "the assertion is local over `S`" of the
paper.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

noncomputable section

variable (T₀ : BigFppfOver B S hS)

/-- `T₀` as a section of the terminal presheaf. -/
def betaT : yoneda.obj (Over.mk T₀.hom) ⟶ yoneda.obj (T1 B S hS) :=
  yoneda.map (Over.mkIdTerminal.from _)

variable (X) in
/-- `X` as a presheaf on the site of `T₀`. -/
abbrev Res : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ ⥤ Type u :=
  fibreOfSection T₀.hom (toT1 X) (betaT T₀)

variable {T₀}

/-- A point of `X` over `(Over.map a).obj W` is a point of the restriction. -/
def resMk {W : BigFppfOver B T₀.left.1 T₀.left.2} (x : X.obj (op ((Over.map T₀.hom).obj W))) :
    (Res X T₀).obj (op W) := ⟨x, t1_ext _ _⟩

/-- A point of `𝔸(P)` over the site of `T₀` is a point of `𝔸(P)` over the site of `S`. -/
def cvP {P : Type u} [AddCommMonoid P] {U : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ}
    (h : APt (fppfO B T₀.left.1 T₀.left.2) P U) :
    APt (fppfO B S hS) P (op ((Over.map T₀.hom).obj U.unop)) := h

/-- And back. -/
def cvQ {P : Type u} [AddCommMonoid P] {U : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ}
    (h : APt (fppfO B S hS) P (op ((Over.map T₀.hom).obj U.unop))) :
    APt (fppfO B T₀.left.1 T₀.left.2) P U := h

lemma cvP_res {P : Type u} [AddCommMonoid P] {U V : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ} (f : U ⟶ V)
    (h : APt (fppfO B T₀.left.1 T₀.left.2) P U) :
    cvP (APt.res f h) = APt.res ((Over.map T₀.hom).map f.unop).op (cvP h) :=
  MonoidHom.ext fun _ => rfl

variable (act : AAction (fppfO B S hS) M X)

/-- The action on the restriction. -/
def resAct : AAction (fppfO B T₀.left.1 T₀.left.2) M (Res X T₀) where
  smul {U} h s := ⟨act.smul (cvP h) s.1, t1_ext _ _⟩
  one_smul {U} x := Subtype.ext (by
    have : cvP (1 : APt (fppfO B T₀.left.1 T₀.left.2) M U) = 1 := MonoidHom.ext fun _ => rfl
    change act.smul (cvP (1 : APt (fppfO B T₀.left.1 T₀.left.2) M U)) x.1 = x.1
    rw [this]; exact act.one_smul x.1)
  mul_smul g h x := Subtype.ext (by
    have : cvP (g * h) = cvP g * cvP h := MonoidHom.ext fun _ => rfl
    change act.smul (cvP (g * h)) x.1 = act.smul (cvP g) (act.smul (cvP h) x.1)
    rw [this]; exact act.mul_smul (cvP g) (cvP h) x.1)
  map_smul f h x := Subtype.ext (by
    change X.map ((Over.map T₀.hom).map f.unop).op (act.smul (cvP h) x.1) =
      act.smul (cvP (APt.res f h)) (X.map ((Over.map T₀.hom).map f.unop).op x.1)
    rw [cvP_res]; exact act.map_smul ((Over.map T₀.hom).map f.unop).op (cvP h) x.1)

variable {act} {N : AddSubmonoid M}

/-- An attractor point of `X` over `T` viewed over `S` gives an attractor point of the restriction. -/
def attrDown {T : BigFppfOver B T₀.left.1 T₀.left.2}
    (φ : AttractorPt act N ((Over.map T₀.hom).obj T)) : AttractorPt (resAct act) N T where
  app {T'} t c := resMk (φ.app ((Over.map T₀.hom).map t) (cvP c))
  naturality {T' T''} s t c := Subtype.ext (by
    have := φ.naturality ((Over.map T₀.hom).map s) ((Over.map T₀.hom).map t) (cvP c)
    rw [← Functor.map_comp] at this
    exact this)
  equivariant {T'} t h c := Subtype.ext (φ.equivariant ((Over.map T₀.hom).map t) (cvP h) (cvP c))

lemma attrDown_toPoint {T : BigFppfOver B T₀.left.1 T₀.left.2}
    (φ : AttractorPt act N ((Over.map T₀.hom).obj T)) : (attrDown φ).toPoint.1 = φ.toPoint := by
  change φ.app ((Over.map T₀.hom).map (𝟙 T)) _ = φ.app (𝟙 _) _
  have : (Over.map T₀.hom).map (𝟙 T) = 𝟙 _ := (Over.map T₀.hom).map_id T
  rw [this]
  rfl

section Up

variable {T : BigFppfOver B T₀.left.1 T₀.left.2}

lemma upw {T' : BigFppfOver B S hS} (t : T' ⟶ (Over.map T₀.hom).obj T) :
    (t.left ≫ T.hom) ≫ T₀.hom = T'.hom := by
  have := Over.w t
  simpa [Category.assoc] using this

/-- The object of the site of `T₀` carried by `t`. -/
abbrev upObj {T' : BigFppfOver B S hS} (t : T' ⟶ (Over.map T₀.hom).obj T) :
    BigFppfOver B T₀.left.1 T₀.left.2 := Over.mk (t.left ≫ T.hom)

/-- Its map to `T`. -/
abbrev upMap {T' : BigFppfOver B S hS} (t : T' ⟶ (Over.map T₀.hom).obj T) : upObj t ⟶ T :=
  Over.homMk t.left rfl

/-- The comparison with `T'`. -/
abbrev upIso {T' : BigFppfOver B S hS} (t : T' ⟶ (Over.map T₀.hom).obj T) :
    T' ≅ (Over.map T₀.hom).obj (upObj t) := overMapMkIso T₀.hom (upw t)

/-- An attractor point of the restriction gives an attractor point of `X`. -/
def attrUp (φ : AttractorPt (resAct act) N T) : AttractorPt act N ((Over.map T₀.hom).obj T) where
  app {T'} t c := X.map (upIso t).hom.op
    (φ.app (upMap t) (cvQ (U := op (upObj t)) (APt.res (upIso t).inv.op c))).1
  naturality {T' T''} s t c := by
    let s' : upObj (s ≫ t) ⟶ upObj t := Over.homMk s.left (by simp)
    have hm : s' ≫ upMap t = upMap (s ≫ t) := Over.OverMorphism.ext rfl
    have h := congrArg Subtype.val (φ.naturality s' (upMap t)
      (cvQ (U := op (upObj t)) (APt.res (upIso t).inv.op c)))
    rw [hm] at h
    have h2 : APt.res s'.op (cvQ (U := op (upObj t)) (APt.res (upIso t).inv.op c)) =
        cvQ (U := op (upObj (s ≫ t))) (APt.res (upIso (s ≫ t)).inv.op (APt.res s.op c)) := by
      refine MonoidHom.ext fun n => ?_
      change ((fppfO B S hS).map ((Over.map T₀.hom).map s').op).hom
        (((fppfO B S hS).map (upIso t).inv.op).hom (c n)) =
        ((fppfO B S hS).map (upIso (s ≫ t)).inv.op).hom (((fppfO B S hS).map s.op).hom (c n))
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 3
    rw [h2] at h
    change X.map (upIso (s ≫ t)).hom.op _ = X.map s.op (X.map (upIso t).hom.op _)
    rw [h]
    change X.map (upIso (s ≫ t)).hom.op (X.map ((Over.map T₀.hom).map s').op _) = _
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    congr 2
  equivariant {T'} t h c := by
    have e : cvQ (U := op (upObj t)) (APt.res (upIso t).inv.op (APt.toMagnet N h * c)) =
        APt.toMagnet N (cvQ (U := op (upObj t)) (APt.res (upIso t).inv.op h)) *
          cvQ (U := op (upObj t)) (APt.res (upIso t).inv.op c) :=
      MonoidHom.ext fun n => map_mul ((fppfO B S hS).map (upIso t).inv.op).hom _ _
    rw [e, φ.equivariant (upMap t)]
    change X.map (upIso t).hom.op (act.smul _ _) = _
    rw [act.map_smul]
    congr 1

lemma attrUp_toPoint (φ : AttractorPt (resAct act) N T) : (attrUp φ).toPoint = φ.toPoint.1 := by
  change X.map (upIso (𝟙 _)).hom.op (φ.app (upMap (𝟙 _)) _).1 = _
  have h1 : cvQ (U := op (upObj (𝟙 ((Over.map T₀.hom).obj T))))
      (APt.res (upIso (𝟙 _)).inv.op (1 : APt (fppfO B S hS) N _)) = APt.res (upMap (𝟙 _)).op 1 :=
    MonoidHom.ext fun n => (map_one ((fppfO B S hS).map (upIso (𝟙 _)).inv.op).hom).trans
      (map_one ((fppfO B S hS).map ((Over.map T₀.hom).map (upMap (𝟙 ((Over.map T₀.hom).obj T)))).op).hom).symm
  have h2 := congrArg Subtype.val (φ.naturality (upMap (𝟙 _)) (𝟙 T) 1)
  rw [Category.comp_id] at h2
  rw [h1, h2]
  change X.map (upIso (𝟙 _)).hom.op (X.map ((Over.map T₀.hom).map (upMap (𝟙 _))).op φ.toPoint.1) = _
  rw [← Functor.map_comp_apply, ← op_comp]
  have : (upIso (𝟙 ((Over.map T₀.hom).obj T))).hom ≫ (Over.map T₀.hom).map (upMap (𝟙 _)) = 𝟙 _ :=
    Over.OverMorphism.ext (by simp)
  rw [this, op_id, X.map_id_apply]

end Up

/-! ### The hypotheses on the site of `T₀` -/

section Geom

open Space

variable (T₀)

theorem res_alg (hX : IsAlgebraicSpace B S hS X) :
    IsAlgebraicSpace B T₀.left.1 T₀.left.2 (Res X T₀) :=
  isAlgebraicSpace_fibreOfSection B S hS T₀ (toT1 X) (betaT T₀)
    (isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS _) hX
      (isAlgebraicSpace_yoneda B S hS _))

/-- The restriction `Res X T₀` is the pullback of `X` along `T₀`. -/
theorem res_sq : IsPullback (relocalizeFibreOfSectionMap T₀.hom (toT1 X) (betaT T₀))
    (relocalizeToYoneda T₀.hom (Res X T₀)) (toT1 X) (betaT T₀) :=
  isPullback_relocalizeFibreOfSectionMap T₀.hom (toT1 X) (betaT T₀)

/-- The restriction of `X` to `T₀` is locally of finite presentation when `X` is. -/
theorem res_lfp (hX : IsAlgebraicSpace B S hS X)
    (hfp : IsLocallyOfFinitePresentation B S hS (toT1 X)) :
    IsLocallyOfFinitePresentation B T₀.left.1 T₀.left.2 (toT1 (Res X T₀)) := by
  have hR := res_alg T₀ hX
  have hL : IsAlgebraicSpace B S hS ((relocalizePresheafFunctor T₀.hom).obj (Res X T₀)) :=
    isAlgebraicSpace_viewOver B _ S T₀.left.2 hS T₀.hom _ hR
  have hy := isAlgebraicSpace_yoneda B S hS
  have hsq : IsPullback
      (ObjectProperty.homMk (relocalizeToYoneda T₀.hom (Res X T₀)) :
        (⟨_, hL⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hy (Over.mk T₀.hom)⟩)
      (ObjectProperty.homMk (relocalizeFibreOfSectionMap T₀.hom (toT1 X) (betaT T₀)) :
        (⟨_, hL⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hX⟩)
      (ObjectProperty.homMk (betaT T₀) :
        (⟨_, hy _⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hy (T1 B S hS)⟩)
      (ObjectProperty.homMk (toT1 X) : (⟨_, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hy (T1 B S hS)⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (fun F => IsAlgebraicSpace B S hS F))
      (res_sq T₀).flip
  have h1 : IsLocallyOfFinitePresentation B S hS (relocalizeToYoneda T₀.hom (Res X T₀)) :=
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsq.flip hfp
  have e : toT1 (Res X T₀) = toYonedaId B _ T₀.left.2 (Res X T₀) := toT1_ext _ _
  rw [e]
  exact (holdsOnEveryEtaleChart_relocalizeToYoneda_iff B _ S T₀.left.2 hS T₀.hom _ _).1 h1

/-- The restriction of `X` to `T₀` is separated when `X` is. -/
theorem res_sep (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X) :
    Space.IsSeparatedOver B T₀.left.1 T₀.left.2 (Res X T₀) := by
  have hR := res_alg T₀ hX
  have hs : Space.IsSeparated B S hS (toT1 X) :=
    (isSeparatedOver_iff_isSeparated_of_isTerminal B S hS (isTerminal_T1 B S hS) (toT1 X)).1 hsep
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have h1 : Space.IsSeparated B S hS (relocalizeToYoneda T₀.hom (Res X T₀)) :=
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).diagonal.of_isPullback (res_sq T₀) hs
  have _ := isIso_relocalizeToYoneda_yonedaId B _ S T₀.left.2 hS T₀.hom
  rw [← relocalizeToYoneda_eq_map_toYonedaId B _ S T₀.left.2 hS T₀.hom] at h1
  have h1' : Space.IsSeparated B S hS ((relocalizePresheafFunctor T₀.hom).map (toYonedaId B _ T₀.left.2 (Res X T₀))) :=
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).diagonal.of_isPullback
      (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans rfl⟩ :
        IsPullback (𝟙 _) ((relocalizePresheafFunctor T₀.hom).map (toYonedaId B _ T₀.left.2 (Res X T₀))) _
          (relocalizeToYoneda T₀.hom (yoneda.obj (Over.mk (𝟙 (B.obj T₀.left.2)))))) h1
  have h2 := isSeparated_of_relocalize B _ T₀.left.2 hS T₀.hom
    (relativelyRepresentable_pullbackDiagonal B _ T₀.left.2 (toYonedaId B _ T₀.left.2 (Res X T₀)) hR) h1'
  exact (isSeparatedOver_iff_isSeparated_of_isTerminal B _ T₀.left.2
    (LimOrbit.isTerminal_T1 B _ T₀.left.2) _).2 h2

end Geom

end

end AlgMag.Final
