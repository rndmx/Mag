/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge2Cart
import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen

/-!
# Stacks 03DX (1), part 2: flat base change for a quasi-coherent module on `(Sch/X)_fppf`

* `cart_assoc`: `𝓕^a` has the base change property between affines.
* `cart_of_hasLocal`: so has `𝒢`, between affines over an object where it is an associated module.
* `exists_family`: finite flat affine coverings by such objects.
* `cart_of_flat`: `𝒢` has the base change property along flat morphisms of affines.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open Stacks.PresheafOfModules
open scoped TensorProduct

noncomputable section

namespace AlgMag.B2

open BigFppfOver

variable {B : BigFppfSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- `𝓕^a` has the base change property between affine objects (Stacks 070S (1), Tag 03DT, Tag 03DX). -/
theorem cart_assoc (F : X.Modules) [F.IsQuasicoherent] {U V : BigFppfOver B X hX}
    (hU : Aff B X hX U) (hV : Aff B X hX V) (f : U ⟶ V) :
    Cart B X hX ((associatedModule B X hX).obj F).val f := by
  haveI := isIso_sheafificationAdjunction_unit_app B X hX
    (sectionsPresheafOfModules B X hX F)
    (isSheaf_sectionsPresheafOfModules B X hX fpqcDescentOfQuasicoherentHoms F)
  let φ : sectionsPresheafOfModules B X hX F ≅
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (structureSheaf B X hX).obj)).obj ((associatedModule B X hX).obj F) :=
    asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B X hX).obj)).unit.app (sectionsPresheafOfModules B X hX F)) ≪≫
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (structureSheaf B X hX).obj)).mapIso (associatedModuleIsoSections B X hX F).symm
  have h1 := cart_sections (B := B) (hX := hX) F hU hV f
  have hi : IsIso (restrictionBaseChange (R := commStructurePresheaf B X hX)
      (sectionsPresheafOfModules B X hX F) f.op) := (ConcreteCategory.isIso_iff_bijective _).2 h1
  haveI := hi
  haveI := isIso_restrictionBaseChange_of_iso (R := commStructurePresheaf B X hX) φ f.op
  have h2 := ConcreteCategory.bijective_of_isIso
    (restrictionBaseChange (R := commStructurePresheaf B X hX)
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (structureSheaf B X hX).obj)).obj ((associatedModule B X hX).obj F)) f.op)
  exact cart_of_isBC (R := commStructurePresheaf B X hX) ((associatedModule B X hX).obj F).val f.op
    (isBC_of_cart (R := commStructurePresheaf B X hX) _ f.op h2)

set_option maxHeartbeats 1600000 in
/-- `𝒢` over the big site of the scheme of `T`: the base change property on the image of that site. -/
theorem cart_big_of_hasLocal (G : SheafOfModules.{u} (structureSheaf B X hX))
    {T : BigFppfOver B X hX} (h : HasLocalAssociatedModule B X hX G T)
    {A A' : BigFppfOver B (objScheme B X hX T) (contains_objScheme B X hX T)}
    (hA : Aff B _ _ A) (hA' : Aff B _ _ A') (a : A ⟶ A') :
    Cart B X hX G.val ((objEquiv B X hX T).functor.map a).left := by
  obtain ⟨F, hF, ⟨i⟩⟩ := h
  haveI := hF
  have h1 := cart_assoc (B := B) (hX := contains_objScheme B X hX T) F hA hA' a
  let P := ((objRestrict B X hX T).obj G).val
  have h2 : Function.Bijective (restrictionBaseChange (R := commStructurePresheaf B _ _) P a.op) := by
    have hi : IsIso (restrictionBaseChange (R := commStructurePresheaf B _ _)
        ((associatedModule B _ _).obj F).val a.op) := (ConcreteCategory.isIso_iff_bijective _).2 h1
    have hi' : IsIso (restrictionBaseChange (R := commStructurePresheaf B _ _)
        ((SheafOfModules.forget _).obj ((associatedModule B _ _).obj F)) a.op) := hi
    have hj : IsIso (restrictionBaseChange (R := commStructurePresheaf B _ _) P a.op) :=
      isIso_restrictionBaseChange_of_iso (R := commStructurePresheaf B _ _)
        ((SheafOfModules.forget _).mapIso i) a.op
    exact (ConcreteCategory.isIso_iff_bijective _).1 hj
  exact cart_of_isBC (R := commStructurePresheaf B X hX) G.val ((objEquiv B X hX T).functor.map a).left.op
    (isBC_of_cart (R := commStructurePresheaf B _ _) P a.op h2)

set_option maxHeartbeats 1600000 in
lemma cart_aux (G : SheafOfModules.{u} (structureSheaf B X hX)) {T : BigFppfOver B X hX}
    (h : HasLocalAssociatedModule B X hX G T) {Yl Yl' : B.Schemes} (al : Yl ⟶ Yl') (yl : Yl' ⟶ T.left)
    {Yh : Yl ⟶ B.obj hX} {Yh' : Yl' ⟶ B.obj hX} (e : Yh' = yl ≫ T.hom) (e2 : Yh = al ≫ Yh')
    (hY : Aff B X hX (Over.mk Yh)) (hY' : Aff B X hX (Over.mk Yh')) :
    Cart B X hX G.val (Over.homMk al e2.symm : Over.mk Yh ⟶ Over.mk Yh') := by
  subst e
  subst e2
  let A' : BigFppfOver B (objScheme B X hX T) (contains_objScheme B X hX T) := Over.mk yl
  let A : BigFppfOver B (objScheme B X hX T) (contains_objScheme B X hX T) := Over.mk (al ≫ yl)
  let a' : A ⟶ A' := Over.homMk al rfl
  exact cart_big_of_hasLocal G h (A := A) (A' := A') hY hY' a'

/-- `𝒢` has the base change property between affines over an object where it is an associated
module (Stacks 03DX (1), the local step followed by Tag 03DT). -/
theorem cart_of_hasLocal (G : SheafOfModules.{u} (structureSheaf B X hX))
    {T : BigFppfOver B X hX} (h : HasLocalAssociatedModule B X hX G T)
    {Y Y' : BigFppfOver B X hX} (hY : Aff B X hX Y) (hY' : Aff B X hX Y') (a : Y ⟶ Y')
    (y : Y' ⟶ T) : Cart B X hX G.val a :=
  cart_aux G h (Yh := Y.hom) (Yh' := Y'.hom) a.left y.left (by simpa using (Over.w y).symm)
    (by simpa using (Over.w a).symm) hY hY'

/-- A finite flat covering of an affine object by affine objects over which `𝒢` is an associated
module (Stacks 03DL (6), read through Tag 03DN, then Tag 021S and quasi-compactness). -/
theorem exists_family (G : SheafOfModules.{u} (structureSheaf B X hX)) (hG : G.IsQuasicoherentOnSite)
    {V : BigFppfOver B X hX} (hV : Aff B X hX V) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (W : I → BigFppfOver B X hX) (g : ∀ i, W i ⟶ V),
      (∀ i, Aff B X hX (W i)) ∧ (∀ i, HasLocalAssociatedModule B X hX G (W i)) ∧
      (∀ i, Flat ((toScheme B X hX).map (g i))) ∧
      Sieve.ofArrows W g ∈ topology B X hX V := by
  classical
  obtain ⟨I, Z, hZ, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation G).1 hG
  obtain ⟨E, W, m, hfac, hflat, hlfp, hsurj⟩ := exists_family_of_mem_topology B X hX (hZ V)
  haveI := hV
  haveI : ∀ j, Flat (B.inclusion.map (m j)) := hflat
  haveI : ∀ j, LocallyOfFinitePresentation (B.inclusion.map (m j)) := hlfp
  have hopen : ∀ j, IsOpenMap (B.inclusion.map (m j)) := fun j =>
    haveI : UniversallyOpen (B.inclusion.map (m j)) :=
      universallyOpen_of_flat_of_locallyOfFinitePresentation (B.inclusion.map (m j))
    (B.inclusion.map (m j)).isOpenMap
  have hch : ∀ x : (B.inclusion.obj V.left), ∃ (j : E) (A : (B.inclusion.obj (W j)).Opens),
      IsAffineOpen A ∧ x ∈ (B.inclusion.map (m j)) '' (A : Set _) := by
    intro x
    obtain ⟨j, y, rfl⟩ := hsurj x
    obtain ⟨A, hA, hyA, -⟩ := exists_isAffineOpen_mem_and_subset (X := B.inclusion.obj (W j))
      (x := y) (U := ⊤) trivial
    exact ⟨j, A, hA, y, hyA, rfl⟩
  choose j A hA hxA using hch
  haveI : CompactSpace (B.inclusion.obj V.left) :=
    inferInstanceAs (CompactSpace ((toScheme B X hX).obj V))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (B.inclusion.map (m (j x))) '' (A x : Set _))
    (fun x => hopen (j x) _ (A x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxA x⟩)
  let J := ULift.{u + 1} t
  let Wo : J → B.Schemes := fun i =>
    B.obj (BigFppfOver.contains_opens B (W (j i.down.1)).property (A i.down.1))
  let m' : ∀ i : J, Wo i ⟶ V.left := fun i =>
    ObjectProperty.homMk (X := Wo i) (Y := V.left) ((A i.down.1).ι ≫ B.inclusion.map (m (j i.down.1)))
  let inc : ∀ i : J, Wo i ⟶ W (j i.down.1) := fun i =>
    ObjectProperty.homMk (X := Wo i) (Y := W (j i.down.1)) (A i.down.1).ι
  have hm' : ∀ i : J, m' i = inc i ≫ m (j i.down.1) := fun i => rfl
  have fl' : ∀ i : J, Flat (B.inclusion.map (m' i)) := fun i =>
    inferInstanceAs (Flat ((A i.down.1).ι ≫ B.inclusion.map (m (j i.down.1))))
  have lf' : ∀ i : J, LocallyOfFinitePresentation (B.inclusion.map (m' i)) := fun i =>
    inferInstanceAs (LocallyOfFinitePresentation ((A i.down.1).ι ≫ B.inclusion.map (m (j i.down.1))))
  have su' : ∀ x : (B.inclusion.obj V.left), ∃ i : J, x ∈ Set.range (B.inclusion.map (m' i)) := by
    intro x
    obtain ⟨c, hc, y, hy, rfl⟩ : ∃ c, c ∈ t ∧ x ∈ (B.inclusion.map (m (j c))) '' (A c : Set _) := by
      have := ht (Set.mem_univ x)
      simpa using this
    refine ⟨⟨⟨c, hc⟩⟩, ⟨y, hy⟩, ?_⟩
    rfl
  haveI : Finite J := inferInstance
  refine ⟨J, inferInstance, fun i => Over.mk (m' i ≫ V.hom), fun i => Over.homMk (m' i), ?_, ?_, fl',
    mem_topology_of_family B X hX Wo m' fl' lf' su'⟩
  · intro i
    exact hA i.down.1
  · intro i
    obtain ⟨c, ⟨b⟩⟩ := hfac (j i.down.1)
    have hc : HasLocalAssociatedModule B X hX G (Z c) :=
      exists_isQuasicoherent_iso_associatedModule_objRestrict B X hX (Z c) (hP c)
    let k : (Over.mk (m' i ≫ V.hom) : BigFppfOver B X hX) ⟶ Over.mk (m (j i.down.1) ≫ V.hom) :=
      Over.homMk (inc i) (by simp [hm'])
    exact hasLocalAssociatedModule_of_hom B X hX G (k ≫ b) hc

lemma aff_pullback {U V W : BigFppfOver B X hX} (hU : Aff B X hX U) (hV : Aff B X hX V)
    (hW : Aff B X hX W) (f : U ⟶ V) (g : W ⟶ V) : Aff B X hX (pullback f g) := by
  haveI := hU; haveI := hV; haveI := hW
  have e := (IsPullback.of_hasPullback f g).map (toScheme B X hX)
  exact IsAffine.of_isIso e.isoPullback.hom

lemma isPushout_rings {P U V W : BigFppfOver B X hX} (hP : Aff B X hX P) (hU : Aff B X hX U)
    (hV : Aff B X hX V) (hW : Aff B X hX W) {fst : P ⟶ U} {snd : P ⟶ W} {a : U ⟶ V} {b : W ⟶ V}
    (h : IsPullback fst snd a b) :
    IsPushout ((commStructurePresheaf B X hX).map a.op) ((commStructurePresheaf B X hX).map b.op)
      ((commStructurePresheaf B X hX).map fst.op) ((commStructurePresheaf B X hX).map snd.op) := by
  haveI := hP; haveI := hU; haveI := hV; haveI := hW
  show IsPushout ((toScheme B X hX).map a).appTop ((toScheme B X hX).map b).appTop
    ((toScheme B X hX).map fst).appTop ((toScheme B X hX).map snd).appTop
  exact isPushout_appTop_of_isPullback (h.map (toScheme B X hX))

/-- The abelian sheaf of a sheaf of modules, as a sheaf of types (on the big site, by the
corepresentability of the forgetful functor). -/
lemma sheaf_forget (G : SheafOfModules.{u} (structureSheaf B X hX)) :
    Presieve.IsSheaf (topology B X hX) (G.val.presheaf ⋙ forget AddCommGrpCat.{u}) :=
  Presieve.isSheaf_iso _ (Functor.isoWhiskerLeft G.val.presheaf AddCommGrpCat.coyonedaObjIsoForget)
    (G.isSheaf (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- **Flat base change** for a quasi-coherent module on `(Sch/X)_fppf`, by descent along the family
of `exists_family`. -/
theorem cart_of_flat (G : SheafOfModules.{u} (structureSheaf B X hX)) (hG : G.IsQuasicoherentOnSite)
    {U V : BigFppfOver B X hX} (hU : Aff B X hX U) (hV : Aff B X hX V) (f : U ⟶ V)
    (hf : Flat ((toScheme B X hX).map f)) : Cart B X hX G.val f := by
  classical
  obtain ⟨I, hI, W, g, hW, hL, hfl, hcover⟩ := exists_family G hG hV
  haveI := hU; haveI := hV
  have hsT := sheaf_forget G
  have hcoverU : Sieve.ofArrows (fun i => pullback f (g i))
      (fun i => pullback.fst f (g i)) ∈ topology B X hX U := by
    refine (topology B X hX).superset_covering ?_ ((topology B X hX).pullback_stable f hcover)
    intro Z h hh
    obtain ⟨Y, g₁, g₂, ⟨i⟩, hg⟩ := hh
    have hmem := (Sieve.ofArrows (fun i => pullback f (g i))
        (fun i => pullback.fst f (g i))).downward_closed
      (Sieve.ofArrows_mk (fun i => pullback f (g i)) (fun i => pullback.fst f (g i)) i)
      (pullback.lift h g₁ hg.symm)
    rwa [pullback.lift_fst] at hmem
  have hsfV : Presieve.IsSheafFor (G.val.presheaf ⋙ forget AddCommGrpCat.{u})
      (Presieve.ofArrows W g) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcover)
  have hsfU : Presieve.IsSheafFor (G.val.presheaf ⋙ forget AddCommGrpCat.{u})
      (Presieve.ofArrows (fun i => pullback f (g i)) (fun i => pullback.fst f (g i))) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcoverU)
  have a12 : ∀ c : I × I, Aff B X hX (pullback (g c.1) (g c.2)) := fun c =>
    aff_pullback (hW _) hV (hW _) _ _
  have hflat' : ((commStructurePresheaf B X hX).map f.op).hom.Flat :=
    show ((toScheme B X hX).map f).appTop.hom.Flat from
      HasRingHomProperty.appTop (P := @Flat) _ hf
  have hiso := isIso_restrictionBaseChange_of_cover (R := commStructurePresheaf B X hX) G.val f W g
    hflat' hsfV hsfU
    (fun i => isPushout_rings (aff_pullback hU hV (hW i) _ _) hU hV (hW i)
      (IsPullback.of_hasPullback f (g i)))
    (fun c => isPushout_rings (aff_pullback hU hV (a12 c) _ _) hU hV (a12 c)
      (IsPullback.of_hasPullback f _))
    (fun i => (ConcreteCategory.isIso_iff_bijective _).2
      (cart_of_hasLocal G (hL i) (aff_pullback hU hV (hW i) _ _) (hW i) (pullback.snd f (g i)) (𝟙 _)))
    (fun c => (ConcreteCategory.isIso_iff_bijective _).2
      (cart_of_hasLocal G (hL c.1) (aff_pullback hU hV (a12 c) _ _) (a12 c)
        (pullback.snd f (pullback.fst (g c.1) (g c.2) ≫ g c.1)) (pullback.fst (g c.1) (g c.2))))
  exact (ConcreteCategory.isIso_iff_bijective _).1 hiso

end AlgMag.B2
