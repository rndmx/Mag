/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesLimitAction
import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAffineApproximation
import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDiagonalDescent
import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
import AlgMag.ChartStratumFlat

/-!
# Theorems 6.8 = A.2 and A.1 for general `S`: the limit argument

Mayeux, *Algebraic Magnetism*, proofs of Theorems A.1 and A.2: reduction to `S` of finite type over `ℤ`.

Over `Spec ℤ`, an affine object `T` of the site is the limit of the stages `Spec ℤ[i]`
(`limitDataZ`), and `D(M)` is represented by `Spec ℤ[M]` (`actGoodZ`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.LimFin

open LimAct Space

noncomputable section

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The functor to schemes for the site of `Spec ℤ`. -/
abbrev SCHZ := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ

/-- `Spec ℤ` as an object of its own site. -/
abbrev T1 : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (𝟙 (B.obj hZ))

def isTerminal_T1 : IsTerminal (yoneda.obj (T1 hZ)) :=
  (Over.mkIdTerminal).isTerminalObj yoneda _

/-- The structure morphism of an object of the site over `Spec ℤ`. -/
def toT1 (V : BigFppfOver B (⊤_ Scheme.{u}) hZ) : V ⟶ T1 hZ := Over.homMk V.hom rfl

lemma toT1_ext {V : BigFppfOver B (⊤_ Scheme.{u}) hZ} (a b : V ⟶ T1 hZ) : a = b :=
  (Over.mkIdTerminal).hom_ext a b

lemma map_ext_terminal {V W : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (f : (SCHZ hZ).obj V ⟶ (SCHZ hZ).obj W) :
    ∃ g : V ⟶ W, (SCHZ hZ).map g = f :=
  ⟨Over.homMk (ObjectProperty.homMk f) (ObjectProperty.hom_ext _ (terminal.hom_ext _ _)), rfl⟩

/-- A morphism of finite type of affine schemes with noetherian target is of finite presentation. -/
lemma finitePresentation_of_lft_affine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (hl : LocallyOfFiniteType f) : FinitePresentation f := by
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have h := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := f)).1 hl
  have : LocallyOfFinitePresentation f :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation) (f := f)).2
      ((RingHom.FinitePresentation.of_finiteType).1 h)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

section Stage

variable (T : BigAffineFppf B (⊤_ Scheme.{u}) hZ)

lemma isAffine_stage (j : (Finset (affineRing hZ T))ᵒᵖ) :
    IsAffine ((SCHZ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj
      ((finsetStageDiagram hZ (affineRing hZ T)).obj j))) :=
  (finsetStage hZ (affineRing hZ T) j).property

lemma stage_isSeparatedOver (j : (Finset (affineRing hZ T))ᵒᵖ) :
    Space.IsSeparatedOver B (⊤_ Scheme.{u}) hZ ((stageSystem hZ T).obj j) := by
  have := isAffine_stage hZ T j
  have hT := isTerminal_T1 hZ
  refine (isSeparatedOver_iff_isSeparated_of_isTerminal B _ hZ hT (hT.from _)).2 ?_
  have e : hT.from ((stageSystem hZ T).obj j) = yoneda.map (toT1 hZ _) := hT.hom_ext _ _
  rw [e]
  refine (isSeparated_yoneda_map_iff B _ hZ _).2 ?_
  have : IsAffine ((SCHZ hZ).obj (T1 hZ)) := by
    change IsAffine (⊤_ Scheme.{u})
    exact .of_isIso (terminalIsoIsTerminal specULiftZIsTerminal).hom
  infer_instance

lemma stage_fp (j : (Finset (affineRing hZ T))ᵒᵖ) :
    IsFinitePresentation B _ hZ (yoneda.map (toT1 hZ ((BigAffineFppf.inclusion _ _ hZ).obj
      ((finsetStageDiagram hZ (affineRing hZ T)).obj j)))) := by
  refine isFinitePresentation_yoneda_map B _ hZ _ ?_
  have := isAffine_stage hZ T j
  have hA : IsAffine ((SCHZ hZ).obj (T1 hZ)) := by
    change IsAffine (⊤_ Scheme.{u})
    exact .of_isIso (terminalIsoIsTerminal specULiftZIsTerminal).hom
  have hN : IsLocallyNoetherian ((SCHZ hZ).obj (T1 hZ)) := by
    change IsLocallyNoetherian (⊤_ Scheme.{u})
    have : IsNoetherianRing (ULift.{u} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv.{0, u} (R := ℤ)).symm
    exact isLocallyNoetherian_of_isOpenImmersion
      (terminalIsoIsTerminal specULiftZIsTerminal).hom
  have hl : LocallyOfFiniteType ((SCHZ hZ).map (toT1 hZ ((BigAffineFppf.inclusion _ _ hZ).obj
      ((finsetStageDiagram hZ (affineRing hZ T)).obj j)))) :=
    locallyOfFiniteType_terminalFrom_specAdjoinFinsetDiagram_obj _ j
  exact finitePresentation_of_lft_affine _ hl

lemma stage_π_affine (j : (Finset (affineRing hZ T))ᵒᵖ) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (SCHZ hZ))) (limit.π (stageSystem hZ T) j) := by
  have e : limit.π (stageSystem hZ T) j = (stageLimitIso hZ T).hom ≫
      yoneda.map ((BigAffineFppf.inclusion _ _ hZ).map ((finsetStageCone hZ T).π.app j)) := by
    exact ((Iso.inv_comp_eq _).1 (stageLimitIso_inv_π hZ T j))
  rw [e]
  refine (MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (SCHZ hZ)))
    (stageLimitIso hZ T).hom _).2 ?_
  refine (presheaf_yoneda_map_iff B _ hZ inferInstance _).2 ?_
  have := isAffine_stage hZ T j
  have : IsAffine ((SCHZ hZ).obj ((BigAffineFppf.inclusion _ _ hZ).obj T)) := T.property
  change IsAffineHom _
  infer_instance

private theorem isSep_comp_iso {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : X ⟶ Y} {g : Y ⟶ Z} {f : X ⟶ Z} [IsIso g]
    (hm : m ≫ g = f) : IsSeparated B S hS f ↔ IsSeparated B S hS m := by
  subst hm
  exact ⟨fun h => isSeparated_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (CommSq.mk (show 𝟙 X ≫ m ≫ g = m ≫ g by simp))) h,
    fun h => isSeparated_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (CommSq.mk (show 𝟙 X ≫ m = (m ≫ g) ≫ inv g by simp))) h⟩

local notation "DZ" => stageSystem hZ T

/-- **Stacks 084W/0851** for the stages. -/
theorem stage_sepDesc (hlimAlg : IsAlgebraicSpace B _ hZ (limit (DZ)))
    (k : (Finset (affineRing hZ T))ᵒᵖ) (W : Over ((DZ).obj k)) (Y : Over (limit (DZ)))
    (q : Y.left ⟶ W.left) (hW : IsAlgebraicSpace B _ hZ W.left)
    (hWfp : IsFinitePresentation B _ hZ W.hom)
    (sq : IsPullback q Y.hom W.hom (limit.π (DZ) k)) (hsep : IsSeparated B _ hZ Y.hom) :
    ∃ (j : (Finset (affineRing hZ T))ᵒᵖ) (e : j ⟶ k),
      IsSeparated B _ hZ (pullback.snd W.hom ((DZ).map e)) := by
  classical
  let M' : MorphismDescentSituation B (⊤_ Scheme.{u}) hZ hZ (Finset (affineRing hZ T)) :=
    { base := DZ
      base_isAlgebraicSpace := fun i => stageSystem_isAlgebraicSpace hZ T (op i)
      transition_affine := fun m => stageSystem_isAffineHom hZ T m
      limit_isAlgebraicSpace := hlimAlg
      initial := k.unop
      source₀ := W.left
      target₀ := (DZ).obj k
      sourceToBase := W.hom
      targetToBase := 𝟙 _
      map₀ := W.hom
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hW
      target₀_isAlgebraicSpace := stageSystem_isAlgebraicSpace hZ T k
      base₀_quasiCompact := stageSystem_isQuasiCompactSpace hZ T k
      base₀_quasiSeparated := stageSystem_isAbsolutelyQuasiSeparated hZ T k
      source₀_quasiCompact := isQuasiCompactSpace_of_isFinitePresentation B _ hZ W.hom
        (stageSystem_isAlgebraicSpace hZ T k) (stageSystem_isQuasiCompactSpace hZ T k) hWfp
      source₀_quasiSeparated := isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ hW
        (stageSystem_isAbsolutelyQuasiSeparated hZ T k) hWfp.2.2
      target₀_quasiCompact := stageSystem_isQuasiCompactSpace hZ T k
      target₀_quasiSeparated := stageSystem_isAbsolutelyQuasiSeparated hZ T k }
  have hlimSep : IsSeparated B _ hZ M'.mapLimit := by
    refine (isSep_comp_iso (g := pullback.fst (limit.π (DZ) k) (𝟙 ((DZ).obj k)))
      (pullback.lift_fst _ _ _)).1 ?_
    exact isSeparated_of_isPullback B _ hZ
      (IsPullback.of_horiz_isIso (fst := sq.flip.isoPullback.inv) (g := 𝟙 _) (CommSq.mk (by
        rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst_assoc, Category.comp_id]))) hsep
  obtain ⟨jj, hjj, hsepj⟩ :=
    M'.exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits
      (stageSystem_siteContainsBaseChangeLimits hZ T) hlimSep
  refine ⟨op jj, (homOfLE hjj).op, ?_⟩
  let τ := (DZ).map (homOfLE hjj).op
  have h1 : IsSeparated B _ hZ (pullback.fst τ W.hom) :=
    (isSep_comp_iso (g := pullback.fst τ (𝟙 ((DZ).obj k))) (pullback.lift_fst _ _ _)).2 hsepj
  have e : (pullbackSymmetry W.hom τ).hom ≫ pullback.fst τ W.hom = pullback.snd W.hom τ := by
    simp
  exact (isSep_comp_iso (m := pullback.snd W.hom τ) (g := 𝟙 _) (Category.comp_id _)).1
    (isSeparated_of_isPullback B _ hZ
      (IsPullback.of_horiz_isIso (fst := (pullbackSymmetry W.hom τ).hom) (g := 𝟙 _)
        (CommSq.mk (by rw [Category.comp_id, e]))) h1)

lemma isAlg_top : IsAlgebraicSpace B _ hZ (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) :=
  Space.isAlgebraicSpace_of_iso B _ hZ ((isTerminal_T1 hZ).uniqueUpToIso terminalIsTerminal)
    (isAlgebraicSpace_yoneda B _ hZ _)

lemma stage_fp_terminal (k : (Finset (affineRing hZ T))ᵒᵖ) (W : Over ((DZ).obj k))
    (hW : IsAlgebraicSpace B _ hZ W.left) (hfp : IsFinitePresentation B _ hZ W.hom) :
    IsFinitePresentation B _ hZ (terminal.from W.left) := by
  have hc := isFinitePresentation_comp B _ hZ hW (stageSystem_isAlgebraicSpace hZ T k)
    (isAlgebraicSpace_yoneda B _ hZ (T1 hZ)) _ _ hfp (stage_fp hZ T k)
  let iso := (isTerminal_T1 hZ).uniqueUpToIso terminalIsTerminal
  exact IsFinitePresentation.of_isPullback B _ hZ hW hW (isAlg_top hZ)
    (isAlgebraicSpace_yoneda B _ hZ (T1 hZ))
    (a := 𝟙 _) (g := iso.inv)
    (IsPullback.of_horiz_isIso (CommSq.mk ((isTerminal_T1 hZ).hom_ext _ _))) hc

/-- **The system of finitely generated subrings** as `LimitData`. -/
def limitDataZ :
    LimitData B (⊤_ Scheme.{u}) hZ hZ (yoneda.obj ((BigAffineFppf.inclusion _ _ hZ).obj T)) where
  I := (Finset (affineRing hZ T))ᵒᵖ
  cat := inferInstance
  cof := inferInstance
  D := DZ
  hD := stageSystem_isAlgebraicSpace hZ T
  hAffine := stageSystem_isAffineHom hZ T
  hQc := stageSystem_isQuasiCompactSpace hZ T
  hQs := stageSystem_isAbsolutelyQuasiSeparated hZ T
  hconv := stageSystem_siteContainsBaseChangeLimits hZ T
  e := stageLimitIso hZ T
  sepDesc k W Y q hW hfp sq hsep := stage_sepDesc hZ T (Space.isAlgebraicSpace_of_iso B _ hZ
    (stageLimitIso hZ T).symm (isAlgebraicSpace_yoneda B _ hZ _)) k W Y q hW hfp sq hsep
  hπ := stage_π_affine hZ T
  stageSep k W _ hs := isSeparatedOver_of_isSeparated B _ hZ (stage_isSeparatedOver hZ T k) hs
  stageFT k W hW hfp := isFiniteType_of_isFinitePresentation B _ hZ
    (stage_fp_terminal hZ T k W hW hfp)
  stageCharts k W hW hfp V φ he := by
    have ht : LocallyOfFiniteType (terminal.from (⊤_ Scheme.{u})) := by
      have : IsIso (terminal.from (⊤_ Scheme.{u})) :=
        ⟨terminal.from _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
      infer_instance
    have h := ChartAssembly.lft_chart ht
      (isFiniteType_of_isFinitePresentation B _ hZ (stage_fp_terminal hZ T k W hW hfp)).1 he
    have e : V.hom.hom = terminal.from _ := terminal.hom_ext _ _
    rw [e]
    exact h

end Stage

section ActGood

variable {M : Type u} [AddCommGroup M]

/-- The site object `Spec ℤ[M]`. -/
def G0 (h : B.Contains (Spec (ZMon M))) : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
  siteObject B _ hZ h (terminal.from _)

/-- Points of `Spec ℤ[M]` are points of `D(M)`. -/
def toApt (h : B.Contains (Spec (ZMon M))) :
    yoneda.obj (G0 hZ h) ⟶ aptP (fppfO B _ hZ) M where
  app T := ↾fun t => MonAff.toSpecEquiv ((SCHZ hZ).map t)
  naturality T T' f := tex fun t => MonoidHom.ext fun p =>
    MonAff.toSpecEquiv_comp ((SCHZ hZ).map f.unop) ((SCHZ hZ).map t) p

instance isIso_toApt (h : B.Contains (Spec (ZMon M))) : IsIso (toApt hZ (M := M) h) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun T => ?_
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab => ?_, fun a => ?_⟩
  · exact (SCHZ hZ).map_injective (MonAff.toSpecEquiv.injective hab)
  · obtain ⟨g, hg⟩ := map_ext_terminal hZ (V := unop T) (W := G0 hZ h)
      (MonAff.toSpecEquiv.symm a)
    refine ⟨g, ?_⟩
    change MonAff.toSpecEquiv ((SCHZ hZ).map g) = a
    rw [hg]
    exact Equiv.apply_symm_apply MonAff.toSpecEquiv a

/-- **`ActGood` over `Spec ℤ`**, `M` finitely generated. -/
theorem actGoodZ [AddMonoid.FG M] (h : B.Contains (Spec (ZMon M))) :
    ActGood B (⊤_ Scheme.{u}) hZ M := by
  refine actGood_of_representable (T1 := T1 hZ) (G0 := G0 hZ h) (isTerminal_T1 hZ) (toT1 hZ _)
    (asIso (toApt hZ h)).symm (isFinitePresentation_yoneda_map B _ hZ _ ?_)
  have hA : IsAffine ((SCHZ hZ).obj (T1 hZ)) := by
    change IsAffine (⊤_ Scheme.{u})
    exact .of_isIso (terminalIsoIsTerminal specULiftZIsTerminal).hom
  have hN : IsLocallyNoetherian ((SCHZ hZ).obj (T1 hZ)) := by
    change IsLocallyNoetherian (⊤_ Scheme.{u})
    have : IsNoetherianRing (ULift.{u} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv.{0, u} (R := ℤ)).symm
    exact isLocallyNoetherian_of_isOpenImmersion
      (terminalIsoIsTerminal specULiftZIsTerminal).hom
  have hG : IsAffine ((SCHZ hZ).obj (G0 hZ h)) := inferInstanceAs (IsAffine (Spec (ZMon M)))
  have hl : LocallyOfFinitePresentation ((SCHZ hZ).map (toT1 hZ (G0 hZ h))) :=
    ChartStratum.lfp_terminal_zmon M
  exact finitePresentation_of_lft_affine _ inferInstance

end ActGood

end

end AlgMag.LimFin
