/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumQuotient
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation

/-!
# Flatness of the relation of a `D(Z)`-action (affine stratum lemma, step 5)

Source and target of `D(Z) × Y ⇉ Y` are base changes of `D(Z) → pt`, hence flat and locally of
finite presentation. This is the input of the bootstrap theorem 04S6.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartStratum

/-- The structure map of `ℤ[P]`. -/
noncomputable def zmonφ (P : Type u) [AddCommMonoid P] : CommRingCat.of (ULift.{u} ℤ) ⟶ ZMon P :=
  CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) P))

lemma terminal_from_zmon (P : Type u) [AddCommMonoid P] :
    terminal.from (Spec (ZMon P)) = Spec.map (zmonφ P) ≫
      (terminalIsoIsTerminal specULiftZIsTerminal).inv := terminal.hom_ext _ _

/-- `ℤ[P]` over the terminal scheme is flat. -/
lemma flat_terminal_zmon (P : Type u) [AddCommMonoid P] :
    Flat (terminal.from (Spec (ZMon P))) := by
  rw [terminal_from_zmon]
  have : Flat (Spec.map (zmonφ P)) := by
    rw [Flat.SpecMap_iff]
    change (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) P)).Flat
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  infer_instance

/-- `ℤ[P]` over the terminal scheme is of finite presentation, for `P` finitely generated. -/
lemma lfp_terminal_zmon (P : Type u) [AddCommMonoid P] [AddMonoid.FG P] :
    LocallyOfFinitePresentation (terminal.from (Spec (ZMon P))) := by
  rw [terminal_from_zmon]
  have : LocallyOfFinitePresentation (Spec.map (zmonφ P)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    change (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) P)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    haveI : IsNoetherianRing (ULift.{u} ℤ) :=
      isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv.{0, u} (R := ℤ)).symm
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  infer_instance

/-- A subgroup of a finitely generated abelian group is finitely generated as a monoid. -/
lemma fg_toAddSubmonoid {M : Type u} [AddCommGroup M] [AddGroup.FG M] (Z : AddSubgroup M) :
    AddMonoid.FG Z.toAddSubmonoid := by
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  haveI : Module.Finite ℤ (AddSubgroup.toIntSubmodule Z) := inferInstance
  have h : AddGroup.FG (AddSubgroup.toIntSubmodule Z) := Module.Finite.iff_addGroup_fg.mp this
  exact AddGroup.fg_iff_addMonoid_fg.mp h

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {Z : AddSubgroup M}
variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

lemma flat_dZ_π : Flat ((BigFppfOver.toScheme B S hS).map (dZ Z B S hS).π) := by
  have := flat_terminal_zmon.{u} Z.toAddSubmonoid
  exact inferInstanceAs (Flat (pullback.fst _ _))

lemma lfp_dZ_π [AddMonoid.FG Z.toAddSubmonoid] :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (dZ Z B S hS).π) := by
  have := lfp_terminal_zmon.{u} Z.toAddSubmonoid
  exact inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ _))

lemma terminal_from_yoneda_dZ :
    terminal.from (yoneda.obj (dZ Z B S hS).P) =
      yoneda.map (dZ Z B S hS).π ≫ (Space.yonedaTerminalIso B S hS).hom := terminal.hom_ext _ _

/-- A morphism which is a base change of `D(Z) → pt` is flat and locally of finite presentation. -/
theorem flat_lfp_of_isPullback [AddMonoid.FG Z.toAddSubmonoid]
    {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hR : IsAlgebraicSpace B S hS R)
    (hY : IsAlgebraicSpace B S hS Y)
    {g : R ⟶ yoneda.obj (dZ Z B S hS).P} {h : R ⟶ Y}
    (sq : IsPullback g h (terminal.from _) (terminal.from Y)) :
    Space.IsFlat B S hS h ∧ Space.IsLocallyOfFinitePresentation B S hS h := by
  let e := Space.yonedaTerminalIso B S hS
  have sq' : IsPullback g h (yoneda.map (dZ Z B S hS).π) (terminal.from Y ≫ e.inv) := by
    refine IsPullback.of_iso sq (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · change _ ≫ e.inv = _
      simp [terminal_from_yoneda_dZ, e]
    · simp
  have hT : IsAlgebraicSpace B S hS (yoneda.obj (⊤_ (BigFppfOver B S hS))) :=
    isAlgebraicSpace_yoneda B S hS _
  have hG : IsAlgebraicSpace B S hS (yoneda.obj (dZ Z B S hS).P) := isAlgebraicSpace_yoneda B S hS _
  let cR : AlgebraicSpaces B S hS := ⟨R, hR⟩
  let cY : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let cG : AlgebraicSpaces B S hS := ⟨_, hG⟩
  let cT : AlgebraicSpaces B S hS := ⟨_, hT⟩
  let tg : cR ⟶ cG := ObjectProperty.homMk g
  let th : cR ⟶ cY := ObjectProperty.homMk h
  let tπ : cG ⟶ cT := ObjectProperty.homMk (yoneda.map (dZ Z B S hS).π)
  let tt : cY ⟶ cT := ObjectProperty.homMk (terminal.from Y ≫ e.inv)
  have sq'' : IsPullback tg th tπ tt := by
    refine IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq'.w) sq'
  exact ⟨(Space.isFlat_isStableUnderBaseChange B S hS).of_isPullback sq''
      (Space.isFlat_yoneda_map B S hS _ flat_dZ_π),
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq''
      (Space.isLocallyOfFinitePresentation_yoneda_map B S hS _ lfp_dZ_π)⟩

/-- The target `(a, x) ↦ a • x` is also a base change of `D(Z) → pt`. -/
theorem relTgt_isPullback (β : AAction (fppfO B S hS) Z.toAddSubmonoid Y) :
    IsPullback (relToG (Y := Y) (Z := Z)) (relTgt β) (terminal.from _) (terminal.from Y) := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Types.isPullback_iff]
  have lift_inj : ∀ (x y : APt (fppfO B S hS) Z.toAddSubmonoid T),
      (dZ Z B S hS).lift (terminal.from _) x = (dZ Z B S hS).lift (terminal.from _) y → x = y := by
    intro x y e
    have h := (dZ Z B S hS).res_lift (terminal.from _) x
    rw [e, (dZ Z B S hS).res_lift] at h
    exact h.symm
  refine ⟨?_, ?_, ?_⟩
  · exact NatTrans.congr_app
      (terminal.hom_ext (relToG (Y := Y) (Z := Z) ≫ terminal.from _) (relTgt β ≫ terminal.from Y)) T
  · rintro x y ⟨e1, e2⟩
    have ea : x.1 = y.1 := lift_inj _ _ e1
    have e2' : β.smul x.1 x.2 = β.smul y.1 y.2 := e2
    refine Prod.ext ea ?_
    rw [ea] at e2'
    have := congrArg (β.smul (zInv y.1)) e2'
    rwa [← β.mul_smul, ← β.mul_smul, zInv_mul, β.one_smul, β.one_smul] at this
  · intro x₂ x₃ _
    let a : APt (fppfO B S hS) Z.toAddSubmonoid T := APt.res (Quiver.Hom.op x₂) (dZ Z B S hS).u
    refine ⟨(a, β.smul (zInv a) x₃), ?_, ?_⟩
    · exact ((dZ Z B S hS).uniq _ _ x₂ (terminal.hom_ext _ _) rfl).symm
    · change β.smul a (β.smul (zInv a) x₃) = x₃
      rw [← β.mul_smul, mul_comm, zInv_mul, β.one_smul]

/-- **Affine stratum lemma, step 5**: the hypotheses of Stacks 04S6 for the relation of a `D(Z)`-action. -/
theorem relJ_flat_lfp [AddMonoid.FG Z.toAddSubmonoid] (β : AAction (fppfO B S hS) Z.toAddSubmonoid Y)
    (hY : IsAlgebraicSpace B S hS Y) :
    Space.IsFlat B S hS (relJ β).target.left ∧
      Space.IsLocallyOfFinitePresentation B S hS (relJ β).target.left ∧
      Space.IsFlat B S hS (relJ β).source.left ∧
      Space.IsLocallyOfFinitePresentation B S hS (relJ β).source.left := by
  have hR := relP_isAlgebraicSpace (Z := Z) hY
  rw [relJ_target, relJ_source]
  obtain ⟨a, b⟩ := flat_lfp_of_isPullback hR hY (relTgt_isPullback β)
  obtain ⟨c, d⟩ := flat_lfp_of_isPullback hR hY (relP_isPullback (Y := Y) (Z := Z))
  exact ⟨a, b, c, d⟩

/-- **Stacks 04S6**: the quotient of an algebraic space by a free action of `D(Z)`. -/
theorem quotient_isAlgebraicSpace [AddMonoid.FG Z.toAddSubmonoid]
    (β : AAction (fppfO B S hS) Z.toAddSubmonoid Y) (hY : IsAlgebraicSpace B S hS Y)
    (hfree : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (a b : APt (fppfO B S hS) Z.toAddSubmonoid T)
      (x : Y.obj T), β.smul a x = β.smul b x → a = b) :
    letI : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
      AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
    IsAlgebraicSpace B S hS (Space.quotientSheaf (relJ β)).obj := by
  obtain ⟨a, b, c, d⟩ := relJ_flat_lfp β hY
  exact Space.bootstrap04S6QuotientSheaf B S hS (relJ β) (relP_isAlgebraicSpace hY) hY
    (relJ_isEquivalenceRelation β hfree) a b c d

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.relJ_flat_lfp
#print axioms AlgMag.ChartStratum.quotient_isAlgebraicSpace
