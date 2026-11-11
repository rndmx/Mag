/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumRelation
import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent

/-!
# The quotient by a free `D(Z)`-action (affine stratum lemma, step 5)

`relP Y Z` is the fibre product of `D(Z)` and `Y` over the terminal presheaf; the quotient of an
algebraic space by a free action is an algebraic space, by Stacks 04S6.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {Z : AddSubgroup M}
variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `D(Z)` over the base, as an object of the site. -/
noncomputable def dZ (Z : AddSubgroup M) (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    UniversalPoint (fppfO B S hS) Z.toAddSubmonoid (⊤_ (BigFppfOver B S hS)) :=
  monAffUniversal Z.toAddSubmonoid (contains_zmon_of_countable hS _) _

/-- The projection `D(Z) × Y → D(Z)`. -/
noncomputable def relToG : relP Y Z ⟶ yoneda.obj (dZ Z B S hS).P where
  app T := ↾ fun r => (dZ Z B S hS).lift (terminal.from _) r.1
  naturality T T' f := by
    ext1
    refine DFunLike.ext _ _ fun r => ?_
    refine ((dZ Z B S hS).uniq _ _ _ (terminal.hom_ext _ _) ?_).symm
    change APt.res (f.unop ≫ (dZ Z B S hS).lift (terminal.from _) r.1).op _ = APt.res f r.1
    rw [op_comp, APt.res_comp]
    exact congrArg (APt.res f.unop.op) ((dZ Z B S hS).res_lift (terminal.from _) r.1)

/-- `D(Z) × Y` is the fibre product over the terminal presheaf. -/
theorem relP_isPullback :
    IsPullback (relToG (Y := Y) (Z := Z)) relSrc (terminal.from _) (terminal.from Y) := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact NatTrans.congr_app (terminal.hom_ext (relToG (Y := Y) (Z := Z) ≫ terminal.from _) (relSrc ≫ terminal.from Y)) T
  · rintro x y ⟨e1, e2⟩
    refine Prod.ext ?_ e2
    have e1' : (dZ Z B S hS).lift (terminal.from _) x.1 = (dZ Z B S hS).lift (terminal.from _) y.1 := e1
    have h := (dZ Z B S hS).res_lift (terminal.from _) x.1
    rw [e1', (dZ Z B S hS).res_lift] at h
    exact h.symm
  · intro x₂ x₃ _
    refine ⟨(APt.res (Quiver.Hom.op x₂) (dZ Z B S hS).u, x₃), ?_, rfl⟩
    exact ((dZ Z B S hS).uniq _ _ x₂ (terminal.hom_ext _ _) rfl).symm

/-- **Stacks 02X2** for `D(Z) × Y`. -/
theorem relP_isAlgebraicSpace (hY : IsAlgebraicSpace B S hS Y) :
    IsAlgebraicSpace B S hS (relP Y Z) := by
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    Space.isAlgebraicSpace_of_iso B S hS (Space.yonedaTerminalIso B S hS)
      (isAlgebraicSpace_yoneda B S hS _)
  have hG : IsAlgebraicSpace B S hS (yoneda.obj (dZ Z B S hS).P) := isAlgebraicSpace_yoneda B S hS _
  have hP := isAlgebraicSpace_pullback B S hS (terminal.from (yoneda.obj (dZ Z B S hS).P))
    (terminal.from Y) hG hY hT
  exact Space.isAlgebraicSpace_of_iso B S hS
    (relP_isPullback (Y := Y) (Z := Z)).isoPullback.symm hP

end AlgMag.ChartStratum
