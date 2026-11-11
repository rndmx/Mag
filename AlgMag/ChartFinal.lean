/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Close
import AlgMag.ChartThm68

/-!
# The chart lemma, and Theorem 6.8

`chartLemma` is `chartLemmaStatementFG_of_section5` applied to `section5FromEffectivity`; the other two
theorems pass it to `thm11_ft_final` and `thm68_i`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- **The chart lemma** (`AlgMag.ChartLemmaStatementFG`, the chart-lemma proof, Theorem). -/
theorem chartLemma : ChartLemmaStatementFG B S hS M :=
  chartLemmaStatementFG_of_section5 section5FromEffectivity

/-- **Strongly-FPR note, Theorem 1.1 (2)**, `S` affine of finite type over `ℤ`, `X` separated of finite
type. -/
theorem thm11_ft [AddGroup.FG M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV actX v ∧
        IsSAffineAtlas actV actX v ∧ IsAffine ((SCH).obj V) :=
  thm11_ft_final hSft hX hsep hft actX (chartLemma (AddGroup.fg_iff_addMonoid_fg.1 inferInstance))

/-- **Theorem 6.8 = Theorem A.2 (i)**, for `X` separated of finite type over `S` affine of finite type
over `ℤ`: an `S`-affine `Z`-FPR atlas, one for all subgroups `Z`. -/
theorem thm68 [AddGroup.FG M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), (∀ Z : AddSubgroup M, IsZFPRAtlas actV actX v Z) ∧
        IsSAffineAtlas actV actX v :=
  thm68_i hSft hX hsep hft actX (chartLemma (AddGroup.fg_iff_addMonoid_fg.1 inferInstance))

end AlgMag.ChartAssembly

#print axioms AlgMag.ChartAssembly.chartLemma
#print axioms AlgMag.ChartAssembly.thm11_ft
#print axioms AlgMag.ChartAssembly.thm68
