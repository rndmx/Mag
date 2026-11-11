/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartFinal
import AlgMag.SpacesLimitThm68

/-!
# Theorem 6.8 over a general base

The theorems of `AlgMag.SpacesLimitThm68`, whose hypothesis `h5` (§5 over `Spec ℤ`) is discharged by
`ChartAssembly.section5FromEffectivity`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartAssembly

open LimThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))

local notation "SCH" => BigFppfOver.toScheme B S hS

include hZ in
/-- **Theorem 6.8 (i)**, `S` separated: `LimThm.thm68_family` without `h5`. -/
theorem thm68_family_spaces [S.IsSeparated]
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (A : Type u) (U : A → BigFppfOver B S hS) (L : EtaleChartFamily act A U),
      (∀ a, IsAffine ((SCH).obj (U a))) ∧ (∀ a, IsStronglyFPR (L.equivariant a)) ∧
      ∀ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V) (hV : IsColimit (Cofan.mk V j)),
        ∃ v : yoneda.obj V ⟶ X, IsStronglyFPRAtlas (coprodAction L.act hV) act v ∧
          ∀ Z : AddSubgroup M, IsZFPRAtlas (coprodAction L.act hV) act v Z :=
  thm68_family hZ section5FromEffectivity hM hX hlfp hsep act

include hZ in
/-- **Theorem 6.8 (i), quasi-compact clause**, `S` separated: `LimThm.thm68_qc` without `h5`. -/
theorem thm68_qc_spaces [S.IsSeparated]
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (hq : Space.IsQuasiCompactSpace B S hS X)
    (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v ∧
        (∀ Z : AddSubgroup M, IsZFPRAtlas actV act v Z) ∧ IsSAffineAtlas actV act v :=
  thm68_qc hZ section5FromEffectivity hM hX hlfp hsep hq act

include hZ in
/-- **Strongly-FPR note, Theorem 1.1 (2)**, `S` affine, `X` separated and of finite presentation:
`LimThm.thm11_affine` without `h5`. -/
theorem thm11_affine_spaces [IsAffine S]
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v ∧ IsSAffineAtlas actV act v ∧
        IsAffine ((SCH).obj V) :=
  thm11_affine hZ section5FromEffectivity hM hX hfp hsep act

end AlgMag.ChartAssembly

#print axioms AlgMag.ChartAssembly.thm68_family_spaces
#print axioms AlgMag.ChartAssembly.thm68_qc_spaces
#print axioms AlgMag.ChartAssembly.thm11_affine_spaces
