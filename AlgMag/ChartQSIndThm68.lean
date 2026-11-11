/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSIndClose

/-!
# Theorem 6.8 (ii) of Algebraic Magnetism, with no named hypothesis

`ChartQSTop.thm68_ii` and `ChartQSTop.thm68_ii_qc_final` with `ChartLemmaQS` proved. The separatedness of `S` is
the addition recorded for `exists_family_qs`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS

open ChartQSTop LimThm LimAct LimOrbit LimView

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- **Theorem 6.8 (ii)** of Algebraic Magnetism: `X` quasi-separated, locally of finite presentation over `S`
separated, `M/Z` torsion-free in the form `IrreducibleFibres`. A chart family from affine schemes, and for each
coproduct of it in the site a `Z`-FPR atlas. -/
theorem thm68_ii_proved [S.IsSeparated] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X)
    {Z : AddSubgroup M} (hMZ : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ (A : Type u) (U : A → BigFppfOver B S hS) (L : EtaleChartFamily act A U),
      (∀ a, IsAffine ((SCH).obj (U a))) ∧
      ∀ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V) (hV : IsColimit (Cofan.mk V j)),
        ∃ v : yoneda.obj V ⟶ X, IsZFPRAtlas (coprodAction L.act hV) act v Z :=
  thm68_ii hZ (chartLemmaQS B _ hZ M) hM hX hlfp hqs act hMZ hirr

/-- **Theorem 6.8 (ii), quasi-compact clause**: an `S`-affine `Z`-FPR atlas. -/
theorem thm68_ii_qc_proved [S.IsSeparated] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (hq : Space.IsQuasiCompactSpace B S hS X)
    (act : AAction (fppfO B S hS) M X)
    {Z : AddSubgroup M} (hMZ : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsZFPRAtlas actV act v Z ∧ IsSAffineAtlas actV act v :=
  thm68_ii_qc_final hZ (chartLemmaQS B _ hZ M) hM hX hlfp hqs hq act hMZ hirr

end AlgMag.ChartMain.DeligneQS

#print axioms AlgMag.ChartMain.DeligneQS.thm68_ii_proved
#print axioms AlgMag.ChartMain.DeligneQS.thm68_ii_qc_proved
