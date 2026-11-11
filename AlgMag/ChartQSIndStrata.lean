/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSIndCharts
import AlgMag.ChartQSIndMain
import AlgMag.ChartQSLocalFinal

/-!
# Lemma 4.3 for `X` quasi-separated: the named hypothesis `ChartQSAsm.StrataOverQS`
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS

open AlgMag.ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]

/-- **`StrataOverQS`**: the Deligne block of Lemma 4.3 for `X` quasi-separated, with no named hypothesis. -/
theorem strataOverQS : AlgMag.ChartQSAsm.StrataOverQS B S hS M := by
  intro haff hSft hfg hdec X hX hqs hlft hq actX C
  haveI := haff
  haveI := hfg
  letI : DecidableEq M := hdec
  have hA := hasAffineAtlas_of_qc hX hq
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) := isAlgebraicSpace_terminal
  have hl : Space.IsLocallyOfFiniteType B S hS (terminal.from C.Z) := by
    have h := Space.isLocallyOfFiniteType_comp B S hS C.alg hX hT C.i (terminal.from X)
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS C.i C.closed) hlft
    rwa [terminal.comp_from] at h
  have hsz : Space.IsQuasiSeparated B S hS (terminal.from C.Z) := by
    haveI : Mono C.i := Space.mono_of_isClosedImmersion B S hS C.i C.closed
    exact AlgMag.ChartQSStrat.isQuasiSeparated_of_mono_qs C.i _ hqs
  exact strataOver_qs C (hA.closedStable C)
    (hasCharts_of_pullbacksQC C.alg (pullbacksQC_of_isQuasiSeparated C.alg hsz))
    (fun V φ hV he => by haveI := hV; exact isNoetherianRing_chart' hSft hl he)

/-- **The chart lemma for quasi-separated spaces**, from Lemma 1.1 and the generic stabilizer of Lemma 4.2 alone:
the noetherian algebraization and the Deligne block (Lemma 4.3) are proved. -/
theorem chartLemmaQS_of_lemma11_generic (h11 : ∀ [IsAffine S], ChartPoint.Lemma11QS B S hS)
    (hgen : AlgMag.ChartQSStrat.GenericStabilizerQS B S hS) : ChartQSTop.ChartLemmaQS B S hS M :=
  AlgMag.ChartQSAsm.chartLemmaQS_of_generic_strata h11 hgen strataOverQS

end AlgMag.ChartMain.DeligneQS

#print axioms AlgMag.ChartMain.DeligneQS.strataOverQS
#print axioms AlgMag.ChartMain.DeligneQS.chartLemmaQS_of_lemma11_generic
