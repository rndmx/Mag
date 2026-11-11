/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSIndStrata
import AlgMag.ChartQSL11Lemma
import AlgMag.ChartQSStabGenFinal

/-!
# The chart lemma for quasi-separated spaces, closed

`ChartQSTop.ChartLemmaQS`: Alper-Hall-Rydh, Corollary 20.2, cited by the printed proof of Theorem A.2 (ii).
-/

universe u

namespace AlgMag.ChartMain.DeligneQS

open AlgebraicGeometry

/-- **`ChartLemmaQS`** holds, for the site, base and `M` of its statement. -/
theorem chartLemmaQS (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] : ChartQSTop.ChartLemmaQS B S hS M :=
  chartLemmaQS_of_lemma11_generic (fun {_} => AlgMag.ChartQSL11.lemma11QS_holds)
    (AlgMag.ChartQSStabGen.genericStabilizerQS B S hS)

end AlgMag.ChartMain.DeligneQS

#print axioms AlgMag.ChartMain.DeligneQS.chartLemmaQS
