/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSAsm
import AlgMag.ChartQSEffective
import AlgMag.ChartQSStratCore

/-!
# `ChartLemmaQS` from the remaining pieces

`EffectivityQS` is discharged by the noetherian induction `ChartQS.effective_of_noetherian`, so that
`ChartQSTop.ChartLemmaQS` depends only on the named hypotheses of the other pieces:

* `ChartPoint.Lemma11QS`: Lemma 1.1;
* `ChartQSStrat.GenericStabilizerQS`: the generic stabilizer in Lemma 4.2;
* `NoetherianAlgebraizationQS`: Step 4 of the chart-lemma proof without separatedness;
* `StrataOverQS`: Lemma 4.3, the output of the Deligne block.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQSAsm

open ChartMain ChartPoint ChartConclude ChartAssembly AlgMag.ChartQSStrat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u) [AddCommGroup M]

/-- **Named hypothesis, Step 4**: noetherian algebraization for quasi-separated `X` locally of finite
type over `S`. `ChartQSAlg.noetherianAlgebraization_of_localModel` reduces it to `LocalModelStep`. -/
def NoetherianAlgebraizationQS : Prop :=
  IsAffine S → LocallyOfFiniteType (terminal.from S) →
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
    Space.IsQuasiSeparated B S hS (terminal.from X) →
    Space.IsLocallyOfFiniteType B S hS (terminal.from X) → NoetherianAlgebraization X

/-- **Named hypothesis, Lemma 4.3**: the output of the Deligne block for quasi-separated `X` locally of
finite type and quasi-compact over `S`. -/
def StrataOverQS : Prop :=
  IsAffine S → LocallyOfFiniteType (terminal.from S) → ∀ (_ : AddMonoid.FG M) (_ : DecidableEq M)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
    Space.IsQuasiSeparated B S hS (terminal.from X) →
    Space.IsLocallyOfFiniteType B S hS (terminal.from X) → Space.IsQuasiCompactSpace B S hS X →
    ∀ (actX : AAction (fppfO B S hS) M X) (C : ClosedStable actX), ChartQS.StrataOver C

variable {B S hS M}

/-- **Theorem 4.1, existence**, `X` quasi-separated, from its three inputs. -/
theorem effectivityQS_of_pieces (hgen : GenericStabilizerQS B S hS)
    (halg : NoetherianAlgebraizationQS B S hS) (hstr : StrataOverQS B S hS M) :
    EffectivityQS B S hS M := by
  intro haff hSft X hX hqs hlft hq actX hfg
  haveI := haff
  haveI := hfg
  intro T _ actT _ m hm φ h1 h2
  have hA := hasAffineAtlas_of_qc hX hq
  haveI := noetherianSpace_points hSft hlft hA
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_terminal
  have hl : ∀ C : ClosedStable actX,
      Space.IsLocallyOfFiniteType B S hS (terminal.from C.Z) := fun C => by
    have h := Space.isLocallyOfFiniteType_comp B S hS C.alg hX hT C.i (terminal.from X)
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS C.i C.closed) hlft
    rwa [terminal.comp_from] at h
  have hsz : ∀ C : ClosedStable actX, Space.IsQuasiSeparated B S hS (terminal.from C.Z) := fun C => by
    haveI : Mono C.i := Space.mono_of_isClosedImmersion B S hS C.i C.closed
    exact isQuasiSeparated_of_mono_qs C.i _ hqs
  have hN : Space.HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
    obtain ⟨U, f, hsu, he⟩ := hX.exists_atlas
    haveI := lft_chart hSft hlft he
    haveI : IsLocallyNoetherian (⊤_ Scheme.{u}) := terminal_noeth
    exact ⟨U, f, hsu, he, LocallyOfFiniteType.isLocallyNoetherian (terminal.from ((BigFppfOver.toScheme B S hS).obj U))⟩
  have hE : Effective actX := ChartQS.effective_of_noetherian hX
    (fun C => halg haff hSft C.Z C.alg (hsz C) (hl C))
    (fun C => affineStratum_closedStable_qs hgen hX hqs hN C)
    (fun C => hstr haff hSft hfg inferInstance X hX hqs hlft hq actX C)
    (ClosedStable.self actX hX)
  obtain ⟨y, hy, he⟩ := hE T actT m hm φ
    ⟨fun n k e he => h1 n k e he, fun n W t t' g ht => h2 n W t g t' ht⟩
  refine ⟨yonedaEquiv.symm y, ?_, fun n => ?_⟩
  · intro W g t
    exact he (W := W.unop) t g
  · exact hy n

/-- **The chart lemma for quasi-separated spaces**, from the four remaining pieces. -/
theorem chartLemmaQS_of_pieces (h11 : ∀ [IsAffine S], Lemma11QS B S hS)
    (hgen : GenericStabilizerQS B S hS) (halg : NoetherianAlgebraizationQS B S hS)
    (hstr : StrataOverQS B S hS M) : ChartQSTop.ChartLemmaQS B S hS M :=
  chartLemmaQS_of_props h11 (effectivityQS_of_pieces hgen halg hstr)

end AlgMag.ChartQSAsm

#print axioms AlgMag.ChartQSAsm.effectivityQS_of_pieces
#print axioms AlgMag.ChartQSAsm.chartLemmaQS_of_pieces
