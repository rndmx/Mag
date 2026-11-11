/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSLocalMain
import AlgMag.ChartQSAsmFinal

/-!
# Noetherian algebraization for `X` quasi-separated

`noetherianAlgebraization_of_atlas`: `X` quasi-separated, locally of finite type over `S` affine of finite type over `ℤ`,
with an affine atlas (in particular `X` quasi-compact). `LocalModelStep X` follows. The named hypothesis
`ChartQSAsm.NoetherianAlgebraizationQS` has no quasi-compactness, and is not needed: it is only used on closed
subspaces of a quasi-compact `X`, see `effectivityQS_of_generic_strata`, `chartLemmaQS_of_generic_strata`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS.ChartQSLocal

open ChartAssembly ChartPoint AlgMag.ChartQSStrat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `HasCharts` for `X` quasi-separated. -/
theorem hasCharts_of_qs [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    (hqs : Space.IsQuasiSeparated B S hS (terminal.from X)) : HasCharts X :=
  hasCharts_of_pullbacksQC hX (pullbacksQC_of_isQuasiSeparated hX hqs)

set_option maxHeartbeats 4000000 in
/-- **Noetherian algebraization**: for `X` quasi-separated, locally of finite type over `S` affine of finite type
over `ℤ`, with an affine atlas. -/
theorem noetherianAlgebraization_of_atlas [IsAffine S] (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hqs : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) (hA : HasAffineAtlas X) :
    NoetherianAlgebraization X := by
  haveI := noetherianSpace_points hSft hlft hA
  let act₀ := trivAct (B := B) (S := S) (hS := hS) X
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) := isAlgebraicSpace_terminal
  have hl : ∀ C : ClosedStable act₀, Space.IsLocallyOfFiniteType B S hS (terminal.from C.Z) := fun C => by
    have h := Space.isLocallyOfFiniteType_comp B S hS C.alg hX hT C.i (terminal.from X)
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS C.i C.closed) hlft
    rwa [terminal.comp_from] at h
  have hsz : ∀ C : ClosedStable act₀, Space.IsQuasiSeparated B S hS (terminal.from C.Z) := fun C => by
    haveI : Mono C.i := Space.mono_of_isClosedImmersion B S hS C.i C.closed
    exact ChartQSStrat.isQuasiSeparated_of_mono_qs C.i _ hqs
  have hbase : Space.IsQuasiSeparated B S hS (toBase X) :=
    Space.isQuasiCompact_of_isPullback B S hS
      (diagPb (𝟙 X) (toBase X) (terminal.from X) (terminal.from _) (terminal.hom_ext _ _)) hqs
  have hE : Effective (ClosedStable.self act₀ hX).actZ := effective_triv hX (fun C => hA.closedStable C)
    (fun C => hasCharts_of_qs C.alg (hsz C))
    (fun C V φ hV he => by haveI := hV; exact isNoetherianRing_chart' hSft (hl C) he)
    (fun C => by
      haveI : Mono C.i := Space.mono_of_isClosedImmersion B S hS C.i C.closed
      exact ChartQSAsm.isAbsolutelyQuasiSeparated_of_mono C.alg C.i hbase)
    (ClosedStable.self act₀ hX)
  refine ChartQSAlg.noetherianAlgebraization_of_exists hX ?_
  intro W _ _ I _ x hx
  let actW := trivAct (B := B) (S := S) (hS := hS) (yoneda.obj W)
  have hιm : ∀ J : Ideal Γ((SCH).obj W, ⊤), Mono (ιc W J) := fun J =>
    (SCH).mono_of_mono_map (inferInstanceAs (Mono (Chart.closedι ((SCH).obj W) J)))
  obtain ⟨φ, hφ, -⟩ := hE W actW I (isCompletePair_of_complete actW I) x ⟨hx, fun n => by
    haveI := hιm (I ^ n)
    exact equivAlong_triv actW _ _ (x n)⟩
  exact ⟨φ, hφ⟩

/-- **`LocalModelStep X`** is not more than noetherian algebraization: it is the intermediate step of the proof. See
`localModelStep`; here `NoetherianAlgebraization` for every closed subspace of `X` of the action `act₀`. -/
theorem noetherianAlgebraization_closed {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hqs : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) (hA : HasAffineAtlas X)
    {act₀ : AAction (fppfO B S hS) M X} (C : ClosedStable act₀) : NoetherianAlgebraization C.Z := by
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) := isAlgebraicSpace_terminal
  have hl : Space.IsLocallyOfFiniteType B S hS (terminal.from C.Z) := by
    have h := Space.isLocallyOfFiniteType_comp B S hS C.alg hX hT C.i (terminal.from X)
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS C.i C.closed) hlft
    rwa [terminal.comp_from] at h
  haveI : Mono C.i := Space.mono_of_isClosedImmersion B S hS C.i C.closed
  exact noetherianAlgebraization_of_atlas hSft C.alg (ChartQSStrat.isQuasiSeparated_of_mono_qs C.i _ hqs) hl
    (hA.closedStable C)

end AlgMag.ChartMain.DeligneQS.ChartQSLocal

namespace AlgMag.ChartQSAsm

open ChartMain ChartPoint ChartConclude ChartAssembly AlgMag.ChartQSStrat
open ChartMain.DeligneQS.ChartQSLocal (noetherianAlgebraization_closed)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]

/-- **Theorem 4.1, existence**, `X` quasi-separated: `effectivityQS_of_pieces` with noetherian algebraization proved. -/
theorem effectivityQS_of_generic_strata (hgen : GenericStabilizerQS B S hS) (hstr : StrataOverQS B S hS M) :
    EffectivityQS B S hS M := by
  intro haff hSft X hX hqs hlft hq actX hfg
  haveI := haff
  haveI := hfg
  intro T _ actT _ m hm φ h1 h2
  have hA := hasAffineAtlas_of_qc hX hq
  haveI := noetherianSpace_points hSft hlft hA
  have hN : Space.HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
    obtain ⟨U, f, hsu, he⟩ := hX.exists_atlas
    haveI := lft_chart hSft hlft he
    haveI : IsLocallyNoetherian (⊤_ Scheme.{u}) := terminal_noeth
    exact ⟨U, f, hsu, he, LocallyOfFiniteType.isLocallyNoetherian (terminal.from ((BigFppfOver.toScheme B S hS).obj U))⟩
  have hE : Effective actX := ChartQS.effective_of_noetherian hX
    (fun C => noetherianAlgebraization_closed hSft hX hqs hlft hA C)
    (fun C => affineStratum_closedStable_qs hgen hX hqs hN C)
    (fun C => hstr haff hSft hfg inferInstance X hX hqs hlft hq actX C)
    (ClosedStable.self actX hX)
  obtain ⟨y, hy, he⟩ := hE T actT m hm φ
    ⟨fun n k e he => h1 n k e he, fun n W t t' g ht => h2 n W t g t' ht⟩
  refine ⟨yonedaEquiv.symm y, ?_, fun n => ?_⟩
  · intro W g t
    exact he (W := W.unop) t g
  · exact hy n

/-- **The chart lemma for quasi-separated spaces**: `chartLemmaQS_of_pieces` with noetherian algebraization proved. -/
theorem chartLemmaQS_of_generic_strata (h11 : ∀ [IsAffine S], Lemma11QS B S hS)
    (hgen : GenericStabilizerQS B S hS) (hstr : StrataOverQS B S hS M) :
    ChartQSTop.ChartLemmaQS B S hS M :=
  chartLemmaQS_of_props h11 (effectivityQS_of_generic_strata hgen hstr)

end AlgMag.ChartQSAsm

#print axioms AlgMag.ChartMain.DeligneQS.ChartQSLocal.tau_thetaY
#print axioms AlgMag.ChartMain.DeligneQS.ChartQSLocal.exists_model
#print axioms AlgMag.ChartMain.DeligneQS.ChartQSLocal.localModelStep
#print axioms AlgMag.ChartMain.DeligneQS.ChartQSLocal.effective_triv
#print axioms AlgMag.ChartMain.DeligneQS.ChartQSLocal.noetherianAlgebraization_of_atlas
#print axioms AlgMag.ChartMain.DeligneQS.ChartQSLocal.noetherianAlgebraization_closed
#print axioms AlgMag.ChartQSAsm.effectivityQS_of_generic_strata
#print axioms AlgMag.ChartQSAsm.chartLemmaQS_of_generic_strata
