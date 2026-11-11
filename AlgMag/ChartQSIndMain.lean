/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSIndInst
import AlgMag.ChartMain

/-!
# Theorem 4.1, existence, for `X` quasi-separated

The noetherian induction `ChartQS.effective_of_noetherian` with Lemma 4.3 from
`DeligneQS.strataOver_qs`. Named hypotheses, each a peer's piece:

* `DeligneQS.HasCharts` on the closed stable subspaces: `Z ×_X V` is covered by an affine;
* `hC`: noetherian algebraization (`chart-qs-proof.md`, Step 4);
* `h42`: Lemma 4.2 (`chart-qs-proof.md`, Step 5 as repaired).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS

open AlgMag.ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- **Theorem 4.1, existence**, `X` quasi-compact, locally of finite type over `S` affine of finite type
over `ℤ`, not assumed separated. As `ChartMain.effective_of_lft`, with `hsep` replaced by the three named
hypotheses. -/
theorem effective_of_lft_qs [AddMonoid.FG M] [DecidableEq M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X)
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (actX : AAction (fppfO B S hS) M X)
    (hch : ∀ C : ClosedStable actX, HasCharts C.Z)
    (hC : ∀ C : ClosedStable actX, NoetherianAlgebraization C.Z)
    (h42 : ∀ C : ClosedStable actX, AffineStratum C.Z C.actZ) :
    Effective actX := by
  have hA := hasAffineAtlas_of_qc hX hq
  haveI := noetherianSpace_points hSft hlft hA
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_terminal
  have hl : ∀ C : ClosedStable actX,
      Space.IsLocallyOfFiniteType B S hS (terminal.from C.Z) := fun C => by
    have h := Space.isLocallyOfFiniteType_comp B S hS C.alg hX hT C.i (terminal.from X)
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS C.i C.closed) hlft
    rwa [terminal.comp_from] at h
  exact ChartQS.effective_of_noetherian hX hC h42
    (fun C => strataOver_qs C (hA.closedStable C) (hch C)
      (fun V φ hV he => by haveI := hV; exact isNoetherianRing_chart' hSft (hl C) he))
    (ClosedStable.self actX hX)

end AlgMag.ChartMain.DeligneQS

#print axioms AlgMag.ChartMain.DeligneQS.effective_of_lft_qs
