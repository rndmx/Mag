/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartFormal2
import AlgMag.ChartArtinFP
import AlgMag.ChartStubs
import AlgMag.ChartS5Input

/-!
# `Section5FromEffectivity`

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.
The equivariant Artin approximation step from equivariant effectivity: `exists_section5_input`
(tower to `Spec C → X`) and `section5Output_of_input`. Some Stacks inputs enter as hypotheses
from `AlgMag.ChartStubs`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartAssembly

open ChartMain ChartS5 ChartConclude ChartPoint

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

/-- `Γ(S)` is of finite type over `ℤ`. -/
theorem finiteType_top [IsAffine S] (hSft : LocallyOfFiniteType (terminal.from S)) :
    Algebra.FiniteType ℤ (RT (siteTop (B := B) (S := S) (hS := hS))) := by
  let e := terminalIsoIsTerminal specULiftZIsTerminal
  let g : S ⟶ Spec (.of (ULift.{u} ℤ)) := terminal.from S ≫ e.hom
  have hg : LocallyOfFiniteType g := inferInstance
  have hft1 := g.finiteType_appLE (U := ⊤) (V := ⊤) (isAffineOpen_top _) (isAffineOpen_top _) le_top
  have h0 : ((g.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv.hom).FiniteType :=
    hft1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv).2)
  have h2 : ((ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ) : ℤ →+* ULift.{u} ℤ).FiniteType :=
    RingHom.FiniteType.of_surjective _ ULift.ringEquiv.symm.surjective
  have h3 := h0.comp h2
  refine (RingHom.finiteType_algebraMap).1 ?_
  rw [show algebraMap ℤ (RT (siteTop (B := B) (S := S) (hS := hS))) = _ from RingHom.ext_int _ _]
  exact h3

/-- **`Section5FromEffectivity`.** -/
theorem section5FromEffectivity : Section5FromEffectivity B S hS M := by
  intro _ hSft X hX hsep hlft _ actX p N hN o u ho hoe hux heff
  obtain ⟨hfin, T, hTa, actT, m, φ, u', D⟩ :=
    exists_section5_input hSft hX hsep hlft actX p N o u ho hoe hux heff
  obtain ⟨V, hVa, e, v, he, hve, hvs⟩ := exists_chart_at_point hX hsep p
  letI := gradedRingOfAction actT
  haveI := D.noeth
  haveI := isNoetherianRing_chart' hSft hlft he
  haveI := finiteType_top (B := B) (hS := hS) hSft
  haveI : Finite p.k := by
    letI := p.field
    let e1 : Γ((BigFppfOver.toScheme B S hS).obj p.P, ⊤) ≃+* Γ(Spec (.of p.k), ⊤) :=
      (Scheme.Γ.mapIso p.iso.symm.op).commRingCatIsoToRingEquiv
    let e2 : Γ(Spec (.of p.k), ⊤) ≃+* p.k := (Scheme.ΓSpecIso (.of p.k)).commRingCatIsoToRingEquiv
    exact Finite.of_surjective _ (e1.trans e2).surjective
  have hXft : Space.IsLocallyOfFiniteType B S hS (toBase X) := by
    intro U' V' f' g' α hf' hg' c
    haveI := Space.isMultiplicative_presheaf_etale B S hS
    have hY : IsTerminal (yoneda.obj (siteTop (B := B) (S := S) (hS := hS))) :=
      (Over.mkIdTerminal).isTerminalObj yoneda
    have hiso : IsIso (terminal.from (yoneda.obj (siteTop (B := B) (S := S) (hS := hS)))) :=
      ⟨hY.from _, hY.hom_ext _ _, terminal.hom_ext _ _⟩
    have hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
        (g' ≫ terminal.from _) :=
      MorphismProperty.comp_mem _ _ _ hg' (MorphismProperty.of_isIso _ _)
    exact hlft U' V' f' (g' ≫ terminal.from _) α hf' hb (terminal.hom_ext _ _)
  obtain ⟨Tg, hTg, hgen⟩ := D.hgen
  exact section5Output_of_input actT ChartArtin.artinApproxFP (toCompletePair D.complete) actX hX hXft
    (limitPreserving_of_lft hSft hX hlft) φ D.equivariant p u' D.liesOver D.kills D.surj Tg hTg hgen
    D.hOfC D.hMono he v hve hvs (fun j hj => by
      obtain ⟨hoj, hi⟩ := D.thick j hj
      exact ⟨hoj, hi e v hve⟩)

end AlgMag.ChartAssembly

#print axioms AlgMag.ChartAssembly.section5FromEffectivity
