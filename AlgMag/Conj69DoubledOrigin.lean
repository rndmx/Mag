/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Conj69DoubledPlane
import AlgMag.Conj69Separated

/-!
# Conjecture 6.9 fails for `S` not separated

`S` the plane with doubled origin over a field, `X` one chart, any `M`, any action. No étale `U → X` with `U` a disjoint
union of `S`-affine schemes reaches the origin, so `X` has no equivariant atlas in the sense of Definition 6.1 (iv).
-/

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite

universe u

namespace AlgMag.Conj69

open AlgMag.ChartAssembly LimThm

variable (k : Type u) [Field k] {B : BigFppfSite.{u}}

/-- The chart is an object of the site as soon as the doubled plane is. -/
theorem contains_Pl (hS : B.Contains (doubledPlane k)) : B.Contains (Pl k) :=
  lt_of_le_of_lt (Scheme.size_le_of_locallyOfFiniteType (chart₁ k)) hS

/-- The first chart, as an object of the site over the doubled plane. -/
noncomputable def chartObj (hS : B.Contains (doubledPlane k)) : BigFppfOver B (doubledPlane k) hS :=
  siteObject B _ hS (contains_Pl k hS) (chart₁ k)

variable {k}

/-- **Remark, `S` not separated.** One chart of the plane with doubled origin has no equivariant atlas (Definition 6.1
(iv)), for any `M` and any action. -/
theorem no_atlas_chart (hS : B.Contains (doubledPlane k)) {M : Type u} [AddCommGroup M]
    (act : AAction (fppfO B _ hS) M (yoneda.obj (chartObj k hS)))
    {U : BigFppfOver B _ hS} (actU : AAction (fppfO B _ hS) M (yoneda.obj U))
    (f : yoneda.obj U ⟶ yoneda.obj (chartObj k hS)) : ¬ IsEquivariantAtlas actU act f := by
  intro h
  obtain ⟨g₀, rfl⟩ : ∃ g₀, yoneda.map g₀ = f := ⟨yoneda.preimage f, yoneda.map_preimage f⟩
  let G := (BigFppfOver.toScheme B _ hS).map g₀
  have he : Etale G := (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B _ hS _ g₀).1 h.etale
  have hs : Surjective G :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B _ hS _ g₀).1 h.surjective
  obtain ⟨z, hz⟩ := exists_origin k
  obtain ⟨u, hu⟩ := hs.surj z
  obtain ⟨A, V, hV⟩ := h.decomposition
  have hmem : u ∈ iSup V := by rw [hV.iSup_eq_top]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  let gw : (V a).toScheme ⟶ Pl k := (V a).ι ≫ G
  have hG : G ≫ chart₁ k = structMap U := congrArg (fun m => m.hom) (Over.w g₀)
  haveI : IsAffineHom (gw ≫ chart₁ k) := by
    have e : gw ≫ chart₁ k = (V a).ι ≫ structMap U := by
      exact (Category.assoc (V a).ι G
        (show (BigFppfOver.toScheme B _ hS).obj (chartObj k hS) ⟶ _ from chart₁ k)).trans
          (congrArg (fun m => (V a).ι ≫ m) hG)
    rw [e]; exact hV.isAffineHom a
  haveI : Flat G := (Etale.iff_flat_and_formallyUnramified.1 he).1
  haveI : Flat gw := MorphismProperty.comp_mem @Flat _ _ inferInstance ‹Flat G›
  refine no_chart_core (chart₁ k) (chart₂ k).opensRange (isAffineOpen_opensRange _)
    (chart₁_mem_iff k) gw (⟨u, ha⟩ : V a) ?_
  have : gw (⟨u, ha⟩ : V a) = z := hu
  rwa [this]

/-- The structure map of the chart, in the site. -/
noncomputable def chartToT1 (hS : B.Contains (doubledPlane k)) : chartObj k hS ⟶ LimOrbit.T1 B _ hS :=
  Over.homMk (ObjectProperty.homMk (chart₁ k)) (by rfl)

/-- The chart satisfies the hypotheses of Conjecture 6.9 (i) over the doubled plane. -/
theorem chart_hyps (hS : B.Contains (doubledPlane k)) :
    IsAlgebraicSpace B _ hS (yoneda.obj (chartObj k hS)) ∧
    Space.IsSeparatedOver B _ hS (yoneda.obj (chartObj k hS)) ∧
    Space.IsLocallyOfFinitePresentation B _ hS (toT1 (yoneda.obj (chartObj k hS))) := by
  have e : toT1 (yoneda.obj (chartObj k hS)) = yoneda.map (chartToT1 hS) := toT1_ext _ _
  haveI hop : IsOpenImmersion ((BigFppfOver.toScheme B _ hS).map (chartToT1 hS)) :=
    inferInstanceAs (IsOpenImmersion (chart₁ k))
  refine ⟨isAlgebraicSpace_yoneda B _ hS _, ?_, ?_⟩
  · refine (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B _ hS (LimOrbit.isTerminal_T1 B _ hS)
      (yoneda.map (chartToT1 hS))).2 ((Space.isSeparated_yoneda_map_iff B _ hS _).2 inferInstance)
  · rw [e]
    exact Space.isLocallyOfFinitePresentation_yoneda_map B _ hS _ inferInstance

/-- **Conjecture 6.9 (i)** for a given `S`, printed form, no separatedness of `S`. -/
def Conj69iOver (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (act : AAction (fppfO B S hS) M X),
    IsAlgebraicSpace B S hS X → Space.IsSeparatedOver B S hS X →
    Space.IsLocallyOfFinitePresentation B S hS (toT1 X) →
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v

/-- Conjecture 6.9 (i) with "`S` arbitrary" fails on the plane with doubled origin, for every `M`, in particular `M = 0`. -/
theorem not_conj69_doubledPlane (hS : B.Contains (doubledPlane k)) (M : Type u) [AddCommGroup M] :
    ¬ Conj69iOver B (doubledPlane k) hS M := by
  intro h
  obtain ⟨h1, h2, h3⟩ := chart_hyps (k := k) hS
  obtain ⟨V, actV, v, hv⟩ := h _ (AAction.trivial _ M _) h1 h2 h3
  exact no_atlas_chart hS _ actV v hv.atlas

end AlgMag.Conj69

#print axioms AlgMag.Conj69.no_atlas_chart
#print axioms AlgMag.Conj69.chart_hyps
#print axioms AlgMag.Conj69.not_conj69_doubledPlane
