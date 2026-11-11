/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumData
import AlgMag.ChartEffectiveFinal
import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties

/-!
# The affine stratum lemma: a nonempty stable affine open

This is the stratification step in the local structure theorem for actions of diagonalizable
groups `D(M)` (the case `G = D(M)` of Alper–Hall–Rydh, Cor. 10.2), used for the
noetherian induction in `ChartMain`.

`affineStratum`: a nonempty separated locally noetherian algebraic space with an action of `D(M)`, `M`
finitely generated, has a nonempty affine `D(M)`-stable open.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A presheaf with a monomorphism to a separated one is separated. -/
theorem isSeparatedOver_of_mono {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ι : Y ⟶ X) [Mono ι]
    (hsep : Space.IsSeparatedOver B S hS X) : Space.IsSeparatedOver B S hS Y := by
  rw [Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS terminalIsTerminal (terminal.from Y)]
  have he := (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS terminalIsTerminal
        (terminal.from X)).1 hsep
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_diagonal_of_mono ι (terminal.from Y) (terminal.from X) (𝟙 _)
      (terminal.hom_ext _ _)) he

/-- An étale morphism is locally of finite type. -/
theorem isLocallyOfFiniteType_of_etale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : Space.IsEtale B S hS f) : Space.IsLocallyOfFiniteType B S hS f := by
  intro U V a b h ha hb comm
  have : Etale ((SCH).map h) := Space.etale_of_comp_etale_chart B S hS (hf U a ha) hb comm
  infer_instance

/-- **Affine stratum lemma**: a nonempty separated, locally noetherian algebraic space with an action of `D(M)`,
for `M` finitely generated, has a nonempty affine `D(M)`-stable open. -/
theorem affineStratum {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hNoe : Space.HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (act : AAction (fppfO B S hS) M X) : ChartMain.AffineStratum X act := by
  classical
  rintro ⟨W, ⟨w⟩, ⟨x₀⟩⟩
  haveI : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  haveI : Countable M := countable_of_fg M
  have hneX : Nonempty (Space.points B S hS X) :=
    ⟨Space.pointsMap B S hS _ (yonedaEquiv.symm x₀) ((Space.pointsEquivScheme B S hS W).symm w)⟩
  obtain ⟨N, K, ⟨T₁, ⟨t₁⟩, ⟨x₁⟩, hu₁⟩, htors, hK⟩ := exists_unit_data (M := M) hneX
  haveI : AddGroup.FG (M ⧸ K) := inferInstance
  haveI : Countable (M ⧸ K) := countable_of_fg _
  -- `Z = X[1/N]`
  let Zf := invSub X N
  have hZo := invSub_isOpen hX N
  let Z := Zf.toFunctor
  have hZ : IsAlgebraicSpace B S hS Z := hZo.1
  have hNZ : ∀ (T : BigFppfOver B S hS) (_ : Z.obj (op T)), IsUnit (N : Γ((SCH).obj T, ⊤)) :=
    fun T z => (mem_invSub_iff N z.1).1 z.2
  have injZ : ∀ T, Function.Injective (Zf.ι.app T) := fun T a b e => Subtype.ext e
  let actZ : AAction (fppfO B S hS) M Z := actOfMono act Zf.ι injZ (fun {T} h t =>
    ⟨⟨act.smul h t.1, (mem_invSub_iff N _).2 (hNZ T.unop t)⟩, rfl⟩)
  have hactZ : IsEquivariant actZ act Zf.ι := actOfMono_spec _ _ _ _
  -- the reduction, with `D(M/K)`
  let Rd := Space.reduction B S hS Z hZ
  have hcl : Space.IsClosedSubspace B S hS Rd :=
    (Space.isAlgebraicSpaceStructure_reduction B S hS Z hZ).isClosedSubspace
  have hRa : IsAlgebraicSpace B S hS Rd.toFunctor := hcl.1
  let act' := actZ.comap (QuotientAddGroup.mk' K)
  have injR : ∀ T, Function.Injective (Rd.ι.app T) := fun T a b e => Subtype.ext e
  let act2 : AAction (fppfO B S hS) (M ⧸ K) Rd.toFunctor := actOfMono act' Rd.ι injR (fun {T} h t =>
    ⟨⟨act'.smul h t.1, smul_mem_reduction act' hZ N hNZ htors (T := T.unop) h t.2⟩, rfl⟩)
  have hact2 : IsEquivariant act2 act' Rd.ι := actOfMono_spec _ _ _ _
  -- a chart of the reduction
  have hsepZ : Space.IsSeparatedOver B S hS Z := isSeparatedOver_of_mono Zf.ι hsep
  have hsepR : Space.IsSeparatedOver B S hS Rd.toFunctor := isSeparatedOver_of_mono Rd.ι hsepZ
  have hlft : Space.IsLocallyOfFiniteType B S hS (Rd.ι ≫ Zf.ι) :=
    Space.isLocallyOfFiniteType_comp B S hS hRa hZ hX Rd.ι Zf.ι
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS Rd.ι hcl.2)
      (isLocallyOfFiniteType_of_etale _ (Space.isEtale_of_isOpenImmersion B S hS hZo.2))
  have hNoeR := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hRa hX _ hlft hNoe
  have hneZ : Nonempty (Space.points B S hS Z) :=
    ⟨Space.pointsMap B S hS _ (yonedaEquiv.symm (⟨x₁, (mem_invSub_iff N _).2 hu₁⟩ : Z.obj (op T₁)))
      ((Space.pointsEquivScheme B S hS T₁).symm t₁)⟩
  have hneR : Nonempty (Space.points B S hS Rd.toFunctor) := by
    obtain ⟨z⟩ := hneZ
    obtain ⟨r, -⟩ := Space.surjective_pointsMap_ι_reduction B S hS Z hZ z
    exact ⟨r⟩
  obtain ⟨V, p, A, hVa, hVd, hVn, hE, hAa, hAo, ⟨v⟩⟩ := exists_integral_chart hRa
    (Space.hasEtaleLocalProperty_isReduced_reduction B S hS Z hZ) hNoeR hneR
  obtain ⟨U', actU', f', hU'a, hU'n, hf'e, hf'o⟩ :=
    exists_stable_affine_of_chart act2 hVa hVd hVn p hRa hsepR hE A hAa hAo v
  obtain ⟨G, hG, ⟨T, hTa, ⟨e⟩⟩, ⟨W', hW'n, ⟨g₀⟩⟩, hst⟩ := exists_stable_open_of_reduction actZ hZ K act2 hact2
    (fun hk b z h => hK hk b z.1 ((mem_invSub_iff N z.1).1 z.2) h) actU' f' hU'a hU'n hf'e hf'o
  -- the stable affine open of `X`
  let f : yoneda.obj T ⟶ X := e.inv ≫ G.ι ≫ Zf.ι
  have hfo : Space.IsOpenImmersion B S hS f := by
    have h1 : Space.IsOpenImmersion B S hS (G.ι ≫ Zf.ι) :=
      Space.isOpenImmersion_comp B S hS _ _ hG.2 hZo.2
    exact MorphismProperty.RespectsIso.precomp _ e.inv _ h1
  have hfm : Mono f := Space.mono_of_isOpenImmersion B S hS f hfo
  have hinj : ∀ T', Function.Injective (f.app T') := fun T' =>
    (CategoryTheory.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hfm T')
  have hstab : ∀ {T' : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T')
      (t : (yoneda.obj T).obj T'), ∃ t', f.app T' t' = act.smul h (f.app T' t) := by
    intro T' h t
    let g := e.inv.app T' t
    let g' : G.toFunctor.obj T' := ⟨actZ.smul h g.1, hst (T := T'.unop) h g.2⟩
    refine ⟨e.hom.app T' g', ?_⟩
    have e1 : e.inv.app T' (e.hom.app T' g') = g' :=
      ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id T') g'
    change Zf.ι.app T' (G.ι.app T' (e.inv.app T' (e.hom.app T' g'))) = _
    rw [e1]
    exact hactZ h g.1
  have hTn : Nonempty ((SCH).obj T) := by
    let t : W' ⟶ T := e.hom.app (op W') ⟨g₀.1, g₀.2⟩
    obtain ⟨w'⟩ := hW'n
    exact ⟨(SCH).map t w'⟩
  exact ⟨T, actOfMono act f hinj hstab, f, hTa, hTn, actOfMono_spec _ _ _ _, hfo⟩

/-- **Affine stratum lemma**, in the form `ChartMain.effective_of_noetherian` and
`ChartMain.effective_of_noetherian_atlas` ask for: every closed stable subspace of a separated, locally
noetherian `X₀` has a nonempty affine stable open, or is empty. -/
theorem affineStratum_closedStable {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
    {act₀ : AAction (fppfO B S hS) M X} (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X)
    (hNoe : Space.HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (C : ChartMain.ClosedStable act₀) : ChartMain.AffineStratum C.Z C.actZ := by
  have hm : Mono C.i := Space.mono_of_isClosedImmersion B S hS C.i C.closed
  exact affineStratum C.alg (isSeparatedOver_of_mono C.i hsep)
    (Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS C.alg hX C.i
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS C.i C.closed) hNoe) C.actZ

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.affineStratum
#print axioms AlgMag.ChartStratum.affineStratum_closedStable
