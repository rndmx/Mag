/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSIndThm68
import AlgMag.FinalNonQCAtlas

/-!
# Theorem 6.8 (ii) of Algebraic Magnetism with a genuine `Z`-FPR atlas

One affine chart per point of an atlas `U₀` of `X`; the coproduct lies in the site by size
(`Final.exists_cofan_of_size`). The separatedness of `S` is the addition recorded for `exists_family_qs`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space Cardinal

universe u

namespace AlgMag.ChartMain.DeligneQS

open ChartQSTop LimThm LimAct LimOrbit LimView ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- One affine étale equivariant chart per point of an atlas of `X`, with a coproduct in the site. -/
theorem final2_exists_small_family_qs [S.IsSeparated] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X) :
    ∃ (A : Type u) (U : A → BigFppfOver B S hS) (L : EtaleChartFamily act A U)
      (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V), Nonempty (IsColimit (Cofan.mk V j)) := by
  obtain ⟨U0, g, hs, -⟩ := hX.exists_atlas
  have hp := fun u : (SCH).obj U0 => exists_charts_at_qs hZ (chartLemmaQS B _ hZ M) hM hX hlfp hqs act
    (Space.pointsMap B S hS _ g ((Space.pointsEquivScheme B S hS U0).symm u))
  choose I U actU f he het haf hhit using hp
  choose c hc using hhit
  let A : Type u := (SCH).obj U0
  let U' : A → BigFppfOver B S hS := fun u => U u (c u)
  let f' : ∀ a : A, yoneda.obj (U' a) ⟶ X := fun a => f a (c a)
  have het' : ∀ a : A, (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f' a) :=
    fun a => het a (c a)
  have hit : ∀ x : Space.points B S hS X, ∃ a, x ∈ Set.range (Space.pointsMap B S hS _ (f' a)) := by
    intro x
    obtain ⟨y, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS g hs x
    refine ⟨Space.pointsToScheme B S hS U0 y, ?_⟩
    have e : (Space.pointsEquivScheme B S hS U0).symm (Space.pointsToScheme B S hS U0 y) = y :=
      (Space.pointsEquivScheme B S hS U0).symm_apply_apply y
    have := hc (Space.pointsToScheme B S hS U0 y)
    rwa [e] at this
  have hft := chartsOfFiniteType_of_lfp ((Final.lfp_toT1_iff hX).1 hlfp)
  have hsize : ∀ a, ((SCH).obj (U' a)).size ≤ S.size := fun a => by
    have : LocallyOfFiniteType (U' a).hom.hom := hft _ _ (het' a)
    have : CompactSpace ((SCH).obj (U' a)) :=
      have := haf a (c a); inferInstance
    exact Scheme.size_le_of_locallyOfFiniteType (U' a).hom.hom
  have hμ : max (2 ^ ((SCH).obj U0).size) S.size < B.cutoff :=
    max_lt (B.cutoff_isStrongPrelimit U0.left.property) hS
  obtain ⟨V, j, hV⟩ := Final.exists_cofan_of_size U' hμ ((Final.mk_scheme_le _).trans (le_max_left _ _))
    fun a => (hsize a).trans (le_max_right _ _)
  exact ⟨A, U', ⟨fun a => actU a (c a), f', fun a => he a (c a), het',
    fun a => isAffineHom_structMap (haf a (c a)), covers_of_hit f' het' hit⟩, V, j, hV⟩

/-- **Theorem 6.8 (ii)** of Algebraic Magnetism: `X` quasi-separated, locally of finite presentation over `S`
separated, `M` f.g., `M/Z` torsion-free in the form `IrreducibleFibres`. `X` has a `Z`-FPR atlas. -/
theorem final2_thm68_ii [S.IsSeparated] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X)
    {Z : AddSubgroup M} (hMZ : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsZFPRAtlas actV act v Z := by
  obtain ⟨A, U, L, V, j, ⟨hV⟩⟩ := final2_exists_small_family_qs hZ hM hX hlfp hqs act
  obtain ⟨v, hv⟩ := thm68_ii_of_charts hX L hV hMZ hirr
  exact ⟨V, _, v, hv⟩

/-- **Theorem 6.8 (ii)**, quasi-compact clause: an `S`-affine `Z`-FPR atlas. -/
theorem final2_thm68_ii_qc [S.IsSeparated] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (hq : Space.IsQuasiCompactSpace B S hS X)
    (act : AAction (fppfO B S hS) M X)
    {Z : AddSubgroup M} (hMZ : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsZFPRAtlas actV act v Z ∧ IsSAffineAtlas actV act v :=
  thm68_ii_qc_proved hZ hM hX hlfp hqs hq act hMZ hirr

end AlgMag.ChartMain.DeligneQS

#print axioms AlgMag.ChartMain.DeligneQS.final2_thm68_ii
#print axioms AlgMag.ChartMain.DeligneQS.final2_thm68_ii_qc
