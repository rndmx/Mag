/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartMain
import AlgMag.StronglyFPRClosed
import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonPointSpace
import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Theorem 6.8 = Theorem A.2, and the strongly-FPR atlas, from the chart lemma

The covering hypothesis `ClosedPointsDetectCovers` is discharged for `X` separated of finite type over
`S` affine of finite type over `ℤ`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartAssembly

open ChartMain ChartPoint

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

omit [AddCommGroup M] in
/-- The site has finite coproducts (proof of Stacks `Spaces/CoproductQuasiCompact.lean`, whose module
is outside the sparse build). -/
theorem hasFiniteCoproducts_site : HasFiniteCoproducts (BigFppfOver B S hS) := by
  have hclosed : (schemeSizeBelow B.cutoff).IsClosedUnderFiniteCoproducts :=
    ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape
      (fun J _ ↦ by
        refine ⟨?_⟩
        rintro X ⟨hX⟩
        set Y : J → Scheme.{u} := fun i ↦ hX.diag.obj ⟨i⟩ with hY
        have hYsize : ∀ i, (Y i).size < B.cutoff := fun i ↦ hX.prop_diag_obj ⟨i⟩
        have hsum : (∐ Y).size < B.cutoff :=
          Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
            Cardinal.mk_le_aleph0 Y hYsize
        have hsumColim : IsColimit ((Cocone.precompose
            (Discrete.natIsoFunctor (F := hX.diag)).symm.hom).obj hX.cocone) :=
          (IsColimit.precomposeHomEquiv (Discrete.natIsoFunctor (F := hX.diag)).symm
            hX.cocone).symm hX.isColimit
        let eX : X ≅ ∐ Y := hsumColim.coconePointUniqueUpToIso (coproductIsCoproduct Y)
        show X.size < B.cutoff
        rw [Scheme.size_congr eX]
        exact hsum)
  have : HasFiniteCoproducts B.Schemes := by
    show HasFiniteCoproducts (schemeSizeBelow B.cutoff).FullSubcategory
    infer_instance
  show HasFiniteCoproducts (Over (B.obj hS))
  infer_instance

/-- `X` of finite type over `S` affine is quasi-compact. -/
theorem qc_of_ft [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsFiniteType B S hS (terminal.from X)) : Space.IsQuasiCompactSpace B S hS X := by
  let T1 : BigFppfOver B S hS := Over.mk (𝟙 _)
  have hT : IsTerminal (yoneda.obj T1) := (Over.mkIdTerminal).isTerminalObj yoneda _
  haveI : IsAffine ((SCH).obj T1) := inferInstanceAs (IsAffine S)
  have hq : Space.IsQuasiCompactSpace B S hS (yoneda.obj T1) :=
    Space.isQuasiCompact_yoneda_of_compact B S hS T1 inferInstance
  have h := hft.2 (yoneda.obj T1) (isAlgebraicSpace_yoneda B S hS _) hq (terminal.from _)
  haveI : IsIso (terminal.from (yoneda.obj T1)) :=
    ⟨hT.from _, hT.hom_ext _ _, terminal.hom_ext _ _⟩
  have hpb : IsAlgebraicSpace B S hS (pullback (terminal.from (yoneda.obj T1)) (terminal.from X)) :=
    Space.isAlgebraicSpace_of_iso B S hS (asIso (pullback.snd _ _)).symm hX
  exact Space.IsQuasiCompactSpace.of_isSurjective B S hS hpb hX
    (Space.pointsMap_surjective_of_isIso B S hS (pullback.snd _ _)) h

/-- Separated over `S` affine implies decent, through absolute quasi-separatedness. -/
theorem decent_of_sep [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) : Space.IsDecentSpace B S hS X := by
  let T1 : BigFppfOver B S hS := Over.mk (𝟙 _)
  have hT : IsTerminal (yoneda.obj T1) := (Over.mkIdTerminal).isTerminalObj yoneda _
  have hs := (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS hT (hT.from X)).1 hsep
  have hq := Space.isQuasiSeparated_of_isSeparated B S hS hs
  have hA : IsAffine ((SCH).obj T1) := inferInstanceAs (IsAffine S)
  exact Space.isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX
    (Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hX
      (Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS B.contains_terminal T1 hA) hq)

/-- `|X|` is Jacobson (Stacks 0BA6): étale charts are of finite type over `ℤ`. -/
theorem jacobson_of_ft (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hdec : Space.IsDecentSpace B S hS X)
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    JacobsonSpace (Space.points B S hS X) := by
  obtain ⟨U, φ, hsu, he⟩ := hX.exists_atlas
  refine Space.jacobsonSpace_points_of_exists_jacobson_atlas B S hS hX hdec ⟨U, φ, hsu, he, ?_⟩
  have h := lft_chart hSft hlft he
  haveI : IsJacobsonRing ℤ := ChartPoint.isJacobsonRing_int'
  haveI : IsJacobsonRing (ULift.{u} ℤ) :=
    isJacobsonRing_of_surjective ⟨(ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).toRingHom,
      (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).surjective⟩
  haveI : JacobsonSpace (Spec (.of (ULift.{u} ℤ))) :=
    (PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace).1 ‹_›
  haveI : JacobsonSpace (⊤_ Scheme.{u}) :=
    JacobsonSpace.of_isClosedEmbedding
      (Scheme.homeoOfIso (terminalIsoIsTerminal specULiftZIsTerminal).symm).symm.isClosedEmbedding
  exact LocallyOfFiniteType.jacobsonSpace (terminal.from _)

/-- `ClosedPointsDetectCovers`, discharged. -/
theorem closedPointsDetectCovers_of_ft [IsAffine S] (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hft : Space.IsFiniteType B S hS (terminal.from X)) : ClosedPointsDetectCovers X :=
  have hdec := decent_of_sep hX hsep
  StronglyFPR.closedPointsDetectCovers hX hdec (jacobson_of_ft hSft hX hdec hft.1)
    ((Space.isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).1 (qc_of_ft hX hft))

/-- **Strongly-FPR note, Theorem 1.1 (2)**, `S` affine of finite type over `ℤ`, `X` separated of finite
type, from the chart lemma. -/
theorem thm11_ft_final [AddGroup.FG M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (hchart : ChartLemmaStatement B S hS M) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV actX v ∧
        IsSAffineAtlas actV actX v ∧ IsAffine ((SCH).obj V) :=
  have hdec := decent_of_sep hX hsep
  haveI : HasFiniteCoproducts (BigFppfOver B S hS) := hasFiniteCoproducts_site
  StronglyFPR.thm11_ft_of_points hSft hX hsep hft actX hchart hdec
    (jacobson_of_ft hSft hX hdec hft.1)
    ((Space.isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).1 (qc_of_ft hX hft))

/-- **Theorem 6.8 = Theorem A.2 (i)**, for `X` separated of finite type over `S` affine of finite type
over `ℤ`, from the chart lemma: an `S`-affine `Z`-FPR atlas, one for all subgroups `Z`. -/
theorem thm68_i [AddGroup.FG M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (hchart : ChartLemmaStatement B S hS M) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), (∀ Z : AddSubgroup M, IsZFPRAtlas actV actX v Z) ∧
        IsSAffineAtlas actV actX v := by
  obtain ⟨V, actV, v, h1, h2, -⟩ := thm11_ft_final hSft hX hsep hft actX hchart
  exact ⟨V, actV, v, h1.isZFPRAtlas, h2⟩

/-- `thm68_i` with §5 as the only named hypothesis. -/
theorem thm68_i_of_section5 [AddGroup.FG M] [IsAffine S]
    (h5 : ∀ [AddMonoid.FG M] [DecidableEq M], Section5FromEffectivity B S hS M)
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), (∀ Z : AddSubgroup M, IsZFPRAtlas actV actX v Z) ∧
        IsSAffineAtlas actV actX v :=
  thm68_i hSft hX hsep hft actX
    (chartLemmaStatementFG_of_section5 h5 (AddGroup.fg_iff_addMonoid_fg.1 inferInstance))

end AlgMag.ChartAssembly

#print axioms AlgMag.ChartAssembly.thm68_i_of_section5
#print axioms AlgMag.ChartAssembly.thm11_ft_final
