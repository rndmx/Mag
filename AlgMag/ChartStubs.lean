/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartThm68
import AlgMag.ChartFormal2
import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PresheafPointTransport
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints

/-!
# The chart at a closed point, and limit preservation

The two inputs of the chart lemma that come from the Stacks library:

* `exists_chart_at_point`: from Stacks 0BBP (`Space.exists_affine_elementaryEtaleNeighborhood'`), an
  affine étale neighbourhood `V` of a closed point `P → X` over which `P` lifts, with `Γ(V) → Γ(P)` onto.
* `limitPreserving_of_lft`: from Stacks 06G4 (1)
  (`Space.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType`) and Stacks 05N0
  (`Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving`, limit preservation in the sense of
  Stacks 049J).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `Spec k`, for the field `k` of the point `p`, as a field-valued point of `P`. -/
noncomputable def pointField (p : AlgMag.ChartPoint X) : Space.FieldValuedPoint B S hS (yoneda.obj p.P) :=
  letI := p.field
  have hc : B.Contains (Spec (.of p.k)) := by
    show (Spec (.of p.k)).size < B.cutoff
    rw [← Scheme.size_congr p.iso]
    exact p.P.left.property
  { carrier := p.k
    field := p.field
    contained := hc
    toBase := p.iso.inv ≫ p.P.hom.1
    value := Over.homMk (⟨p.iso.inv⟩ : B.obj hc ⟶ p.P.left) }

/-- The site object of `pointField` is `P`. -/
noncomputable def pointFieldIso (p : AlgMag.ChartPoint X) :
    (pointField p).siteObject B S hS (yoneda.obj p.P) ≅ p.P :=
  letI := p.field
  Over.isoMk
    { hom := ⟨p.iso.inv⟩
      inv := ⟨p.iso.hom⟩
      hom_inv_id := by apply ObjectProperty.hom_ext; exact p.iso.inv_hom_id
      inv_hom_id := by apply ObjectProperty.hom_ext; exact p.iso.hom_inv_id }
    rfl

/-- The points of the presheaf represented by `P` form a subsingleton. -/
lemma subsingleton_points_chartPoint (p : AlgMag.ChartPoint X) :
    Subsingleton (Space.points B S hS (yoneda.obj p.P)) := by
  letI := p.field
  haveI : Subsingleton ((SCH).obj p.P) :=
    (show Function.Injective p.iso.hom from
      (Scheme.homeoOfIso p.iso).injective).subsingleton
  exact (Space.injective_pointsToScheme B S hS p.P).subsingleton

/-- **The chart at a closed point.** Stacks 0BBP at the point of `X` given by `p`: an affine `V`, étale
over `X`, with one point `w` above `p` and `κ(p) = κ(w)`. By uniqueness of monomorphic field-valued
representatives, `P → X` factors through `Spec κ(w) → V`. The fibre of `V → X` over the closed `P → X` is
a closed subscheme of `V` with support `w`, so `w` is closed in `V`, `Spec κ(w) → V` is a closed
immersion, and `Γ(V) → Γ(P)` is onto. -/
theorem exists_chart_at_point [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (p : AlgMag.ChartPoint X) :
    ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj V))
      (e : yoneda.obj V ⟶ X) (v : p.P ⟶ V),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) e ∧
      yoneda.map v ≫ e = p.x ∧
      Function.Surjective ((SCH).map v).appTop.hom := by
  classical
  letI := p.field
  have hdec := ChartAssembly.decent_of_sep hX hsep
  haveI hPs := subsingleton_points_chartPoint p
  -- the field-valued point of `X`
  let q₀ := pointField p
  let q := Space.FieldValuedPoint.map B S hS (yoneda.obj p.P) p.x q₀
  let x₀ : Space.points B S hS X := q.class B S hS X
  have hx₀ : ∀ t : Space.points B S hS (yoneda.obj p.P), Space.pointsMap B S hS _ p.x t = x₀ := fun t => by
    rw [Subsingleton.elim t (q₀.class B S hS _)]
    rfl
  obtain ⟨E, hEa, huniq, φ, hφ, g, hgS, hgsq⟩ :=
    Space.exists_affine_elementaryEtaleNeighborhood' B S hS hX hdec x₀
  -- `fieldMorphism q` is the composite with `P ≅ Spec k`
  let iso' : q.siteObject B S hS X ≅ p.P := pointFieldIso p
  have hfm : yonedaEquiv.symm q.value = yoneda.map iso'.hom ≫ p.x := by
    have hq₀ : yonedaEquiv.symm q₀.value = yoneda.map (pointFieldIso p).hom := by
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
      apply Over.OverMorphism.ext
      rfl
    have h := yonedaEquiv_symm_naturality_right (q₀.siteObject B S hS (yoneda.obj p.P)) p.x q₀.value
    rw [hq₀] at h
    exact h.symm
  haveI hmx : Mono p.x := ChartMain.mono_of_closedP p.isClosed
  haveI hmq : Mono (yonedaEquiv.symm q.value) := by
    rw [hfm]
    exact mono_comp _ _
  -- the chosen representative
  let r := (Space.residueFieldRepresentative B S hS X hdec x₀).1
  haveI hmr : Mono (yonedaEquiv.symm r.value) := (Space.residueFieldRepresentative B S hS X hdec x₀).2.2
  obtain ⟨e₀, he₀⟩ := Space.iso_of_mono_of_point_eq B S hS X hX r q
    (Space.residueFieldRepresentative B S hS X hdec x₀).2.1
  have hrq : yoneda.map e₀.hom ≫ yonedaEquiv.symm q.value = yonedaEquiv.symm r.value := by
    rw [yonedaEquiv_symm_naturality_left e₀.hom X q.value, he₀]
  -- `g` is invertible
  haveI hφi : IsIso (CommRingCat.ofHom φ) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hφ
  haveI hgi : IsIso g := by
    haveI : IsIso (B.inclusion.map ((Over.forget (B.obj hS)).map g)) := by
      show IsIso (B.inclusion.map g.left)
      rw [hgS]
      exact CategoryTheory.Functor.map_isIso Scheme.Spec (CommRingCat.ofHom φ).op
    haveI : IsIso ((Over.forget (B.obj hS)).map g) := isIso_of_reflects_iso _ B.inclusion
    exact isIso_of_reflects_iso _ (Over.forget (B.obj hS))
  let w := E.point
  let hw := E.residueField_contained
  let resW := Space.residueFieldMap B S hS E.scheme w hw
  let v : p.P ⟶ E.scheme := iso'.inv ≫ e₀.inv ≫ inv g ≫ resW
  have hvx : yoneda.map v ≫ E.toSpace = p.x := by
    have h1 : yoneda.map resW ≫ E.toSpace = yoneda.map g ≫ yonedaEquiv.symm r.value := hgsq.symm
    have h2 : yoneda.map (inv g) ≫ yoneda.map resW ≫ E.toSpace = yonedaEquiv.symm r.value := by
      rw [h1, ← Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    have h3 : yoneda.map e₀.inv ≫ yonedaEquiv.symm r.value = yonedaEquiv.symm q.value := by
      rw [← hrq, ← Category.assoc, ← CategoryTheory.Functor.map_comp, e₀.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [v, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [h2, h3, hfm, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  -- a map to `V` lying over `P` hits only `w`
  have honly : ∀ {T : BigFppfOver B S hS} (t : T ⟶ E.scheme) (b : T ⟶ p.P),
      yoneda.map t ≫ E.toSpace = yoneda.map b ≫ p.x → ∀ τ : (SCH).obj T, (SCH).map t τ = w := by
    intro T t b hsq τ
    have hc := B.residueField_spec_contains T.left.property τ
    have hc' := B.residueField_spec_contains E.scheme.left.property ((SCH).map t τ)
    have hu : Space.pointsMap B S hS _ E.toSpace
        (Space.presheafPoint B S hS E.scheme ((SCH).map t τ) hc') = x₀ := by
      have e1 := Space.pointsMap_presheafPoint B S hS T E.scheme t τ hc hc'
      calc Space.pointsMap B S hS _ E.toSpace
            (Space.presheafPoint B S hS E.scheme ((SCH).map t τ) hc')
          = Space.pointsMap B S hS _ E.toSpace (Space.pointsMap B S hS _ (yoneda.map t)
              (Space.presheafPoint B S hS T τ hc)) := congrArg _ e1.symm
        _ = Space.pointsMap B S hS _ (yoneda.map t ≫ E.toSpace)
              (Space.presheafPoint B S hS T τ hc) := (Space.pointsMap_comp_apply ..).symm
        _ = Space.pointsMap B S hS _ (yoneda.map b ≫ p.x)
              (Space.presheafPoint B S hS T τ hc) := by rw [hsq]
        _ = Space.pointsMap B S hS _ p.x (Space.pointsMap B S hS _ (yoneda.map b)
              (Space.presheafPoint B S hS T τ hc)) := Space.pointsMap_comp_apply ..
        _ = x₀ := hx₀ _
    have h := huniq _ hu
    have h2 := congrArg (Space.pointsToScheme B S hS E.scheme) h
    rwa [Space.pointsToScheme_presheafPoint, Space.pointsToScheme_presheafPoint] at h2
  -- the fibre over the closed `P → X`
  have hrep := p.isClosed.rep
  have sq := hrep.isPullback E.toSpace
  let Y := hrep.pullback E.toSpace
  let ι : Y ⟶ E.scheme := hrep.snd E.toSpace
  obtain ⟨toP, htoP⟩ := yoneda.map_surjective (hrep.fst E.toSpace)
  have hcl : IsClosedImmersion ((SCH).map ι) := p.isClosed.property_snd E.toSpace
  have hιw : ∀ y : (SCH).obj Y, (SCH).map ι y = w := fun y =>
    honly ι toP (by rw [htoP]; exact sq.w.symm) y
  have hl : yoneda.map (𝟙 p.P) ≫ p.x = yoneda.map v ≫ E.toSpace := by simp [hvx]
  let lift0 := sq.lift (yoneda.map (𝟙 p.P)) (yoneda.map v) hl
  obtain ⟨l, hl0⟩ := yoneda.map_surjective lift0
  have hPne : Nonempty ((SCH).obj p.P) := ⟨p.iso.inv (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum p.k)⟩
  obtain ⟨y₀⟩ := hPne
  have hrange : Set.range ((SCH).map ι) = {w} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact hιw y
    · rintro rfl
      exact ⟨(SCH).map l y₀, hιw _⟩
  have hclw : IsClosed ({w} : Set E.scheme.left.1) := by
    rw [← hrange]
    exact ((SCH).map ι).isClosedEmbedding.isClosed_range
  haveI hci : IsClosedImmersion (E.scheme.left.1.fromSpecResidueField w) :=
    isClosed_singleton_iff_isClosedImmersion.1 hclw
  haveI hEa' : IsAffine ((SCH).obj E.scheme) := hEa
  haveI hci' : IsClosedImmersion ((SCH).map resW) := hci
  haveI hi0 : IsIso (iso'.inv ≫ e₀.inv ≫ inv g) := inferInstance
  haveI hi1 : IsIso ((SCH).map (iso'.inv ≫ e₀.inv ≫ inv g)) := CategoryTheory.Functor.map_isIso _ _
  have hvcl : IsClosedImmersion ((SCH).map v) := by
    have hv : (SCH).map v = (SCH).map (iso'.inv ≫ e₀.inv ≫ inv g) ≫ (SCH).map resW := by
      rw [← CategoryTheory.Functor.map_comp]
      simp only [v, Category.assoc]
    rw [hv]
    infer_instance
  exact ⟨E.scheme, hEa, E.toSpace, v, Space.presheaf_etale_of_isEtale B S hS E.etale_toSpace, hvx,
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map v)).2⟩

/-- **Limit preservation.** Stacks 06G4 (1) over the locally Noetherian base, then Stacks 05N0. -/
theorem limitPreserving_of_lft [IsAffine S] (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X)
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    LimitPreserving.{u, u, u, u, u + 1, u} (SCH) X := by
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    ChartAssembly.isAlgebraicSpace_terminal
  have hlT : Space.IsLocallyOfFiniteType B S hS (terminal.from (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) := by
    intro U' V' f' g' α hf' hg' c
    haveI := Space.isMultiplicative_presheaf_etale B S hS
    have hiso : IsIso (terminal.from (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) :=
      ⟨𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    have hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f' ≫ terminal.from _) :=
      MorphismProperty.comp_mem _ _ _ hf' (MorphismProperty.of_isIso _ _)
    haveI : Etale ((SCH).map α) := Space.etale_of_etale_charts B S hS (f' ≫ terminal.from _) g' hb hg' α c
    infer_instance
  have hN : Space.HasEtaleLocalProperty B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
    obtain ⟨U, φ, hsu, he⟩ := hT.exists_atlas
    haveI := ChartAssembly.lft_chart hSft hlT he
    haveI : IsLocallyNoetherian (⊤_ Scheme.{u}) := ChartAssembly.terminal_noeth
    exact ⟨U, φ, hsu, he, LocallyOfFiniteType.isLocallyNoetherian (terminal.from ((SCH).obj U))⟩
  exact (Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS hX).1
    (Space.isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS hX hT (terminal.from X) hN hlft)

end AlgMag.ChartAssembly

#print axioms AlgMag.ChartAssembly.exists_chart_at_point
#print axioms AlgMag.ChartAssembly.limitPreserving_of_lft
