/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono

/-!
# A bounded atlas of a space mapping by a monomorphism to `X`

`Q` algebraic space with étale charts locally of finite type over `S`, `Q ⟶ X` a monomorphism: one affine chart for each point of an
atlas of `X` gives an atlas of `Q`, with size bounded in terms of `S` and the atlas of `X` only.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A family of at most `μ` objects of the site, each of size at most `μ`, has a coproduct in the site of size
at most `μ`, for `ℵ₀ ≤ μ` below the cutoff of the site. -/
theorem exists_cofan_size {A : Type u} (U : A → BigFppfOver B S hS) {μ : Cardinal.{u}}
    (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hA : #A ≤ μ) (hU : ∀ a, ((SCH).obj (U a)).size ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V), Nonempty (IsColimit (Cofan.mk V j)) ∧
      ((SCH).obj V).size ≤ μ := by
  let Y : A → Scheme.{u} := fun a => (SCH).obj (U a)
  have hle := schemeSize_coproduct_le Y μ hℵ hA hU
  have hC : B.Contains (∐ Y) := hle.trans_lt hμ
  let f : ∐ Y ⟶ S := Sigma.desc fun a => (U a).hom.hom
  let V : BigFppfOver B S hS := siteObject B S hS hC f
  let j : ∀ a, U a ⟶ V := fun a => siteHom (Sigma.ι Y a) (Sigma.ι_desc _ _)
  refine ⟨V, j, ⟨mkCofanColimit _ (fun s => siteHom (Sigma.desc fun a => (SCH).map (s.inj a)) ?_)
    (fun s a => ?_) (fun s m hm => ?_)⟩, hle⟩
  · refine Sigma.hom_ext _ _ fun a => ?_
    rw [Sigma.ι_desc_assoc]
    have h1 : (SCH).map (s.inj a) ≫ s.pt.hom.hom = (U a).hom.hom :=
      congrArg (fun k => k.hom) (Over.w (s.inj a))
    exact h1.trans (Sigma.ι_desc (fun a => (U a).hom.hom) a).symm
  · exact site_hom_ext (Sigma.ι_desc _ _)
  · refine site_hom_ext (Sigma.hom_ext _ _ fun a => ?_)
    have := congrArg (SCH).map (hm a)
    exact this.trans (Sigma.ι_desc (fun a => (SCH).map (s.inj a)) a).symm

/-- The bounded atlas. -/
theorem exists_small_atlas {Q X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (hft : ChartsOfFiniteType Q) (m : Q ⟶ X) [Mono m]
    {W : BigFppfOver B S hS} {w : yoneda.obj W ⟶ X}
    (hws : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) w)
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hμS : S.size ≤ μ)
    (hμW : 2 ^ ((SCH).obj W).size ≤ μ) :
    ∃ (Y : BigFppfOver B S hS) (b : yoneda.obj Y ⟶ Q),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) b ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) b ∧ ((SCH).obj Y).size ≤ μ := by
  classical
  obtain ⟨G, g, hgs, hge⟩ := hQ.exists_atlas
  have hinj := Space.pointsMap_injective_of_mono B S hS m
  -- the index set: points of the atlas of `X` that come from `Q`
  let ptW : (SCH).obj W → Space.points B S hS X := fun u =>
    Space.pointsMap B S hS _ w ((Space.pointsEquivScheme B S hS W).symm u)
  let A : Type u := { u : (SCH).obj W // ∃ y, Space.pointsMap B S hS _ m y = ptW u }
  have hgpt := Space.isSurjective_of_presheafSurjective B S hS g hgs
  have hsel : ∀ a : A, ∃ V : ((SCH).obj G).affineOpens, ∃ τ ∈ V.1,
      Space.pointsMap B S hS _ g ((Space.pointsEquivScheme B S hS G).symm τ) = a.2.choose := by
    intro a
    obtain ⟨y, hy⟩ := hgpt a.2.choose
    let τ := Space.pointsToScheme B S hS G y
    obtain ⟨_, ⟨V, hV, rfl⟩, hτ, -⟩ := ((SCH).obj G).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ τ) isOpen_univ
    refine ⟨⟨V, hV⟩, τ, hτ, ?_⟩
    have e : (Space.pointsEquivScheme B S hS G).symm (Space.pointsToScheme B S hS G y) = y :=
      (Space.pointsEquivScheme B S hS G).symm_apply_apply y
    rw [show (Space.pointsEquivScheme B S hS G).symm τ = y from e, hy]
  choose Vs τs hτs hτpt using hsel
  have hC : ∀ a, B.Contains ((Vs a).1 : Scheme.{u}) := fun a =>
    Scheme.size_lt_of_isOpenImmersion (Vs a).1.ι G.left.property
  let U : A → BigFppfOver B S hS := fun a => siteObject B S hS (hC a) ((Vs a).1.ι ≫ G.hom.hom)
  let ιa : ∀ a, U a ⟶ G := fun a => siteHom (Vs a).1.ι rfl
  have hoi : ∀ a, IsOpenImmersion ((SCH).map (ιa a)) := fun a =>
    inferInstanceAs (IsOpenImmersion (Vs a).1.ι)
  have hme := Space.isMultiplicative_presheaf_etale B S hS
  have hye : ∀ {V₁ V₂ : BigFppfOver B S hS} (k : V₁ ⟶ V₂), Etale ((SCH).map k) →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map k) := fun k hk =>
    (Space.presheaf_yoneda_map_iff B S hS inferInstance k).2 hk
  have hfe : ∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (ιa a) ≫ g) := fun a =>
    have := hoi a
    MorphismProperty.comp_mem _ _ _ (hye _ inferInstance) hge
  have hsize : ∀ a, ((SCH).obj (U a)).size ≤ μ := fun a => by
    haveI : LocallyOfFiniteType (U a).hom.hom := hft _ _ (hfe a)
    haveI : CompactSpace (Over.left (U a)).obj :=
      have : IsAffine ((Vs a).1 : Scheme.{u}) := (Vs a).2
      inferInstanceAs (CompactSpace ((Vs a).1 : Scheme.{u}))
    exact (Scheme.size_le_of_locallyOfFiniteType (U a).hom.hom).trans hμS
  have hAle : #A ≤ μ := (Cardinal.mk_subtype_le _).trans ((mk_scheme_le _).trans hμW)
  obtain ⟨V, j, ⟨hV⟩, hVs⟩ := exists_cofan_size U hℵ hμ hAle hsize
  let c : V ⟶ G := hV.desc (Cofan.mk G ιa)
  have hjc : ∀ a, j a ≫ c = ιa a := fun a => hV.fac (Cofan.mk G ιa) ⟨a⟩
  have hjo := fun a => isOpenImmersion_toScheme_map_cofan hV a
  have hce : Etale ((SCH).map c) := by
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
    have hcov : (⨆ a, have := hjo a; ((SCH).map (j a)).opensRange) = ⊤ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion,
        Set.mem_univ, iff_true]
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 ((iUnion_range_toScheme_map_cofan hV).symm ▸ Set.mem_univ x)
      exact ⟨a, ha⟩
    refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) _ hcov).mpr fun a => ?_
    have := hjo a
    have := hoi a
    have e : ((SCH).map (j a)).opensRange.ι ≫ (SCH).map c =
        ((SCH).map (j a)).isoOpensRange.inv ≫ (SCH).map (ιa a) := by
      rw [← hjc a, (SCH).map_comp, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    rw [e]
    infer_instance
  let v : yoneda.obj V ⟶ Q := yoneda.map c ≫ g
  have hve : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) v :=
    MorphismProperty.comp_mem _ _ _ (hye _ hce) hge
  have hhit : ∀ x : Space.points B S hS Q, ∃ a,
      x ∈ Set.range (Space.pointsMap B S hS _ (yoneda.map (ιa a) ≫ g)) := by
    intro x
    obtain ⟨w₀, hw₀⟩ := Space.isSurjective_of_presheafSurjective B S hS w hws
      (Space.pointsMap B S hS _ m x)
    let u := Space.pointsToScheme B S hS W w₀
    have hu : ptW u = Space.pointsMap B S hS _ m x := by
      have e : (Space.pointsEquivScheme B S hS W).symm (Space.pointsToScheme B S hS W w₀) = w₀ :=
        (Space.pointsEquivScheme B S hS W).symm_apply_apply w₀
      change Space.pointsMap B S hS _ w ((Space.pointsEquivScheme B S hS W).symm
        (Space.pointsToScheme B S hS W w₀)) = _
      rw [e, hw₀]
    let a : A := ⟨u, x, hu.symm⟩
    have hax : a.2.choose = x := hinj (a.2.choose_spec.trans hu)
    refine ⟨a, ?_⟩
    let τ' : (SCH).obj (U a) := ⟨τs a, hτs a⟩
    refine ⟨(Space.pointsEquivScheme B S hS (U a)).symm τ', ?_⟩
    rw [Space.pointsMap_comp_apply]
    have e0 : Space.pointsMap B S hS _ (yoneda.map (ιa a))
        ((Space.pointsEquivScheme B S hS (U a)).symm τ') =
        (Space.pointsEquivScheme B S hS G).symm ((SCH).map (ιa a) τ') :=
      Space.injective_pointsToScheme B S hS G (by
        rw [Space.pointsToScheme_pointsMap_yoneda]
        exact (congrArg _ ((Space.pointsEquivScheme B S hS (U a)).apply_symm_apply τ')).trans
          ((Space.pointsEquivScheme B S hS G).apply_symm_apply _).symm)
    rw [e0]
    exact (hτpt a).trans hax
  have hcov := covers_of_hit (fun a => yoneda.map (ιa a) ≫ g) hfe hhit
  have hrep : yoneda.relativelyRepresentable v := hQ.diagonal_representable.of_diag v
  refine ⟨V, v, ⟨hrep, ?_⟩, hve, hVs⟩
  intro T P t fst snd hpb
  refine (surjective_iff _).mpr fun y => ?_
  obtain ⟨a, z, hz⟩ := hcov T t y
  have hw := ((hfe a).rep.isPullback t).w
  have hc : yoneda.map ((hfe a).rep.fst' t ≫ j a) ≫ v = yoneda.map ((hfe a).rep.snd t) ≫ t := by
    have h1 : yoneda.map (j a) ≫ v = yoneda.map (ιa a) ≫ g := by
      rw [← Category.assoc, ← yoneda.map_comp, hjc]
    rw [yoneda.map_comp, Category.assoc, h1, Functor.relativelyRepresentable.map_fst']
    exact hw
  let l := hpb.lift _ _ hc
  have hl₂ : l ≫ yoneda.map snd = yoneda.map ((hfe a).rep.snd t) := hpb.lift_snd _ _ hc
  let n := yoneda.preimage l
  have hn : n ≫ snd = (hfe a).rep.snd t := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.map_preimage, hl₂])
  refine ⟨(SCH).map n z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← (SCH).map_comp, hn]
  exact hz

end AlgMag.Final
