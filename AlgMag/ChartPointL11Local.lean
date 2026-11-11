/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointL11Stable

/-!
# Locality of the image; `image_stable` (Lemma 1.1 of the chart-lemma proof, step A)
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartPoint

open ChartMain

section Schemes

/-- A flat local ring map is injective. -/
lemma injective_of_flat_local {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [IsLocalRing A₀]
    [IsLocalRing B₀] (a : A₀ →+* B₀) [IsLocalHom a] (ha : a.Flat) : Function.Injective a := by
  letI := a.toAlgebra
  haveI : Module.Flat A₀ B₀ := ha
  haveI : IsLocalHom (algebraMap A₀ B₀) := ‹IsLocalHom a›
  haveI : Module.FaithfullyFlat A₀ B₀ := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective A₀ B₀

/-- A closed immersion through which, locally at every point of the target, a flat morphism
factors is an isomorphism. -/
theorem isIso_of_closed_of_flat_factor {C T : Scheme.{u}} (i : C ⟶ T) [IsClosedImmersion i]
    (h : ∀ x : T, ∃ (V : Scheme.{u}) (e : V ⟶ T) (_ : Flat e) (v : V) (l : V ⟶ C),
      l ≫ i = e ∧ e v = x) : IsIso i := by
  have hsurj : Surjective i := ⟨fun x => by
    obtain ⟨V, e, -, v, l, rfl, hv⟩ := h x
    exact ⟨l v, by rw [← hv]; simp⟩⟩
  have hflat : Flat i := Flat.of_stalkMap i fun c => by
    obtain ⟨V, e, hfl, v, l, rfl, hv⟩ := h (i c)
    have hc : l v = c := i.injective (by rw [← hv]; simp)
    subst hc
    have hs := Flat.stalkMap (l ≫ i) v
    have hinj : Function.Injective (i.stalkMap (l v)).hom := by
      have h0 := injective_of_flat_local ((l ≫ i).stalkMap v).hom hs
      rw [Scheme.Hom.stalkMap_comp] at h0
      exact Function.Injective.of_comp (f := (l.stalkMap v).hom) h0
    exact RingHom.Flat.of_bijective ⟨hinj, i.stalkMap_surjective _⟩
  exact Flat.isIso_of_surjective_of_mono i

/-- Flatness at a point descends along a morphism flat at that point. -/
lemma flat_stalk_descend {F Y Z : Scheme.{u}} (b : F ⟶ Y) (a : Y ⟶ Z) (z : F)
    (hb : (b.stalkMap z).hom.Flat) (hc : ((b ≫ a).stalkMap z).hom.Flat) :
    (a.stalkMap (b z)).hom.Flat := by
  rw [Scheme.Hom.stalkMap_comp] at hc
  exact flat_of_comp_flat_local _ _ hb hc

end Schemes

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- Membership in a closed subspace is local for flat morphisms. -/
theorem mem_of_flat_local {Y : Subfunctor X} (hY : Space.IsClosedImmersion B S hS Y.ι)
    {T : BigFppfOver B S hS} (s : X.obj (op T))
    (h : ∀ x : (SCH).obj T, ∃ (V : BigFppfOver B S hS) (e : V ⟶ T) (_ : Flat ((SCH).map e))
      (v : (SCH).obj V), (SCH).map e v = x ∧ X.map e.op s ∈ Y.obj (op V)) :
    s ∈ Y.obj (op T) := by
  let g : yoneda.obj T ⟶ X := yonedaEquiv.symm s
  have hgapp : ∀ {V : BigFppfOver B S hS} (e : V ⟶ T), g.app (op V) e = X.map e.op s := by
    intro V e
    simp [g, yonedaEquiv]
  let C := hY.rep.pullback g
  let c : C ⟶ T := hY.rep.snd g
  have sq : IsPullback (hY.rep.fst g) (yoneda.map c) Y.ι g := hY.rep.isPullback g
  have hc : IsClosedImmersion ((SCH).map c) := hY.property_snd g
  have hlift : ∀ {V : BigFppfOver B S hS} (e : V ⟶ T), X.map e.op s ∈ Y.obj (op V) →
      ∃ l : V ⟶ C, l ≫ c = e := by
    intro V e he
    let a : yoneda.obj V ⟶ Y.toFunctor := yonedaEquiv.symm ⟨X.map e.op s, he⟩
    have hcomm : a ≫ Y.ι = yoneda.map e ≫ g := by
      apply yonedaEquiv.injective
      simp [a, g, yonedaEquiv]
      rfl
    obtain ⟨l, hl⟩ := Functor.Full.map_surjective (F := yoneda) (sq.lift a (yoneda.map e) hcomm)
    refine ⟨l, Functor.Faithful.map_injective (F := yoneda) ?_⟩
    rw [Functor.map_comp, hl]
    exact sq.lift_snd _ _ _
  have hiso : IsIso ((SCH).map c) := by
    refine isIso_of_closed_of_flat_factor _ fun x => ?_
    obtain ⟨V, e, hfl, v, hv, hm⟩ := h x
    obtain ⟨l, hl⟩ := hlift e hm
    exact ⟨(SCH).obj V, (SCH).map e, hfl, v, (SCH).map l, by rw [← Functor.map_comp, hl], hv⟩
  let l0 : T ⟶ C := siteHom (inv ((SCH).map c)) (by
    rw [IsIso.inv_comp_eq, site_w])
  have hl0 : l0 ≫ c = 𝟙 T := site_hom_ext (by
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact IsIso.inv_hom_id _)
  have e : Y.ι.app (op T) ((hY.rep.fst g).app (op T) l0) = g.app (op T) ((yoneda.map c).app (op T) l0) :=
    congrArg (fun k => k.app (op T) l0) sq.w
  have e2 : g.app (op T) ((yoneda.map c).app (op T) l0) = s := by
    have : (yoneda.map c).app (op T) l0 = 𝟙 T := hl0
    rw [this, hgapp]
    simp
  rw [← e2, ← e]
  exact ((hY.rep.fst g).app (op T) l0).2

/-- **An affine étale chart through a point.** For `s` a point of `X` on `T` and `y ∈ T`: a flat
`T₁ → T` hitting `y`, an affine étale chart `U' → X`, and `T₁ → U'` compatible with `s`. -/
theorem exists_affine_chart (hX : IsAlgebraicSpace B S hS X) {T : BigFppfOver B S hS}
    (s : yoneda.obj T ⟶ X) (y : (SCH).obj T) :
    ∃ (T₁ U' : BigFppfOver B S hS) (e : T₁ ⟶ T) (y₁ : (SCH).obj T₁) (g : yoneda.obj U' ⟶ X)
      (u : T₁ ⟶ U'), IsAffine ((SCH).obj U') ∧ Etale ((SCH).map e) ∧ (SCH).map e y₁ = y ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g ∧
      g.app (op T₁) u = s.app (op T₁) e := by
  obtain ⟨U, φ, hs, he⟩ := hX.exists_atlas
  let W := he.rep.pullback s
  let sn : W ⟶ T := he.rep.snd s
  have sq : IsPullback (he.rep.fst s) (yoneda.map sn) φ s := he.rep.isPullback s
  obtain ⟨toU, htoU⟩ := yoneda.map_surjective (he.rep.fst s)
  have sq' : IsPullback (yoneda.map toU) (yoneda.map sn) φ s := by rw [htoU]; exact sq
  have hsnE : Etale ((SCH).map sn) := he.property_snd s
  have hsnS : Surjective ((SCH).map sn) := hs.property _ _ _ sq'
  obtain ⟨y0, hy0⟩ := ((SCH).map sn).surjective y
  obtain ⟨U0, hU0, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (SCH).map toU y0) (U := ⊤) trivial
  let U' := Space.openSiteObject B S hS U U0
  let ι : U' ⟶ U := Space.openSiteObjectHom B S hS U U0
  let V0 : ((SCH).obj W).Opens := ((SCH).map toU) ⁻¹ᵁ U0
  let T₁ := Space.openSiteObject B S hS W V0
  let j : T₁ ⟶ W := Space.openSiteObjectHom B S hS W V0
  let u : T₁ ⟶ U' := siteHom (((SCH).map toU) ∣_ U0) (by
    have e0 := morphismRestrict_ι ((SCH).map toU) U0
    change ((SCH).map toU ∣_ U0) ≫ (U0.ι ≫ U.hom.hom) = V0.ι ≫ W.hom.hom
    rw [← Category.assoc, e0, Category.assoc, site_w])
  have hu : u ≫ ι = j ≫ toU := site_hom_ext (morphismRestrict_ι ((SCH).map toU) U0)
  have hjO : IsOpenImmersion ((SCH).map j) := by
    change IsOpenImmersion V0.ι
    infer_instance
  have hιO : IsOpenImmersion ((SCH).map ι) := by
    change IsOpenImmersion U0.ι
    infer_instance
  refine ⟨T₁, U', j ≫ sn, (show (SCH).obj T₁ from (⟨y0, hmem⟩ : V0)), yoneda.map ι ≫ φ, u, hU0, ?_, ?_, ?_, ?_⟩
  · rw [Functor.map_comp]; infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hy0
  · have hι : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map ι) :=
      Space.presheaf_yoneda_map_of_inverseImage B S hS inferInstance _
        (show Etale ((SCH).map ι) from inferInstance)
    have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (SCH)).IsStableUnderComposition := ⟨fun f g hf hg => by
      change Etale _
      rw [Functor.map_comp]
      have : Etale ((SCH).map f) := hf
      have : Etale ((SCH).map g) := hg
      infer_instance⟩
    exact MorphismProperty.comp_mem _ _ _ hι he
  · have e1 : (yoneda.map ι ≫ φ).app (op T₁) u = φ.app (op T₁) (u ≫ ι) := rfl
    rw [e1, hu]
    have e2 := pb_comm sq'
    rw [hom_nat, e2, ← hom_nat]

variable [IsAffine S] {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]
  {o : yoneda.obj (Ob P N) ⟶ X}

/-- **Lemma 1.1, step A**: the scheme-theoretic image of the orbit is stable under `D(M)`. -/
theorem image_stable (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o)
    {T : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : X.obj (op T))
    (ht : t ∈ (imS o).obj (op T)) : actX.smul (U := op T) h t ∈ (imS o).obj (op T) := by
  have hcl := Space.isClosedSubspace_schemeTheoreticImageSubfunctor B S hS o hX
  refine mem_of_flat_local hcl.2 _ fun x => ?_
  obtain ⟨T₁, U₁, e₁, y₁, g₁, u₁, hU₁, hE₁, hy₁, hg₁, hu₁⟩ :=
    exists_affine_chart hX (yonedaEquiv.symm t) x
  let t₁ := X.map e₁.op t
  let h₁ : Multiplicative M →* Γ((SCH).obj T₁, ⊤) :=
    secPt ((SCH).map e₁).appTop.hom h
  obtain ⟨T₂, U₂, e₂, y₂, g₂, u₂, hU₂, hE₂, hy₂, hg₂, hu₂⟩ :=
    exists_affine_chart hX (yonedaEquiv.symm (actX.smul (U := op T₁) h₁ t₁)) y₁
  refine ⟨T₂, e₂ ≫ e₁, ?_, y₂, ?_, ?_⟩
  · rw [Functor.map_comp]; infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_apply, hy₂, hy₁]
  have happ : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A V : BigFppfOver B S hS} (a : F.obj (op A))
      (r : V ⟶ A), (yonedaEquiv.symm a : yoneda.obj A ⟶ F).app (op V) r = F.map r.op a := by
    intro F A V a r
    simp [yonedaEquiv]
  have hu₁' : g₁.app (op T₁) u₁ = t₁ := by rw [hu₁, happ]
  have hu₂' : g₂.app (op T₂) u₂ = X.map e₂.op (actX.smul (U := op T₁) h₁ t₁) := by
    rw [hu₂, happ]
  -- the pullback squares
  obtain ⟨W₁, p₁, w₁, hw₁, sq₁⟩ := exists_pull hsep o g₁
  obtain ⟨W₂, p₂, w₂, hw₂, sq₂⟩ := exists_pull hsep o g₂
  haveI := isAffine_of_isAffineHom ((SCH).map w₁)
  have hmem₁ : g₁.app (op T₂) (e₂ ≫ u₁) ∈ (imS o).obj (op T₂) := by
    rw [hom_nat, hu₁']
    change X.map e₂.op (X.map e₁.op t) ∈ _
    exact (imS o).map _ ((imS o).map _ ht)
  have hkey := image_stable_chart hX hsep actX hoe hlfp hg₁ hg₂ sq₁ sq₂ (e₂ ≫ u₁) u₂
    (secPt ((SCH).map e₂).appTop.hom h₁) (by
      rw [hu₂', hom_nat, hu₁']
      exact actX.map_smul (U := op T₁) (V := op T₂) e₂.op h₁ t₁) hmem₁
  rw [hu₂'] at hkey
  have e3 : X.map (e₂ ≫ e₁).op (actX.smul (U := op T) h t) =
      X.map e₂.op (actX.smul (U := op T₁) h₁ t₁) := by
    rw [op_comp, Functor.map_comp_apply]
    congr 1
    exact actX.map_smul (U := op T) (V := op T₁) e₁.op h t
  rw [e3]
  exact hkey

end AlgMag.ChartPoint
