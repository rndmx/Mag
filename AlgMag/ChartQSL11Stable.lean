/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSL11Pull

/-!
# Lemma 1.1 for quasi-separated `X`, step A: the image of the orbit is stable

`O ×_X T` is covered by finitely many affine opens, and the kernel of `Γ(T) → Γ(O_T)` is the
intersection of the kernels to them; flat base change commutes with that intersection
(`mem_map_iInf_ker`). `T[M] ×_X T₂` is handled locally on the test object.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct TopologicalSpace

universe u

namespace AlgMag.ChartQSL11

open ChartMain AlgMag.ChartPoint

/-- `mem_map_ker_of_tmul_eq_zero` for a finite family of algebras. -/
theorem mem_map_iInf_ker {ι : Type u} [Finite ι] {A₀ E₀ : Type u} {C : ι → Type u} [CommRing A₀]
    [CommRing E₀] [∀ i, CommRing (C i)] [Algebra A₀ E₀] [∀ i, Algebra A₀ (C i)] [Module.Flat A₀ E₀]
    (x : E₀) (hx : ∀ i, x ⊗ₜ[A₀] (1 : C i) = 0) :
    x ∈ (⨅ i, RingHom.ker (algebraMap A₀ (C i))).map (algebraMap A₀ E₀) := by
  classical
  haveI := Fintype.ofFinite ι
  have h0 : x ⊗ₜ[A₀] (1 : ∀ i, C i) = 0 := by
    apply (TensorProduct.piRight A₀ A₀ E₀ C).injective
    rw [map_zero]
    funext i
    simpa using hx i
  have := mem_map_ker_of_tmul_eq_zero (B₀ := ∀ i, C i) x h0
  have e : RingHom.ker (algebraMap A₀ (∀ i, C i)) = ⨅ i, RingHom.ker (algebraMap A₀ (C i)) := by
    ext a
    simp [RingHom.mem_ker, Ideal.mem_iInf, funext_iff, Pi.algebraMap_apply]
  rwa [e] at this

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable [IsAffine S] {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]

variable {o : yoneda.obj (Ob P N) ⟶ X}

/-- **Stacks 082Z(3)**, for an étale chart: the image pulls back to the image. -/
lemma preimage_image_chart_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    {T W : BigFppfOver B S hS} {g : yoneda.obj T ⟶ X}
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    {p : W ⟶ Ob P N} {w : W ⟶ T} (sq : IsPullback (yoneda.map p) (yoneda.map w) o g) :
    (imS o).preimage g = imS (yoneda.map w) := by
  have hbc := Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact'
    B S hS o g (isAlgebraicSpace_yoneda B S hS _) hX (isAlgebraicSpace_yoneda B S hS _)
    hqc (Space.isEtale_of_presheafEtale B S hS g hg)
  rw [← hbc]
  refine Space.schemeTheoreticImageSubfunctor_congr_range B S hS _ _
    (isAlgebraicSpace_yoneda B S hS _) ?_
  have e : sq.isoPullback.hom ≫ pullback.snd o g = yoneda.map w := sq.isoPullback_hom_snd
  have e' : sq.isoPullback.inv ≫ yoneda.map w = pullback.snd o g := by
    rw [Iso.inv_comp_eq]; exact e.symm
  apply le_antisymm
  · rintro V _ ⟨x, rfl⟩
    exact ⟨sq.isoPullback.inv.app V x, congrArg (fun k => k.app V x) e'⟩
  · rintro V _ ⟨x, rfl⟩
    exact ⟨sq.isoPullback.hom.app V x, congrArg (fun k => k.app V x) e⟩

/-- A point of an étale chart lying in the image kills the kernel of `Γ(T) → Γ(O_T)`. -/
lemma chart_kills_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    {T W : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] {g : yoneda.obj T ⟶ X}
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    {p : W ⟶ Ob P N} {w : W ⟶ T} (sq : IsPullback (yoneda.map p) (yoneda.map w) o g)
    {V : BigFppfOver B S hS} (τ : V ⟶ T) (hτ : g.app (op V) τ ∈ (imS o).obj (op V)) (a : RT T)
    (ha : ((SCH).map w).appTop.hom a = 0) : ((SCH).map τ).appTop.hom a = 0 := by
  have : τ ∈ (imS (yoneda.map w)).obj (op V) := by
    rw [← preimage_image_chart_qs hX hqc hg sq]
    exact hτ
  exact kills_of_mem_image w a ha τ this

/-- A point of an étale chart killing the kernel lies in the image. -/
lemma chart_mem_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    {T W : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] {g : yoneda.obj T ⟶ X}
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    {p : W ⟶ Ob P N} {w : W ⟶ T} (sq : IsPullback (yoneda.map p) (yoneda.map w) o g)
    {V : BigFppfOver B S hS} (τ : V ⟶ T)
    (h : ∀ a : RT T, ((SCH).map w).appTop.hom a = 0 → ((SCH).map τ).appTop.hom a = 0) :
    g.app (op V) τ ∈ (imS o).obj (op V) := by
  obtain ⟨C, c, hc, hr, hk⟩ := exists_closed_image w
  have hCa : IsAffine ((SCH).obj C) := isAffine_of_isAffineHom ((SCH).map c)
  have hsurj : Function.Surjective ((SCH).map c).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map c)).2
  have hker : RingHom.ker ((SCH).map c).appTop.hom ≤ RingHom.ker ((SCH).map τ).appTop.hom := by
    rw [hk]; exact fun a ha => h a ha
  obtain ⟨φ, hφ⟩ := exists_ringHom_lift _ hsurj ((SCH).map τ).appTop.hom hker
  have hfacS : toAffine (T := (SCH).obj V) (U := (SCH).obj C) φ ≫ (SCH).map c = (SCH).map τ := by
    refine toAffine_ext ?_
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, toAffine_appTop]
    exact hφ
  let l : V ⟶ C := siteHom (toAffine (T := (SCH).obj V) (U := (SCH).obj C) φ) (by
    rw [← site_w c, ← Category.assoc, hfacS, site_w])
  have hl : l ≫ c = τ := site_hom_ext (by rw [Functor.map_comp]; exact hfacS)
  have : τ ∈ (imS (yoneda.map w)).obj (op V) := by
    rw [← hr]; exact ⟨l, hl⟩
  rw [← preimage_image_chart_qs hX hqc hg sq] at this
  exact this

/-- The key of `image_stable_chart` for one affine `E` over `T₁[M] ×_X T₂` and one affine `W` over
`O ×_X T₁`. -/
theorem tmul_eq_zero_of_affine (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    {T₁ T₂ W₂ E W : BigFppfOver B S hS} [IsAffine ((SCH).obj T₁)] [IsAffine ((SCH).obj T₂)]
    [IsAffine ((SCH).obj E)] [IsAffine ((SCH).obj W)]
    {g₁ : yoneda.obj T₁ ⟶ X} {g₂ : yoneda.obj T₂ ⟶ X}
    {p₂ : W₂ ⟶ Ob P N} {w₂ : W₂ ⟶ T₂} (sq₂ : IsPullback (yoneda.map p₂) (yoneda.map w₂) o g₂)
    {e2 : E ⟶ T₂} {e1 : E ⟶ Gk M T₁}
    (he : g₂.app (op E) e2 = (orbMap actX g₁).app (op E) e1)
    {p : W ⟶ Ob P N} {w : W ⟶ T₁} (hc : o.app (op W) p = g₁.app (op W) w)
    [Algebra (RT T₁) (RT E)] (hα : algebraMap (RT T₁) (RT E) = ((SCH).map (e1 ≫ Gπ M T₁)).appTop.hom)
    [Algebra (RT T₁) (RT W)] (hβ : algebraMap (RT T₁) (RT W) = ((SCH).map w).appTop.hom)
    [Algebra.FiniteType (RT T₁) (RT W)]
    (a₂ : RT T₂) (ha₂ : ((SCH).map w₂).appTop.hom a₂ = 0) :
    (((SCH).map e2).appTop.hom a₂) ⊗ₜ[RT T₁] (1 : RT W) = 0 := by
  classical
  let μ := orbMap actX g₁
  let e0 : E ⟶ T₁ := e1 ≫ Gπ M T₁
  let α : RT T₁ →+* RT E := ((SCH).map e0).appTop.hom
  let β : RT T₁ →+* RT W := ((SCH).map w).appTop.hom
  let Ra := RT E ⊗[RT T₁] RT W
  haveI : Algebra.FiniteType (RT E) Ra := inferInstance
  have hC : B.Contains (Spec (.of Ra)) := contains_ft (RT E) Ra (contains_RT E)
  let Ef : BigFppfOver B S hS := spObj E (algebraMap (RT E) Ra) hC
  let s : Ef ⟶ E := spToT E _ hC
  let inr : RT W →+* Ra := (Algebra.TensorProduct.includeRight : RT W →ₐ[RT T₁] Ra).toRingHom
  let j : RT W →+* Γ((SCH).obj Ef, ⊤) := (spSec E (algebraMap (RT E) Ra) hC).comp inr
  have hjc : j.comp β = ((SCH).map (s ≫ e0)).appTop.hom := by
    refine RingHom.ext fun x => ?_
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change spSec E (algebraMap (RT E) Ra) hC (inr (β x)) =
      ((SCH).map s).appTop.hom (α x)
    rw [spToT_appTop]
    congr 1
    change (1 : RT E) ⊗ₜ[RT T₁] (β x) = (α x) ⊗ₜ[RT T₁] (1 : RT W)
    have e1' : β x = x • (1 : RT W) := by rw [Algebra.smul_def, mul_one, hβ]
    have e2' : α x = x • (1 : RT E) := by rw [Algebra.smul_def, mul_one, hα]
    rw [e1', e2', TensorProduct.smul_tmul]
  let tw : (SCH).obj Ef ⟶ (SCH).obj W := toAffine (T := (SCH).obj Ef) (U := (SCH).obj W) j
  have htw : tw ≫ (SCH).map w = (SCH).map (s ≫ e0) := by
    haveI : IsAffine ((SCH).obj Ef) := inferInstance
    refine toAffine_ext ?_
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, toAffine_appTop]
    exact hjc
  let toW : Ef ⟶ W := siteHom tw (by
    rw [← site_w w, ← Category.assoc, htw, site_w])
  have h2 : toW ≫ w = s ≫ e0 := site_hom_ext (by rw [Functor.map_comp]; exact htw)
  let ζ : Ef ⟶ Gk M T₁ := s ≫ e1
  let hE : Multiplicative M →* Γ((SCH).obj Ef, ⊤) :=
    secPt ((SCH).map ζ).appTop.hom (univPt1 (U := T₁))
  let x : Ef ⟶ Ob P N := oSmul N hE (toW ≫ p)
  have hx : o.app (op Ef) x = g₂.app (op Ef) (s ≫ e2) := by
    have a1 : o.app (op Ef) x = actX.smul (U := op Ef) hE (o.app (op Ef) (toW ≫ p)) :=
      hoe (T := op Ef) hE (toW ≫ p)
    have a2 : o.app (op Ef) (toW ≫ p) = g₁.app (op Ef) (toW ≫ w) := by
      rw [hom_nat, hom_nat, hc]
    have a3 : μ.app (op Ef) ζ = actX.smul (U := op Ef) hE (g₁.app (op Ef) (ζ ≫ Gπ M T₁)) :=
      orbMap_app actX g₁ ζ
    have a4 : g₂.app (op Ef) (s ≫ e2) = μ.app (op Ef) ζ := by
      rw [hom_nat, hom_nat, he]
    have a5 : toW ≫ w = ζ ≫ Gπ M T₁ := by
      rw [h2]; simp [ζ, e0]
    rw [a1, a2, a4, a3, a5]
  obtain ⟨l2, -, hl2⟩ := pb_lift sq₂ x (s ≫ e2) hx
  have hz : ((SCH).map (s ≫ e2)).appTop.hom a₂ = 0 := by
    rw [← hl2, Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map l2).appTop.hom (((SCH).map w₂).appTop.hom a₂) = 0
    rw [ha₂, map_zero]
  rw [Functor.map_comp, Scheme.Hom.comp_appTop] at hz
  change ((SCH).map s).appTop.hom (((SCH).map e2).appTop.hom a₂) = 0 at hz
  rw [spToT_appTop] at hz
  exact (spSec_bijective E _ hC).1 (hz.trans (map_zero _).symm)

/-- **Lemma 1.1, step A, on charts**, `X` not separated. -/
theorem image_stable_chart_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o)
    {T₁ T₂ W₁ W₂ : BigFppfOver B S hS} [IsAffine ((SCH).obj T₁)] [IsAffine ((SCH).obj T₂)]
    {g₁ : yoneda.obj T₁ ⟶ X} {g₂ : yoneda.obj T₂ ⟶ X}
    (hg₁ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g₁)
    (hg₂ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g₂)
    {p₁ : W₁ ⟶ Ob P N} {w₁ : W₁ ⟶ T₁} (sq₁ : IsPullback (yoneda.map p₁) (yoneda.map w₁) o g₁)
    {p₂ : W₂ ⟶ Ob P N} {w₂ : W₂ ⟶ T₂} (sq₂ : IsPullback (yoneda.map p₂) (yoneda.map w₂) o g₂)
    {V : BigFppfOver B S hS} (v₁ : V ⟶ T₁) (v₂ : V ⟶ T₂)
    (h : Multiplicative M →* Γ((SCH).obj V, ⊤))
    (hv : g₂.app (op V) v₂ = actX.smul (U := op V) h (g₁.app (op V) v₁))
    (hm : g₁.app (op V) v₁ ∈ (imS o).obj (op V)) :
    g₂.app (op V) v₂ ∈ (imS o).obj (op V) := by
  classical
  refine chart_mem_qs hX hqc hg₂ sq₂ v₂ fun a₂ ha₂ => ?_
  let μ := orbMap actX g₁
  obtain ⟨E, e₂, e₁, sqE⟩ := exists_pull_qs hX g₂ μ
  have hEet : Etale ((SCH).map e₁) := hg₂.property _ _ _ sqE
  obtain ⟨τ, hτ₁, hres⟩ := exists_gk_lift (M := M) v₁ h
  have hμτ : μ.app (op V) τ = g₂.app (op V) v₂ := by
    have := orbMap_app actX g₁ τ
    rw [hres, hτ₁] at this
    exact this.trans hv.symm
  obtain ⟨l, hl₂, hl₁⟩ := pb_lift sqE v₂ τ hμτ.symm
  -- the finite affine cover of `O ×_X T₁`
  haveI hcW := compactSpace_of_pull hX hqc sq₁
  obtain ⟨t, A, hA, hAc⟩ := exists_finite_affine_cover ((SCH).obj W₁)
  let Wi : t → BigFppfOver B S hS := fun i => Space.openSiteObject B S hS W₁ (A i)
  let ji : ∀ i, Wi i ⟶ W₁ := fun i => Space.openSiteObjectHom B S hS W₁ (A i)
  haveI hWi : ∀ i, IsAffine ((SCH).obj (Wi i)) := fun i => hA i
  letI algW : ∀ i, Algebra (RT T₁) (RT (Wi i)) := fun i => ((SCH).map (ji i ≫ w₁)).appTop.hom.toAlgebra
  have hβi : ∀ i, algebraMap (RT T₁) (RT (Wi i)) = ((SCH).map (ji i ≫ w₁)).appTop.hom := fun _ => rfl
  haveI hft : ∀ i, Algebra.FiniteType (RT T₁) (RT (Wi i)) := fun i => by
    have h1 : LocallyOfFinitePresentation ((SCH).map w₁) := hlfp.property _ _ _ sq₁
    have h2 : IsOpenImmersion ((SCH).map (ji i)) := by
      change IsOpenImmersion (A i).ι
      infer_instance
    have h3 : LocallyOfFiniteType ((SCH).map (ji i ≫ w₁)) := by
      rw [Functor.map_comp]; infer_instance
    exact (RingHom.finiteType_algebraMap).1
      ((HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 h3)
  have hI : ∀ x : RT T₁, x ∈ (⨅ i, RingHom.ker (algebraMap (RT T₁) (RT (Wi i)))) →
      ((SCH).map v₁).appTop.hom x = 0 := by
    intro x hx
    refine chart_kills_qs hX hqc hg₁ sq₁ v₁ hm x ?_
    refine eq_zero_of_cover A hAc _ fun i => ?_
    have := (Ideal.mem_iInf.1 hx) i
    rw [RingHom.mem_ker, hβi, Functor.map_comp, Scheme.Hom.comp_appTop] at this
    exact this
  -- local on `V`
  have hxE : ∀ x : (SCH).obj V, ∃ E0 : ((SCH).obj E).Opens, IsAffineOpen E0 ∧ (SCH).map l x ∈ E0 := fun x => by
    obtain ⟨E0, h0, hm0, -⟩ := exists_isAffineOpen_mem_and_subset (x := (SCH).map l x) (U := ⊤) trivial
    exact ⟨E0, h0, hm0⟩
  choose E0 hE0 hmE0 using hxE
  refine eq_zero_of_cover (fun x => (SCH).map l ⁻¹ᵁ E0 x) (fun x => ⟨x, hmE0 x⟩) _ fun x => ?_
  let Es := Space.openSiteObject B S hS E (E0 x)
  let jE : Es ⟶ E := Space.openSiteObjectHom B S hS E (E0 x)
  let Vs := Space.openSiteObject B S hS V ((SCH).map l ⁻¹ᵁ E0 x)
  let jV : Vs ⟶ V := Space.openSiteObjectHom B S hS V ((SCH).map l ⁻¹ᵁ E0 x)
  haveI hEs : IsAffine ((SCH).obj Es) := hE0 x
  let ls : Vs ⟶ Es := siteHom (((SCH).map l) ∣_ E0 x) (by
    have e0 := morphismRestrict_ι ((SCH).map l) (E0 x)
    change ((SCH).map l ∣_ E0 x) ≫ ((E0 x).ι ≫ E.hom.hom) = ((SCH).map l ⁻¹ᵁ E0 x).ι ≫ V.hom.hom
    rw [← Category.assoc, e0, Category.assoc, site_w])
  have hls : ls ≫ jE = jV ≫ l := site_hom_ext (morphismRestrict_ι ((SCH).map l) (E0 x))
  let e1s : Es ⟶ Gk M T₁ := jE ≫ e₁
  let e2s : Es ⟶ T₂ := jE ≫ e₂
  letI algE : Algebra (RT T₁) (RT Es) := ((SCH).map (e1s ≫ Gπ M T₁)).appTop.hom.toAlgebra
  have hαE : algebraMap (RT T₁) (RT Es) = ((SCH).map (e1s ≫ Gπ M T₁)).appTop.hom := rfl
  haveI hfl : Module.Flat (RT T₁) (RT Es) := by
    have h2 : Flat ((SCH).map (Gπ M T₁)) := flat_gπ T₁
    have h3 : IsOpenImmersion ((SCH).map jE) := by
      change IsOpenImmersion (E0 x).ι
      infer_instance
    have h4 : Flat ((SCH).map (e1s ≫ Gπ M T₁)) := by
      simp only [e1s, Functor.map_comp]; infer_instance
    change (algebraMap (RT T₁) (RT Es)).Flat
    rw [hαE]
    exact (HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 h4
  have hgE : g₂.app (op Es) e2s = μ.app (op Es) e1s := by
    rw [hom_nat, hom_nat, pb_comm sqE]
  have hkey : ((SCH).map e2s).appTop.hom a₂ ∈
      (⨅ i, RingHom.ker (algebraMap (RT T₁) (RT (Wi i)))).map (algebraMap (RT T₁) (RT Es)) := by
    refine mem_map_iInf_ker _ fun i => ?_
    have hc : o.app (op (Wi i)) (ji i ≫ p₁) = g₁.app (op (Wi i)) (ji i ≫ w₁) := by
      rw [hom_nat, hom_nat, pb_comm sq₁]
    exact tmul_eq_zero_of_affine actX hoe sq₂ hgE hc hαE (hβi i) a₂ ha₂
  have hcomp : ls ≫ e1s ≫ Gπ M T₁ = jV ≫ v₁ := by
    change ls ≫ (jE ≫ e₁) ≫ Gπ M T₁ = _
    simp only [Category.assoc]
    rw [← Category.assoc ls, hls, Category.assoc, ← Category.assoc l, hl₁, hτ₁]
  have hfin : ((SCH).map ls).appTop.hom.comp (algebraMap (RT T₁) (RT Es)) =
      ((SCH).map (jV ≫ v₁)).appTop.hom := by
    rw [← hcomp, hαE, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  have hker : (⨅ i, RingHom.ker (algebraMap (RT T₁) (RT (Wi i)))).map (algebraMap (RT T₁) (RT Es)) ≤
      RingHom.ker ((SCH).map ls).appTop.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hfin, Functor.map_comp,
      Scheme.Hom.comp_appTop]
    change ((SCH).map jV).appTop.hom (((SCH).map v₁).appTop.hom y) = 0
    rw [hI y hy, map_zero]
  have hz := hker hkey
  rw [RingHom.mem_ker] at hz
  have e3 : ls ≫ e2s = jV ≫ v₂ := by
    change ls ≫ jE ≫ e₂ = _
    rw [← Category.assoc, hls, Category.assoc, hl₂]
  have e4 : ((SCH).map (jV ≫ v₂)).appTop.hom a₂ = 0 := by
    rw [← e3, Functor.map_comp, Scheme.Hom.comp_appTop]
    exact hz
  rw [Functor.map_comp, Scheme.Hom.comp_appTop] at e4
  exact e4

/-- **Lemma 1.1, step A**: the scheme-theoretic image of the orbit is stable under `D(M)`. -/
theorem image_stable_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
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
  obtain ⟨W₁, p₁, w₁, sq₁⟩ := exists_pull_qs hX o g₁
  obtain ⟨W₂, p₂, w₂, sq₂⟩ := exists_pull_qs hX o g₂
  have hmem₁ : g₁.app (op T₂) (e₂ ≫ u₁) ∈ (imS o).obj (op T₂) := by
    rw [hom_nat, hu₁']
    change X.map e₂.op (X.map e₁.op t) ∈ _
    exact (imS o).map _ ((imS o).map _ ht)
  have hkey := image_stable_chart_qs hX hqc actX hoe hlfp hg₁ hg₂ sq₁ sq₂ (e₂ ≫ u₁) u₂
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

end AlgMag.ChartQSL11
