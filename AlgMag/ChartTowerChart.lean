/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartTowerPoints
import AlgMag.ChartEffective

/-!
# An affine chart of the thickenings

* `AlgMag.ChartMain.exists_affine_chart_over_orbit`: finitely many affines of an atlas, whose
  coproduct is an affine étale `V → X` through which every point of an affine `O` lifts.
* `AlgMag.ChartMain.thick_etale`, `thick_surjective`: `V(𝒥^{n+1}) → X_n` is a surjective étale chart.
* `AlgMag.ChartMain.isAffine_relation`: its relation is affine, `X` separated and `S` affine.
* `AlgMag.ChartMain.exists_affine_thickening`: `X_n` is affine.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- Base change of a representable property, on the site. -/
lemma presheaf_of_isPullback {Q : MorphismProperty Scheme.{u}} [Q.IsStableUnderBaseChange]
    {A' A Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f' : A' ⟶ A} {g' : A' ⟶ Y'} {g : A ⟶ Y}
    {f : Y' ⟶ Y} (sq : IsPullback f' g' g f)
    (hg : (Q.inverseImage (SCH)).presheaf g) : (Q.inverseImage (SCH)).presheaf g' := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hQ : Q.IsStableUnderBaseChange := inferInstance
  have : (Q.inverseImage (SCH)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ hQ.of_isPullback (hsq.map (SCH)) hg⟩
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) (Q.inverseImage (SCH))
  exact MorphismProperty.of_isPullback sq hg

section Cover

variable {U O : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X} {j : yoneda.obj O ⟶ X}
  (ho : ClosedP j)

/-- **§2 (1)**: finitely many affines of an atlas `U` cover an affine `O ⊂ X`. -/
theorem exists_affine_chart_over_orbit [IsAffine ((SCH).obj O)]
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ) :
    ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj V)) (r : V ⟶ U), Etale ((SCH).map r) ∧
      ∀ w : (SCH).obj O, ∃ q : (SCH).obj (ho.rep.pullback (yoneda.map r ≫ φ)),
        ((SCH).map (yoneda.preimage (ho.rep.fst (yoneda.map r ≫ φ)))) q = w := by
  let G := SCH
  let P := ho.rep.pullback φ
  let i := ho.rep.snd φ
  obtain ⟨f, hf⟩ := yoneda.map_surjective (ho.rep.fst φ)
  have sq0 : IsPullback (yoneda.map i) (yoneda.map f) φ j := by
    rw [hf]; exact (ho.rep.isPullback φ).flip
  have hfe : Etale (G.map f) := he.property j (yoneda.map i) f sq0
  have hfs : Surjective (G.map f) := hs.property j (yoneda.map i) f sq0
  -- an affine open around each point of `P`
  have hW : ∀ a : G.obj P, ∃ W : (G.obj U).Opens, IsAffineOpen W ∧ (G.map i) a ∈ W := fun a => by
    obtain ⟨W, hW, ha, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp (G.obj U).isBasis_affineOpens
      (show (G.map i) a ∈ (⊤ : (G.obj U).Opens) from trivial)
    exact ⟨W, hW, ha⟩
  choose W hWa hWm using hW
  let A : G.obj P → Set (G.obj O) := fun a => (G.map f) '' ((G.map i) ⁻¹' (W a : Set (G.obj U)))
  have hAo : ∀ a, IsOpen (A a) := fun a =>
    (G.map f).isOpenMap _ ((W a).2.preimage (G.map i).continuous)
  have hAc : (Set.univ : Set (G.obj O)) ⊆ ⋃ a, A a := fun w _ => by
    obtain ⟨a, rfl⟩ := (G.map f).surjective w
    exact Set.mem_iUnion.2 ⟨a, a, hWm a, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover A hAo hAc
  -- the coproduct
  let Y : t → Scheme.{u} := fun a => (W a.1).toScheme
  let Z : Scheme.{u} := ∐ Y
  have hYa : ∀ a, IsAffine (Y a) := fun a => hWa a.1
  have hZa : IsAffine Z := inferInstance
  let ρ : Z ⟶ G.obj U := Sigma.desc fun a => (W a.1).ι
  have hρ : Etale ρ := by
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
    refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale.{u}) (f := ρ)
      (sigmaOpenCover Y)).2 fun a => ?_
    have e : Sigma.ι Y a ≫ ρ = (W a.1).ι := Sigma.ι_desc _ _
    change Etale (Sigma.ι Y a ≫ ρ)
    rw [e]
    infer_instance
  have hC : B.Contains Z := by
    refine Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
      (Cardinal.lt_aleph0_of_finite _).le Y fun a => ?_
    exact Scheme.size_lt_of_isOpenImmersion (W a.1).ι U.left.2
  let V : BigFppfOver B S hS := Over.mk (⟨ρ ≫ U.hom.hom⟩ : B.obj hC ⟶ B.obj hS)
  let r : V ⟶ U := Over.homMk ⟨ρ⟩ rfl
  have hGr : G.map r = ρ := rfl
  refine ⟨V, hZa, r, hρ, fun w => ?_⟩
  -- the point
  obtain ⟨c, hc⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ w))
  obtain ⟨hct, hc⟩ := Set.mem_iUnion.1 hc
  obtain ⟨p, hp, rfl⟩ := hc
  let v : Z := (Sigma.ι Y ⟨c, hct⟩ : Y _ ⟶ Z) (⟨(G.map i) p, hp⟩ : (W c).toScheme)
  have hv : ρ v = (G.map i) p := by
    have e : (Sigma.ι Y ⟨c, hct⟩ : Y _ ⟶ Z) ≫ ρ = (W c).ι := Sigma.ι_desc _ _
    have h2 : ((Sigma.ι Y ⟨c, hct⟩ : Y _ ⟶ Z) ≫ ρ) (⟨(G.map i) p, hp⟩ : (W c).toScheme) = (G.map i) p := by
      rw [e]; rfl
    exact h2
  obtain ⟨m, hm, hm'⟩ := isPullback_snd_comp ho r φ _ rfl
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hPb := (hm.map G)
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.map i) (g := G.map r)
    p v hv.symm
  refine ⟨hPb.isoPullback.inv q, ?_⟩
  have hfst : yoneda.preimage (ho.rep.fst (yoneda.map r ≫ φ)) = m ≫ f := by
    apply yoneda.map_injective
    rw [Functor.map_preimage, Functor.map_comp, hf, hm']
  have hin : (G.map m) (hPb.isoPullback.inv q) = p := by
    have e := hPb.isoPullback_inv_fst
    have e2 := congrArg (fun z : pullback (G.map i) (G.map r) ⟶ G.obj P => z q) e
    exact e2.trans hq1
  rw [hfst, Functor.map_comp]
  change (G.map f) ((G.map m) _) = _
  rw [hin]

end Cover

/-- Pullback squares and a monomorphism on the base. -/
lemma isPullback_comp_mono_iff {C : Type*} [Category C] {A Y Z W W' : C} {a : A ⟶ Y} {b : A ⟶ Z}
    {u : Y ⟶ W} {v : Z ⟶ W} (ι : W ⟶ W') [Mono ι] :
    IsPullback a b (u ≫ ι) (v ≫ ι) ↔ IsPullback a b u v := by
  constructor
  · intro h
    have hw : a ≫ u = b ≫ v := (cancel_mono ι).1 (by simpa using h.w)
    refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
      (fun s => h.lift s.fst s.snd (by rw [← Category.assoc, s.condition, Category.assoc]))
      (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _) (fun s m h1 h2 => h.hom_ext
        (by rw [h1, h.lift_fst]) (by rw [h2, h.lift_snd])))
  · intro h
    have hw : a ≫ u ≫ ι = b ≫ v ≫ ι := by rw [← Category.assoc, h.w, Category.assoc]
    refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
      (fun s => h.lift s.fst s.snd ((cancel_mono ι).1 (by simpa using s.condition)))
      (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _) (fun s m h1 h2 => h.hom_ext
        (by rw [h1, h.lift_fst]) (by rw [h2, h.lift_snd])))

section Thick

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {O : BigFppfOver B S hS}
  {j : yoneda.obj O ⟶ X} (ho : ClosedP j)

include ho in
/-- A closed immersion factoring through a monomorphism is closed in the middle. -/
lemma closedP_of_comp_mono {j' : yoneda.obj O ⟶ Y} (ι : Y ⟶ X) [Mono ι] (h : j' ≫ ι = j) :
    ClosedP j' := by
  have hr : (MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  subst h
  refine MorphismProperty.relative.of_exists fun a g => ⟨ho.rep.pullback (g ≫ ι),
    ho.rep.fst (g ≫ ι), ho.rep.snd (g ≫ ι),
    (isPullback_comp_mono_iff ι).1 (ho.rep.isPullback (g ≫ ι)), ho.property_snd (g ≫ ι)⟩

variable {U V : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  {ψ : yoneda.obj V ⟶ X}
  (heψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) ψ)
  (hcov : ∀ w : (BigFppfOver.toScheme B S hS).obj O,
    ∃ q : (BigFppfOver.toScheme B S hS).obj (ho.rep.pullback ψ),
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (ho.rep.fst ψ))) q = w)

include heψ in
/-- The chart of `X_n` is étale. -/
theorem thick_etale {n : ℕ} {k : yoneda.obj (thickChart ho ψ n) ⟶ (thickening ho φ n).toFunctor}
    (sq : IsPullback k (yoneda.map (thickChartι ho ψ n)) (thickening ho φ n).ι ψ) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) k :=
  presheaf_of_isPullback sq.flip heψ

include hs he hcov in
/-- **§2 (1)**: the chart of `X_n` is surjective, because the ideal of `T ×_X O` is nilpotent. -/
theorem thick_surjective {n : ℕ}
    {k : yoneda.obj (thickChart ho ψ n) ⟶ (thickening ho φ n).toFunctor}
    (sq : IsPullback k (yoneda.map (thickChartι ho ψ n)) (thickening ho φ n).ι ψ)
    (hk : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) k) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) k := by
  have hr : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hk.rep fun T g => ?_
  change Surjective _
  refine ⟨fun τ => ?_⟩
  let G := SCH
  let ι := (thickening ho φ n).ι
  let t : yoneda.obj T ⟶ X := g ≫ ι
  have hP : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hJ : idealOf ho t ^ (n + 1) = ⊥ := by
    have hm : yonedaEquiv t ∈ (thickening ho φ n).obj (op T) := by
      rw [yonedaEquiv_comp]; exact (yonedaEquiv g).2
    have := (mem_thickening_iff ho hs he n _).1 hm
    rwa [Equiv.symm_apply_apply] at this
  have hc := snd_closed ho t
  have hsup : (idealOf ho t).support = ⊤ := by
    rw [← Scheme.IdealSheafData.support_pow_succ _ n, hJ, Scheme.IdealSheafData.support_bot]
  have hτ : τ ∈ Set.range (G.map (ho.rep.snd t)) := by
    have h1 : τ ∈ ((idealOf ho t).support : Set (G.obj T)) := by rw [hsup]; trivial
    rw [idealOf, Scheme.Hom.support_ker] at h1
    rwa [(G.map (ho.rep.snd t)).isClosedEmbedding.isClosed_range.closure_eq] at h1
  obtain ⟨pt, rfl⟩ := hτ
  obtain ⟨qt, hqt⟩ := hcov ((G.map (yoneda.preimage (ho.rep.fst t))) pt)
  let ft : ho.rep.pullback t ⟶ O := yoneda.preimage (ho.rep.fst t)
  let fψ : ho.rep.pullback ψ ⟶ O := yoneda.preimage (ho.rep.fst ψ)
  let W := pullback ft fψ
  have hW : IsPullback (G.map (pullback.fst ft fψ)) (G.map (pullback.snd ft fψ)) (G.map ft) (G.map fψ) :=
    (IsPullback.of_hasPullback ft fψ).map G
  obtain ⟨z0, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.map ft) (g := G.map fψ)
    pt qt hqt.symm
  have outer := (hk.rep.isPullback g).paste_horiz sq.flip
  have hft : yoneda.map ft = ho.rep.fst t := Functor.map_preimage _ _
  have hfψ : yoneda.map fψ = ho.rep.fst ψ := Functor.map_preimage _ _
  have hcomm : yoneda.map (pullback.snd ft fψ ≫ ho.rep.snd ψ) ≫ ψ =
      yoneda.map (pullback.fst ft fψ ≫ ho.rep.snd t) ≫ (g ≫ ι) := by
    rw [Functor.map_comp, Category.assoc, ← ho.rep.w ψ, Functor.map_comp, Category.assoc,
      show g ≫ ι = t from rfl, ← ho.rep.w t, ← hft, ← hfψ, ← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  let l0 := outer.lift _ _ hcomm
  have hl0 : l0 ≫ yoneda.map (hk.rep.snd g) = yoneda.map (pullback.fst ft fψ ≫ ho.rep.snd t) :=
    outer.lift_snd _ _ _
  obtain ⟨l, hl⟩ := yoneda.map_surjective l0
  have hl' : l ≫ hk.rep.snd g = pullback.fst ft fψ ≫ ho.rep.snd t := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hl, hl0]
  let z : G.obj W := hW.isoPullback.inv z0
  have hzp : (G.map (pullback.fst ft fψ)) z = pt := by
    have e := hW.isoPullback_inv_fst
    exact (congrArg (fun m : _ ⟶ G.obj _ => m z0) e).trans hz1
  refine ⟨(G.map l) z, ?_⟩
  have e : G.map l ≫ G.map (hk.rep.snd g) =
      G.map (pullback.fst ft fψ) ≫ G.map (ho.rep.snd t) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hl']
  change (G.map l ≫ G.map (hk.rep.snd g)) z = _
  rw [e]
  change (G.map (ho.rep.snd t)) ((G.map (pullback.fst ft fψ)) z) = _
  rw [hzp]

/-- **§2 (1)**: the relation of an affine chart of a subfunctor of a separated `X` is affine, over an
affine base. -/
theorem isAffine_relation [IsAffine S] (hsep : Space.IsSeparatedOver B S hS X)
    {V' : BigFppfOver B S hS} [IsAffine ((SCH).obj V')] (ι : Y ⟶ X) [Mono ι]
    {k : yoneda.obj V' ⟶ Y}
    (hk : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) k) :
    IsAffine ((SCH).obj (Space.atlasRelation B S hS hk)) := by
  let G := SCH
  have hP : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  let T1 : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hT1 : IsAffine (G.obj T1) := ‹IsAffine S›
  let a : V' ⟶ T1 := (Over.mkIdTerminal).from V'
  let W := pullback a a
  have hsq : IsPullback (G.map (pullback.fst a a)) (G.map (pullback.snd a a)) (G.map a) (G.map a) :=
    (IsPullback.of_hasPullback a a).map G
  have hWa : IsAffine (G.obj W) := by
    have h1 : IsAffineHom (G.map a) := isAffineHom_of_isAffine _
    have h2 : IsAffineHom (G.map (pullback.fst a a)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) hsq.flip h1
    exact isAffine_of_isAffineHom (G.map (pullback.fst a a))
  let p := yonedaEquiv (yoneda.map (pullback.fst a a) ≫ k ≫ ι)
  let q := yonedaEquiv (yoneda.map (pullback.snd a a) ≫ k ≫ ι)
  obtain ⟨E, i, hi, hE⟩ := Chart.exists_eqLocus hsep W p q
  have hEa : IsAffine (G.obj E) := isAffine_of_isAffineHom (G.map i)
  let R := Space.atlasRelation B S hS hk
  let tR := Space.atlasRelationTarget B S hS hk
  let sR := Space.atlasRelationSource B S hS hk
  have hw : yoneda.map tR ≫ k = yoneda.map sR ≫ k := rel_w hk
  have hE' : ∀ {W' : BigFppfOver B S hS} (τ : W' ⟶ W),
      yoneda.map (τ ≫ pullback.fst a a) ≫ k = yoneda.map (τ ≫ pullback.snd a a) ≫ k ↔
        ∃ u : W' ⟶ E, u ≫ i = τ := fun {W'} τ => by
    rw [← hE W' τ]
    change _ ↔ X.map τ.op (yonedaEquiv _) = X.map τ.op (yonedaEquiv _)
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality, yonedaEquiv.apply_eq_iff_eq]
    simp only [Functor.map_comp, Category.assoc]
    constructor
    · intro h
      simpa only [Category.assoc] using congrArg (· ≫ ι) h
    · intro h
      exact (cancel_mono ι).1 (by simpa only [Category.assoc] using h)
  let u0 : R ⟶ W := pullback.lift tR sR (Subsingleton.elim (α := R ⟶ T1)
    (h := ⟨fun _ _ => (Over.mkIdTerminal).hom_ext _ _⟩) _ _)
  have hu01 : u0 ≫ pullback.fst a a = tR := pullback.lift_fst _ _ _
  have hu02 : u0 ≫ pullback.snd a a = sR := pullback.lift_snd _ _ _
  obtain ⟨u, hu⟩ := (hE' u0).1 (by rw [hu01, hu02]; exact hw)
  have hm : Mono i := (SCH).mono_of_mono_map inferInstance
  have hii : yoneda.map (i ≫ pullback.fst a a) ≫ k = yoneda.map (i ≫ pullback.snd a a) ≫ k :=
    (hE' i).2 ⟨𝟙 _, Category.id_comp _⟩
  let v : E ⟶ R := hk.rep.lift' (i ≫ pullback.fst a a) (i ≫ pullback.snd a a) hii
  have hv1 : v ≫ tR = i ≫ pullback.fst a a := hk.rep.lift'_fst _ _ _
  have hv2 : v ≫ sR = i ≫ pullback.snd a a := hk.rep.lift'_snd _ _ _
  have hvu : v ≫ u = 𝟙 _ := by
    rw [← cancel_mono i, Category.assoc, hu, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, hu01, hv1]
    · rw [Category.assoc, hu02, hv2]
  have huv : u ≫ v = 𝟙 _ := by
    apply yoneda.map_injective
    refine (hk.rep.isPullback k).hom_ext ?_ ?_
    · have e : u ≫ v ≫ tR = tR := by rw [hv1, ← Category.assoc, hu, hu01]
      have e1 : yoneda.map tR = hk.rep.fst k := Functor.map_preimage _ _
      rw [← e1, ← Functor.map_comp, ← Functor.map_comp, Category.assoc, e, Category.id_comp]
    · have e : u ≫ v ≫ sR = sR := by rw [hv2, ← Category.assoc, hu, hu02]
      change _ ≫ yoneda.map sR = _ ≫ yoneda.map sR
      rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, e, Category.id_comp]
  have hiso : IsIso u := ⟨v, huv, hvu⟩
  exact IsAffine.of_isIso (G.map u)

/-- `O → X_n`. -/
lemma range_le_thickening (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ) (n : ℕ) :
    Subfunctor.range j ≤ thickening ho φ n := by
  rintro ⟨T⟩ _ ⟨g, rfl⟩
  refine (mem_thickening_iff ho hs he n _).2 ?_
  have hc : yonedaEquiv.symm (j.app (op T) g) = yoneda.map g ≫ j := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    simp
  rw [hc, idealOf_eq_bot_of_factors, pow_succ', Scheme.IdealSheafData.bot_mul]

/-- The ideal of `O` on the chart `V`, on global sections. -/
noncomputable abbrev chartIdeal (ψ : yoneda.obj V ⟶ X) : Ideal Γ((SCH).obj V, ⊤) :=
  RingHom.ker ((SCH).map (ho.rep.snd ψ)).appTop.hom

lemma ker_thickChartι_appTop [IsAffine ((SCH).obj V)] (ψ : yoneda.obj V ⟶ X) (n : ℕ) :
    RingHom.ker ((SCH).map (thickChartι ho ψ n)).appTop.hom = chartIdeal ho ψ ^ (n + 1) := by
  have := thickChartι_closed ho ψ n
  have := snd_closed ho ψ
  have h := congrArg (fun I : ((SCH).obj V).IdealSheafData =>
    I.ideal ⟨⊤, isAffineOpen_top _⟩) (ker_thickChartι ho ψ n)
  simp only [idealOf, Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] at h
  exact h

include heψ hcov in
/-- **§2**: `X_n` is affine (Stacks 05ZR). -/
theorem exists_affine_thickening [IsAffine S] [IsAffine ((SCH).obj O)] [IsAffine ((SCH).obj V)]
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ) (n : ℕ) :
    ∃ (T : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj T)),
      Nonempty (yoneda.obj T ≅ (thickening ho φ n).toFunctor) := by
  let G := SCH
  have hA := (isClosedSubspace_thickening ho hX hs he n).1
  obtain ⟨k, sq⟩ := exists_isPullback_thickening ho hs he ψ n
  have hke := thick_etale ho heψ sq
  have hks := thick_surjective ho hs he hcov sq hke
  have hcl := thickChartι_closed ho ψ n
  have hVa : IsAffine (G.obj (thickChart ho ψ n)) :=
    isAffine_of_isAffineHom (G.map (thickChartι ho ψ n))
  have hRa := isAffine_relation hsep (thickening ho φ n).ι hks
  let jn : yoneda.obj O ⟶ (thickening ho φ n).toFunctor :=
    Subfunctor.lift j (range_le_thickening ho hs he n)
  have hjn : jn ≫ (thickening ho φ n).ι = j := Subfunctor.lift_ι _ _
  have hon : ClosedP jn := closedP_of_comp_mono ho _ hjn
  refine exists_affine_of_nilpotent_chart (ho := hon) hA hks hke (n := n + 1) ?_
  -- nilpotence, compared with `chartZ`
  have hP : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hs1 := hon.rep.isPullback k
  have hs2 : IsPullback (hon.rep.fst k) (yoneda.map (hon.rep.snd k)) j
      (yoneda.map (thickChartι ho ψ n) ≫ ψ) := by
    have e : yoneda.map (thickChartι ho ψ n) ≫ ψ = k ≫ (thickening ho φ n).ι := sq.w.symm
    have h := (isPullback_comp_mono_iff (thickening ho φ n).ι).2 hs1
    rw [hjn] at h
    rw [e]
    exact h
  have hc' : hon.rep.fst k ≫ j = yoneda.map (hon.rep.snd k ≫ thickChartι ho ψ n) ≫ ψ := by
    rw [hs2.w, Functor.map_comp, Category.assoc]
  let m : hon.rep.pullback k ⟶ ho.rep.pullback ψ :=
    ho.rep.lift (hon.rep.fst k) (hon.rep.snd k ≫ thickChartι ho ψ n) hc'
  have hm : m ≫ ho.rep.snd ψ = hon.rep.snd k ≫ thickChartι ho ψ n := ho.rep.lift_snd _ _ _
  have hm' : yoneda.map m ≫ ho.rep.fst ψ = hon.rep.fst k := ho.rep.lift_fst _ _ _
  have sq3 : IsPullback (yoneda.map m) (yoneda.map (hon.rep.snd k)) (yoneda.map (ho.rep.snd ψ))
      (yoneda.map (thickChartι ho ψ n)) := by
    refine IsPullback.of_right (h₁₂ := ho.rep.fst ψ) (v₁₃ := j) (h₂₂ := ψ) ?_ ?_
      (ho.rep.isPullback ψ)
    · rw [hm']; exact hs2
    · rw [← Functor.map_comp, ← Functor.map_comp, hm]
  have sq4 : IsPullback m (hon.rep.snd k) (ho.rep.snd ψ) (thickChartι ho ψ n) :=
    IsPullback.of_map yoneda (by rw [hm]) sq3
  have hc1 : IsClosedImmersion (G.map (ho.rep.snd ψ)) := snd_closed ho ψ
  have hc2 : IsClosedImmersion (G.map (hon.rep.snd k)) := snd_closed hon k
  have hkm := ker_map_of_isPullback ((sq4.map G).flip)
  rw [hkm, ← Ideal.map_pow, ← ker_thickChartι_appTop ho ψ n]
  exact (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl

end Thick

end AlgMag.ChartMain
