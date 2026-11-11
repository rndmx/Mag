/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSL11Flat

/-!
# Lemma 1.1 for quasi-separated `X`, step B: generic flatness of the orbit

`exists_chart_affine_pull` finds a chart over which `O ×_X U` is affine, and the proof of
`exists_good_basicOpen` runs on it.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace AlgMag.ChartQSL11

open ChartMain AlgMag.ChartPoint

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]

variable [IsAffine S] {o : yoneda.obj (Ob P N) ⟶ X}

/-- **The generic chart.** There is an affine étale chart `U → X` over which `O ×_X U` is affine and
nonempty. Choose `y` a generic point of the closure of the image of `O ×_X U₀ → U₀`: it is the image of
a point `η` of `O ×_X U₀`, and is not a specialization of any other point of the image, the map being
injective. So `y` is outside the closure of the image of the complement of an affine open containing
`η`, and a principal open of `U₀` around `y` does the job. -/
theorem exists_chart_affine_pull (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    (hoi : ∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P N),
      o.app (op T) a = o.app (op T) b → a = b)
    (x0 : (SCH).obj (Ob P N)) :
    ∃ (U' W0 : BigFppfOver B S hS) (g : yoneda.obj U' ⟶ X) (p0 : W0 ⟶ Ob P N) (w0 : W0 ⟶ U'),
      IsAffine ((SCH).obj U') ∧ IsAffine ((SCH).obj W0) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g ∧ Nonempty ((SCH).obj W0) ∧
      IsPullback (yoneda.map p0) (yoneda.map w0) o g := by
  classical
  obtain ⟨T₁, U, e, y₁, g, u, hU, hE, hy, hg, hu⟩ := exists_affine_chart hX o x0
  haveI := hU
  obtain ⟨W, p, w, sq⟩ := exists_pull_qs hX o g
  obtain ⟨l, hl1, -⟩ := pb_lift sq e u hu.symm
  let η0 : (SCH).obj W := (SCH).map l y₁
  haveI hcW := compactSpace_of_pull hX hqc sq
  obtain ⟨t, A, hA, hAc⟩ := exists_finite_affine_cover ((SCH).obj W)
  let f : (SCH).obj W ⟶ (SCH).obj U := (SCH).map w
  haveI hmf : Mono f := mono_of_pull hoi sq
  have hfinj : Function.Injective f := f.injective
  let h : (SCH).obj U ≃ₜ PrimeSpectrum Γ((SCH).obj U, ⊤) := ((SCH).obj U).isoSpec.hom.homeomorph
  let I : Ideal Γ((SCH).obj U, ⊤) := PrimeSpectrum.vanishingIdeal (h '' Set.range f)
  have hmemI : ∀ z : (SCH).obj W, I ≤ (h (f z)).asIdeal := fun z a ha =>
    (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha _ ⟨f z, ⟨z, rfl⟩, rfl⟩
  have hIle : I ≤ (h (f η0)).asIdeal := hmemI η0
  haveI hη0p : (h (f η0)).asIdeal.IsPrime := (h (f η0)).isPrime
  obtain ⟨y, hy, hyle⟩ := Ideal.exists_minimalPrimes_le hIle
  haveI hyp : y.IsPrime := hy.1.1
  let yS : PrimeSpectrum Γ((SCH).obj U, ⊤) := ⟨y, hyp⟩
  let yT : (SCH).obj U := h.symm yS
  have hyT : h yT = yS := h.apply_symm_apply _
  -- closure
  have hycl : yT ∈ closure (Set.range f) := by
    have : yS ∈ closure (h '' Set.range f) := by
      rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact hy.1.2
    rw [← h.image_closure] at this
    obtain ⟨z, hz, hzy⟩ := this
    have : z = yT := by rw [← h.symm_apply_apply z, hzy]
    rwa [← this]
  -- `y` is generic in the image
  have hgen : ∀ z : (SCH).obj W, f z ⤳ yT → f z = yT := by
    intro z hz
    have h1 : h (f z) ⤳ yS := by rw [← hyT]; exact hz.map h.continuous
    have h2 : (h (f z)).asIdeal ≤ y := (PrimeSpectrum.le_iff_specializes _ _).2 h1
    have h3 : I ≤ (h (f z)).asIdeal := hmemI z
    have h4 : y ≤ (h (f z)).asIdeal := hy.2 ⟨(h (f z)).isPrime, h3⟩ h2
    have h5 : h (f z) = yS := PrimeSpectrum.ext (le_antisymm h2 h4)
    exact h.injective (h5.trans hyT.symm)
  -- generization in a piece
  have hpiece : ∀ (Q : Set ((SCH).obj W)), IsClosed Q → yT ∈ closure (f '' Q) → ∃ z ∈ Q, f z = yT := by
    intro Q hQ hin
    have hunion : f '' Q = ⋃ i, (f '' (Q ∩ (A i : Set _))) := by
      ext a
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨i, hi⟩ := hAc z
        exact Set.mem_iUnion.2 ⟨i, z, ⟨hz, hi⟩, rfl⟩
      · intro ha
        obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 ha
        exact ⟨z, hz.1, rfl⟩
    rw [hunion, closure_iUnion_of_finite] at hin
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hin
    haveI : IsAffine (A i).toScheme := hA i
    let fi : (A i).toScheme ⟶ (SCH).obj U := (A i).ι ≫ f
    let Qi : Set (A i).toScheme := (A i).ι ⁻¹' Q
    have hQi : IsClosed Qi := hQ.preimage (A i).ι.continuous
    have hsub : f '' (Q ∩ (A i : Set _)) ⊆ fi '' Qi := by
      rintro _ ⟨z, ⟨hz, hzi⟩, rfl⟩
      exact ⟨⟨z, hzi⟩, hz, rfl⟩
    obtain ⟨z, hz, hs⟩ := exists_specializes_of_mem_closure fi Qi hQi yT (closure_mono hsub hi)
    exact ⟨(A i).ι z, hz, hgen _ hs⟩
  obtain ⟨η, -, hη⟩ := hpiece Set.univ isClosed_univ (by rwa [Set.image_univ])
  obtain ⟨i0, hi0⟩ := hAc η
  let Ai := A i0
  have hnot : yT ∉ closure (f '' ((Ai : Set ((SCH).obj W))ᶜ)) := by
    intro hin
    obtain ⟨z, hz, hzy⟩ := hpiece _ Ai.isOpen.isClosed_compl hin
    have : z = η := hfinj (hzy.trans hη.symm)
    exact hz (this ▸ hi0)
  let Vc : ((SCH).obj U).Opens := ⟨(closure (f '' ((Ai : Set ((SCH).obj W))ᶜ)))ᶜ, isClosed_closure.isOpen_compl⟩
  obtain ⟨fb, hfb, hfx⟩ := (isAffineOpen_top ((SCH).obj U)).exists_basicOpen_le
    (V := Vc) (x := ⟨yT, hnot⟩) trivial
  let D : ((SCH).obj U).Opens := ((SCH).obj U).basicOpen fb
  have hDa : IsAffineOpen D := (isAffineOpen_top _).basicOpen fb
  let Wf : ((SCH).obj W).Opens := f ⁻¹ᵁ D
  have hWfle : Wf ≤ Ai := by
    intro z hz
    by_contra hzn
    exact (hfb hz) (subset_closure ⟨z, hzn, rfl⟩)
  have hWfa : IsAffineOpen Wf := by
    have e1 : Wf = ((SCH).obj W).basicOpen (((SCH).obj W).presheaf.map (homOfLE le_top : Ai ⟶ ⊤).op
        (f.appTop.hom fb)) := by
      rw [Scheme.basicOpen_res]
      have e2 : Wf = ((SCH).obj W).basicOpen (f.appTop.hom fb) := Scheme.preimage_basicOpen _ _
      rw [← e2]
      exact (inf_eq_right.2 hWfle).symm
    rw [e1]
    exact (hA i0).basicOpen _
  -- the site objects
  let Us := Space.openSiteObject B S hS U D
  let ι : Us ⟶ U := Space.openSiteObjectHom B S hS U D
  let Ws := Space.openSiteObject B S hS W Wf
  let j : Ws ⟶ W := Space.openSiteObjectHom B S hS W Wf
  let ws : Ws ⟶ Us := siteHom (f ∣_ D) (by
    have e0 := morphismRestrict_ι f D
    change (f ∣_ D) ≫ (D.ι ≫ U.hom.hom) = Wf.ι ≫ W.hom.hom
    rw [← Category.assoc, e0, Category.assoc]
    exact congrArg (Wf.ι ≫ ·) (site_w w))
  have hws : ws ≫ ι = j ≫ w := site_hom_ext (morphismRestrict_ι f D)
  have hιO : IsOpenImmersion ((SCH).map ι) := by
    change IsOpenImmersion D.ι
    infer_instance
  have hjO : IsOpenImmersion ((SCH).map j) := by
    change IsOpenImmersion Wf.ι
    infer_instance
  haveI hιm : Mono ι := (SCH).mono_of_mono_map inferInstance
  haveI hjm : Mono j := (SCH).mono_of_mono_map inferInstance
  refine ⟨Us, Ws, yoneda.map ι ≫ g, j ≫ p, ws, hDa, hWfa, ?_, ?_, pb_mk ?_ ?_ ?_⟩
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
    exact MorphismProperty.comp_mem _ _ _ hι hg
  · have hηD : η ∈ Wf := by
      change f η ∈ D
      rw [hη]
      exact hfx
    exact ⟨(⟨η, hηD⟩ : Wf)⟩
  · change o.app (op Ws) (j ≫ p) = g.app (op Ws) (ws ≫ ι)
    rw [hws, hom_nat, hom_nat, pb_comm sq]
  · intro V a b hab
    have hab' : o.app (op V) a = g.app (op V) (b ≫ ι) := hab
    obtain ⟨l0, hl1, hl2⟩ := pb_lift sq a (b ≫ ι) hab'
    have hrg : Set.range ((SCH).map l0) ⊆ Set.range Wf.ι := by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      change f ((SCH).map l0 v) ∈ D
      have e : f ((SCH).map l0 v) = (SCH).map (l0 ≫ w) v := by
        rw [Functor.map_comp, Scheme.Hom.comp_apply]
      rw [e, hl2, Functor.map_comp, Scheme.Hom.comp_apply]
      exact ((SCH).map b v).2
    let lr := IsOpenImmersion.lift Wf.ι ((SCH).map l0) hrg
    have hlr : lr ≫ Wf.ι = (SCH).map l0 := IsOpenImmersion.lift_fac _ _ _
    let r : V ⟶ Ws := siteHom lr (by
      change lr ≫ Wf.ι ≫ W.hom.hom = _
      rw [← Category.assoc, hlr, site_w])
    have hr : r ≫ j = l0 := site_hom_ext hlr
    refine ⟨r, by rw [← Category.assoc, hr, hl1], (cancel_mono ι).1 ?_⟩
    rw [Category.assoc, hws, ← Category.assoc, hr, hl2]
  · intro V a b h1 h2
    have h2' : a ≫ ws = b ≫ ws := h2
    refine (cancel_mono j).1 (pb_ext sq ?_ ?_)
    · simpa only [Category.assoc] using h1
    · have := congrArg (· ≫ ι) h2'
      simp only [Category.assoc, hws] at this
      simpa only [Category.assoc] using this

set_option maxHeartbeats 1000000 in
/-- **Lemma 1.1, step B.** `o : O → Y` is flat over a nonempty basic open of `O`. -/
theorem exists_good_basicOpen_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    (hK : IsField (RT P))
    (hoi : ∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P N),
      o.app (op T) a = o.app (op T) b → a = b)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o) :
    ∃ h : RN P N, ¬ IsNilpotent h ∧ ∀ x : (SCH).obj (Ob P N),
      x ∈ ((SCH).obj (Ob P N)).basicOpen (spSec P _ (containsN N) h) → GoodAtQS o x := by
  classical
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  haveI hRNn : IsNoetherianRing (RN P N) := isNoetherian_RN hK
  haveI : Nontrivial (RT P) := ⟨hK.exists_pair_ne⟩
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (RN P N)
  let x0 : (SCH).obj (Ob P N) := (⟨m0, hm0.isPrime⟩ : PrimeSpectrum (RN P N))
  obtain ⟨U', W0, g, p0, w0, hU', hW0, hg, hb0, sq0⟩ := exists_chart_affine_pull hX hqc hoi x0
  haveI := hU'
  haveI := hW0
  have hp0 : Etale ((SCH).map p0) := hg.property _ _ _ sq0.flip
  haveI : Nontrivial (RT W0) := by
    haveI : Nonempty (⊤ : ((SCH).obj W0).Opens) := ⟨⟨hb0.some, trivial⟩⟩
    exact Scheme.component_nontrivial _ ⊤
  obtain ⟨C, c, hc, hr, hk⟩ := exists_closed_image w0
  haveI hCa : IsAffine ((SCH).obj C) := isAffine_of_isAffineHom ((SCH).map c)
  have hsurj : Function.Surjective ((SCH).map c).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map c)).2
  have hw0r : w0 ∈ (Subfunctor.range (yoneda.map c)).obj (op W0) := by
    rw [hr]
    exact Space.range_le_schemeTheoreticImageSubfunctor B S hS (yoneda.map w0) (op W0)
      ⟨𝟙 W0, by simp⟩
  obtain ⟨(w' : W0 ⟶ C), hw'⟩ := hw0r
  have hw'' : w' ≫ c = w0 := hw'
  let f : RT C →+* RT W0 := ((SCH).map w').appTop.hom
  have hfc : ∀ a, f (((SCH).map c).appTop.hom a) = ((SCH).map w0).appTop.hom a := by
    intro a
    rw [← hw'', Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := hsurj x
    rw [hfc] at hx
    have : a ∈ RingHom.ker ((SCH).map c).appTop.hom := by rw [hk]; exact hx
    exact this
  haveI hmw0 : Mono ((SCH).map w0) := mono_of_pull hoi sq0
  have hepi : ∀ (R : Type u) [CommRing R] (a b : RT W0 →+* R), a.comp f = b.comp f → a = b := by
    intro R _ a b hab
    let sec : R →+* Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv.hom
    have hsec : Function.Injective sec :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1
    let ma := toAffine (T := Spec (.of R)) (U := (SCH).obj W0) (sec.comp a)
    let mb := toAffine (T := Spec (.of R)) (U := (SCH).obj W0) (sec.comp b)
    have h1 : ma ≫ (SCH).map w0 = mb ≫ (SCH).map w0 := by
      rw [← hw'', Functor.map_comp, ← Category.assoc, ← Category.assoc]
      congr 1
      refine toAffine_ext ?_
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, CommRingCat.hom_comp,
        toAffine_appTop, toAffine_appTop]
      refine RingHom.ext fun x => ?_
      exact congrArg sec (congrArg (fun k => k x) hab)
    have h2 : ma = mb := (cancel_mono _).1 h1
    refine RingHom.ext fun x => hsec ?_
    have e1 : ma.appTop.hom = sec.comp a := toAffine_appTop _
    have e2 : mb.appTop.hom = sec.comp b := toAffine_appTop _
    have e3 : ma.appTop.hom = mb.appTop.hom := by rw [h2]
    have := congrArg (fun k => k x) (e1.symm.trans (e3.trans e2))
    exact this
  have hft0 : ((SCH).map w0).appTop.hom.FiniteType := by
    have : LocallyOfFinitePresentation ((SCH).map w0) := hlfp.property _ _ _ sq0
    have h2 : LocallyOfFiniteType ((SCH).map w0) := inferInstance
    exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 h2
  have hft : f.FiniteType := by
    have e2 : ((SCH).map w0).appTop.hom = f.comp ((SCH).map c).appTop.hom :=
      RingHom.ext fun a => (hfc a).symm
    rw [e2] at hft0
    exact RingHom.FiniteType.of_comp_finiteType hft0
  have hBn : IsNoetherianRing (RT W0) := by
    have hft1 : ((SCH).map p0).appTop.hom.FiniteType :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 inferInstance
    letI := ((SCH).map p0).appTop.hom.toAlgebra
    haveI : Algebra.FiniteType (RT (Ob P N)) (RT W0) := (RingHom.finiteType_algebraMap).1 hft1
    haveI : IsNoetherianRing (RT (Ob P N)) :=
      isNoetherianRing_of_surjective (RN P N) (RT (Ob P N)) (spSec P _ (containsN N))
        (spSec_bijective P _ (containsN N)).2
    exact Algebra.FiniteType.isNoetherianRing (RT (Ob P N)) (RT W0)
  haveI : Nontrivial (RT C) := f.domain_nontrivial
  obtain ⟨s, hsn, hsfl⟩ := exists_away_flat_of_epi f hinj hft hepi
  let Bs := Localization.Away (f s)
  haveI hBsn : Nontrivial Bs := by
    by_contra hcon
    haveI : Subsingleton Bs := not_nontrivial_iff_subsingleton.1 hcon
    have h0 : algebraMap (RT W0) Bs 1 = 0 := Subsingleton.elim _ _
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f s)) Bs 1).1 h0
    exact hsn ⟨n, by simpa using hc⟩
  haveI : Algebra.FiniteType (RT W0) Bs :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (f s)) Bs
  have hC : B.Contains (Spec (.of Bs)) := contains_ft (RT W0) Bs (contains_RT W0)
  let F0 : BigFppfOver B S hS := spObj W0 (algebraMap (RT W0) Bs) hC
  let j : F0 ⟶ W0 := spToT W0 _ hC
  have hjO : IsOpenImmersion ((SCH).map j) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (RT W0) Bs)) ≫
      ((SCH).obj W0).isoSpec.inv)
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (RT W0) Bs))) :=
      IsOpenImmersion.of_isLocalization (f s)
    infer_instance
  have hq0 : Flat ((SCH).map (j ≫ w')) := by
    refine (HasRingHomProperty.iff_of_isAffine (P := @Flat)).2 ?_
    have e4 : ((SCH).map (j ≫ w')).appTop.hom = (spSec W0 _ hC).comp
        ((algebraMap (RT W0) Bs).comp f) := by
      refine RingHom.ext fun a => ?_
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]
      change ((SCH).map j).appTop.hom (f a) = _
      rw [spToT_appTop]
      rfl
    rw [e4]
    exact RingHom.Flat.comp hsfl (RingHom.Flat.of_bijective (spSec_bijective W0 _ hC))
  -- the open image in `O`
  let mm : (SCH).obj F0 ⟶ (SCH).obj (Ob P N) := (SCH).map (j ≫ p0)
  have hmE : Etale mm := by
    change Etale ((SCH).map (j ≫ p0))
    rw [Functor.map_comp]
    infer_instance
  let D1 : ((SCH).obj (Ob P N)).Opens := ⟨Set.range mm, mm.isOpenMap.isOpen_range⟩
  obtain ⟨m1, hm1⟩ := Ideal.exists_maximal Bs
  let z1 : (SCH).obj F0 := (⟨m1, hm1.isPrime⟩ : PrimeSpectrum Bs)
  have hx1 : mm z1 ∈ D1 := ⟨z1, rfl⟩
  obtain ⟨fb, hfb, hfx⟩ := (isAffineOpen_top ((SCH).obj (Ob P N))).exists_basicOpen_le ⟨mm z1, hx1⟩ trivial
  obtain ⟨h, hh⟩ := (spSec_bijective P _ (containsN N)).2 fb
  have hfb' : fb = spSec P _ (containsN N) h := hh.symm
  subst hfb'
  refine ⟨h, orbit_not_nil h (x := mm z1) hfx, ?_⟩
  intro x hx T W _ g' hg' p w sq v hv
  have hzz : x ∈ Set.range mm := hfb hx
  obtain ⟨z, hz⟩ := id hzz
  -- `E₂ = T ×_X U'`
  obtain ⟨E2, e₂, e₁, sqT⟩ := exists_pull_qs hX g g'
  have he₁ : Etale ((SCH).map e₁) := hg.property _ _ _ sqT
  have hmemY : e₂ ∈ (Subfunctor.range (yoneda.map c)).obj (op E2) := by
    rw [hr, ← preimage_image_chart_qs hX hqc hg sq0]
    change g.app (op E2) e₂ ∈ (imS o).obj (op E2)
    rw [pb_comm sqT]
    have : g'.app (op E2) e₁ = X.map e₁.op (g'.app (op T) (𝟙 T)) := by
      rw [← hom_nat]; simp
    rw [this]
    exact (imS o).map _ hg'
  obtain ⟨(q : E2 ⟶ C), hq⟩ := hmemY
  have hq' : q ≫ c = e₂ := hq
  haveI hcm : Mono c := (SCH).mono_of_mono_map inferInstance
  -- `F = W ×_O F₀`
  let F := pullback p (j ≫ p0)
  let A1 : F ⟶ W := pullback.fst p (j ≫ p0)
  let A2 : F ⟶ F0 := pullback.snd p (j ≫ p0)
  have hA : IsPullback A1 A2 p (j ≫ p0) := IsPullback.of_hasPullback _ _
  have hAS := hA.map (SCH)
  have hA1 : Flat ((SCH).map A1) := by
    have : Etale ((SCH).map A1) := MorphismProperty.of_isPullback (P := @Etale) hAS.flip hmE
    infer_instance
  have hcomm0 : o.app (op F) (A2 ≫ j ≫ p0) = g'.app (op F) (A1 ≫ w) := by
    rw [← hA.w]
    rw [hom_nat, hom_nat, pb_comm sq]
  have hg0 : ∀ {V : BigFppfOver B S hS} (r : V ⟶ W0), o.app (op V) (r ≫ p0) = g.app (op V) (r ≫ w0) := by
    intro V r
    rw [hom_nat, hom_nat, pb_comm sq0]
  obtain ⟨r, hr2, hr1⟩ := pb_lift sqT (A2 ≫ j ≫ w0) (A1 ≫ w) (by
    rw [← hcomm0, ← Category.assoc, ← Category.assoc, ← hg0, Category.assoc])
  have hsqY : IsPullback (yoneda.map A2) (yoneda.map r) (yoneda.map (j ≫ w')) (yoneda.map q) := by
    refine pb_mk ?_ ?_ ?_
    · change A2 ≫ j ≫ w' = r ≫ q
      refine (cancel_mono c).1 ?_
      simp only [Category.assoc]
      rw [hw'', hq', hr2]
    · intro V a b hab
      have hab' : a ≫ j ≫ w' = b ≫ q := hab
      have e5 : a ≫ j ≫ w0 = b ≫ e₂ := by
        rw [← hw'', ← hq']
        simpa using congrArg (· ≫ c) hab'
      have e6 : o.app (op V) (a ≫ j ≫ p0) = g'.app (op V) (b ≫ e₁) := by
        rw [← Category.assoc, hg0, Category.assoc, e5, hom_nat, hom_nat, pb_comm sqT]
      obtain ⟨k, hk1, hk2⟩ := pb_lift sq _ _ e6
      refine ⟨hA.lift k a hk1, hA.lift_snd _ _ _, pb_ext sqT ?_ ?_⟩
      · rw [Category.assoc, hr2, ← Category.assoc, hA.lift_snd, e5]
      · rw [Category.assoc, hr1, ← Category.assoc, hA.lift_fst, hk2]
    · intro V l l' h1 h2
      have h1' : l ≫ A2 = l' ≫ A2 := h1
      have h2' : l ≫ r = l' ≫ r := h2
      refine hA.hom_ext (pb_ext sq ?_ ?_) h1'
      · simp only [Category.assoc]
        rw [hA.w, ← Category.assoc, h1', Category.assoc]
      · have := congrArg (· ≫ e₁) h2'
        simpa [hr1] using this
  have hsqS : IsPullback A2 r (j ≫ w') q :=
    IsPullback.of_map yoneda (Functor.Faithful.map_injective (F := yoneda) (by
      simpa using hsqY.w)) (by simpa using hsqY)
  have hSq := hsqS.map (SCH)
  have hrF : Flat ((SCH).map r) := MorphismProperty.of_isPullback (P := @Flat) hSq hq0
  have hcompF : Flat ((SCH).map A1 ≫ (SCH).map w) := by
    rw [← Functor.map_comp, ← hr1, Functor.map_comp]
    infer_instance
  -- the point over `v`
  have hpz : (SCH).map p v = (SCH).map (j ≫ p0) z := by rw [hv]; exact hz.symm
  obtain ⟨φ0, hφ1, -⟩ : ∃ y : (SCH).obj F, (SCH).map A1 y = v ∧ (SCH).map A2 y = z := by
    obtain ⟨y, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback v z hpz
    refine ⟨hAS.isoPullback.inv y, ?_, ?_⟩
    · rw [← h1, ← Scheme.Hom.comp_apply, hAS.isoPullback_inv_fst]
    · rw [← h2, ← Scheme.Hom.comp_apply, hAS.isoPullback_inv_snd]
  have := flat_stalk_descend ((SCH).map A1) ((SCH).map w) φ0 (Flat.stalkMap _ _) (Flat.stalkMap _ _)
  rwa [hφ1] at this

end AlgMag.ChartQSL11
