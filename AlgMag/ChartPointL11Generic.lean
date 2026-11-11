/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointL11Flat

/-!
# Generic flatness of the orbit (Lemma 1.1 of the chart-lemma proof, step B)
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]

variable [IsAffine S] {o : yoneda.obj (Ob P N) ⟶ X}

lemma isNoetherian_RN (hK : IsField (RT P)) : IsNoetherianRing (RN P N) := by
  letI : Field (RT P) := hK.toField
  haveI : Algebra.FiniteType (RT P) (RN P N) := AddMonoidAlgebra.finiteType_of_fg _ _
  exact Algebra.FiniteType.isNoetherianRing (RT P) (RN P N)

/-- The pullback of the orbit along any point is a monomorphism of schemes. -/
lemma mono_of_pull (hoi : ∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P N),
      o.app (op T) a = o.app (op T) b → a = b)
    {T W : BigFppfOver B S hS} {g : yoneda.obj T ⟶ X} {p : W ⟶ Ob P N} {w : W ⟶ T}
    (sq : IsPullback (yoneda.map p) (yoneda.map w) o g) : Mono ((SCH).map w) := by
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  have hm : Mono w := ⟨fun {V} l l' h => pb_ext sq (hoi _ _ (by
    rw [hom_nat, hom_nat, pb_comm sq, ← hom_nat, ← hom_nat, h])) h⟩
  infer_instance

lemma not_nil_of_mem_basicOpen {Z : Scheme.{u}} {r : Γ(Z, ⊤)} {x : Z} (hx : x ∈ Z.basicOpen r) :
    ¬ IsNilpotent r := fun hn => by
  have hu := (Z.mem_basicOpen_top r x).1 hx
  exact (hn.map (Z.presheaf.germ ⊤ x trivial).hom).not_isUnit hu

lemma orbit_not_nil (h : RN P N) {x : (SCH).obj (Ob P N)}
    (hx : x ∈ ((SCH).obj (Ob P N)).basicOpen (spSec P AddMonoidAlgebra.singleZeroRingHom (containsN N) h)) :
    ¬ IsNilpotent h := by
  rintro ⟨n, hn⟩
  refine not_nil_of_mem_basicOpen hx ⟨n, ?_⟩
  rw [← map_pow, hn, map_zero]

set_option maxHeartbeats 1000000 in
/-- **Lemma 1.1, step B.** `o : O → Y` is flat over a nonempty basic open of `O`. -/
theorem exists_good_basicOpen (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    (hK : IsField (RT P))
    (hoi : ∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P N),
      o.app (op T) a = o.app (op T) b → a = b)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o) :
    ∃ h : RN P N, ¬ IsNilpotent h ∧ ∀ x : (SCH).obj (Ob P N),
      x ∈ ((SCH).obj (Ob P N)).basicOpen (spSec P _ (containsN N) h) → GoodAt o x := by
  classical
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  haveI hRNn : IsNoetherianRing (RN P N) := isNoetherian_RN hK
  haveI : Nontrivial (RT P) := ⟨hK.exists_pair_ne⟩
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (RN P N)
  let x0 : (SCH).obj (Ob P N) := (⟨m0, hm0.isPrime⟩ : PrimeSpectrum (RN P N))
  obtain ⟨T₁, U', e, y₁, g, u, hU', hE, hy, hg, hu⟩ := exists_affine_chart hX o x0
  obtain ⟨W0, p0, w0, hw0, sq0⟩ := exists_pull hsep o g
  haveI hW0 : IsAffine ((SCH).obj W0) := isAffine_of_isAffineHom ((SCH).map w0)
  have hp0 : Etale ((SCH).map p0) := hg.property _ _ _ sq0.flip
  obtain ⟨l, hl1, -⟩ := pb_lift sq0 e u hu.symm
  have hb0 : Nonempty ((SCH).obj W0) := ⟨(SCH).map l y₁⟩
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
  intro x hx T W _ _ g' hg' p w sq v hv
  have hzz : x ∈ Set.range mm := hfb hx
  obtain ⟨z, hz⟩ := id hzz
  -- `E₂ = T ×_X U'`
  obtain ⟨E2, e₂, e₁, -, sqT⟩ := exists_pull hsep g g'
  have he₁ : Etale ((SCH).map e₁) := hg.property _ _ _ sqT
  have hmemY : e₂ ∈ (Subfunctor.range (yoneda.map c)).obj (op E2) := by
    rw [hr, ← preimage_image_chart hX hsep hg sq0]
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

end AlgMag.ChartPoint
