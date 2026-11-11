/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11Schemes

/-!
# Formal étaleness of attractors and smoothness of `X^N → X^F`, for schemes

Mayeux, *Algebraic Magnetism*, §11, schemes only.

* `isFormallyUnramified_attractorMap_scheme`: **Proposition 11.3**.
* `isFormallyEtale_attractorMap_scheme`: **Proposition 11.5**.
* `milnorPushout`: **Fact 11.8** in schemes, for `T` affine.
* `isFormallySmooth_faceMap_scheme`: **Proposition 11.7**.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.SmoothSchemes

open AlgMag.GB AlgMag.Lifts

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

lemma thick_of_ring {R R₀ : Type u} [CommRing R] [CommRing R₀] (φ : R →+* R₀)
    (hs : Function.Surjective φ) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) :
    Stacks.Thickenings.IsFirstOrderThickening (Spec.map (CommRingCat.ofHom φ)) :=
  Stacks.Smooth.isFirstOrderThickening_specMap _ hs (by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx z hz
    exact hq x z hx hz)

/-- **Proposition 11.3**, schemes only. -/
theorem isFormallyUnramified_attractorMap_scheme {X Y : Over S}
    {aX : AAction (overO S) M (yoneda.obj X)} {aY : AAction (overO S) M (yoneda.obj Y)}
    (g : X ⟶ Y) (hg : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X),
      sm aX h x ≫ g = sm aY h (x ≫ g)) [FormallyUnramified g.left] :
    FormallyUnramifiedFor (fun {_ _} i => IsAffineThick i) (attractorMap (eqHom g hg) N) := by
  intro T₀ T i hi x y h₀ h₁
  have := hi.affine₀
  have := hi.affine
  let φ := AddMonoidAlgebra.mapRingHom N i.left.appTop.hom
  let t := magnetπ N T.left ≫ T.hom
  have hs₀ : magnetπ N T₀.left ≫ T₀.hom = sp φ ≫ t := π_thick N i
  let U := specUP N T t rfl
  let U₀ := specUP N T₀ (sp φ ≫ t) hs₀
  have hj : U.lift (U₀.π ≫ i) U₀.u = (ovHom φ rfl : Ov (sp φ ≫ t) ⟶ Ov t) := by
    symm
    refine U.uniq _ _ _ (Over.OverMorphism.ext (π_sq N i).symm) (MonoidHom.ext fun n => ?_)
    refine (sp_inv φ _).trans (congrArg _ ?_)
    refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
    rw [map_one]
  have e₀ : (ovHom φ rfl : Ov (sp φ ≫ t) ⟶ Ov t) ≫ x.app U.π U.u =
      (ovHom φ rfl : Ov (sp φ ≫ t) ⟶ Ov t) ≫ y.app U.π U.u := by
    rw [← hj]
    have ex := x.app_eq_of_universal U (U₀.π ≫ i) U₀.u
    have ey := y.app_eq_of_universal U (U₀.π ≫ i) U₀.u
    refine ex.symm.trans (Eq.trans ?_ ey)
    exact congrArg (fun z : AttractorPt aX N T₀ => z.app U₀.π U₀.u) h₀
  have e₁ : x.app U.π U.u ≫ g = y.app U.π U.u ≫ g :=
    congrArg (fun z : AttractorPt aY N T => z.app U.π U.u) h₁
  have key : x.app U.π U.u = y.app U.π U.u :=
    Over.OverMorphism.ext (Stacks.Smooth.lift_unique g.left
      (thick_of_ring φ (mapRingHom_surjective _ hi.surjective)
        (magnetAlgebra_mul_eq_zero _ hi.sq_zero))
      (congrArg (fun k => k.left) e₁) rfl rfl (congrArg (fun k => k.left) e₀).symm)
  exact (attractorPtEquivOfUniversal (act := aX) U).injective (Subtype.ext key)

/-- **Proposition 11.5**, schemes only: `g` étale gives `g^N` formally smooth and formally
unramified as a transformation of functors. -/
theorem isFormallyEtale_attractorMap_scheme {X Y : Over S}
    {aX : AAction (overO S) M (yoneda.obj X)} {aY : AAction (overO S) M (yoneda.obj Y)}
    (g : X ⟶ Y) (hg : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X),
      sm aX h x ≫ g = sm aY h (x ≫ g)) [Etale g.left] :
    FormallySmoothFor (fun {_ _} i => IsAffineThick i) (attractorMap (eqHom g hg) N) ∧
      FormallyUnramifiedFor (fun {_ _} i => IsAffineThick i) (attractorMap (eqHom g hg) N) :=
  ⟨isFormallySmooth_attractorMap_scheme N g hg, isFormallyUnramified_attractorMap_scheme N g hg⟩

section Face

variable {F : AddSubmonoid M} (hF : IsFace F N) [DecidableEq M]

section Rings

variable {D D₁ : Type u} [CommRing D] [CommRing D₁] (ι : D →+* D₁)

/-- The Milnor square of the push-out ring (Fact 11.8). -/
noncomputable def pFst : pushoutRing hF ι →+* AddMonoidAlgebra D F :=
  (RingHom.fst _ _).comp (pushoutRing hF ι).subtype

noncomputable def pSnd : pushoutRing hF ι →+* AddMonoidAlgebra D₁ N :=
  (RingHom.snd _ _).comp (pushoutRing hF ι).subtype

theorem milnor_pushout (hι : Function.Surjective ι) :
    MilnorData (pFst N hF ι) (pSnd N hF ι) (AddMonoidAlgebra.mapRingHom F ι) (faceRingHom hF D₁) where
  comm p := p.2
  surj := mapRingHom_surjective ι hι
  inj z h₁ h₂ := Subtype.ext (Prod.ext h₁ h₂)
  ex x y h := ⟨⟨(x, y), h⟩, rfl, rfl⟩

lemma pSnd_surjective (hι : Function.Surjective ι) : Function.Surjective (pSnd N hF ι) := fun y => by
  obtain ⟨x, hx⟩ := mapRingHom_surjective (L := F) ι hι (faceRingHom hF D₁ y)
  exact ⟨⟨(x, y), hx⟩, rfl⟩

lemma pFst_ker (y : AddMonoidAlgebra D F) (hy : AddMonoidAlgebra.mapRingHom F ι y = 0) :
    ∃ z, pFst N hF ι z = y ∧ pSnd N hF ι z = 0 :=
  ⟨⟨(y, 0), by
    change AddMonoidAlgebra.mapRingHom F ι y = faceRingHom hF D₁ 0
    rw [hy, map_zero]⟩, rfl, rfl⟩

/-- **Fact 11.8**, schemes only: `Spec` of the push-out ring is the push-out in schemes of
`𝔸(F)_{T₀} → 𝔸(F)_T` and `𝔸(F)_{T₀} → 𝔸(N)_{T₀}`, for `T` affine. -/
theorem milnorPushout (hι : Function.Surjective ι) {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of (AddMonoidAlgebra D F)) ⟶ Y)
    (g : Spec (CommRingCat.of (AddMonoidAlgebra D₁ N)) ⟶ Y)
    (h : sp (AddMonoidAlgebra.mapRingHom F ι) ≫ f = sp (faceRingHom hF D₁) ≫ g) :
    ∃! k : Spec (CommRingCat.of (pushoutRing hF ι)) ⟶ Y, sp (pFst N hF ι) ≫ k = f ∧
      sp (pSnd N hF ι) ≫ k = g :=
  milnor_desc (milnor_pushout N hF ι hι) (pSnd_surjective N hF ι hι)
    (fun y hy => pFst_ker N hF ι y hy) f g h

/-- A Milnor square stays one after applying `(-)[M]`. -/
theorem milnor_map {R₁ A₀ C₀ B₀ : Type u} [CommRing R₁] [CommRing A₀] [CommRing C₀] [CommRing B₀]
    {p : R₁ →+* A₀} {q : R₁ →+* C₀} {i : A₀ →+* B₀} {j : C₀ →+* B₀} (H : MilnorData p q i j) :
    MilnorData (AddMonoidAlgebra.mapRingHom M p) (AddMonoidAlgebra.mapRingHom M q)
      (AddMonoidAlgebra.mapRingHom M i) (AddMonoidAlgebra.mapRingHom M j) where
  comm z := by
    rw [map_map_apply i p (i.comp p) (fun _ => rfl),
      map_map_apply j q (i.comp p) (fun a => (H.comm a).symm)]
  surj := mapRingHom_surjective i H.surj
  inj z h₁ h₂ := by
    ext m
    refine H.inj _ ?_ ?_
    · simpa using congrArg (fun w => w.coeff m) h₁
    · simpa using congrArg (fun w => w.coeff m) h₂
  ex x y h := by
    classical
    have hc : ∀ m, i (x.coeff m) = j (y.coeff m) := fun m => by
      simpa using congrArg (fun w => w.coeff m) h
    choose z hz₁ hz₂ using fun m => H.ex _ _ (hc m)
    have h0 : ∀ m, m ∉ x.coeff.support ∪ y.coeff.support → x.coeff m = 0 ∧ y.coeff m = 0 := by
      intro m hm
      simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hm
      exact hm
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (x.coeff.support ∪ y.coeff.support)
      (fun m => if m ∈ x.coeff.support ∪ y.coeff.support then z m else 0) (fun m hm => by
        by_contra hc
        exact hm (if_neg hc))), ?_, ?_⟩
    · ext m
      simp only [AddMonoidAlgebra.coeff_mapRingHom]
      by_cases hm : m ∈ x.coeff.support ∪ y.coeff.support
      · change p (if m ∈ x.coeff.support ∪ y.coeff.support then z m else 0) = x.coeff m
        rw [if_pos hm, hz₁]
      · change p (if m ∈ x.coeff.support ∪ y.coeff.support then z m else 0) = x.coeff m
        rw [if_neg hm, map_zero, (h0 m hm).1]
    · ext m
      simp only [AddMonoidAlgebra.coeff_mapRingHom]
      by_cases hm : m ∈ x.coeff.support ∪ y.coeff.support
      · change q (if m ∈ x.coeff.support ∪ y.coeff.support then z m else 0) = y.coeff m
        rw [if_pos hm, hz₂]
      · change q (if m ∈ x.coeff.support ∪ y.coeff.support then z m else 0) = y.coeff m
        rw [if_neg hm, map_zero, (h0 m hm).2]

lemma coact_face (w : AddMonoidAlgebra D N) :
    AddMonoidAlgebra.mapRingHom M (faceRingHom hF D) (coactN (M := M) N D w) =
      coactN (M := M) F D (faceRingHom hF D w) := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n r =>
    by_cases hn : (n : M) ∈ F
    · rw [faceRingHom_single_pos hF n hn, coactN_single, coactN_single,
        AddMonoidAlgebra.mapRingHom_single, faceRingHom_single_pos hF n hn]
    · rw [faceRingHom_single_neg hF n hn, coactN_single, AddMonoidAlgebra.mapRingHom_single,
        faceRingHom_single_neg hF n hn, map_zero, AddMonoidAlgebra.single_zero]

lemma pushout_single_zero (n : N) (c : D) (h₁ : ι c = 0) (h₂ : (n : M) ∈ F → c = 0) :
    pushoutMap hF ι (AddMonoidAlgebra.single n c) = 0 := by
  have e₁ : faceRingHom hF D (AddMonoidAlgebra.single n c) = 0 := by
    by_cases hn : (n : M) ∈ F
    · rw [h₂ hn, AddMonoidAlgebra.single_zero, map_zero]
    · exact faceRingHom_single_neg hF n hn c
  have e₂ : AddMonoidAlgebra.mapRingHom N ι (AddMonoidAlgebra.single n c) = 0 := by
    rw [AddMonoidAlgebra.mapRingHom_single, h₁, AddMonoidAlgebra.single_zero]
  exact Subtype.ext (Prod.ext e₁ e₂)

lemma coact_ker (w : AddMonoidAlgebra D N) (hw : pushoutMap hF ι w = 0) :
    AddMonoidAlgebra.mapRingHom M (pushoutMap hF ι) (coactN (M := M) N D w) = 0 := by
  have hc := (pushoutMap_eq_zero_iff hF ι w).1 hw
  have ew : w = w.coeff.sum AddMonoidAlgebra.single := (AddMonoidAlgebra.sum_coeff_single w).symm
  rw [ew, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [coactN_single, AddMonoidAlgebra.mapRingHom_single,
    pushout_single_zero N hF ι n _ (hc n).1 (hc n).2, AddMonoidAlgebra.single_zero]

/-- The coaction on the push-out ring: the one induced from `D[N]` (Fact 11.8). -/
noncomputable def coactP (hι : Function.Surjective ι) :
    pushoutRing hF ι →+* AddMonoidAlgebra (pushoutRing hF ι) M :=
  RingHom.liftOfSurjective (pushoutMap hF ι) (pushoutMap_surjective hF ι hι)
    ⟨(AddMonoidAlgebra.mapRingHom M (pushoutMap hF ι)).comp (coactN (M := M) N D),
      fun w hw => coact_ker N hF ι w hw⟩

lemma coactP_π (hι : Function.Surjective ι) (w : AddMonoidAlgebra D N) :
    coactP (M := M) N hF ι hι (pushoutMap hF ι w) =
      AddMonoidAlgebra.mapRingHom M (pushoutMap hF ι) (coactN (M := M) N D w) :=
  RingHom.liftOfRightInverse_comp_apply (pushoutMap hF ι)
    (Function.surjInv (pushoutMap_surjective hF ι hι)) _ _ w

lemma coactP_fst (hι : Function.Surjective ι) (p : pushoutRing hF ι) :
    AddMonoidAlgebra.mapRingHom M (pFst N hF ι) (coactP (M := M) N hF ι hι p) =
      coactN (M := M) F D (pFst N hF ι p) := by
  obtain ⟨w, rfl⟩ := pushoutMap_surjective hF ι hι p
  rw [coactP_π, map_map_apply (pFst N hF ι) (pushoutMap hF ι) (faceRingHom hF D) (fun _ => rfl)]
  exact coact_face N hF w

lemma coactP_snd (hι : Function.Surjective ι) (p : pushoutRing hF ι) :
    AddMonoidAlgebra.mapRingHom M (pSnd N hF ι) (coactP (M := M) N hF ι hι p) =
      coactN (M := M) N D₁ (pSnd N hF ι p) := by
  obtain ⟨w, rfl⟩ := pushoutMap_surjective hF ι hι p
  rw [coactP_π, map_map_apply (pSnd N hF ι) (pushoutMap hF ι) (AddMonoidAlgebra.mapRingHom N ι)
    (fun _ => rfl)]
  exact coactN_map N ι w

end Rings

lemma face_π (T : Scheme.{u}) [IsAffine T] :
    sp (faceRingHom hF Γ(T, ⊤)) ≫ magnetπ N T = magnetπ F T := by
  let sz : Γ(T, ⊤) →+* AddMonoidAlgebra Γ(T, ⊤) N := AddMonoidAlgebra.singleZeroRingHom
  let sf : Γ(T, ⊤) →+* AddMonoidAlgebra Γ(T, ⊤) F := AddMonoidAlgebra.singleZeroRingHom
  have e : (faceRingHom hF Γ(T, ⊤)).comp sz = sf := RingHom.ext fun r =>
    faceRingHom_single_pos hF 0 F.zero_mem r
  have : sp (faceRingHom hF Γ(T, ⊤)) ≫ sp sz = sp sf := by rw [← sp_comp, e]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ T.isoSpec.inv) this)

lemma tri3 {C : Type*} [Category C] {P Q R W V E : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ W}
    {d : P ⟶ E} {e : E ⟶ W} (h : a ≫ b ≫ c = d ≫ e) (z : W ⟶ V) : a ≫ b ≫ c ≫ z = d ≫ e ≫ z := by
  calc a ≫ b ≫ c ≫ z = (a ≫ b ≫ c) ≫ z := by simp only [Category.assoc]
    _ = (d ≫ e) ≫ z := by rw [h]
    _ = d ≫ e ≫ z := Category.assoc _ _ _

/-- Trivial action on `S` itself. -/
def trivAction : AAction (overO S) M (yoneda.obj (Over.mk (𝟙 S))) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  map_smul _ _ _ := rfl

lemma term_ext {T : Over S} (x y : T ⟶ Over.mk (𝟙 S)) : x = y := by
  refine Over.OverMorphism.ext ?_
  have h₁ : x.left = T.hom := by simpa using Over.w x
  have h₂ : y.left = T.hom := by simpa using Over.w y
  exact h₁.trans h₂.symm

lemma lift_face (T : Over S) [IsAffine T.left] (s : Spec (magnetRing N T.left) ⟶ S)
    (hs : magnetπ N T.left ≫ T.hom = s) (s₁ : Spec (magnetRing F T.left) ⟶ S)
    (hs₁ : magnetπ F T.left ≫ T.hom = s₁) (h : sp (faceRingHom hF Γ(T.left, ⊤)) ≫ s = s₁) :
    (specUP N T s hs).lift (specUP F T s₁ hs₁).π (APt.faceExt hF (specUP F T s₁ hs₁).u) =
      (ovHom (faceRingHom hF Γ(T.left, ⊤)) h : Ov s₁ ⟶ Ov s) := by
  symm
  have h1 : (ovHom (faceRingHom hF Γ(T.left, ⊤)) h : Ov s₁ ⟶ Ov s) ≫ (specUP N T s hs).π =
      (specUP F T s₁ hs₁).π := Over.OverMorphism.ext (face_π N hF T.left)
  refine (specUP N T s hs).uniq _ _ _ h1 ?_
  refine MonoidHom.ext fun n => ?_
  refine (sp_inv _ _).trans ?_
  by_cases hn : ((Multiplicative.toAdd n : N) : M) ∈ F
  · rw [faceRingHom_single_pos hF _ hn]
    exact (APt.faceExt_pos (𝒪 := overO S) (U := op (Ov s₁)) hF (specUP F T s₁ hs₁).u hn).symm
  · rw [faceRingHom_single_neg hF _ hn, map_zero]
    exact (APt.faceExt_neg (𝒪 := overO S) (U := op (Ov s₁)) hF (specUP F T s₁ hs₁).u hn).symm

omit [DecidableEq M] in
set_option maxHeartbeats 3000000 in
/-- **Proposition 11.7**, schemes only: if `X → S` is smooth and `F` is a face of `N`, then
`X^N → X^F` is formally smooth as a transformation of functors. -/
theorem isFormallySmooth_faceMap_scheme {X : Over S} (aX : AAction (overO S) M (yoneda.obj X))
    [Smooth X.hom] : FormallySmoothFor (fun {_ _} i => IsAffineThick i) (faceMap aX hF) := by
  classical
  intro T₀ T i hi x₀ y hc
  have := hi.affine₀
  have := hi.affine
  let ι := i.left.appTop.hom
  have hι : Function.Surjective ι := hi.surjective
  let t := magnetπ N T.left ≫ T.hom
  let π₁ := pushoutMap hF ι
  have hπs : Function.Surjective π₁ := pushoutMap_surjective hF ι hι
  have hπq : ∀ x y, π₁ x = 0 → π₁ y = 0 → x * y = 0 := pushoutMap_mul_eq_zero hF ι hi.sq_zero
  let sF := sp (faceRingHom hF Γ(T.left, ⊤)) ≫ t
  have hsF : magnetπ F T.left ≫ T.hom = sF :=
    ((congrArg (· ≫ T.hom) (face_π N hF T.left)).symm.trans (Category.assoc _ _ _))
  let s₀ := sp (AddMonoidAlgebra.mapRingHom N ι) ≫ t
  have hs₀ : magnetπ N T₀.left ≫ T₀.hom = s₀ := π_thick N i
  let sF₀ := sp (AddMonoidAlgebra.mapRingHom F ι) ≫ sF
  have hsF₀ : magnetπ F T₀.left ≫ T₀.hom = sF₀ :=
    (π_thick F i).trans (congrArg (fun z => sp (AddMonoidAlgebra.mapRingHom F ι) ≫ z) hsF)
  let U := specUP N T t rfl
  let UF := specUP F T sF hsF
  let U₀ := specUP N T₀ s₀ hs₀
  let UF₀ := specUP F T₀ sF₀ hsF₀
  let yF : UF.P ⟶ X := y.app UF.π UF.u
  let x₀U : U₀.P ⟶ X := x₀.app U₀.π U₀.u
  have hface₀ : sp (faceRingHom hF Γ(T₀.left, ⊤)) ≫ s₀ = sF₀ :=
    tri (sp_sq (RingHom.ext fun w => face_comm hF ι w)) t
  have hmF : (ovHom (AddMonoidAlgebra.mapRingHom F ι) rfl : Ov sF₀ ⟶ Ov sF) =
      UF.lift (UF₀.π ≫ i) UF₀.u := by
    refine UF.uniq _ _ _ (Over.OverMorphism.ext (π_sq F i).symm) (MonoidHom.ext fun n => ?_)
    refine (sp_inv _ _).trans (congrArg _ ?_)
    refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
    rw [map_one]
  have hcomp : sp (AddMonoidAlgebra.mapRingHom F ι) ≫ yF.left =
      sp (faceRingHom hF Γ(T₀.left, ⊤)) ≫ x₀U.left := by
    have e := congrArg (fun z : AttractorPt aX F T₀ => z.app UF₀.π UF₀.u) hc
    have e₁ : x₀.app UF₀.π (APt.faceExt hF UF₀.u) = (ovHom (faceRingHom hF Γ(T₀.left, ⊤)) hface₀ :
        Ov sF₀ ⟶ Ov s₀) ≫ x₀U := by
      refine (x₀.app_eq_of_universal U₀ _ _).trans ?_
      exact congrArg (fun z : Ov sF₀ ⟶ Ov s₀ => z ≫ x₀U) (lift_face N hF T₀ s₀ hs₀ sF₀ hsF₀ hface₀)
    have e₂ : y.app (UF₀.π ≫ i) UF₀.u = (ovHom (AddMonoidAlgebra.mapRingHom F ι) rfl :
        Ov sF₀ ⟶ Ov sF) ≫ yF := by
      refine (y.app_eq_of_universal UF _ _).trans ?_
      exact congrArg (fun z : Ov sF₀ ⟶ Ov sF => z ≫ yF) hmF.symm
    have e₃ : (ovHom (faceRingHom hF Γ(T₀.left, ⊤)) hface₀ : Ov sF₀ ⟶ Ov s₀) ≫ x₀U =
        (ovHom (AddMonoidAlgebra.mapRingHom F ι) rfl : Ov sF₀ ⟶ Ov sF) ≫ yF :=
      e₁.symm.trans (e.trans e₂)
    exact (congrArg (fun k => k.left) e₃).symm
  let Pu := pushoutRing hF ι
  let H := milnor_pushout N hF ι hι
  obtain ⟨k, ⟨hk1, hk2⟩, -⟩ := milnorPushout N hF ι hι yF.left x₀U.left hcomp
  have hpf : (pFst N hF ι).comp π₁ = faceRingHom hF Γ(T.left, ⊤) := rfl
  have hps : (pSnd N hF ι).comp π₁ = AddMonoidAlgebra.mapRingHom N ι := rfl
  have hspf : sp (pFst N hF ι) ≫ sp π₁ = sp (faceRingHom hF Γ(T.left, ⊤)) := by rw [← sp_comp, hpf]
  have hsps : sp (pSnd N hF ι) ≫ sp π₁ = sp (AddMonoidAlgebra.mapRingHom N ι) := by rw [← sp_comp, hps]
  have hkw : k ≫ X.hom = sp π₁ ≫ t := by
    refine milnor_ext H ?_ ?_
    · rw [← Category.assoc, hk1]
      exact (Over.w yF).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) hspf)).symm
    · rw [← Category.assoc, hk2]
      exact (Over.w x₀U).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) hsps)).symm
  let a : Ov (sp π₁ ≫ t) ⟶ X := Over.homMk k hkw
  have hpFs : sp (pFst N hF ι) ≫ sp π₁ ≫ t = sF :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) hspf)
  have hpSs : sp (pSnd N hF ι) ≫ sp π₁ ≫ t = s₀ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) hsps)
  let pF : Ov sF ⟶ Ov (sp π₁ ≫ t) := ovHom (pFst N hF ι) hpFs
  let pS : Ov s₀ ⟶ Ov (sp π₁ ≫ t) := ovHom (pSnd N hF ι) hpSs
  have hpFa : pF ≫ a = yF := Over.OverMorphism.ext hk1
  have hpSa : pS ≫ a = x₀U := Over.OverMorphism.ext hk2
  let b : Ov t ⟶ Over.mk (𝟙 S) := Over.homMk t (Category.comp_id t)
  obtain ⟨α₁, hα₁, hα₂⟩ := Stacks.Smooth.formallySmoothScheme_of_smooth X.hom
    (T := Spec (CommRingCat.of Pu)) (T' := Spec (CommRingCat.of (RR N T)))
    inferInstance inferInstance (Spec.map (CommRingCat.ofHom π₁)) (thick_of_ring π₁ hπs hπq) k t hkw
  let α : Ov t ⟶ X := Over.homMk α₁ hα₁
  let ρ := coactN (M := M) N Γ(T.left, ⊤)
  let ρ₀ := coactP (M := M) N hF ι hι
  have hρt : sp ρ ≫ t = sp (cst _ M) ≫ t := hρs N T t rfl
  have hρφ : ∀ w, AddMonoidAlgebra.mapRingHom M π₁ (ρ w) = ρ₀ (π₁ w) := fun w =>
    (coactP_π N hF ι hι w).symm
  have h₀c : sp (cst Pu M) ≫ sp π₁ ≫ t = sp (AddMonoidAlgebra.mapRingHom M π₁) ≫ sp (cst _ M) ≫ t :=
    tri (sp_sq (RingHom.ext fun w => (map_cst π₁ w).symm)) t
  have h₀ρ : sp ρ₀ ≫ sp π₁ ≫ t = sp (AddMonoidAlgebra.mapRingHom M π₁) ≫ sp (cst _ M) ≫ t := by
    rw [← hρt]
    exact tri (sp_sq (RingHom.ext fun w => (hρφ w).symm)) t
  let HM := milnor_map (M := M) H
  let s₁ := sp (AddMonoidAlgebra.mapRingHom M π₁) ≫ sp (cst (RR N T) M) ≫ t
  let sF₁ := sp (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) ≫ s₁
  let s₀₁ := sp (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) ≫ s₁
  have e1F : sp (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) ≫ sp (AddMonoidAlgebra.mapRingHom M π₁) ≫
      sp (cst (RR N T) M) = sp (cst _ M) ≫ sp (faceRingHom hF Γ(T.left, ⊤)) := by
    rw [← Category.assoc, sp_sq (g₃ := AddMonoidAlgebra.mapRingHom M (faceRingHom hF Γ(T.left, ⊤)))
      (g₄ := RingHom.id _) (RingHom.ext fun w => map_map_apply _ _ _ (fun _ => rfl) w), sp_id',
      Category.id_comp]
    exact sp_sq (RingHom.ext fun w => map_cst _ w)
  have e1S : sp (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) ≫ sp (AddMonoidAlgebra.mapRingHom M π₁) ≫
      sp (cst (RR N T) M) = sp (cst _ M) ≫ sp (AddMonoidAlgebra.mapRingHom N ι) := by
    rw [← Category.assoc, sp_sq (g₃ := AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom N ι))
      (g₄ := RingHom.id _) (RingHom.ext fun w => map_map_apply _ _ _ (fun _ => rfl) w), sp_id',
      Category.id_comp]
    exact sp_sq (RingHom.ext fun w => map_cst _ w)
  have hF₁c : sp (cst _ M) ≫ sF = sF₁ := (tri3 e1F t).symm
  have hS₁c : sp (cst _ M) ≫ s₀ = s₀₁ := (tri3 e1S t).symm
  have hF₁ρ : sp (coactN (M := M) F Γ(T.left, ⊤)) ≫ sF = sF₁ := (hρs F T sF hsF).trans hF₁c
  have hS₁ρ : sp (coactN (M := M) N Γ(T₀.left, ⊤)) ≫ s₀ = s₀₁ := (hρs N T₀ s₀ hs₀).trans hS₁c
  let PM : Ov sF₁ ⟶ Ov s₁ := ovHom (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) rfl
  let QM : Ov s₀₁ ⟶ Ov s₁ := ovHom (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) rfl
  have ha : ovHom ρ₀ h₀ρ ≫ a = sm aX (eOf s₁ (eU Pu M)) (ovHom (cst Pu M) h₀c ≫ a) := by
    refine Over.OverMorphism.ext (milnor_ext HM ?_ ?_)
    · have key : PM ≫ ovHom ρ₀ h₀ρ ≫ a = PM ≫ sm aX (eOf s₁ (eU Pu M)) (ovHom (cst Pu M) h₀c ≫ a) := by
        have l₁ := tri (u := PM) (v := ovHom ρ₀ h₀ρ) (w := ovHom (coactN (M := M) F Γ(T.left, ⊤)) hF₁ρ)
          (x := pF) (Over.OverMorphism.ext (sp_sq (RingHom.ext fun p => coactP_fst N hF ι hι p))) a
        have l₂ := tri (u := PM) (v := ovHom (cst Pu M) h₀c) (w := ovHom (cst _ M) hF₁c)
          (x := pF) (Over.OverMorphism.ext (sp_sq (RingHom.ext fun p => map_cst _ p))) a
        have l₃ : APt.res PM.op (eOf s₁ (eU Pu M)) = eOf sF₁ (eU _ M) :=
          (res_eOf _ _ _).trans (eOf_congr _ (hof _))
        refine l₁.trans ((congrArg (fun z => _ ≫ z) hpFa).trans
          ((equiv_of_attPt F sF hsF y sF₁ hF₁c hF₁ρ).trans ?_))
        refine Eq.trans ?_ (comp_sm aX PM _ _).symm
        exact congrArg₂ (fun h z => sm aX h z) l₃.symm
          ((congrArg (fun z => _ ≫ z) hpFa).symm.trans l₂.symm)
      exact congrArg (fun z => z.left) key
    · have key : QM ≫ ovHom ρ₀ h₀ρ ≫ a = QM ≫ sm aX (eOf s₁ (eU Pu M)) (ovHom (cst Pu M) h₀c ≫ a) := by
        have l₁ := tri (u := QM) (v := ovHom ρ₀ h₀ρ) (w := ovHom (coactN (M := M) N Γ(T₀.left, ⊤)) hS₁ρ)
          (x := pS) (Over.OverMorphism.ext (sp_sq (RingHom.ext fun p => coactP_snd N hF ι hι p))) a
        have l₂ := tri (u := QM) (v := ovHom (cst Pu M) h₀c) (w := ovHom (cst _ M) hS₁c)
          (x := pS) (Over.OverMorphism.ext (sp_sq (RingHom.ext fun p => map_cst _ p))) a
        have l₃ : APt.res QM.op (eOf s₁ (eU Pu M)) = eOf s₀₁ (eU _ M) :=
          (res_eOf _ _ _).trans (eOf_congr _ (hof _))
        refine l₁.trans ((congrArg (fun z => _ ≫ z) hpSa).trans
          ((equiv_of_attPt N s₀ hs₀ x₀ s₀₁ hS₁c hS₁ρ).trans ?_))
        refine Eq.trans ?_ (comp_sm aX QM _ _).symm
        exact congrArg₂ (fun h z => sm aX h z) l₃.symm
          ((congrArg (fun z => _ ≫ z) hpSa).symm.trans l₂.symm)
      exact congrArg (fun z => z.left) key
  obtain ⟨l, hl₁, -, hl₃⟩ := exists_equivariant_of_lift π₁ hπs hπq t ρ ρ₀ hρt hρφ
    (coactN_coassoc N _) aX trivAction (Over.homMk X.hom (Category.comp_id _))
    (fun _ _ => term_ext _ _) a b α (Over.OverMorphism.ext hα₂)
    (Over.OverMorphism.ext hα₁) h₀ρ h₀c ha (term_ext _ _)
  have a1 : (attPtOf N t rfl l hρt hl₃).app U.π U.u = l := attPtOf_app N t rfl l hρt hl₃
  have hπ₁l : (ovHom (faceRingHom hF Γ(T.left, ⊤)) rfl : Ov sF ⟶ Ov t) ≫ l = yF := by
    have sq : (ovHom (faceRingHom hF Γ(T.left, ⊤)) rfl : Ov sF ⟶ Ov t) = pF ≫ ovHom π₁ rfl :=
      Over.OverMorphism.ext hspf.symm
    rw [sq]
    exact (Category.assoc _ _ _).trans ((congrArg (fun z => pF ≫ z) hl₁).trans hpFa)
  have hπ₂l : (ovHom (AddMonoidAlgebra.mapRingHom N ι) rfl : Ov s₀ ⟶ Ov t) ≫ l = x₀U := by
    have sq : (ovHom (AddMonoidAlgebra.mapRingHom N ι) rfl : Ov s₀ ⟶ Ov t) = pS ≫ ovHom π₁ rfl :=
      Over.OverMorphism.ext hsps.symm
    rw [sq]
    exact (Category.assoc _ _ _).trans ((congrArg (fun z => pS ≫ z) hl₁).trans hpSa)
  refine ⟨attPtOf N t rfl l hρt hl₃, ?_, ?_⟩
  · refine (attractorPtEquivOfUniversal (act := aX) U₀).injective (Subtype.ext ?_)
    change (attPtOf N t rfl l hρt hl₃).app (U₀.π ≫ i) U₀.u = x₀U
    refine ((attPtOf N t rfl l hρt hl₃).app_eq_of_universal U _ _).trans ?_
    refine (congrArg (fun z : U.P ⟶ X => U.lift (U₀.π ≫ i) U₀.u ≫ z) a1).trans ?_
    have hj : (ovHom (AddMonoidAlgebra.mapRingHom N ι) rfl : Ov s₀ ⟶ Ov t) =
        U.lift (U₀.π ≫ i) U₀.u := by
      refine U.uniq _ _ _ (Over.OverMorphism.ext (π_sq N i).symm) (MonoidHom.ext fun n => ?_)
      refine (sp_inv _ _).trans (congrArg _ ?_)
      refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
      rw [map_one]
    exact (congrArg (fun z => z ≫ l) hj.symm).trans hπ₂l
  · refine (attractorPtEquivOfUniversal (act := aX) UF).injective (Subtype.ext ?_)
    change (attPtOf N t rfl l hρt hl₃).app UF.π (APt.faceExt hF UF.u) = yF
    refine ((attPtOf N t rfl l hρt hl₃).app_eq_of_universal U _ _).trans ?_
    refine (congrArg (fun z : U.P ⟶ X => U.lift UF.π (APt.faceExt hF UF.u) ≫ z) a1).trans ?_
    exact (congrArg (fun z => z ≫ l) (lift_face N hF T t rfl sF hsF rfl)).trans hπ₁l

end Face

end AlgMag.SmoothSchemes
