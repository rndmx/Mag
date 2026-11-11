/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedCor
import AlgMag.Sec11SchemesFace

/-!
# Propositions 11.1 and 11.7, on the printed Corollary 10.3

Mayeux, *Algebraic Magnetism*. The proofs of `AlgMag.SmoothSchemes`, with the lift given by
`Sec10Printed.exists_equivariant_of_lift_printed` instead of the integration proof.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.Sec11Printed

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

lemma coactN_aug (D : Type u) [CommRing D] :
    (Sec10Printed.aug (AddMonoidAlgebra D N) M).comp (coactN (M := M) N D) = RingHom.id _ := by
  refine RingHom.ext fun w => ?_
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n r =>
    simp only [RingHom.comp_apply, coactN_single, RingHom.id_apply]
    have e : (AddMonoidAlgebra.single (n : M) (AddMonoidAlgebra.single n r) :
        AddMonoidAlgebra (AddMonoidAlgebra D N) M) =
        Sec10Printed.cs _ M (AddMonoidAlgebra.single n r) * AddMonoidAlgebra.single (n : M) 1 := by
      change _ = AddMonoidAlgebra.single 0 _ * _
      rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rw [e, map_mul, Sec10Printed.aug_of, mul_one]
    exact RingHom.congr_fun Sec10Printed.aug_cs _

/-- **Proposition 11.1**, schemes only: if `g : X → Y` is smooth and equivariant, then
`g^N : X^N → Y^N` is formally smooth as a transformation of functors. `S` is any scheme, `M` any
commutative group, `N` any magnet. Test objects are first order thickenings of affine schemes. -/
theorem isFormallySmooth_attractorMap_scheme {X Y : Over S}
    {aX : AAction (overO S) M (yoneda.obj X)} {aY : AAction (overO S) M (yoneda.obj Y)}
    (g : X ⟶ Y) (hg : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X),
      sm aX h x ≫ g = sm aY h (x ≫ g)) [Smooth g.left] :
    FormallySmoothFor (fun {_ _} i => IsAffineThick i) (attractorMap (eqHom g hg) N) := by
  intro T₀ T i hi x₀ y hc
  have := hi.affine₀
  have := hi.affine
  let ι := i.left.appTop.hom
  let φ := AddMonoidAlgebra.mapRingHom N ι
  let t := magnetπ N T.left ≫ T.hom
  have hs₀ : magnetπ N T₀.left ≫ T₀.hom = sp φ ≫ t := π_thick N i
  let U := specUP N T t rfl
  let U₀ := specUP N T₀ (sp φ ≫ t) hs₀
  let ρ := coactN (M := M) N Γ(T.left, ⊤)
  let ρ₀ := coactN (M := M) N Γ(T₀.left, ⊤)
  have hρφ : ∀ w, AddMonoidAlgebra.mapRingHom M φ (ρ w) = ρ₀ (φ w) := coactN_map N ι
  have hρt : sp ρ ≫ t = sp (cst _ M) ≫ t := hρs N T t rfl
  have hφs : Function.Surjective φ := mapRingHom_surjective ι hi.surjective
  have hφq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0 := magnetAlgebra_mul_eq_zero ι hi.sq_zero
  have h₀c : sp (cst _ M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst _ M) ≫ t :=
    tri (sp_sq (RingHom.ext fun w => (map_cst φ w).symm)) t
  have h₀ρ : sp ρ₀ ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst _ M) ≫ t := by
    rw [← hρt]
    exact tri (sp_sq (RingHom.ext fun w => (hρφ w).symm)) t
  let a : U₀.P ⟶ X := x₀.app U₀.π U₀.u
  let b : U.P ⟶ Y := y.app U.π U.u
  have hj : (ovHom φ rfl : Ov (sp φ ≫ t) ⟶ Ov t) = U.lift (U₀.π ≫ i) U₀.u := by
    refine U.uniq _ _ _ ?_ ?_
    · refine Over.OverMorphism.ext ?_
      exact (π_sq N i).symm
    · refine MonoidHom.ext fun n => ?_
      refine (sp_inv φ _).trans ?_
      refine congrArg _ ?_
      refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
      rw [map_one]
  have hab : a ≫ g = ovHom φ rfl ≫ b := by
    have e := congrArg (fun z : AttractorPt aY N T₀ => z.app U₀.π U₀.u) hc
    rw [hj]
    refine e.trans ?_
    exact y.app_eq_of_universal U _ _
  obtain ⟨α₁, hα₁, hα₂⟩ := Stacks.Smooth.formallySmoothScheme_of_smooth g.left
    (T := Spec (CommRingCat.of (RR N T₀))) (T' := Spec (CommRingCat.of (RR N T)))
    inferInstance inferInstance (Spec.map (CommRingCat.ofHom φ))
    (Stacks.Smooth.isFirstOrderThickening_specMap _ hφs (by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro x hx z hz
      exact hφq x z hx hz)) a.left b.left (congrArg (fun k => k.left) hab)
  let α : U.P ⟶ X := Over.homMk α₁ (by
    change α₁ ≫ X.hom = t
    rw [← Over.w g, ← Category.assoc, hα₁]
    exact Over.w b)
  obtain ⟨l, hl₁, hl₂, hl₃⟩ := Sec10Printed.exists_equivariant_of_lift_printed (coactN_aug N _) φ hφs hφq t ρ ρ₀ rfl hρt hρφ
    (coactN_coassoc N _) aX aY g hg a b α (Over.OverMorphism.ext hα₂) (Over.OverMorphism.ext hα₁)
    h₀ρ h₀c (equiv_of_attPt N (sp φ ≫ t) hs₀ x₀ _ h₀c h₀ρ)
    (equiv_of_attPt N t rfl y _ rfl hρt)
  have a1 : (attPtOf N t rfl l hρt hl₃).app U.π U.u = l := attPtOf_app N t rfl l hρt hl₃
  refine ⟨attPtOf N t rfl l hρt hl₃, ?_, ?_⟩
  · refine (attractorPtEquivOfUniversal (act := aX) U₀).injective (Subtype.ext ?_)
    change (attPtOf N t rfl l hρt hl₃).app (U₀.π ≫ i) U₀.u = x₀.app U₀.π U₀.u
    refine ((attPtOf N t rfl l hρt hl₃).app_eq_of_universal U _ _).trans ?_
    refine (congrArg (fun z : U.P ⟶ X => U.lift (U₀.π ≫ i) U₀.u ≫ z) a1).trans ?_
    exact (congrArg (fun z => z ≫ l) hj.symm).trans hl₁
  · refine (attractorPtEquivOfUniversal (act := aY) U).injective (Subtype.ext ?_)
    exact (congrArg (fun z : U.P ⟶ X => z ≫ g) a1).trans hl₂


section Face

variable {F : AddSubmonoid M} (hF : IsFace F N) [DecidableEq M]

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
  obtain ⟨l, hl₁, -, hl₃⟩ := Sec10Printed.exists_equivariant_of_lift_printed (coactN_aug N _) π₁ hπs hπq t ρ ρ₀ rfl hρt hρφ
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

end AlgMag.Sec11Printed
