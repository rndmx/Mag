/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesCore
import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.OfIsSmooth

/-!
# Propositions 11.1 and 11.5 for algebraic spaces

Mayeux, *Algebraic Magnetism*, §11. `lift103` discharges `AlgMag.Sec11Spaces.Lift103` for algebraic
spaces. The only size condition is `SM B M`, that `#M` is below the cutoff of the site; it makes
`𝔸(N)_T`, `𝔸(N)_T × 𝔸(M)` and the rings of the integration argument objects of the site.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes AlgMag.Sec11Spaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommMonoid M]
  [SM B M] (N : AddSubmonoid M)

/-- The scheme underlying an object of the site. -/
abbrev τS (T : BigFppfOver B S hS) : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj T

lemma sr_sections (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    SR B Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := by
  refine sr_iff.2 ?_
  have h : ((BigFppfOver.toScheme B S hS).obj T).size < B.cutoff := T.left.2
  rw [Scheme.size_of_isAffine] at h
  exact (le_max_right _ _).trans_lt h

/-- `R[N]`, for `R = Γ(X, ⊤)`. -/
abbrev RS (X : Scheme.{u}) : Type u := AddMonoidAlgebra Γ(X, ⊤) N

lemma rhoπ (X : Scheme.{u}) [IsAffine X] : sp (coactN (M := M) N Γ(X, ⊤)) ≫ magnetπ N X =
    sp (cst (RS N X) M) ≫ magnetπ N X :=
  haveI : IsAffine (Over.mk (𝟙 X) : Over X).left := inferInstanceAs (IsAffine X)
  hρπ (S := X) N (Over.mk (𝟙 X))

lemma piSq {X₀ X : Scheme.{u}} [IsAffine X₀] [IsAffine X] (e : X₀ ⟶ X) :
    magnetπ N X₀ ≫ e = sp (AddMonoidAlgebra.mapRingHom N e.appTop.hom) ≫ magnetπ N X := by
  haveI : IsAffine (Over.mk e : Over X).left := inferInstanceAs (IsAffine X₀)
  haveI : IsAffine (Over.mk (𝟙 X) : Over X).left := inferInstanceAs (IsAffine X)
  exact π_sq (S := X) N (T₀ := Over.mk e) (T := Over.mk (𝟙 X)) (Over.homMk e (by simp))

section Up

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [SR B Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]

/-- `𝔸(N)_T` in the site, with a chosen form `s` of its structure morphism. -/
noncomputable def specU (s : Spec (CommRingCat.of (RS N (τS T))) ⟶ S)
    (hs : magnetπ N (τS T) ≫ T.hom.hom = s) : UniversalPoint (fppfO B S hS) N T where
  P := Sv B hS s
  π := Over.homMk (ObjectProperty.homMk (magnetπ N _)) (ObjectProperty.hom_ext _ hs)
  u := magnetU N _
  lift {T₁} t a := Over.homMk (ObjectProperty.homMk
    (magnetLift N ((BigFppfOver.toScheme B S hS).map t) a)) (by
      have h : (BigFppfOver.toScheme B S hS).map t ≫ T.hom.hom = T₁.hom.hom :=
        congrArg (fun k => k.hom) (Over.w t)
      refine ObjectProperty.hom_ext _ ?_
      have h₂ := magnetLift_π N ((BigFppfOver.toScheme B S hS).map t) a
      change magnetLift N _ a ≫ s = T₁.hom.hom
      rw [← hs, ← Category.assoc, h₂, h])
  lift_π t a := site_ext (magnetLift_π N ((BigFppfOver.toScheme B S hS).map t) a)
  res_lift t a := MonoidHom.ext fun n => magnetLift_res N _ a n
  uniq t a x h₁ h₂ := site_ext (magnetLift_uniq N ((BigFppfOver.toScheme B S hS).map t) a
      ((BigFppfOver.toScheme B S hS).map x) (by rw [← h₁]; rfl) (fun n => by rw [← h₂]; rfl))

variable {T} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  (s : Spec (CommRingCat.of (RS N (τS T))) ⟶ S) (hs : magnetπ N (τS T) ≫ T.hom.hom = s)

include hs in
lemma rhoS : sp (coactN (M := M) N Γ(τS T, ⊤)) ≫ s = sp (cst (RS N (τS T)) M) ≫ s := by
  subst hs
  exact tri (rhoπ N (τS T)) _

/-- `𝔸(M)` acts on the universal point through `ρ`. -/
lemma res_coactS (s₁ : Spec (CommRingCat.of (AddMonoidAlgebra (RS N (τS T)) M)) ⟶ S)
    (h₁ : sp (cst (RS N (τS T)) M) ≫ s = s₁) (h₂ : sp (coactN (M := M) N Γ(τS T, ⊤)) ≫ s = s₁) :
    APt.res (svHom B hS (coactN (M := M) N Γ(τS T, ⊤)) h₂ : Sv B hS s₁ ⟶ (specU N T s hs).P).op
        (specU N T s hs).u =
      APt.toMagnet N (eS B hS s₁ (eU (RS N (τS T)) M)) *
        APt.res (svHom B hS (cst (RS N (τS T)) M) h₁ : Sv B hS s₁ ⟶ (specU N T s hs).P).op
          (specU N T s hs).u := by
  refine MonoidHom.ext fun n => ?_
  have e₁ := sp_inv (coactN (M := M) N Γ(τS T, ⊤))
    (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  have e₂ := sp_inv (cst (RS N (τS T)) M) (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  refine e₁.trans ?_
  refine Eq.trans ?_ (congrArg (fun z => _ * z) e₂.symm)
  refine Eq.trans ?_ (map_mul (Scheme.ΓSpecIso (CommRingCat.of _)).inv.hom _ _)
  congr 1
  rw [coactN_single]
  change _ = AddMonoidAlgebra.single _ 1 * AddMonoidAlgebra.single 0 _
  rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul]
  rfl

/-- The value of an attractor point at the universal point is equivariant. -/
lemma equiv_of_attPtS (φ₀ : AttractorPt aX N T)
    (s₁ : Spec (CommRingCat.of (AddMonoidAlgebra (RS N (τS T)) M)) ⟶ S)
    (h₁ : sp (cst (RS N (τS T)) M) ≫ s = s₁) (h₂ : sp (coactN (M := M) N Γ(τS T, ⊤)) ≫ s = s₁) :
    pb X (svHom B hS (coactN (M := M) N Γ(τS T, ⊤)) h₂ : Sv B hS s₁ ⟶ (specU N T s hs).P)
        (φ₀.app (specU N T s hs).π (specU N T s hs).u) =
      ss aX (eS B hS s₁ (eU (RS N (τS T)) M))
        (pb X (svHom B hS (cst (RS N (τS T)) M) h₁ : Sv B hS s₁ ⟶ (specU N T s hs).P)
          (φ₀.app (specU N T s hs).π (specU N T s hs).u)) := by
  let U := specU N T s hs
  let c : Sv B hS s₁ ⟶ U.P := svHom B hS (cst (RS N (τS T)) M) h₁
  let r : Sv B hS s₁ ⟶ U.P := svHom B hS (coactN (M := M) N Γ(τS T, ⊤)) h₂
  have hc : c = U.lift (c ≫ U.π) (APt.res c.op U.u) := U.uniq _ _ _ rfl rfl
  have hr : r = U.lift (c ≫ U.π)
      (APt.toMagnet N (eS B hS s₁ (eU (RS N (τS T)) M)) * APt.res c.op U.u) :=
    U.uniq _ _ _ (site_ext (rhoπ N (τS T))) (res_coactS N s hs s₁ h₁ h₂)
  have key := φ₀.equivariant (c ≫ U.π) (eS B hS s₁ (eU (RS N (τS T)) M)) (APt.res c.op U.u)
  rw [φ₀.app_eq_of_universal U, φ₀.app_eq_of_universal U (c ≫ U.π) (APt.res c.op U.u), ← hr, ← hc]
    at key
  exact key

/-- The classifying morphism of a pair (point of `Spec D`, point of `𝔸(M)`). -/
lemma exists_classifyS {D : Type u} [CommRing D] [SR B D] {s₀ : Spec (CommRingCat.of D) ⟶ S}
    {T₁ : BigFppfOver B S hS} (κ : T₁ ⟶ Sv B hS s₀) (h : APt (fppfO B S hS) M (op T₁)) :
    ∃ κ₁ : T₁ ⟶ Sv B hS (sp (cst D M) ≫ s₀), κ₁ ≫ svHom B hS (cst D M) rfl = κ ∧
      APt.res κ₁.op (eS B hS (sp (cst D M) ≫ s₀) (eU D M)) = h := by
  let K := (BigFppfOver.toScheme B S hS).map κ
  let ψ : D →+* Γ(τS T₁, ⊤) := (homSpecEquiv (τS T₁) (CommRingCat.of D) K).hom
  let Ψ : AddMonoidAlgebra D M →+* Γ(τS T₁, ⊤) :=
    AddMonoidAlgebra.liftNCRingHom ψ h (fun _ _ => Commute.all _ _)
  let w : τS T₁ ⟶ Spec (CommRingCat.of (AddMonoidAlgebra D M)) :=
    (homSpecEquiv (τS T₁) _).symm (CommRingCat.ofHom Ψ)
  have hw : homSpecEquiv (τS T₁) _ w = CommRingCat.ofHom Ψ := Equiv.apply_symm_apply _ _
  have hc : w ≫ sp (cst D M) = K := by
    apply (homSpecEquiv (τS T₁) (CommRingCat.of D)).injective
    rw [hse_comp, hw]
    ext x
    change Ψ (AddMonoidAlgebra.single 0 x) = ψ x
    simp only [Ψ, AddMonoidAlgebra.liftNCRingHom]
    have e := AddMonoidAlgebra.liftNC_single (ψ : D →+ Γ(τS T₁, ⊤)) h (0 : M) x
    refine e.trans ?_
    have h1 : h (Multiplicative.ofAdd (0 : M)) = 1 := map_one h
    exact (congrArg (fun z => ψ x * z) h1).trans (mul_one _)
  refine ⟨Over.homMk (ObjectProperty.homMk w) (ObjectProperty.hom_ext _ ?_), site_ext hc,
    MonoidHom.ext fun m => ?_⟩
  · change w ≫ sp (cst D M) ≫ s₀ = T₁.hom.hom
    rw [← Category.assoc, hc]
    exact congrArg (fun k => k.hom) (Over.w κ)
  · have := congrArg (fun k => k.hom (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1)) hw
    refine this.trans ?_
    change Ψ (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1) = h m
    simp [Ψ, AddMonoidAlgebra.liftNCRingHom]
    rfl

/-- An equivariant section over the universal point is an attractor point. -/
noncomputable def attPtOfS (l : X.obj (op (specU N T s hs).P))
    (h₂ : sp (coactN (M := M) N Γ(τS T, ⊤)) ≫ s = sp (cst (RS N (τS T)) M) ≫ s)
    (hl : pb X (svHom B hS (coactN (M := M) N Γ(τS T, ⊤)) h₂ : _ ⟶ (specU N T s hs).P) l =
      ss aX (eS B hS (sp (cst (RS N (τS T)) M) ≫ s) (eU (RS N (τS T)) M))
        (pb X (svHom B hS (cst (RS N (τS T)) M) rfl : _ ⟶ (specU N T s hs).P) l)) :
    AttractorPt aX N T :=
  (attractorPtEquivOfUniversal (act := aX) (specU N T s hs)).symm ⟨l, by
    intro T₁ t h a
    let U := specU N T s hs
    let s₁ := sp (cst (RS N (τS T)) M) ≫ s
    let r : Sv B hS s₁ ⟶ U.P := svHom B hS (coactN (M := M) N Γ(τS T, ⊤)) h₂
    let c : Sv B hS s₁ ⟶ U.P := svHom B hS (cst (RS N (τS T)) M) rfl
    obtain ⟨κ₁, h₁, he⟩ := exists_classifyS (M := M) (s₀ := s) (U.lift t a) h
    have hc : κ₁ ≫ c = U.lift t a := h₁
    have hπ : r ≫ U.π = c ≫ U.π := site_ext (rhoπ N (τS T))
    have hl₁ : κ₁ ≫ r = U.lift t (APt.toMagnet N h * a) := by
      refine U.uniq _ _ _ ?_ ?_
      · refine (Category.assoc κ₁ r U.π).trans ?_
        rw [hπ]
        exact (Category.assoc κ₁ c U.π).symm.trans ((congrArg (· ≫ U.π) hc).trans (U.lift_π t a))
      · have e : APt.res r.op U.u =
            APt.toMagnet N (eS B hS s₁ (eU (RS N (τS T)) M)) * APt.res c.op U.u :=
          res_coactS N s hs s₁ rfl h₂
        refine (APt.res_comp r.op κ₁.op U.u).trans ?_
        rw [e, APt.res_mul, ← APt.toMagnet_res]
        have e₁ : APt.res κ₁.op (eS B hS s₁ (eU (RS N (τS T)) M)) = h := he
        have e₂ : APt.res κ₁.op (APt.res c.op U.u) = a :=
          (APt.res_comp c.op κ₁.op U.u).symm.trans
            ((congrArg (fun z : T₁ ⟶ U.P => APt.res z.op U.u) hc).trans (U.res_lift t a))
        rw [e₁, e₂]
    change pb X (U.lift t (APt.toMagnet N h * a)) l = ss aX h (pb X (U.lift t a) l)
    rw [← hl₁, ← hc, pb_comp, pb_comp]
    have e₃ : pb X r l = ss aX (eS B hS s₁ (eU (RS N (τS T)) M)) (pb X c l) := hl
    rw [e₃, pb_ss]
    have e₁ : APt.res κ₁.op (eS B hS s₁ (eU (RS N (τS T)) M)) = h := he
    rw [e₁]⟩

lemma attPtOfS_app (l : X.obj (op (specU N T s hs).P))
    (h₂ : sp (coactN (M := M) N Γ(τS T, ⊤)) ≫ s = sp (cst (RS N (τS T)) M) ≫ s)
    (hl : pb X (svHom B hS (coactN (M := M) N Γ(τS T, ⊤)) h₂ : _ ⟶ (specU N T s hs).P) l =
      ss aX (eS B hS (sp (cst (RS N (τS T)) M) ≫ s) (eU (RS N (τS T)) M))
        (pb X (svHom B hS (cst (RS N (τS T)) M) rfl : _ ⟶ (specU N T s hs).P) l)) :
    (attPtOfS N s hs l h₂ hl).app (specU N T s hs).π (specU N T s hs).u = l :=
  congrArg Subtype.val ((attractorPtEquivOfUniversal (act := aX) (specU N T s hs)).apply_symm_apply ⟨l, _⟩)

end Up

end AlgMag.SpacesLift

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes AlgMag.Sec11Spaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]
  [SM B M] (N : AddSubmonoid M)

section Lift

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {aY : AAction (fppfO B S hS) M Y}

/-- A square zero surjection of rings in the site is a square zero closed immersion. -/
lemma sqZero_svHom {R R₀ : Type u} [CommRing R] [CommRing R₀] [SR B R] [SR B R₀] (φ : R →+* R₀)
    (hs : Function.Surjective φ) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    {t : Spec (CommRingCat.of R) ⟶ S} :
    Space.IsSquareZeroClosedImmersion B S hS (svHom B hS φ (s := t) rfl) :=
  Stacks.Smooth.isFirstOrderThickening_specMap _ hs (by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx z hz
    exact hq x z hx hz)

/-- **Corollary 10.3 for algebraic spaces**, on the thickening `𝔸(N)_{T₀} → 𝔸(N)_T`: the conclusion
`Lift103` of `AlgMag.Sec11Spaces`, for `f` formally smooth and `#M` below the cutoff. -/
theorem lift103 (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : EquivariantHom aX aY) (hf : Space.FormallySmooth f.hom) :
    Lift103 (fun {_ _} i => IsAffineThickening i) f N := by
  intro T₀ T i hi
  have := hi.affine₀
  have := hi.affine
  haveI := sr_sections T₀
  haveI := sr_sections T
  let e := (BigFppfOver.toScheme B S hS).map i
  let ι := e.appTop.hom
  let φ := AddMonoidAlgebra.mapRingHom N ι
  let t := magnetπ N (τS T) ≫ T.hom.hom
  have hw : e ≫ T.hom.hom = T₀.hom.hom := congrArg (fun k => k.hom) (Over.w i)
  have hs₀ : magnetπ N (τS T₀) ≫ T₀.hom.hom = sp φ ≫ t := by
    rw [← hw, ← Category.assoc, piSq N e, Category.assoc]
  let U := specU N T t rfl
  let U₀ := specU N T₀ (sp φ ≫ t) hs₀
  let ρ := coactN (M := M) N Γ(τS T, ⊤)
  let ρ₀ := coactN (M := M) N Γ(τS T₀, ⊤)
  have hρφ : ∀ w, AddMonoidAlgebra.mapRingHom M φ (ρ w) = ρ₀ (φ w) := coactN_map N ι
  have hρt : sp ρ ≫ t = sp (cst _ M) ≫ t := rhoS N t rfl
  have hφs : Function.Surjective φ := mapRingHom_surjective ι hi.surjective
  have hφq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0 := magnetAlgebra_mul_eq_zero ι hi.sq_zero
  have h₀c : sp (cst _ M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst _ M) ≫ t :=
    tri (sp_sq (RingHom.ext fun w => (map_cst φ w).symm)) t
  have h₀ρ : sp ρ₀ ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst _ M) ≫ t := by
    rw [← hρt]
    exact tri (sp_sq (RingHom.ext fun w => (hρφ w).symm)) t
  have hj : svHom B hS φ (s := t) rfl = U.lift (U₀.π ≫ i) U₀.u := by
    refine U.uniq _ _ _ (site_ext (piSq N e).symm) (MonoidHom.ext fun n => ?_)
    refine (sp_inv φ _).trans ?_
    refine congrArg _ ?_
    refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
    rw [map_one]
  refine ⟨U₀, U, fun x₀ y hc => ?_⟩
  rw [← hj] at hc ⊢
  obtain ⟨α, hα₁, hα₂⟩ := hf _ _ (inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsAffine (Spec _))) (svHom B hS φ (s := t) rfl)
    (sqZero_svHom φ hφs hφq) (x₀.app U₀.π U₀.u) (y.app U.π U.u) hc
  obtain ⟨l, hl₁, hl₂, hl₃⟩ := exists_equivariant_of_lift φ hφs hφq t ρ ρ₀ hρt hρφ
    (coactN_coassoc N _) hX hY f (x₀.app U₀.π U₀.u) (y.app U.π U.u) α hα₁ hα₂
    h₀ρ h₀c (equiv_of_attPtS N (sp φ ≫ t) hs₀ x₀ _ h₀c h₀ρ)
    (equiv_of_attPtS N t rfl y _ rfl hρt)
  have a1 : (attPtOfS N t rfl l hρt hl₃).app U.π U.u = l := attPtOfS_app N t rfl l hρt hl₃
  refine ⟨attPtOfS N t rfl l hρt hl₃, ?_, ?_⟩
  · rw [a1]
    exact hl₁
  · rw [a1]
    exact hl₂

/-- **Proposition 11.1** for algebraic spaces: if `f : X → Y` is smooth and equivariant, `f^N` is
formally smooth. `#M` is below the cutoff of the site. -/
theorem isFormallySmooth_attractorMap_spaces (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : EquivariantHom aX aY) (hf : Space.IsSmooth B S hS f.hom) :
    IsFormallySmooth (attractorMap f N) :=
  isFormallySmooth_attractorMap N f
    (lift103 N hX hY f (Space.formallySmooth_of_isSmooth' hX hY hf))

end Lift

end AlgMag.SpacesLift

