/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10LiftsCore
import AlgMag.Sec11Formal
import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag

/-!
# Formal smoothness of attractors, for schemes

Mayeux, *Algebraic Magnetism*, §11, schemes only: `S` is any scheme, `X`, `Y` are `S`-schemes, the
site is `Over S`, and test objects are first order thickenings of affine schemes. `M` is any
commutative group (the paper assumes it finitely generated) and `N` any magnet; the lemmas
before Proposition 11.1 hold for a commutative monoid.

* `isFormallySmooth_attractorMap_scheme`: **Proposition 11.1**.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.SmoothSchemes

open AlgMag.GB AlgMag.Lifts

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M] (N : AddSubmonoid M)

/-- The coaction `D[N] → D[N][M]`, `r e^n ↦ r e^n e^n`. -/
noncomputable def coactN (D : Type u) [CommRing D] :
    AddMonoidAlgebra D N →+* AddMonoidAlgebra (AddMonoidAlgebra D N) M :=
  AddMonoidAlgebra.liftNCRingHom ((cst _ M).comp AddMonoidAlgebra.singleZeroRingHom)
    { toFun := fun n => AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M)
        (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
      map_one' := rfl
      map_mul' := fun x y => by simp [AddMonoidAlgebra.single_mul_single] }
    (fun _ _ => Commute.all _ _)

lemma coactN_single (D : Type u) [CommRing D] (n : N) (r : D) :
    coactN N D (AddMonoidAlgebra.single n r) =
      AddMonoidAlgebra.single (n : M) (AddMonoidAlgebra.single n r) := by
  simp [coactN, cst, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.singleZeroRingHom,
    AddMonoidAlgebra.single_mul_single]

lemma coactN_coassoc (D : Type u) [CommRing D] (w : AddMonoidAlgebra D N) :
    AddMonoidAlgebra.mapRingHom M (coactN N D) (coactN N D w) =
      diag (AddMonoidAlgebra D N) M (coactN N D w) := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n r => simp [coactN_single, diag_single]

lemma coactN_map {D E : Type u} [CommRing D] [CommRing E] (g : D →+* E)
    (w : AddMonoidAlgebra D N) :
    AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom N g) (coactN N D w) =
      coactN N E (AddMonoidAlgebra.mapRingHom N g w) := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n r => simp [coactN_single]

lemma coactN_const (D : Type u) [CommRing D] (r : D) :
    coactN N D (AddMonoidAlgebra.singleZeroRingHom r) =
      cst _ M (AddMonoidAlgebra.singleZeroRingHom r) := by
  simpa [cst, AddMonoidAlgebra.singleZeroRingHom] using coactN_single N D (0 : N) r

/-- `𝔸(N)_T` over `S`, for `T` affine, with a chosen form `s` of its structure morphism. -/
noncomputable def specUP (T : Over S) [IsAffine T.left]
    (s : Spec (magnetRing N T.left) ⟶ S) (hs : magnetπ N T.left ≫ T.hom = s) :
    UniversalPoint (overO S) N T where
  P := Ov s
  π := Over.homMk (magnetπ N T.left) hs
  u := magnetU N T.left
  lift {T₁} t a := Over.homMk (magnetLift N t.left a) (by
    have h₂ := magnetLift_π N t.left a
    have h : t.left ≫ T.hom = T₁.hom := Over.w t
    change magnetLift N t.left a ≫ s = T₁.hom
    rw [← hs, ← Category.assoc, h₂, h])
  lift_π t a := Over.OverMorphism.ext (magnetLift_π N t.left a)
  res_lift t a := MonoidHom.ext fun n => magnetLift_res N _ a n
  uniq t a x h₁ h₂ := Over.OverMorphism.ext (magnetLift_uniq N t.left a x.left
    (congrArg (fun k => k.left) h₁) (fun n => by rw [← h₂]; rfl))

section Equivariance

variable {X : Over S} {aX : AAction (overO S) M (yoneda.obj X)} (T : Over S) [IsAffine T.left]
  (s : Spec (magnetRing N T.left) ⟶ S) (hs : magnetπ N T.left ≫ T.hom = s)

abbrev RR (T : Over S) : Type u := AddMonoidAlgebra Γ(T.left, ⊤) N

lemma hρπ : sp (coactN (M := M) N Γ(T.left, ⊤)) ≫ magnetπ N T.left =
    sp (cst (RR N T) M) ≫ magnetπ N T.left := by
  let sz : Γ(T.left, ⊤) →+* RR N T := AddMonoidAlgebra.singleZeroRingHom
  have sq : sp (coactN (M := M) N Γ(T.left, ⊤)) ≫ sp sz = sp (cst (RR N T) M) ≫ sp sz :=
    sp_sq (g := sz) (g₃ := sz) (RingHom.ext fun r => coactN_const N _ r)
  exact tri sq T.left.isoSpec.inv

include hs in
lemma hρs : sp (coactN (M := M) N Γ(T.left, ⊤)) ≫ s = sp (cst (RR N T) M) ≫ s := by
  subst hs
  exact tri (hρπ N T) _

lemma sp_inv {D E : Type u} [CommRing D] [CommRing E] (g : D →+* E) (x : D) :
    (sp g).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom (g x) :=
  (congrArg (fun k => k.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm

variable {T}

/-- The value of an attractor point at the universal point is equivariant. -/
lemma equiv_of_attPt (φ₀ : AttractorPt aX N T) (s₁ : Spec (CommRingCat.of (AddMonoidAlgebra (RR N T) M)) ⟶ S)
    (h₁ : sp (cst (RR N T) M) ≫ s = s₁) (h₂ : sp (coactN (M := M) N Γ(T.left, ⊤)) ≫ s = s₁) :
    ovHom (coactN (M := M) N Γ(T.left, ⊤)) h₂ ≫ φ₀.app (specUP N T s hs).π (specUP N T s hs).u =
      sm aX (eOf s₁ (eU (RR N T) M))
        (ovHom (cst (RR N T) M) h₁ ≫ φ₀.app (specUP N T s hs).π (specUP N T s hs).u) := by
  let U := specUP N T s hs
  let c : Ov s₁ ⟶ U.P := ovHom (cst (RR N T) M) h₁
  let r : Ov s₁ ⟶ U.P := ovHom (coactN (M := M) N Γ(T.left, ⊤)) h₂
  have hc : c = U.lift (c ≫ U.π) (APt.res c.op U.u) := U.uniq _ _ _ rfl rfl
  have hr : r = U.lift (c ≫ U.π) (APt.toMagnet N (eOf s₁ (eU (RR N T) M)) * APt.res c.op U.u) := by
    refine U.uniq _ _ _ ?_ ?_
    · refine Over.OverMorphism.ext ?_
      exact hρπ N T
    · refine MonoidHom.ext fun n => ?_
      have e₁ := sp_inv (coactN (M := M) N Γ(T.left, ⊤))
        (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
      have e₂ := sp_inv (cst (RR N T) M) (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
      refine e₁.trans ?_
      refine Eq.trans ?_ (congrArg (fun z => _ * z) e₂.symm)
      refine Eq.trans ?_ (map_mul (Scheme.ΓSpecIso (CommRingCat.of _)).inv.hom _ _)
      congr 1
      rw [coactN_single]
      change _ = AddMonoidAlgebra.single _ 1 * AddMonoidAlgebra.single 0 _
      rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul]
      rfl
  have key := φ₀.equivariant (c ≫ U.π) (eOf s₁ (eU (RR N T) M)) (APt.res c.op U.u)
  rw [φ₀.app_eq_of_universal U, φ₀.app_eq_of_universal U (c ≫ U.π) (APt.res c.op U.u), ← hr, ← hc] at key
  exact key

/-- `𝔸(M)` acts on the universal point through `ρ`. -/
lemma res_coact (s₁ : Spec (CommRingCat.of (AddMonoidAlgebra (RR N T) M)) ⟶ S)
    (h₁ : sp (cst (RR N T) M) ≫ s = s₁) (h₂ : sp (coactN (M := M) N Γ(T.left, ⊤)) ≫ s = s₁) :
    APt.res (ovHom (coactN (M := M) N Γ(T.left, ⊤)) h₂ : Ov s₁ ⟶ (specUP N T s hs).P).op
        (specUP N T s hs).u =
      APt.toMagnet N (eOf s₁ (eU (RR N T) M)) *
        APt.res (ovHom (cst (RR N T) M) h₁ : Ov s₁ ⟶ (specUP N T s hs).P).op (specUP N T s hs).u := by
  refine MonoidHom.ext fun n => ?_
  have e₁ := sp_inv (coactN (M := M) N Γ(T.left, ⊤))
    (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  have e₂ := sp_inv (cst (RR N T) M) (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  refine e₁.trans ?_
  refine Eq.trans ?_ (congrArg (fun z => _ * z) e₂.symm)
  refine Eq.trans ?_ (map_mul (Scheme.ΓSpecIso (CommRingCat.of _)).inv.hom _ _)
  congr 1
  rw [coactN_single]
  change _ = AddMonoidAlgebra.single _ 1 * AddMonoidAlgebra.single 0 _
  rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul]
  rfl

/-- The classifying morphism of a pair (point of `Spec D`, point of `𝔸(M)`). -/
lemma exists_classify {D : Type u} [CommRing D] {s₀ : Spec (CommRingCat.of D) ⟶ S} {T₁ : Over S}
    (κ : T₁ ⟶ Ov s₀) (h : APt (overO S) M (op T₁)) :
    ∃ κ₁ : T₁ ⟶ Ov (sp (cst D M) ≫ s₀), κ₁ ≫ ovHom (cst D M) rfl = κ ∧
      APt.res κ₁.op (eOf (sp (cst D M) ≫ s₀) (eU D M)) = h := by
  let ψ : D →+* Γ(T₁.left, ⊤) := (homSpecEquiv T₁.left (CommRingCat.of D) κ.left).hom
  let Ψ : AddMonoidAlgebra D M →+* Γ(T₁.left, ⊤) :=
    AddMonoidAlgebra.liftNCRingHom ψ h (fun _ _ => Commute.all _ _)
  let w : T₁.left ⟶ Spec (CommRingCat.of (AddMonoidAlgebra D M)) :=
    (homSpecEquiv T₁.left _).symm (CommRingCat.ofHom Ψ)
  have hw : homSpecEquiv T₁.left _ w = CommRingCat.ofHom Ψ := Equiv.apply_symm_apply _ _
  have hc : w ≫ sp (cst D M) = κ.left := by
    apply (homSpecEquiv T₁.left (CommRingCat.of D)).injective
    rw [hse_comp, hw]
    ext x
    change Ψ (AddMonoidAlgebra.single 0 x) = ψ x
    simp only [Ψ, AddMonoidAlgebra.liftNCRingHom]
    have e := AddMonoidAlgebra.liftNC_single
      (ψ : D →+ Γ(T₁.left, ⊤)) h (0 : M) x
    refine e.trans ?_
    have h1 : h (Multiplicative.ofAdd (0 : M)) = 1 := map_one h
    refine (congrArg (fun z => ψ x * z) h1).trans (mul_one _)
  refine ⟨Over.homMk w (by
    change w ≫ sp (cst D M) ≫ s₀ = T₁.hom
    rw [← Category.assoc, hc]
    exact Over.w κ), Over.OverMorphism.ext hc, MonoidHom.ext fun m => ?_⟩
  have := congrArg (fun k => k.hom (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1)) hw
  refine this.trans ?_
  change Ψ (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1) = h m
  simp [Ψ, AddMonoidAlgebra.liftNCRingHom]
  rfl

/-- An equivariant morphism out of the universal point is an attractor point. -/
noncomputable def attPtOf (l : (specUP N T s hs).P ⟶ X)
    (h₂ : sp (coactN (M := M) N Γ(T.left, ⊤)) ≫ s = sp (cst (RR N T) M) ≫ s)
    (hl : ovHom (coactN (M := M) N Γ(T.left, ⊤)) h₂ ≫ l =
      sm aX (eOf (sp (cst (RR N T) M) ≫ s) (eU (RR N T) M)) (ovHom (cst (RR N T) M) rfl ≫ l)) :
    AttractorPt aX N T :=
  (attractorPtEquivOfUniversal (act := aX) (specUP N T s hs)).symm ⟨l, by
    intro T₁ t h a
    let U := specUP N T s hs
    let s₁ := sp (cst (RR N T) M) ≫ s
    let r : Ov s₁ ⟶ U.P := ovHom (coactN (M := M) N Γ(T.left, ⊤)) h₂
    let c : Ov s₁ ⟶ U.P := ovHom (cst (RR N T) M) rfl
    obtain ⟨κ₁, h₁, he⟩ := exists_classify (M := M) (s₀ := s) (U.lift t a) h
    have hc : κ₁ ≫ c = U.lift t a := h₁
    have hπ : r ≫ U.π = c ≫ U.π := Over.OverMorphism.ext (hρπ N T)
    have hl₁ : κ₁ ≫ r = U.lift t (APt.toMagnet N h * a) := by
      refine U.uniq _ _ _ ?_ ?_
      · refine (Category.assoc κ₁ r U.π).trans ?_
        rw [hπ]
        exact (Category.assoc κ₁ c U.π).symm.trans ((congrArg (· ≫ U.π) hc).trans (U.lift_π t a))
      · have e : APt.res r.op U.u = APt.toMagnet N (eOf s₁ (eU (RR N T) M)) * APt.res c.op U.u :=
          res_coact N s hs s₁ rfl h₂
        refine (APt.res_comp r.op κ₁.op U.u).trans ?_
        rw [e, APt.res_mul, ← APt.toMagnet_res]
        have e₁ : APt.res κ₁.op (eOf s₁ (eU (RR N T) M)) = h := he
        have e₂ : APt.res κ₁.op (APt.res c.op U.u) = a :=
          (APt.res_comp c.op κ₁.op U.u).symm.trans
            ((congrArg (fun z : T₁ ⟶ U.P => APt.res z.op U.u) hc).trans (U.res_lift t a))
        rw [e₁, e₂]
    change U.lift t (APt.toMagnet N h * a) ≫ l = sm aX h (U.lift t a ≫ l)
    rw [← hl₁, ← hc]
    refine (Category.assoc κ₁ r l).trans ?_
    have e₃ : r ≫ l = sm aX (eOf s₁ (eU (RR N T) M)) (c ≫ l) := hl
    rw [e₃, comp_sm]
    have e₁ : APt.res κ₁.op (eOf s₁ (eU (RR N T) M)) = h := he
    rw [e₁]
    exact congrArg (sm aX h) (Category.assoc κ₁ c l).symm⟩

lemma attPtOf_app (l : (specUP N T s hs).P ⟶ X)
    (h₂ : sp (coactN (M := M) N Γ(T.left, ⊤)) ≫ s = sp (cst (RR N T) M) ≫ s)
    (hl : ovHom (coactN (M := M) N Γ(T.left, ⊤)) h₂ ≫ l =
      sm aX (eOf (sp (cst (RR N T) M) ≫ s) (eU (RR N T) M)) (ovHom (cst (RR N T) M) rfl ≫ l)) :
    (attPtOf N s hs l h₂ hl).app (specUP N T s hs).π (specUP N T s hs).u = l :=
  congrArg Subtype.val ((attractorPtEquivOfUniversal (act := aX) (specUP N T s hs)).apply_symm_apply ⟨l, _⟩)

end Equivariance

/-- A first order thickening of affine `S`-schemes. -/
structure IsAffineThick {T₀ T : Over S} (i : T₀ ⟶ T) : Prop where
  affine₀ : IsAffine T₀.left
  affine : IsAffine T.left
  surjective : Function.Surjective i.left.appTop.hom
  sq_zero : ∀ x y, i.left.appTop.hom x = 0 → i.left.appTop.hom y = 0 → x * y = 0

/-- An equivariant morphism of `S`-schemes, as an `EquivariantHom`. -/
def eqHom {X Y : Over S} {aX : AAction (overO S) M (yoneda.obj X)}
    {aY : AAction (overO S) M (yoneda.obj Y)} (g : X ⟶ Y)
    (hg : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X),
      sm aX h x ≫ g = sm aY h (x ≫ g)) : EquivariantHom aX aY where
  hom := yoneda.map g
  map_smul h x := hg h x

lemma π_sq {T₀ T : Over S} (i : T₀ ⟶ T) [IsAffine T₀.left] [IsAffine T.left] :
    magnetπ N T₀.left ≫ i.left =
      sp (AddMonoidAlgebra.mapRingHom N i.left.appTop.hom) ≫ magnetπ N T.left := by
  refine ext_of_isAffine ?_
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, magnetπ_appTop, magnetπ_appTop]
  ext x
  change (Scheme.ΓSpecIso _).inv.hom (AddMonoidAlgebra.single 0 _) =
    (sp _).appTop.hom ((Scheme.ΓSpecIso _).inv.hom (AddMonoidAlgebra.single 0 x))
  rw [sp_inv, AddMonoidAlgebra.mapRingHom_single]
  rfl

lemma π_thick {T₀ T : Over S} (i : T₀ ⟶ T) [IsAffine T₀.left] [IsAffine T.left] :
    magnetπ N T₀.left ≫ T₀.hom =
      sp (AddMonoidAlgebra.mapRingHom N i.left.appTop.hom) ≫ magnetπ N T.left ≫ T.hom := by
  rw [← Over.w i, ← Category.assoc, π_sq N i, Category.assoc]

section Group

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

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
  obtain ⟨l, hl₁, hl₂, hl₃⟩ := exists_equivariant_of_lift φ hφs hφq t ρ ρ₀ hρt hρφ
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

end Group

end AlgMag.SmoothSchemes
