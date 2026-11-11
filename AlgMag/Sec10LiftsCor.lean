/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11Schemes

/-!
# Corollary 10.3 for schemes

Mayeux, *Algebraic Magnetism*, Corollary 10.3, schemes only, with `X'` affine (the printed statement
is false without it). Here `M` is any commutative group and no finiteness is needed on `X' → S`.
Formal smoothness of `Y → Z` is `Stacks.Smooth.FormallySmoothScheme`, which holds for smooth
morphisms by `Stacks.Smooth.formallySmoothScheme_of_smooth`.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.SmoothSchemes

open AlgMag.GB AlgMag.Lifts

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]

lemma sp_preimage {D E : Type u} [CommRing D] [CommRing E]
    (x : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of D)) :
    sp (Spec.preimage x).hom = x := by
  change Spec.map (CommRingCat.ofHom (Spec.preimage x).hom) = x
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- **Corollary 10.3** with `X'` given as `Spec A₁` and `X` as `Spec A`. -/
theorem exists_equivariant_lift_spec {A₁ A : Type u} [CommRing A₁] [CommRing A] (φ : A₁ →+* A)
    (hs : Function.Surjective φ) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (t : Spec (CommRingCat.of A₁) ⟶ S)
    (a₁ : AAction (overO S) M (yoneda.obj (Ov t)))
    (a₀ : AAction (overO S) M (yoneda.obj (Ov (sp φ ≫ t))))
    (hi : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ Ov (sp φ ≫ t)),
      sm a₀ h x ≫ ovHom φ rfl = sm a₁ h (x ≫ ovHom φ rfl))
    {Y Z : Over S} (aY : AAction (overO S) M (yoneda.obj Y))
    (aZ : AAction (overO S) M (yoneda.obj Z)) (f : Y ⟶ Z)
    (hfs : Stacks.Smooth.FormallySmoothScheme f.left)
    (hf : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ Y),
      sm aY h x ≫ f = sm aZ h (x ≫ f))
    (a : Ov (sp φ ≫ t) ⟶ Y) (b : Ov t ⟶ Z)
    (ha : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ Ov (sp φ ≫ t)),
      sm a₀ h x ≫ a = sm aY h (x ≫ a))
    (hb : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ Ov t),
      sm a₁ h x ≫ b = sm aZ h (x ≫ b))
    (w : a ≫ f = ovHom φ rfl ≫ b) :
    ∃ l : Ov t ⟶ Y, ovHom φ rfl ≫ l = a ∧ l ≫ f = b ∧
      ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ Ov t),
        sm a₁ h x ≫ l = sm aY h (x ≫ l) := by
  let s₁ := sp (cst A₁ M) ≫ t
  let e₁ := eOf s₁ (eU A₁ M)
  let c : Ov s₁ ⟶ Ov t := ovHom (cst A₁ M) rfl
  let x₁ : Ov s₁ ⟶ Ov t := sm a₁ e₁ c
  let ρ := (Spec.preimage x₁.left).hom
  have hρ : sp ρ = x₁.left := sp_preimage _
  have hρt : sp ρ ≫ t = s₁ := by rw [hρ]; exact Over.w x₁
  have hr : (ovHom ρ hρt : Ov s₁ ⟶ Ov t) = x₁ := Over.OverMorphism.ext hρ
  -- the coaction on `A`
  let φM := AddMonoidAlgebra.mapRingHom M φ
  let s₀ := sp φM ≫ s₁
  have h₀c : sp (cst A M) ≫ sp φ ≫ t = s₀ :=
    tri (sp_sq (RingHom.ext fun w => (map_cst φ w).symm)) t
  let e₀ := eOf s₀ (eU A M)
  let c₀ : Ov s₀ ⟶ Ov (sp φ ≫ t) := ovHom (cst A M) h₀c
  let x₀ : Ov s₀ ⟶ Ov (sp φ ≫ t) := sm a₀ e₀ c₀
  let ρ₀ := (Spec.preimage x₀.left).hom
  have hρ₀ : sp ρ₀ = x₀.left := sp_preimage _
  have h₀ρ : sp ρ₀ ≫ sp φ ≫ t = s₀ := by rw [hρ₀]; exact Over.w x₀
  have hr₀ : (ovHom ρ₀ h₀ρ : Ov s₀ ⟶ Ov (sp φ ≫ t)) = x₀ := Over.OverMorphism.ext hρ₀
  let rd : Ov s₀ ⟶ Ov s₁ := ovHom φM rfl
  have hrd : APt.res rd.op e₁ = e₀ := (res_eOf _ _ _).trans (eOf_congr _ (hof φ))
  have hcc : c₀ ≫ ovHom φ rfl = rd ≫ c := Over.OverMorphism.ext (sp_sq (RingHom.ext fun w => (map_cst φ w).symm))
  have hsq : rd ≫ x₁ = x₀ ≫ ovHom φ rfl := by
    change rd ≫ sm a₁ e₁ c = sm a₀ e₀ c₀ ≫ ovHom φ rfl
    rw [comp_sm, hrd, hi, hcc]
  have hρφ : ∀ w, AddMonoidAlgebra.mapRingHom M φ (ρ w) = ρ₀ (φ w) := by
    have e₂ : sp φM ≫ sp ρ = sp ρ₀ ≫ sp φ := by
      rw [hρ, hρ₀]
      exact congrArg (fun k => k.left) hsq
    rw [← sp_comp, ← sp_comp] at e₂
    exact fun w => RingHom.congr_fun (sp_injective e₂) w
  -- coassociativity
  let s₂ := sp (cst (AddMonoidAlgebra A₁ M) M) ≫ s₁
  have hτ : sp (AddMonoidAlgebra.mapRingHom M ρ) ≫ s₁ = s₂ := by
    change _ ≫ sp (cst A₁ M) ≫ t = _ ≫ sp (cst A₁ M) ≫ t
    rw [← Category.assoc, sp_sq (g₃ := ρ) (g₄ := cst _ M) (RingHom.ext fun x => map_cst ρ x),
      Category.assoc]
    exact congrArg (fun z => _ ≫ z) hρt
  have hμ : sp (diag A₁ M) ≫ s₁ = s₂ := hμs t
  let τt : Ov s₂ ⟶ Ov s₁ := ovHom _ hτ
  let μt : Ov s₂ ⟶ Ov s₁ := ovHom _ hμ
  let c₂ : Ov s₂ ⟶ Ov s₁ := ovHom (cst _ M) rfl
  let eo := eOf s₂ (eU (AddMonoidAlgebra A₁ M) M)
  let ei := eOf s₂ ((cst (AddMonoidAlgebra A₁ M) M).toMonoidHom.comp (eU A₁ M))
  have hco : ∀ w, AddMonoidAlgebra.mapRingHom M ρ (ρ w) = diag A₁ M (ρ w) := by
    have e₂ : τt ≫ x₁ = μt ≫ x₁ := by
      have h₁ : τt ≫ c = c₂ ≫ ovHom ρ hρt :=
        Over.OverMorphism.ext (sp_sq (RingHom.ext fun x => map_cst ρ x))
      have h₂ : μt ≫ c = c₂ ≫ c := Over.OverMorphism.ext (sp_sq (RingHom.ext fun x => diag_cst x))
      have r₁ : APt.res τt.op e₁ = eo := (res_eOf _ _ _).trans (eOf_congr _ (hof ρ))
      have r₂ : APt.res μt.op e₁ = ei * eo :=
        (res_eOf _ _ _).trans ((eOf_congr _ (hμe (A₁ := A₁) (M := M))).trans (eOf_mul _ _ _))
      have r₃ : APt.res c₂.op e₁ = ei := res_eOf _ _ _
      change τt ≫ sm a₁ e₁ c = μt ≫ sm a₁ e₁ c
      rw [comp_sm, comp_sm, r₁, r₂, h₁, h₂, hr]
      change sm a₁ eo (c₂ ≫ sm a₁ e₁ c) = _
      rw [comp_sm, r₃, sm_sm, mul_comm]
    have e₃ : sp (AddMonoidAlgebra.mapRingHom M ρ) ≫ sp ρ = sp (diag A₁ M) ≫ sp ρ := by
      rw [hρ]
      exact congrArg (fun k => k.left) e₂
    rw [← sp_comp, ← sp_comp] at e₃
    exact fun w => RingHom.congr_fun (sp_injective e₃) w
  -- the non equivariant lift
  obtain ⟨α₁, hα₁, hα₂⟩ := hfs (T := Spec (CommRingCat.of A)) (T' := Spec (CommRingCat.of A₁))
    inferInstance inferInstance (Spec.map (CommRingCat.ofHom φ))
    (Stacks.Smooth.isFirstOrderThickening_specMap _ hs (by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro x hx z hz
      exact hq x z hx hz)) a.left b.left (congrArg (fun k => k.left) w)
  let α : Ov t ⟶ Y := Over.homMk α₁ (by
    change α₁ ≫ Y.hom = t
    rw [← Over.w f, ← Category.assoc, hα₁]
    exact Over.w b)
  have ha' : ovHom ρ₀ h₀ρ ≫ a = sm aY e₀ (ovHom (cst A M) h₀c ≫ a) := by
    rw [hr₀]
    exact ha _ _
  have hb' : ovHom ρ hρt ≫ b = sm aZ e₁ (c ≫ b) := by
    rw [hr]
    exact hb _ _
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_equivariant_of_lift φ hs hq t ρ ρ₀ hρt hρφ hco aY aZ f hf a b α
    (Over.OverMorphism.ext hα₂) (Over.OverMorphism.ext hα₁) h₀ρ h₀c ha' hb'
  refine ⟨l, h₁, h₂, ?_⟩
  intro T h x
  obtain ⟨κ, hκ₁, hκ₂⟩ := exists_classify (M := M) x h
  have e₂ : sm a₁ h x = κ ≫ x₁ := by
    change _ = κ ≫ sm a₁ e₁ c
    rw [comp_sm]
    have : APt.res κ.op e₁ = h := hκ₂
    rw [this]
    exact congrArg _ hκ₁.symm
  rw [e₂, Category.assoc, ← hr, h₃, comp_sm]
  have : APt.res κ.op e₁ = h := hκ₂
  rw [this, ← Category.assoc]
  exact congrArg (fun z => sm aY h (z ≫ l)) hκ₁

/-- Transport of an action along an isomorphism. -/
noncomputable def transportAction {X X₁ : Over S} (e : X ≅ X₁)
    (a : AAction (overO S) M (yoneda.obj X₁)) : AAction (overO S) M (yoneda.obj X) where
  smul {U} h x := (a.smul (U := U) h ((show unop U ⟶ X from x) ≫ e.hom) : unop U ⟶ X₁) ≫ e.inv
  one_smul {U} x := by
    change sm a (T := unop U) 1 ((show unop U ⟶ X from x) ≫ e.hom) ≫ e.inv = x
    rw [sm_one]
    simp
  mul_smul {U} g h x := by
    change sm a (T := unop U) (g * h) ((show unop U ⟶ X from x) ≫ e.hom) ≫ e.inv =
      sm a (T := unop U) g ((sm a (T := unop U) h ((show unop U ⟶ X from x) ≫ e.hom) ≫ e.inv) ≫ e.hom) ≫ e.inv
    rw [Category.assoc, e.inv_hom_id, Category.comp_id, sm_sm]
  map_smul {U V} f h x := by
    change f.unop ≫ sm a (T := unop U) h ((show unop U ⟶ X from x) ≫ e.hom) ≫ e.inv =
      sm a (T := unop V) (APt.res f h) ((f.unop ≫ (show unop U ⟶ X from x)) ≫ e.hom) ≫ e.inv
    rw [← Category.assoc, Category.assoc f.unop]
    exact congrArg (· ≫ e.inv) (a.map_smul f h _)

lemma transport_apply {X X₁ : Over S} (e : X ≅ X₁) (a : AAction (overO S) M (yoneda.obj X₁))
    {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X) :
    sm (transportAction e a) h x = sm a h (x ≫ e.hom) ≫ e.inv := rfl

lemma transport_hom {X X₁ : Over S} (e : X ≅ X₁) (a : AAction (overO S) M (yoneda.obj X₁))
    {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X) :
    sm (transportAction e a) h x ≫ e.hom = sm a h (x ≫ e.hom) := by
  rw [transport_apply, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- **Corollary 10.3**, schemes only, `X₁` (the paper's `X'`) affine. `M` is any commutative group.
The thickening is given on global sections. There exists an equivariant morphism filling the square. -/
theorem exists_equivariant_lift_scheme {X X₁ Y Z : Over S}
    (aX : AAction (overO S) M (yoneda.obj X)) (aX₁ : AAction (overO S) M (yoneda.obj X₁))
    (aY : AAction (overO S) M (yoneda.obj Y)) (aZ : AAction (overO S) M (yoneda.obj Z))
    (i : X ⟶ X₁) (hi : IsAffineThick i)
    (hie : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X),
      sm aX h x ≫ i = sm aX₁ h (x ≫ i))
    (f : Y ⟶ Z) (hfs : Stacks.Smooth.FormallySmoothScheme f.left)
    (hf : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ Y),
      sm aY h x ≫ f = sm aZ h (x ≫ f))
    (a : X ⟶ Y) (ha : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X),
      sm aX h x ≫ a = sm aY h (x ≫ a))
    (b : X₁ ⟶ Z) (hb : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X₁),
      sm aX₁ h x ≫ b = sm aZ h (x ≫ b))
    (w : a ≫ f = i ≫ b) :
    ∃ l : X₁ ⟶ Y, i ≫ l = a ∧ l ≫ f = b ∧
      ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X₁),
        sm aX₁ h x ≫ l = sm aY h (x ≫ l) := by
  have := hi.affine₀
  have := hi.affine
  let φ := i.left.appTop.hom
  let t : Spec (CommRingCat.of Γ(X₁.left, ⊤)) ⟶ S := X₁.left.isoSpec.inv ≫ X₁.hom
  let e₁ : Ov t ≅ X₁ := Over.isoMk X₁.left.isoSpec.symm rfl
  have hee : sp φ ≫ X₁.left.isoSpec.inv = X.left.isoSpec.inv ≫ i.left :=
    Scheme.isoSpec_inv_naturality i.left
  let e₀ : Ov (sp φ ≫ t) ≅ X := Over.isoMk X.left.isoSpec.symm (by
    change X.left.isoSpec.inv ≫ X.hom = sp φ ≫ X₁.left.isoSpec.inv ≫ X₁.hom
    rw [← Category.assoc, hee, Category.assoc, Over.w i])
  let j₀ : Ov (sp φ ≫ t) ⟶ Ov t := ovHom φ rfl
  have hii : j₀ ≫ e₁.hom = e₀.hom ≫ i := Over.OverMorphism.ext hee
  have hie₂ : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ Ov (sp φ ≫ t)),
      sm (transportAction e₀ aX) h x ≫ j₀ = sm (transportAction e₁ aX₁) h (x ≫ j₀) := by
    intro T h x
    refine (cancel_mono e₁.hom).1 ?_
    have l : (sm (transportAction e₀ aX) h x ≫ j₀) ≫ e₁.hom = sm aX₁ h ((x ≫ e₀.hom) ≫ i) := by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => _ ≫ z) hii).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ i) (transport_hom e₀ aX h x)).trans ?_
      exact hie h _
    have r : sm (transportAction e₁ aX₁) h (x ≫ j₀) ≫ e₁.hom = sm aX₁ h ((x ≫ e₀.hom) ≫ i) := by
      refine (transport_hom e₁ aX₁ h _).trans (congrArg _ ?_)
      refine (Category.assoc _ _ _).trans ?_
      exact (congrArg (fun z => x ≫ z) hii).trans (Category.assoc _ _ _).symm
    exact l.trans r.symm
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_equivariant_lift_spec φ hi.surjective hi.sq_zero t
    (transportAction e₁ aX₁) (transportAction e₀ aX) hie₂
    aY aZ f hfs hf (e₀.hom ≫ a) (e₁.hom ≫ b)
    (fun {T} h x => by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ a) (transport_hom e₀ aX h x)).trans ?_
      refine (ha h _).trans (congrArg _ (Category.assoc _ _ _)))
    (fun {T} h x => by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ b) (transport_hom e₁ aX₁ h x)).trans ?_
      refine (hb h _).trans (congrArg _ (Category.assoc _ _ _)))
    (by
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z => e₀.hom ≫ z) w).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ b) hii.symm).trans (Category.assoc _ _ _))
  refine ⟨e₁.inv ≫ l, ?_, ?_, ?_⟩
  · refine (cancel_epi e₀.hom).1 ?_
    have e₄ : e₀.hom ≫ i ≫ e₁.inv = j₀ :=
      (Category.assoc e₀.hom i e₁.inv).symm.trans ((congrArg (· ≫ e₁.inv) hii.symm).trans
        ((Category.assoc _ _ _).trans ((congrArg (fun z => j₀ ≫ z) e₁.hom_inv_id).trans
          (Category.comp_id _))))
    calc e₀.hom ≫ i ≫ e₁.inv ≫ l = (e₀.hom ≫ i ≫ e₁.inv) ≫ l := by simp only [Category.assoc]
      _ = j₀ ≫ l := congrArg (· ≫ l) e₄
      _ = e₀.hom ≫ a := h₁
  · rw [Category.assoc, h₂, ← Category.assoc, e₁.inv_hom_id, Category.id_comp]
  · intro T h x
    have e₃ := h₃ h (x ≫ e₁.inv)
    have e₂ : sm (transportAction e₁ aX₁) h (x ≫ e₁.inv) = sm aX₁ h x ≫ e₁.inv := by
      rw [transport_apply, Category.assoc, e₁.inv_hom_id, Category.comp_id]
    rw [e₂, Category.assoc] at e₃
    rw [e₃, Category.assoc]

end AlgMag.SmoothSchemes
