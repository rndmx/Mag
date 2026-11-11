/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedMain
import AlgMag.Sec10LiftsCor

/-!
# Corollary 10.3 for `X'` affine, along the printed proof

Mayeux, *Algebraic Magnetism*, Proposition 10.1 and Corollary 10.3. The signatures of
`AlgMag.Lifts.exists_equivariant_of_lift` (with a counit in addition) and
`AlgMag.SmoothSchemes.exists_equivariant_lift_spec`, proved by `exists_invariant_lift`: the integration
proof is not used.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1500000

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]

/-- An `S`-action on an `S`-scheme, as an action on the underlying scheme. -/
noncomputable def absSmul {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) {T : Scheme.{u}}
    (h : Multiplicative M →* Γ(T, ⊤)) (x : T ⟶ Y.left) : T ⟶ Y.left :=
  (sm aY (T := Over.mk (x ≫ Y.hom)) h (Over.homMk x rfl)).left

lemma abs_aux {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) {T₀ : Scheme.{u}} (x : T₀ ⟶ Y.left)
    (s : T₀ ⟶ S) (hs : x ≫ Y.hom = s) (h : Multiplicative M →* Γ(T₀, ⊤)) :
    (sm aY (T := Over.mk s) h (Over.homMk x hs)).left = absSmul aY h x := by
  subst hs
  rfl

lemma abs_eq {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) {T : Over S}
    (h : Multiplicative M →* Γ(T.left, ⊤)) (w : T ⟶ Y) :
    (sm aY (T := T) h w).left = absSmul aY h w.left := by
  exact abs_aux aY w.left T.hom (Over.w w) h

/-- The action on the underlying scheme. -/
noncomputable def absOf {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) : AbsAct M Y.left where
  smul := absSmul aY
  one_smul x := congrArg (fun k => k.left) (sm_one aY (T := Over.mk (x ≫ Y.hom)) (Over.homMk x rfl))
  mul_smul g h x := by
    have e := sm_sm aY (T := Over.mk (x ≫ Y.hom)) g h (Over.homMk x rfl)
    refine (congrArg (fun k => k.left) e.symm).trans ?_
    exact abs_eq aY (T := Over.mk (x ≫ Y.hom)) g _
  comp {T T'} s h x := by
    let j : Over.mk ((s ≫ x) ≫ Y.hom) ⟶ Over.mk (x ≫ Y.hom) := Over.homMk s (Category.assoc _ _ _).symm
    have e := comp_sm aY j h (Over.homMk x rfl)
    exact (congrArg (fun k => k.left) e).trans (abs_eq aY (T := Over.mk ((s ≫ x) ≫ Y.hom)) _ (j ≫ Over.homMk x rfl))

/-- **Proposition 10.1 / Corollary 10.3**, `X'` = `Spec A₁` affine, along the printed proof: the signature
of `exists_equivariant_of_lift`, with the counit of `ρ`. -/
theorem exists_equivariant_of_lift_printed {A₁ A : Type u} [CommRing A₁] [CommRing A]
    {ρ : A₁ →+* AddMonoidAlgebra A₁ M} (hc : (aug A₁ M).comp ρ = RingHom.id _) (φ : A₁ →+* A)
    (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (t : Spec (CommRingCat.of A₁) ⟶ S)
    (ρ' : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M) (hρρ : ρ' = ρ)
    (hρt : sp ρ' ≫ t = sp (cst A₁ M) ≫ t)
    (hρφ : ∀ a, AddMonoidAlgebra.mapRingHom M φ (ρ' a) = ρ₀ (φ a))
    (hco : ∀ a, AddMonoidAlgebra.mapRingHom M ρ' (ρ' a) = Lifts.diag A₁ M (ρ' a))
    {Y Z : Over S} (aY : AAction (overO S) M (yoneda.obj Y))
    (aZ : AAction (overO S) M (yoneda.obj Z)) (f : Y ⟶ Z)
    (hf : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ Y),
      sm aY h x ≫ f = sm aZ h (x ≫ f))
    (a : Ov (sp φ ≫ t) ⟶ Y) (b : Ov t ⟶ Z) (α : Ov t ⟶ Y)
    (hαa : ovHom φ rfl ≫ α = a) (hαb : α ≫ f = b)
    (h₀ρ : sp ρ₀ ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (h₀c : sp (cst A M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (ha : ovHom ρ₀ h₀ρ ≫ a = sm aY (eOf _ (eU A M)) (ovHom (cst A M) h₀c ≫ a))
    (hb : ovHom ρ' hρt ≫ b = sm aZ (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M)) (ovHom (cst A₁ M) rfl ≫ b)) :
    ∃ l : Ov t ⟶ Y, ovHom φ rfl ≫ l = a ∧ l ≫ f = b ∧
      ovHom ρ' hρt ≫ l = sm aY (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M)) (ovHom (cst A₁ M) rfl ≫ l) := by
  subst hρρ
  have hN : Function.Surjective φ := hs
  have h2 : RingHom.ker φ ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx z hz
    exact hq x z hx hz
  letI := Stacks.Smooth.kerModule hs h2
  have hNN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n := fun x n => by
    rw [Stacks.Smooth.kerModule_smul hs h2]
    rfl
  have hfa : ∀ {T : Scheme.{u}} (h : Multiplicative M →* Γ(T, ⊤)) (x : T ⟶ Y.left),
      (absOf aY).smul h x ≫ f.left = (absOf aZ).smul h (x ≫ f.left) := by
    intro T h x
    have e := congrArg (fun k => k.left) (hf (T := Over.mk (x ≫ Y.hom)) h (Over.homMk x rfl))
    exact e.trans (abs_eq aZ (T := Over.mk (x ≫ Y.hom)) h _)
  have hA : IsEq (absOf aY) ρ₀ a.left := by
    have e := congrArg (fun k => Over.Hom.left k) ha
    exact e.trans (abs_eq aY (T := Ov (sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)) _ _)
  have hB : IsEq (absOf aZ) ρ' b.left := by
    have e := congrArg (fun k => Over.Hom.left k) hb
    exact e.trans (abs_eq aZ (T := Ov (sp (cst A₁ M) ≫ t)) _ _)
  have hw : a.left ≫ f.left = sp φ ≫ b.left := by
    rw [← hαa, ← hαb]
    change (sp φ ≫ α.left) ≫ f.left = sp φ ≫ α.left ≫ f.left
    rw [Category.assoc]
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_invariant_lift hs hNN hq ρ' ρ₀ (RingHom.ext hρφ) hco hc f.left a.left b.left
    (absOf aY) (absOf aZ) hfa hA hB hw α.left (congrArg (fun k => k.left) hαa) (congrArg (fun k => k.left) hαb)
  have hlt : l ≫ Y.hom = t := by
    rw [← Over.w f, ← Category.assoc, h₂]
    exact Over.w b
  refine ⟨Over.homMk l hlt, Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂, Over.OverMorphism.ext ?_⟩
  exact h₃.trans (abs_eq aY (T := Ov (sp (cst A₁ M) ≫ t)) (eUn A₁ M)
    (ovHom (cst A₁ M) rfl ≫ Over.homMk l hlt)).symm

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
  have hμ : sp (Lifts.diag A₁ M) ≫ s₁ = s₂ := hμs t
  let τt : Ov s₂ ⟶ Ov s₁ := ovHom _ hτ
  let μt : Ov s₂ ⟶ Ov s₁ := ovHom _ hμ
  let c₂ : Ov s₂ ⟶ Ov s₁ := ovHom (cst _ M) rfl
  let eo := eOf s₂ (eU (AddMonoidAlgebra A₁ M) M)
  let ei := eOf s₂ ((cst (AddMonoidAlgebra A₁ M) M).toMonoidHom.comp (eU A₁ M))
  have hco : ∀ w, AddMonoidAlgebra.mapRingHom M ρ (ρ w) = Lifts.diag A₁ M (ρ w) := by
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
    have e₃ : sp (AddMonoidAlgebra.mapRingHom M ρ) ≫ sp ρ = sp (Lifts.diag A₁ M) ≫ sp ρ := by
      rw [hρ]
      exact congrArg (fun k => k.left) e₂
    rw [← sp_comp, ← sp_comp] at e₃
    exact fun w => RingHom.congr_fun (sp_injective e₃) w
  have hc : (aug A₁ M).comp ρ = RingHom.id _ := by
    have hj : sp (aug A₁ M) ≫ s₁ = t := by
      change sp (aug A₁ M) ≫ sp (cst A₁ M) ≫ t = t
      rw [← Category.assoc, ← sp_comp]
      have : (aug A₁ M).comp (cst A₁ M) = RingHom.id _ := aug_cs
      rw [this, sp_id', Category.id_comp]
    let j : Ov t ⟶ Ov s₁ := ovHom (aug A₁ M) hj
    have e₁₀ : APt.res j.op e₁ = 1 := (res_eOf _ _ _).trans (MonoidHom.ext fun m => by
      change (Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom (aug A₁ M (AddMonoidAlgebra.single _ 1)) = 1
      rw [aug_of, map_one])
    have e₂ : j ≫ c = 𝟙 _ := Over.OverMorphism.ext (by
      change sp (aug A₁ M) ≫ sp (cst A₁ M) = 𝟙 _
      rw [← sp_comp]
      have : (aug A₁ M).comp (cst A₁ M) = RingHom.id _ := aug_cs
      rw [this, sp_id'])
    have e₃ : j ≫ x₁ = 𝟙 _ := by
      change j ≫ sm a₁ e₁ c = _
      rw [comp_sm, e₁₀, e₂, sm_one]
    have e₄ : sp (aug A₁ M) ≫ sp ρ = 𝟙 _ := by
      rw [hρ]
      exact congrArg (fun k => k.left) e₃
    rw [← sp_comp] at e₄
    exact sp_injective (e₄.trans sp_id'.symm)
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
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_equivariant_of_lift_printed hc φ hs hq t ρ ρ₀ rfl hρt hρφ hco aY aZ f hf a b α
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

end AlgMag.Sec10Printed
