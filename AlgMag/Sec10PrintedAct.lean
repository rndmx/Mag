/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedLifts

/-!
# `g · a = g a g⁻¹` on the test objects `D(P)`

Mayeux, *Algebraic Magnetism*, proof of Proposition 10.1. An `S`-action on an `S`-scheme is an action
of `D(M)` on the underlying scheme (the action of the printed proof, over `Spec ℤ`): `AbsAct`. For a
ring `W` with a coaction `ϱ` and `g : M → P`, the point `g` of `D(M)` acts on `Spec W[P]` by `sig ϱ g`,
and on morphisms `Spec W[P] → Y` by `act`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts

variable {M : Type u} [AddCommGroup M]

/-- The action on points, for all schemes. -/
structure AbsAct (M : Type u) [AddCommGroup M] (Y : Scheme.{u}) where
  /-- the action -/
  smul : ∀ {T : Scheme.{u}}, (Multiplicative M →* Γ(T, ⊤)) → (T ⟶ Y) → (T ⟶ Y)
  one_smul : ∀ {T : Scheme.{u}} (x : T ⟶ Y), smul 1 x = x
  mul_smul : ∀ {T : Scheme.{u}} (g h : Multiplicative M →* Γ(T, ⊤)) (x : T ⟶ Y),
    smul (g * h) x = smul g (smul h x)
  comp : ∀ {T T' : Scheme.{u}} (s : T' ⟶ T) (h : Multiplicative M →* Γ(T, ⊤)) (x : T ⟶ Y),
    s ≫ smul h x = smul (s.appTop.hom.toMonoidHom.comp h) (s ≫ x)

/-- The point of `D(M)` over `Spec R` given by a monoid map to `R`. -/
noncomputable def eG {R : Type u} [CommRing R] (e : Multiplicative M →* R) :
    Multiplicative M →* Γ(Spec (CommRingCat.of R), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom).comp e

lemma res_eG {R R₁ : Type u} [CommRing R] [CommRing R₁] (g : R →+* R₁) (e : Multiplicative M →* R) :
    (sp g).appTop.hom.toMonoidHom.comp (eG e) = eG (g.toMonoidHom.comp e) := by
  ext m
  have := congrArg (fun k => k.hom (e m)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact this.symm

lemma eG_mul {R : Type u} [CommRing R] (e e₁ : Multiplicative M →* R) :
    eG (e * e₁) = eG e * eG e₁ := by
  ext m
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom _ _

lemma eG_one {R : Type u} [CommRing R] : eG (1 : Multiplicative M →* R) = 1 := by
  ext m
  exact map_one (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

section Sig

variable {P P₁ : Type u} [AddCommGroup P] [AddCommGroup P₁]
variable {W W₁ : Type u} [CommRing W] [CommRing W₁]

/-- Maps out of `W[P]` agree when they agree on constants and on the group elements. -/
lemma rh_ext {E : Type u} [CommRing E] {r s : AddMonoidAlgebra W P →+* E}
    (h₁ : r.comp (cs W P) = s.comp (cs W P))
    (h₂ : ∀ k, r (AddMonoidAlgebra.single k 1) = s (AddMonoidAlgebra.single k 1)) : r = s := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single k c =>
    have e : (AddMonoidAlgebra.single k c : AddMonoidAlgebra W P) = cs W P c * AddMonoidAlgebra.single k 1 := by
      change _ = AddMonoidAlgebra.single 0 c * _
      rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rw [e, map_mul, map_mul, h₂]
    exact congrArg (· * _) (RingHom.congr_fun h₁ c)

/-- Group elements as a monoid map. -/
noncomputable def gl1 (W : Type u) [CommRing W] (g : M →+ P) : Multiplicative M →* AddMonoidAlgebra W P where
  toFun m := AddMonoidAlgebra.single (g (Multiplicative.toAdd m)) 1
  map_one' := by
    change AddMonoidAlgebra.single (g 0) 1 = 1
    rw [map_zero]
    rfl
  map_mul' x y := by
    rw [AddMonoidAlgebra.single_mul_single, mul_one]
    simp

/-- A ring map out of `W[P]`. -/
noncomputable def lft {E : Type u} [CommRing E] (c : W →+* E) (e : Multiplicative P →* E) :
    AddMonoidAlgebra W P →+* E :=
  AddMonoidAlgebra.liftNCRingHom c e (fun _ _ => Commute.all _ _)

lemma lft_cs {E : Type u} [CommRing E] (c : W →+* E) (e : Multiplicative P →* E) :
    (lft c e).comp (cs W P) = c := by
  refine RingHom.ext fun x => ?_
  change AddMonoidAlgebra.liftNC (c : W →+ E) e (AddMonoidAlgebra.single 0 x) = c x
  rw [AddMonoidAlgebra.liftNC_single]
  have h1 : e (Multiplicative.ofAdd (0 : P)) = 1 := map_one e
  exact (congrArg (fun z => c x * z) h1).trans (mul_one _)

lemma lft_of {E : Type u} [CommRing E] (c : W →+* E) (e : Multiplicative P →* E) (k : P) :
    lft c e (AddMonoidAlgebra.single k 1) = e (Multiplicative.ofAdd k) := by
  change AddMonoidAlgebra.liftNC (c : W →+ E) e (AddMonoidAlgebra.single k 1) = _
  rw [AddMonoidAlgebra.liftNC_single]
  simp

/-- Elements `g` as a monoid map to `W[P]`, in the variable. -/
noncomputable def idP (W : Type u) [CommRing W] (P : Type u) [AddCommGroup P] :
    Multiplicative P →* AddMonoidAlgebra W P := gl1 W (AddMonoidHom.id P)

/-- `g` acts on `W[P]`: `x e^p ↦ ϱ_g(x) e^p`. -/
noncomputable def sig (ϱ : W →+* AddMonoidAlgebra W M) (g : M →+ P) :
    AddMonoidAlgebra W P →+* AddMonoidAlgebra W P :=
  lft ((md W g).comp ϱ) (idP W P)

lemma sig_cs (ϱ : W →+* AddMonoidAlgebra W M) (g : M →+ P) :
    (sig ϱ g).comp (cs W P) = (md W g).comp ϱ := lft_cs _ _

lemma sig_of (ϱ : W →+* AddMonoidAlgebra W M) (g : M →+ P) (k : P) :
    sig ϱ g (AddMonoidAlgebra.single k 1) = AddMonoidAlgebra.single k 1 :=
  lft_of ((md W g).comp ϱ) (idP W P) k

lemma md_single {R : Type u} [CommRing R] (h : P →+ P₁) (k : P) (r : R) :
    md R h (AddMonoidAlgebra.single k r) = AddMonoidAlgebra.single (h k) r :=
  AddMonoidAlgebra.mapDomain_single

lemma mr_cs (w : W →+* W₁) : (mr P w).comp (cs W P) = (cs W₁ P).comp w :=
  RingHom.ext fun x => mr_single w 0 x

lemma md_cs (h : P →+ P₁) : (md W h).comp (cs W P) = cs W P₁ :=
  RingHom.ext fun x => by
    change md W h (AddMonoidAlgebra.single 0 x) = AddMonoidAlgebra.single 0 x
    rw [md_single, map_zero]

lemma mr_md (w : W →+* W₁) (h : P →+ P₁) : (mr P₁ w).comp (md W h) = (md W₁ h).comp (mr P w) := by
  refine rh_ext ?_ fun k => ?_
  · rw [RingHom.comp_assoc, md_cs, mr_cs, RingHom.comp_assoc, mr_cs, ← RingHom.comp_assoc, md_cs]
  · simp only [RingHom.comp_apply]
    rw [md_single, mr_single, mr_single, md_single, map_one]

/-- Naturality of `sig` in the ring. -/
lemma mr_sig (w : W →+* W₁) (ϱ : W →+* AddMonoidAlgebra W M) (ϱ₁ : W₁ →+* AddMonoidAlgebra W₁ M)
    (h : ϱ₁.comp w = (mr M w).comp ϱ) (g : M →+ P) :
    (mr P w).comp (sig ϱ g) = (sig ϱ₁ g).comp (mr P w) := by
  refine rh_ext ?_ fun k => ?_
  · have e₁ : (sig ϱ₁ g).comp ((cs W₁ P).comp w) = ((md W₁ g).comp ϱ₁).comp w := by
      rw [← RingHom.comp_assoc, sig_cs]
    rw [RingHom.comp_assoc, sig_cs, RingHom.comp_assoc, mr_cs, e₁]
    refine RingHom.ext fun x => ?_
    have h₃ := RingHom.congr_fun (mr_md (P := M) (P₁ := P) w g) (ϱ x)
    have h₂ := RingHom.congr_fun h x
    simp only [RingHom.comp_apply] at h₂ h₃ ⊢
    rw [h₂]
    exact h₃
  · simp only [RingHom.comp_apply]
    rw [sig_of, mr_single, map_one, sig_of]

/-- Naturality of `sig` in `P`. -/
lemma md_sig (ϱ : W →+* AddMonoidAlgebra W M) (u : P →+ P₁) (g : M →+ P) :
    (md W u).comp (sig ϱ g) = (sig ϱ (u.comp g)).comp (md W u) := by
  refine rh_ext ?_ fun k => ?_
  · rw [RingHom.comp_assoc, sig_cs, RingHom.comp_assoc, md_cs, sig_cs, ← RingHom.comp_assoc]
    congr 1
    refine rh_ext ?_ fun m => ?_
    · rw [RingHom.comp_assoc, md_cs, md_cs, md_cs]
    · simp only [RingHom.comp_apply]
      rw [md_single, md_single, md_single]
      rfl
  · simp only [RingHom.comp_apply]
    rw [sig_of, md_single, sig_of]

/-- The augmentation. -/
noncomputable def aug (W : Type u) [CommRing W] (M : Type u) [AddCommGroup M] :
    AddMonoidAlgebra W M →+* W := lft (RingHom.id W) 1

lemma md_zero (x : AddMonoidAlgebra W M) : md W (0 : M →+ P) x = cs W P (aug W M x) := by
  have : md W (0 : M →+ P) = (cs W P).comp (aug W M) := by
    refine rh_ext ?_ fun m => ?_
    · rw [md_cs, RingHom.comp_assoc, aug, lft_cs, RingHom.comp_id]
    · simp only [RingHom.comp_apply, aug]
      rw [md_single, lft_of]
      exact map_one (cs W P)
  exact RingHom.congr_fun this x

lemma sig_zero (ϱ : W →+* AddMonoidAlgebra W M) (hc : (aug W M).comp ϱ = RingHom.id W) :
    sig ϱ (0 : M →+ P) = RingHom.id _ := by
  refine rh_ext ?_ fun k => ?_
  · rw [sig_cs]
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, md_zero]
    rw [show aug W M (ϱ x) = x from RingHom.congr_fun hc x]
    rfl
  · rw [sig_of]; rfl

/-- `D(M)` on `D(M)`-variable: the ring map used for coassociativity. -/
lemma sig_comp (ϱ : W →+* AddMonoidAlgebra W M)
    (hco : ∀ x, mr M ϱ (ϱ x) = Lifts.diag W M (ϱ x)) (g g' : M →+ P) :
    (sig ϱ g).comp (sig ϱ g') = sig ϱ (g + g') := by
  let K : AddMonoidAlgebra (AddMonoidAlgebra W M) M →+* AddMonoidAlgebra W P :=
    lft (md W g) (gl1 W g')
  have h₁ : (sig ϱ g).comp (md W g') = K.comp (mr M ϱ) := by
    refine rh_ext ?_ fun m => ?_
    · rw [RingHom.comp_assoc, md_cs, sig_cs, RingHom.comp_assoc, mr_cs, ← RingHom.comp_assoc, lft_cs]
    · simp only [RingHom.comp_apply]
      rw [md_single, sig_of, mr_single, map_one]
      exact (lft_of (md W g) (gl1 W g') m).symm
  have h₂ : K.comp (Lifts.diag W M) = md W (g + g') := by
    refine rh_ext ?_ fun m => ?_
    · have e : (Lifts.diag W M).comp (cs W M) = (cs _ M).comp (cs W M) := RingHom.ext fun x => diag_cst x
      rw [RingHom.comp_assoc, e, ← RingHom.comp_assoc, lft_cs, md_cs, md_cs]
    · simp only [RingHom.comp_apply]
      rw [diag_single]
      have e : (AddMonoidAlgebra.single m (AddMonoidAlgebra.single m (1 : W)) :
          AddMonoidAlgebra (AddMonoidAlgebra W M) M) =
          cs _ M (AddMonoidAlgebra.single m 1) * AddMonoidAlgebra.single m 1 := by
        change _ = AddMonoidAlgebra.single 0 _ * _
        rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
      rw [e, map_mul]
      have e₂ := RingHom.congr_fun (lft_cs (md W g) (gl1 W g')) (AddMonoidAlgebra.single m 1)
      rw [RingHom.comp_apply] at e₂
      rw [e₂, lft_of, md_single, md_single]
      change AddMonoidAlgebra.single _ _ * AddMonoidAlgebra.single _ _ = _
      rw [AddMonoidAlgebra.single_mul_single, mul_one]
      rfl
  refine rh_ext ?_ fun k => ?_
  · rw [RingHom.comp_assoc, sig_cs, ← RingHom.comp_assoc, h₁, sig_cs, ← h₂]
    exact RingHom.ext fun x => congrArg K (hco x)
  · simp only [RingHom.comp_apply]
    rw [sig_of, sig_of, sig_of]

end Sig

section Act

variable {P P₁ : Type u} [AddCommGroup P] [AddCommGroup P₁]
variable {W W₁ : Type u} [CommRing W] [CommRing W₁] {Y Y₁ : Scheme.{u}}

/-- `g · ℓ = g_Y ∘ ℓ ∘ g⁻¹`. -/
noncomputable def act (ay : AbsAct M Y) (ϱ : W →+* AddMonoidAlgebra W M) (g : M →+ P)
    (l : Spec (CommRingCat.of (AddMonoidAlgebra W P)) ⟶ Y) :
    Spec (CommRingCat.of (AddMonoidAlgebra W P)) ⟶ Y :=
  ay.smul (eG (gl1 W g)) (sp (sig ϱ (-g)) ≫ l)

lemma res_gl1_mr (w : W →+* W₁) (g : M →+ P) :
    (mr P w).toMonoidHom.comp (gl1 W g) = gl1 W₁ g := by
  refine MonoidHom.ext fun m => ?_
  change mr P w (AddMonoidAlgebra.single _ 1) = _
  rw [mr_single, map_one]
  rfl

lemma res_gl1_md (u : P →+ P₁) (g : M →+ P) :
    (md W u).toMonoidHom.comp (gl1 W g) = gl1 W (u.comp g) := by
  refine MonoidHom.ext fun m => ?_
  change md W u (AddMonoidAlgebra.single _ 1) = _
  rw [md_single]
  rfl

lemma res_gl1_sig (ϱ : W →+* AddMonoidAlgebra W M) (g' g : M →+ P) :
    (sig ϱ g').toMonoidHom.comp (gl1 W g) = gl1 W g := by
  refine MonoidHom.ext fun m => ?_
  change sig ϱ g' (AddMonoidAlgebra.single _ 1) = _
  rw [sig_of]
  rfl

lemma gl1_add (g g' : M →+ P) : gl1 W (g + g') = gl1 W g * gl1 W g' := by
  refine MonoidHom.ext fun m => ?_
  change (AddMonoidAlgebra.single _ _ : AddMonoidAlgebra W P) =
    AddMonoidAlgebra.single _ _ * AddMonoidAlgebra.single _ _
  rw [AddMonoidAlgebra.single_mul_single, mul_one]
  rfl

lemma gl1_zero : gl1 W (0 : M →+ P) = 1 :=
  MonoidHom.ext fun m => rfl

/-- `act` on `W[P]`, ring naturality. -/
lemma act_mr (ay : AbsAct M Y) (w : W →+* W₁) (ϱ : W →+* AddMonoidAlgebra W M)
    (ϱ₁ : W₁ →+* AddMonoidAlgebra W₁ M) (h : ϱ₁.comp w = (mr M w).comp ϱ) (g : M →+ P)
    (l : Spec (CommRingCat.of (AddMonoidAlgebra W P)) ⟶ Y) :
    sp (mr P w) ≫ act ay ϱ g l = act ay ϱ₁ g (sp (mr P w) ≫ l) := by
  rw [act, ay.comp, res_eG, res_gl1_mr, act, ← Category.assoc (sp (sig ϱ₁ (-g))), ← sp_comp,
    ← mr_sig w ϱ ϱ₁ h, sp_comp, Category.assoc]

lemma act_md (ay : AbsAct M Y) (ϱ : W →+* AddMonoidAlgebra W M) (u : P →+ P₁) (g : M →+ P)
    (l : Spec (CommRingCat.of (AddMonoidAlgebra W P)) ⟶ Y) :
    sp (md W u) ≫ act ay ϱ g l = act ay ϱ (u.comp g) (sp (md W u) ≫ l) := by
  have e := md_sig ϱ u (-g)
  have e₂ : u.comp (-g) = -(u.comp g) := by ext; simp
  rw [e₂] at e
  rw [act, ay.comp, res_eG, res_gl1_md, act, ← Category.assoc (sp (sig ϱ (-(u.comp g)))), ← sp_comp,
    ← e, sp_comp, Category.assoc]

lemma act_add (ay : AbsAct M Y) (ϱ : W →+* AddMonoidAlgebra W M)
    (hco : ∀ x, mr M ϱ (ϱ x) = Lifts.diag W M (ϱ x)) (g g' : M →+ P)
    (l : Spec (CommRingCat.of (AddMonoidAlgebra W P)) ⟶ Y) :
    act ay ϱ (g + g') l = act ay ϱ g (act ay ϱ g' l) := by
  have e : sig ϱ (-(g + g')) = (sig ϱ (-g)).comp (sig ϱ (-g')) := by
    rw [sig_comp ϱ hco]
    congr 1
    ext; simp [add_comm]
  rw [act, act, act, gl1_add, eG_mul, ay.mul_smul, ay.comp, res_eG, res_gl1_sig, e, sp_comp,
    Category.assoc]

lemma act_zero (ay : AbsAct M Y) (ϱ : W →+* AddMonoidAlgebra W M)
    (hc : (aug W M).comp ϱ = RingHom.id W)
    (l : Spec (CommRingCat.of (AddMonoidAlgebra W P)) ⟶ Y) :
    act ay ϱ (0 : M →+ P) l = l := by
  rw [act, gl1_zero, eG_one, ay.one_smul, neg_zero, sig_zero ϱ hc, sp_id', Category.id_comp]

lemma act_comp_f (ay : AbsAct M Y) (ay₁ : AbsAct M Y₁) (f : Y ⟶ Y₁)
    (hf : ∀ {T : Scheme.{u}} (h : Multiplicative M →* Γ(T, ⊤)) (x : T ⟶ Y),
      ay.smul h x ≫ f = ay₁.smul h (x ≫ f))
    (ϱ : W →+* AddMonoidAlgebra W M) (g : M →+ P)
    (l : Spec (CommRingCat.of (AddMonoidAlgebra W P)) ⟶ Y) :
    act ay ϱ g l ≫ f = act ay₁ ϱ g (l ≫ f) := by
  rw [act, hf, act, Category.assoc]

/-- The universal point of `D(M)` over `Spec W[M]`. -/
noncomputable abbrev eUn (W : Type u) [CommRing W] (M : Type u) [AddCommGroup M] :
    Multiplicative M →* Γ(Spec (CommRingCat.of (AddMonoidAlgebra W M)), ⊤) :=
  eG (gl1 W (AddMonoidHom.id M))

/-- `x : Spec W → Y` equivariant. -/
def IsEq (ay : AbsAct M Y) (ϱ : W →+* AddMonoidAlgebra W M) (x : Spec (CommRingCat.of W) ⟶ Y) : Prop :=
  sp ϱ ≫ x = ay.smul (eUn W M) (sp (cs W M) ≫ x)

/-- An equivariant `x` is invariant at all `g`, by the action `g x g⁻¹`. -/
lemma act_of_isEq (ay : AbsAct M Y) (ϱ : W →+* AddMonoidAlgebra W M)
    (x : Spec (CommRingCat.of W) ⟶ Y) (hx : IsEq ay ϱ x) (g : M →+ P) :
    act ay ϱ g (sp (cs W P) ≫ x) = sp (cs W P) ≫ x := by
  have h₁ : sp (sig ϱ (-g)) ≫ sp (cs W P) ≫ x = ay.smul (eG (gl1 W (-g))) (sp (cs W P) ≫ x) := by
    rw [← Category.assoc, ← sp_comp, sig_cs, sp_comp, Category.assoc, hx, ay.comp, res_eG]
    have e₁ : (md W (-g)).toMonoidHom.comp (gl1 W (AddMonoidHom.id M)) = gl1 W (-g) :=
      (res_gl1_md (-g) (AddMonoidHom.id M))
    rw [e₁, ← Category.assoc, ← sp_comp, md_cs]
  rw [act, h₁, ← ay.mul_smul, ← eG_mul, ← gl1_add, add_neg_cancel, gl1_zero, eG_one, ay.one_smul]

/-- Conversely: invariance of the universal point gives equivariance. -/
lemma isEq_of_act (ay : AbsAct M Y) (ϱ : W →+* AddMonoidAlgebra W M)
    (x : Spec (CommRingCat.of W) ⟶ Y)
    (h : act ay ϱ (AddMonoidHom.id M) (sp (cs W M) ≫ x) = sp (cs W M) ≫ x) : IsEq ay ϱ x := by
  have h₀ := congrArg (fun z => sp (md W (-AddMonoidHom.id M)) ≫ z) h
  beta_reduce at h₀
  rw [act_md] at h₀
  have e₁ : (-AddMonoidHom.id M).comp (AddMonoidHom.id M) = -AddMonoidHom.id M := by ext; simp
  rw [e₁] at h₀
  have e₂ : sp (md W (-AddMonoidHom.id M)) ≫ sp (cs W M) ≫ x = sp (cs W M) ≫ x := by
    rw [← Category.assoc, ← sp_comp, md_cs]
  rw [e₂] at h₀
  -- `h₀ : act (-id) (cst ≫ x) = cst ≫ x`, i.e. `(-u) • (ϱ ≫ x) = cst ≫ x`
  have h₁ : sp (sig ϱ (-(-AddMonoidHom.id M))) ≫ sp (cs W M) ≫ x = sp ϱ ≫ x := by
    rw [← Category.assoc, ← sp_comp, sig_cs, neg_neg]
    have : (md W (AddMonoidHom.id M)).comp ϱ = ϱ := by
      have : md W (AddMonoidHom.id M) = RingHom.id _ := by
        refine rh_ext ?_ fun k => ?_
        · exact md_cs _
        · rw [md_single]; rfl
      rw [this, RingHom.id_comp]
    rw [this]
  rw [act, h₁] at h₀
  rw [IsEq]
  have h₂ := congrArg (fun z => ay.smul (eG (gl1 W (AddMonoidHom.id M))) z) h₀
  beta_reduce at h₂
  rw [← ay.mul_smul, ← eG_mul, ← gl1_add, add_neg_cancel, gl1_zero, eG_one, ay.one_smul] at h₂
  exact h₂

end Act

end AlgMag.Sec10Printed
