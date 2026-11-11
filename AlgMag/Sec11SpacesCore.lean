/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesBase

/-!
# Equivariant lifts over an affine thickening, for algebraic spaces

Mayeux, *Algebraic Magnetism*, Corollary 10.3, with `X'` affine (the printed statement is false
without it). This is `AlgMag.Lifts.exists_equivariant_of_lift`, with elements of a functor in place
of morphisms to a scheme, and Stacks 07SY in place of the push-out in schemes. The targets are
algebraic spaces.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommMonoid M]

instance srAvg {D D₀ : Type u} [CommRing D] [CommRing D₀] [SR B D₀] [SR B D] [SM B M]
    (φ : D →+* D₀) : SR B (avgRing (M := M) φ) := sr_subring _

variable (B hS) in
/-- The point of `𝔸(M)` over `Spec R` given by a monoid map to `R`. -/
noncomputable def eS {R : Type u} [CommRing R] [SR B R] (s : Spec (CommRingCat.of R) ⟶ S)
    (e : Multiplicative M →* R) : APt (fppfO B S hS) M (op (Sv B hS s)) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom).comp e

lemma res_eS {R R₁ : Type u} [CommRing R] [CommRing R₁] [SR B R] [SR B R₁] (g : R →+* R₁)
    {s : Spec (CommRingCat.of R) ⟶ S} {s₁ : Spec (CommRingCat.of R₁) ⟶ S} (h : sp g ≫ s = s₁)
    (e : Multiplicative M →* R) :
    APt.res (svHom B hS g h).op (eS B hS s e) = eS B hS s₁ (g.toMonoidHom.comp e) := by
  ext m
  have := congrArg (fun k => k.hom (e m))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact this.symm

lemma eS_congr {R : Type u} [CommRing R] [SR B R] (s : Spec (CommRingCat.of R) ⟶ S)
    {e e₁ : Multiplicative M →* R} (h : e = e₁) : eS B hS s e = eS B hS s e₁ := by rw [h]

lemma eS_mul {R : Type u} [CommRing R] [SR B R] (s : Spec (CommRingCat.of R) ⟶ S)
    (e e₁ : Multiplicative M →* R) : eS B hS s (e * e₁) = eS B hS s e * eS B hS s e₁ := by
  ext m
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom _ _

section Act

variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (aY : AAction (fppfO B S hS) M P)

/-- The action on sections over an object of the site. -/
abbrev ss {T : BigFppfOver B S hS} (h : APt (fppfO B S hS) M (op T)) (x : P.obj (op T)) :
    P.obj (op T) := aY.smul h x

lemma pb_ss {T T₁ : BigFppfOver B S hS} (g : T₁ ⟶ T) (h : APt (fppfO B S hS) M (op T))
    (x : P.obj (op T)) : pb P g (ss aY h x) = ss aY (APt.res g.op h) (pb P g x) :=
  aY.map_smul g.op h x

lemma ss_ss {T : BigFppfOver B S hS} (h k : APt (fppfO B S hS) M (op T)) (x : P.obj (op T)) :
    ss aY h (ss aY k x) = ss aY (h * k) x := (aY.mul_smul h k x).symm

end Act

section Avg

variable {A₁ A : Type u} [CommRing A₁] [CommRing A] [SR B A₁] [SR B A] [SM B M]

variable (B hS) in
/-- `Spec D[M] → Spec (avgRing φ)` in the site. -/
noncomputable abbrev pV (φ : A₁ →+* A) (t : Spec (CommRingCat.of A₁) ⟶ S) :
    Sv B hS (sp (cst A₁ M) ≫ t) ⟶ Sv B hS (sU (M := M) φ t) := svHom B hS (R := avgRing (M := M) φ) (avgSnd (M := M) φ) (hP (M := M) φ t)

variable (B hS) in
/-- `Spec D₀ → Spec (avgRing φ)` in the site. -/
noncomputable abbrev qV (φ : A₁ →+* A) (t : Spec (CommRingCat.of A₁) ⟶ S) :
    Sv B hS (sp φ ≫ t) ⟶ Sv B hS (sU (M := M) φ t) := svHom B hS (R := avgRing (M := M) φ) (avgFst (M := M) φ) (hQ (M := M) φ t)

lemma avgGlue (φ : A₁ →+* A) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (t : Spec (CommRingCat.of A₁) ⟶ S)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP' : IsAlgebraicSpace B S hS P)
    (β : P.obj (op (Sv B hS (sp (cst A₁ M) ≫ t)))) (a : P.obj (op (Sv B hS (sp φ ≫ t))))
    (h₀c : sp (cst A M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (h : pb P (svHom B hS (AddMonoidAlgebra.mapRingHom M φ) rfl) β = pb P (svHom B hS (cst A M) h₀c) a) :
    ∃! x : P.obj (op (Sv B hS (sU (M := M) φ t))), pb P (pV B hS φ t) x = β ∧
      pb P (qV B hS φ t) x = a :=
  glue (milnor_avg φ hs) (avgFst_surjective φ hs) (fun y hy => ker_map_lift φ y hy)
    (map_sq_zero φ hq) (hP φ t) (hQ φ t) rfl h₀c P hP' β a h

/-- Equality of sections over `Spec (avgRing φ)`. -/
lemma avg_ext (φ : A₁ →+* A) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (t : Spec (CommRingCat.of A₁) ⟶ S)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP' : IsAlgebraicSpace B S hS P)
    {x y : P.obj (op (Sv B hS (sU (M := M) φ t)))}
    (e₁ : pb P (pV B hS φ t) x = pb P (pV B hS φ t) y)
    (e₂ : pb P (qV B hS φ t) x = pb P (qV B hS φ t) y) : x = y := by
  have h₀c : sp (cst A M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t :=
    tri (sp_sq (RingHom.ext fun w => (map_cst φ w).symm)) t
  have sq : svHom B hS (AddMonoidAlgebra.mapRingHom M φ) rfl ≫ pV B hS φ t =
      svHom B hS (cst A M) h₀c ≫ qV B hS φ t :=
    site_ext (sp_sq (RingHom.ext fun p => avg_prop φ p))
  exact (avgGlue φ hs hq t hP' _ _ h₀c (pb_sq P sq x)).unique ⟨rfl, rfl⟩ ⟨e₁.symm, e₂.symm⟩

end Avg

section Main

variable {A₁ A : Type u} [CommRing A₁] [CommRing A] [SR B A₁] [SR B A] [SM B M]

end Main

section Group

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]
variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable {A₁ A : Type u} [CommRing A₁] [CommRing A] [SR B A₁] [SR B A] [SM B M]

/-- The inverse point. -/
noncomputable def pinvS {U : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M U) :
    APt (fppfO B S hS) M U := h.comp invMonoidHom

lemma pinvS_mul_self {U : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M U) :
    pinvS h * h = 1 := by
  have : ∀ n : Multiplicative M, h n⁻¹ * h n = 1 := fun n => by
    rw [← map_mul, inv_mul_cancel, map_one]
  ext m
  exact this _

lemma pinvS_mul {U : (BigFppfOver B S hS)ᵒᵖ} (h k : APt (fppfO B S hS) M U) :
    pinvS (h * k) = pinvS h * pinvS k := by
  ext m; rfl

lemma res_pinvS {U V : (BigFppfOver B S hS)ᵒᵖ} (g : U ⟶ V) (h : APt (fppfO B S hS) M U) :
    APt.res g (pinvS h) = pinvS (APt.res g h) := rfl

variable (aY : AAction (fppfO B S hS) M P) in
lemma ss_pinv_ss {T : BigFppfOver B S hS} (h : APt (fppfO B S hS) M (op T)) (x : P.obj (op T)) :
    ss aY (pinvS h) (ss aY h x) = x := by
  rw [ss_ss, pinvS_mul_self]
  exact aY.one_smul x

variable (B hS) in
/-- The integral `Spec D → Spec (avgRing φ)` in the site. -/
noncomputable abbrev iV (φ : A₁ →+* A) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (t : Spec (CommRingCat.of A₁) ⟶ S) : Sv B hS t ⟶ Sv B hS (sU (M := M) φ t) :=
  svHom B hS (R := avgRing (M := M) φ) (avgInt (M := M) φ hq) (hI (M := M) φ hq t)

/-- The first order `★` identity: `e₂⁻¹ • (β ∘ τ) = β ∘ μ` for `β = e⁻¹ • (α ∘ ρ)`. -/
lemma star_identity (t : Spec (CommRingCat.of A₁) ⟶ S)
    (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (hρt : sp ρ ≫ t = sp (cst A₁ M) ≫ t)
    (hco : ∀ a, AddMonoidAlgebra.mapRingHom M ρ (ρ a) = diag A₁ M (ρ a))
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (aY : AAction (fppfO B S hS) M P)
    (α : P.obj (op (Sv B hS t))) :
    ss aY (pinvS (eS B hS (sp (cst (AddMonoidAlgebra A₁ M) M) ≫ sp (cst A₁ M) ≫ t)
        ((cst (AddMonoidAlgebra A₁ M) M).toMonoidHom.comp (eU A₁ M))))
      (pb P (svHom B hS (AddMonoidAlgebra.mapRingHom M ρ) (hτs t ρ hρt))
        (ss aY (pinvS (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M))) (pb P (svHom B hS ρ hρt) α))) =
    pb P (svHom B hS (diag A₁ M) (hμs t))
        (ss aY (pinvS (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M))) (pb P (svHom B hS ρ hρt) α)) := by
  have hx : pb P (svHom B hS (AddMonoidAlgebra.mapRingHom M ρ) (hτs t ρ hρt)) (pb P (svHom B hS ρ hρt) α) =
      pb P (svHom B hS (diag A₁ M) (hμs t)) (pb P (svHom B hS ρ hρt) α) :=
    pb_sq P (u := svHom B hS (AddMonoidAlgebra.mapRingHom M ρ) (hτs t ρ hρt)) (v := svHom B hS ρ hρt)
      (w := svHom B hS (diag A₁ M) (hμs t)) (x := svHom B hS ρ hρt)
      (site_ext (sp_sq (RingHom.ext hco))) α
  rw [pb_ss, pb_ss, res_pinvS, res_pinvS, res_eS, res_eS, hof, hμe, eS_mul, ss_ss, pinvS_mul, hx]

/-- The equivariance step. -/
lemma equivariance_step (φ : A₁ →+* A) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (t : Spec (CommRingCat.of A₁) ⟶ S)
    (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
    (hρt : sp ρ ≫ t = sp (cst A₁ M) ≫ t)
    (hρφ : ∀ a, AddMonoidAlgebra.mapRingHom M φ (ρ a) = ρ₀ (φ a))
    (hco : ∀ a, AddMonoidAlgebra.mapRingHom M ρ (ρ a) = diag A₁ M (ρ a))
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP' : IsAlgebraicSpace B S hS P)
    (aY : AAction (fppfO B S hS) M P)
    (a : P.obj (op (Sv B hS (sp φ ≫ t)))) (α : P.obj (op (Sv B hS t)))
    (h₀ρ : sp ρ₀ ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (h₀c : sp (cst A M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (ha : pb P (svHom B hS ρ₀ h₀ρ) a = ss aY (eS B hS _ (eU A M)) (pb P (svHom B hS (cst A M) h₀c) a))
    (βt : P.obj (op (Sv B hS (sU (M := M) φ t))))
    (hβ : pb P (pV B hS φ t) βt =
      ss aY (pinvS (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M))) (pb P (svHom B hS ρ hρt) α))
    (hβa : pb P (qV B hS φ t) βt = a) :
    pb P (svHom B hS ρ hρt) (pb P (iV B hS φ hq t) βt) =
      ss aY (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M))
        (pb P (svHom B hS (cst A₁ M) rfl) (pb P (iV B hS φ hq t) βt)) := by
  have hs₂ := map_surjective (M := M) φ hs
  have hq₂ := map_sq_zero (M := M) φ hq
  let φ₂ := AddMonoidAlgebra.mapRingHom M φ
  let t₂ := sp (cst A₁ M) ≫ t
  let τU : Sv B hS (sU φ₂ t₂) ⟶ Sv B hS (sU (M := M) φ t) :=
    svHom B hS (τ₂ φ ρ ρ₀ hρφ) (hτ₂ φ t ρ ρ₀ hρt hρφ)
  let μU : Sv B hS (sU φ₂ t₂) ⟶ Sv B hS (sU (M := M) φ t) :=
    svHom B hS (μ₂ (M := M) φ) (hμ₂ φ t)
  let c₂ := avgCst (M := M) φ₂
  let e₂U := eS B hS (sU φ₂ t₂) (c₂.toMonoidHom.comp (eU A₁ M))
  have hLR : ss aY (pinvS e₂U) (pb P τU βt) = pb P μU βt := by
    refine avg_ext _ hs₂ hq₂ _ hP' ?_ ?_
    · have e₁ : APt.res (pV (M := M) B hS φ₂ t₂).op e₂U =
          eS B hS (sp (cst (AddMonoidAlgebra A₁ M) M) ≫ sp (cst A₁ M) ≫ t)
            ((cst (AddMonoidAlgebra A₁ M) M).toMonoidHom.comp (eU A₁ M)) := res_eS _ _ _
      have e₂ := pb_sq P (u := pV (M := M) B hS φ₂ t₂) (v := τU)
        (w := svHom B hS (AddMonoidAlgebra.mapRingHom M ρ) (hτs t ρ hρt)) (x := pV (M := M) B hS φ t)
        (site_ext (sp_sq rfl)) βt
      have e₃ := pb_sq P (u := pV (M := M) B hS φ₂ t₂) (v := μU)
        (w := svHom B hS (diag A₁ M) (hμs t)) (x := pV (M := M) B hS φ t)
        (site_ext (sp_sq rfl)) βt
      refine (pb_ss aY _ _ _).trans ?_
      rw [res_pinvS, e₁, e₂, e₃, hβ]
      exact star_identity t ρ hρt hco aY α
    · have e₁ : APt.res (qV (M := M) B hS φ₂ t₂).op e₂U =
          eS B hS (sp φ₂ ≫ sp (cst A₁ M) ≫ t) (eU A M) :=
        (res_eS _ _ _).trans (eS_congr _ (hof φ))
      have e₂ := pb_sq P (u := qV (M := M) B hS φ₂ t₂) (v := τU)
        (w := svHom B hS ρ₀ h₀ρ) (x := qV (M := M) B hS φ t) (site_ext (sp_sq rfl)) βt
      have e₃ := pb_sq P (u := qV (M := M) B hS φ₂ t₂) (v := μU)
        (w := svHom B hS (cst A M) h₀c) (x := qV (M := M) B hS φ t) (site_ext (sp_sq rfl)) βt
      refine (pb_ss aY _ _ _).trans ?_
      rw [res_pinvS, e₁, e₂, e₃, hβa, ha]
      exact ss_pinv_ss aY _ _
  have hfin := congrArg (fun z => pb P (iV (M := M) B hS φ₂ hq₂ t₂) z) hLR
  have eJ : APt.res (iV (M := M) B hS φ₂ hq₂ t₂).op e₂U =
      eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M) := (res_eS _ _ _).trans (eS_congr _ (by
        refine MonoidHom.ext fun m => ?_
        exact RingHom.congr_fun (avgInt_cst _ hq₂) _))
  have e₂ := pb_sq P (u := iV (M := M) B hS φ₂ hq₂ t₂) (v := τU)
    (w := svHom B hS ρ hρt) (x := iV (M := M) B hS φ hq t)
    (site_ext (sp_sq (RingHom.ext fun p =>
      AddMonoidAlgebra.coeff_mapRingHom ρ (avgSnd φ p) 0))) βt
  have e₃ := pb_sq P (u := iV (M := M) B hS φ₂ hq₂ t₂) (v := μU)
    (w := svHom B hS (cst A₁ M) rfl) (x := iV (M := M) B hS φ hq t)
    (site_ext (sp_sq (RingHom.ext fun p => coeff_diag (avgSnd φ p)))) βt
  have h₂ : ss aY (pinvS (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M)))
      (pb P (svHom B hS ρ hρt) (pb P (iV B hS φ hq t) βt)) =
      pb P (svHom B hS (cst A₁ M) rfl) (pb P (iV B hS φ hq t) βt) := by
    refine Eq.trans ?_ (hfin.trans e₃)
    refine Eq.trans ?_ (pb_ss aY _ _ _).symm
    rw [res_pinvS, eJ, e₂]
  rw [← h₂, ss_ss, mul_comm, pinvS_mul_self]
  exact (aY.one_smul _).symm

/-- **Integration over `D(M)`, for algebraic spaces.** From any lift `α` over the affine `Spec A₁`
of a square with equivariant sides, the integral of `g⁻¹ α g` is an equivariant lift. -/
theorem exists_equivariant_of_lift (φ : A₁ →+* A) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (t : Spec (CommRingCat.of A₁) ⟶ S)
    (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
    (hρt : sp ρ ≫ t = sp (cst A₁ M) ≫ t)
    (hρφ : ∀ a, AddMonoidAlgebra.mapRingHom M φ (ρ a) = ρ₀ (φ a))
    (hco : ∀ a, AddMonoidAlgebra.mapRingHom M ρ (ρ a) = diag A₁ M (ρ a))
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP' : IsAlgebraicSpace B S hS P)
    (hQ' : IsAlgebraicSpace B S hS Q)
    {aY : AAction (fppfO B S hS) M P} {aZ : AAction (fppfO B S hS) M Q} (f : EquivariantHom aY aZ)
    (a : P.obj (op (Sv B hS (sp φ ≫ t)))) (b : Q.obj (op (Sv B hS t))) (α : P.obj (op (Sv B hS t)))
    (hαa : pb P (svHom B hS φ rfl) α = a) (hαb : f.hom.app _ α = b)
    (h₀ρ : sp ρ₀ ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (h₀c : sp (cst A M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (ha : pb P (svHom B hS ρ₀ h₀ρ) a = ss aY (eS B hS _ (eU A M)) (pb P (svHom B hS (cst A M) h₀c) a))
    (hb : pb Q (svHom B hS ρ hρt) b =
      ss aZ (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M)) (pb Q (svHom B hS (cst A₁ M) rfl) b)) :
    ∃ l : P.obj (op (Sv B hS t)), pb P (svHom B hS φ rfl) l = a ∧ f.hom.app _ l = b ∧
      pb P (svHom B hS ρ hρt) l =
        ss aY (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M)) (pb P (svHom B hS (cst A₁ M) rfl) l) := by
  have nat : ∀ {T T₁ : BigFppfOver B S hS} (u : T₁ ⟶ T) (x : P.obj (op T)),
      f.hom.app _ (pb P u x) = pb Q u (f.hom.app _ x) := fun u x =>
    NatTrans.naturality_apply f.hom u.op x
  let E := eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M)
  let β₀ := ss aY (pinvS E) (pb P (svHom B hS ρ hρt) α)
  have hrd : pb P (svHom B hS (AddMonoidAlgebra.mapRingHom M φ) rfl) β₀ =
      pb P (svHom B hS (cst A M) h₀c) a := by
    have h1 : pb P (svHom B hS (AddMonoidAlgebra.mapRingHom M φ) rfl) (pb P (svHom B hS ρ hρt) α) =
        pb P (svHom B hS ρ₀ h₀ρ) a := by
      have sq : svHom B hS (AddMonoidAlgebra.mapRingHom M φ) rfl ≫ svHom B hS ρ hρt =
          svHom B hS ρ₀ h₀ρ ≫ svHom B hS φ rfl := site_ext (sp_sq (RingHom.ext hρφ))
      rw [← hαa]
      exact pb_sq P sq α
    refine (pb_ss aY _ _ _).trans ?_
    rw [res_pinvS, res_eS, hof, h1, ha]
    exact ss_pinv_ss aY _ _
  have hβf : f.hom.app _ β₀ = pb Q (svHom B hS (cst A₁ M) rfl) b := by
    refine (f.map_smul _ _).trans ?_
    have : f.hom.app _ (pb P (svHom B hS ρ hρt) α) = pb Q (svHom B hS ρ hρt) b := by
      rw [nat, hαb]
    rw [this, hb]
    exact ss_pinv_ss aZ _ _
  obtain ⟨βt, ⟨hβ, hβa⟩, -⟩ := avgGlue φ hs hq t hP' β₀ a h₀c hrd
  refine ⟨pb P (iV (M := M) B hS φ hq t) βt, ?_, ?_, ?_⟩
  · have e : svHom B hS φ rfl ≫ iV (M := M) B hS φ hq t = qV (M := M) B hS φ t := site_ext (by
      change sp φ ≫ sp _ = sp _
      rw [← sp_comp, φ_avgInt])
    rw [← hβa, ← pb_comp, e]
  · let cU : Sv B hS (sU (M := M) φ t) ⟶ Sv B hS t :=
      svHom B hS (R₁ := avgRing (M := M) φ) (avgCst (M := M) φ) rfl
    have e₁ : pV (M := M) B hS φ t ≫ cU = svHom B hS (cst A₁ M) rfl := site_ext (by
      change sp _ ≫ sp _ = sp _
      rw [← sp_comp, avgSnd_cst])
    have e₂ : qV (M := M) B hS φ t ≫ cU = svHom B hS φ rfl := site_ext (by
      change sp _ ≫ sp _ = sp _
      rw [← sp_comp, avgFst_cst])
    have h₁ : f.hom.app _ βt = pb Q cU b := by
      refine avg_ext φ hs hq t hQ' ?_ ?_
      · rw [← nat, hβ, ← pb_comp, e₁]
        exact hβf
      · rw [← nat, hβa, ← pb_comp, e₂, ← hαa, nat, hαb]
    have e₃ : iV (M := M) B hS φ hq t ≫ cU = 𝟙 _ := site_ext (by
      change sp _ ≫ sp _ = 𝟙 _
      rw [← sp_comp, avgInt_cst, sp_id'])
    rw [nat, h₁, ← pb_comp, e₃, pb_id]
  · exact equivariance_step φ hs hq t ρ ρ₀ hρt hρφ hco hP' aY a α h₀ρ h₀c ha βt hβ hβa

end Group

end AlgMag.SpacesLift
