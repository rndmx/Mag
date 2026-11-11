/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Prop101General4

/-!
# Proposition 10.1 for a general affine flat `G`: the action of `G(T)` on the torsor

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), proof of Proposition 10.1 (p. 169).
Setting: `S = Spec R` affine, `G = Spec H`, `X' = Spec A₁` affine (agreed erratum), `X = Spec A`.
For `T = Spec B` and `g ∈ G(T) = Hom(H, B)`, `g · a' = g_Y ∘ a' ∘ g⁻¹_{X'}` on lifts
`a' : X'_T → Y`, and the same formula on `F(T) = Hom(a^*Ω, C)(X'_T)`. Here `g⁻¹_{X'}` is the ring
map `τ g` of `B ⊗ A₁`. The difference of lifts is equivariant (`diffB_act`).
-/

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts AlgMag.Prop101General Algebra.TensorProduct

attribute [local instance] Stacks.Smooth.moduleMulOpposite

/-! ### Transport of lifts along equal base points -/

section Cast

variable {A₁ A : Type u} [CommRing A₁] [CommRing A] {φ : A₁ →+* A} (hs : Function.Surjective φ)
  [Module A (RingHom.ker φ)]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
  {Y Z : Scheme.{u}} {f : Y ⟶ Z} {a a' : Spec (CommRingCat.of A) ⟶ Y}
  {b b' : Spec (CommRingCat.of A₁) ⟶ Z} {P : Type u} [AddCommGroup P]
  {N : Type u} [AddCommGroup N] [Module A N]

/-- A lift of `(a, b)` is a lift of `(a', b')` when `a = a'`, `b = b'`. -/
def Pl.cast (ha : a = a') (hb : b = b') (x : Pl φ f a b P) : Pl φ f a' b' P :=
  ⟨x.1, ha ▸ x.2.1, hb ▸ x.2.2⟩

def L.cast (ha : a = a') (x : L f a N P) : L f a' N P :=
  ⟨x.1, ha ▸ x.2.1, ha ▸ x.2.2⟩

lemma diffL_cast (ha : a = a') (hb : b = b') (w : a ≫ f = sp φ ≫ b) (w' : a' ≫ f = sp φ ≫ b')
    (x y : Pl φ f a b P) :
    diffL hs hN hq w' (Pl.cast ha hb x) (Pl.cast ha hb y) = L.cast ha (diffL hs hN hq w x y) := by
  subst ha hb; rfl

lemma L.cast_add (ha : a = a') (x y : L f a N P) : L.cast ha (x + y) = L.cast ha x + L.cast ha y := by
  subst ha; rfl

end Cast

/-! ### The data of Proposition 10.1 -/

variable {R : Type u} [CommRing R] {Hh : Type u} [CommRing Hh] [HopfAlgebra R Hh]
  {A₁ A : Type u} [CommRing A₁] [CommRing A] [Algebra R A₁] [Algebra R A] (φ : A₁ →ₐ[R] A)

/-- `φ` is a first order thickening. -/
class IsThick : Prop where
  surj : Function.Surjective φ
  sq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0

variable [IsThick φ] (B : Type u) [CommRing B] [Algebra R B]

/-- `ψ_B = B ⊗ φ`. -/
noncomputable abbrev psB : B ⊗[R] A₁ →+* B ⊗[R] A := (phB B φ).toRingHom

lemma psB_surj : Function.Surjective (psB φ B) := phB_surjective B (IsThick.surj (φ := φ))
lemma psB_sq : ∀ x y, psB φ B x = 0 → psB φ B y = 0 → x * y = 0 :=
  phB_sq' (IsThick.surj (φ := φ)) (IsThick.sq (φ := φ))

noncomputable instance kerInst : Module (B ⊗[R] A) (RingHom.ker (psB φ B)) :=
  kerModule (psB_surj φ B) (psB_sq φ B)

lemma psB_N : ∀ (x : B ⊗[R] A₁) (n : RingHom.ker (psB φ B)),
    ((psB φ B x • n : RingHom.ker (psB φ B)) : B ⊗[R] A₁) = x * n :=
  kerModule_hN (psB_surj φ B) (psB_sq φ B)

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) (a : Spec (CommRingCat.of A) ⟶ Y)
  (b : Spec (CommRingCat.of A₁) ⟶ Z)

/-- `P(T)`, the lifts `X'_T → Y` over `Z` of `a`. -/
abbrev PB := Pl (psB φ B) f (aB (R := R) (B := B) a) (bB (R := R) (B := B) b) PUnit.{u + 1}

/-- `F(T) = Hom(a^*Ω_{Y/Z}, C)(X'_T)`. -/
abbrev FB := L f (aB (R := R) (B := B) a) (RingHom.ker (psB φ B)) PUnit.{u + 1}

variable {φ f a b}

/-- The difference on `P(T)`. -/
noncomputable def diffB (w : a ≫ f = sp φ.toRingHom ≫ b) (x y : PB φ B f a b) : FB φ B f a :=
  diffL (psB_surj φ B) (psB_N φ B) (psB_sq φ B) (wB f a b w) x y

/-! ### The action -/

variable (c₁ : Coact (R := R) Hh A₁) (c₀ : Coact (R := R) Hh A)
  (hφρ : (Algebra.TensorProduct.map (AlgHom.id R Hh) φ).comp c₁.ρ = c₀.ρ.comp φ)

include hφρ in
lemma phB_tau {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) :
    (phB B φ).comp (tau c₁ g) = (tau c₀ g).comp (phB B φ) := by
  have h1 : (phB B φ).comp (Algebra.TensorProduct.map g (AlgHom.id R A₁)) =
      (Algebra.TensorProduct.map g (AlgHom.id R A)).comp (Algebra.TensorProduct.map (AlgHom.id R Hh) φ) := by
    refine Algebra.TensorProduct.ext ?_ ?_ <;> ext <;> simp [phB]
  have hk : ∀ x, phB B φ (kap c₁ g x) = kap c₀ g (φ x) := fun x => by
    have e := AlgHom.congr_fun hφρ x
    simp only [AlgHom.comp_apply] at e
    rw [kap, kap, AlgHom.comp_apply, AlgHom.comp_apply, ← e, ← AlgHom.comp_apply (phB B φ), h1,
      AlgHom.comp_apply]
  refine Algebra.TensorProduct.ext ?_ ?_
  · ext x
    simp [Prop101General.tau_tmul, phB, ← Algebra.TensorProduct.one_def]
  · ext x
    simp only [AlgHom.restrictScalars_apply, AlgHom.comp_apply, includeRight_apply,
      Prop101General.tau_tmul, ← Algebra.TensorProduct.one_def, one_mul, phB,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    exact hk x

include hφρ in
lemma psB_tau {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) :
    (psB φ B).comp (tau c₁ g).toRingHom = (tau c₀ g).toRingHom.comp (psB φ B) :=
  congrArg AlgHom.toRingHom (phB_tau c₁ c₀ hφρ g)

variable {πZ : Z ⟶ Spec (CommRingCat.of R)}
  (αY : GAct R Hh Y (f ≫ πZ)) (αZ : GAct R Hh Z πZ)
  (hf : ∀ {E : Type u} [CommRing E] (g : Hh →+* E) (z : Spec (CommRingCat.of E) ⟶ Y)
    (hz : z ≫ f ≫ πZ = sp (g.comp (algebraMap R Hh))) (hz' : (z ≫ f) ≫ πZ = sp (g.comp (algebraMap R Hh))),
    αY.act g z hz ≫ f = αZ.act g (z ≫ f) hz')
  (hbS : b ≫ πZ = sp (algebraMap R A₁))
  (w : a ≫ f = sp φ.toRingHom ≫ b)

/-- The point `g` of `G` on `X'_T`. -/
noncomputable abbrev pt₁ {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) : Hh →+* B ⊗[R] A₁ :=
  (includeLeft (R := R) (S := R) (A := B) (B := A₁)).toRingHom.comp g.toRingHom

include hbS in
lemma hbS' {B : Type u} [CommRing B] [Algebra R B] (g t : Hh →ₐ[R] B) :
    (sp (tau c₁ t).toRingHom ≫ bB (R := R) b) ≫ πZ = sp ((pt₁ g).comp (algebraMap R Hh)) := by
  rw [Category.assoc, Category.assoc, hbS, ← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun r => by simp

include hφρ w in
lemma w' {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) :
    (sp (tau c₀ g).toRingHom ≫ aB (R := R) a) ≫ f =
      sp (psB φ B) ≫ (sp (tau c₁ g).toRingHom ≫ bB (R := R) b) := by
  rw [Category.assoc, wB f a b w, ← Category.assoc, ← sp_comp, ← psB_tau c₁ c₀ hφρ g, sp_comp,
    Category.assoc]

/-- **`g_Y ∘ a' ∘ τ t`** on `P(T)`, for `g_Y ∘ a ∘ τ t = a` and `g_Z ∘ b ∘ τ t = b`; with `t = g⁻¹`
this is `g · a'`. -/
noncomputable def gact' {B : Type u} [CommRing B] [Algebra R B] (g t : Hh →ₐ[R] B)
    (ha : ∀ hz, αY.act ((psB φ B).comp (pt₁ g)) (sp (tau c₀ t).toRingHom ≫ aB (R := R) a) hz = aB a)
    (hb : ∀ hz, αZ.act (pt₁ g) (sp (tau c₁ t).toRingHom ≫ bB (R := R) b) hz = bB b)
    (x : PB φ B f a b) : PB φ B f a b :=
  Pl.cast (ha _) (hb _)
    (Pl.post αY αZ hf (pt₁ g) (hbS' c₁ hbS g t) (w' c₁ c₀ hφρ w t)
      (Pl.pull (psB_tau c₁ c₀ hφρ t) rfl rfl x))

/-- The same on `F(T)`. -/
noncomputable def gactF' {B : Type u} [CommRing B] [Algebra R B] (g t : Hh →ₐ[R] B)
    (ha : ∀ hz, αY.act ((psB φ B).comp (pt₁ g)) (sp (tau c₀ t).toRingHom ≫ aB (R := R) a) hz = aB a)
    (x : FB φ B f a) : FB φ B f a :=
  L.cast (ha _)
    (L.post αY αZ hf ((psB φ B).comp (pt₁ g)) (a_over (pt₁ g) (hbS' c₁ hbS g t) (w' c₁ c₀ hφρ w t))
      (L.pull rfl (kσ (psB_tau c₁ c₀ hφρ t))
        (kσ_smul (psB_surj φ B) (psB_N φ B) (psB_N φ B) (psB_tau c₁ c₀ hφρ t)) x))

/-- **The difference is equivariant**: `g · b - g · c = g · (b - c)`. -/
theorem diffB_act {B : Type u} [CommRing B] [Algebra R B] (g t : Hh →ₐ[R] B) ha hb (x y : PB φ B f a b) :
    diffB B w (gact' c₁ c₀ hφρ αY αZ hf hbS w g t ha hb x) (gact' c₁ c₀ hφρ αY αZ hf hbS w g t ha hb y) =
      gactF' c₁ c₀ hφρ αY αZ hf hbS w g t ha (diffB B w x y) := by
  unfold diffB gact' gactF'
  rw [diffL_cast _ _ _ _ _ (w_post αY αZ hf (pt₁ g) (hbS' c₁ hbS g t) (w' c₁ c₀ hφρ w t)),
    diffL_post, diffL_pull (psB_surj φ B) (psB_surj φ B) (psB_N φ B) (psB_sq φ B) (psB_N φ B) (psB_sq φ B)
      (psB_tau c₁ c₀ hφρ t) rfl rfl (wB f a b w)]

end AlgMag.Sec10Printed
