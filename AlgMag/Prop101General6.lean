/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Prop101General5

/-!
# Proposition 10.1 for a general affine flat `G`: the group action on the torsor

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), proof of Proposition 10.1 (p. 169).
Setting: `S = Spec R` affine, `G = Spec H`, `X' = Spec A₁` affine (agreed erratum).
`a`, `b`, `f` are `G`-equivariant: `a ∘ g_X = g_Y ∘ a` and `b ∘ g_{X'} = g_Z ∘ b` on `T`-points.
Then `g · a' = g_Y ∘ a' ∘ g⁻¹_{X'}` is an action of `G(T)` on `P(T)` (`gact_mul`), natural in `T`
(`pullP_gact`), and the difference of lifts is natural in `T` (`diffB_pull`).
-/

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts AlgMag.Prop101General Algebra.TensorProduct

attribute [local instance] Stacks.Smooth.moduleMulOpposite

variable {R : Type u} [CommRing R] {Hh : Type u} [CommRing Hh] [HopfAlgebra R Hh]

/-! ### Points of `G` -/

/-- The convolution product. -/
noncomputable abbrev cmul {B : Type u} [CommRing B] [Algebra R B] (g g' : Hh →ₐ[R] B) : Hh →ₐ[R] B :=
  WithConv.ofConv (WithConv.toConv g * WithConv.toConv g')

/-- The inverse `g ∘ S`. -/
noncomputable abbrev ginv {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) : Hh →ₐ[R] B :=
  g.comp (HopfAlgebra.antipodeAlgHom R Hh)

lemma ginv_mul {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) :
    WithConv.toConv (ginv g) * WithConv.toConv g = 1 := by
  have H : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map g g) =
      g.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
  trans WithConv.toConv <| ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map g g)).comp
    ((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R Hh) (.id _ _)).comp (Bialgebra.comulAlgHom R Hh))
  · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map g g),
      ← Algebra.TensorProduct.map_comp]; rfl
  rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
  change g.toLinearMap.comp (WithConv.toConv (HopfAlgebra.antipode R (A := Hh)) *
    WithConv.toConv LinearMap.id).ofConv = WithConv.ofConv (1 : WithConv <| Hh →ₗ[R] B)
  rw [LinearMap.antipode_mul_id]
  ext
  simp

lemma mul_ginv {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) :
    WithConv.toConv g * WithConv.toConv (ginv g) = 1 := by
  have H : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map g g) =
      g.comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
  trans WithConv.toConv <| ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map g g)).comp
    ((Algebra.TensorProduct.map (.id _ _) (HopfAlgebra.antipodeAlgHom R Hh)).comp (Bialgebra.comulAlgHom R Hh))
  · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map g g),
      ← Algebra.TensorProduct.map_comp]; rfl
  rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
  change g.toLinearMap.comp (WithConv.toConv LinearMap.id *
    WithConv.toConv (HopfAlgebra.antipode R (A := Hh))).ofConv = WithConv.ofConv (1 : WithConv <| Hh →ₗ[R] B)
  rw [LinearMap.id_mul_antipode]
  ext
  simp

/-- `(g g')⁻¹ = g'⁻¹ g⁻¹`. -/
lemma ginv_cmul {B : Type u} [CommRing B] [Algebra R B] (g g' : Hh →ₐ[R] B) :
    ginv (cmul g g') = cmul (ginv g') (ginv g) := by
  have h₁ : WithConv.toConv (ginv (cmul g g')) * (WithConv.toConv g * WithConv.toConv g') = 1 :=
    ginv_mul (cmul g g')
  have h₂ : (WithConv.toConv g * WithConv.toConv g') *
      (WithConv.toConv (ginv g') * WithConv.toConv (ginv g)) = 1 := by
    rw [mul_assoc, ← mul_assoc (WithConv.toConv g'), mul_ginv, one_mul, mul_ginv]
  exact congrArg WithConv.ofConv (left_inv_eq_right_inv h₁ h₂)

lemma comp_alg {B E : Type u} [CommRing B] [Algebra R B] [CommRing E] (k : B →+* E) (g : Hh →ₐ[R] B) :
    (k.comp g.toRingHom).comp (algebraMap R Hh) = k.comp (algebraMap R B) :=
  RingHom.ext fun r => by simp

lemma convR_comp {B E : Type u} [CommRing B] [Algebra R B] [CommRing E] (k : B →+* E) (g g' : Hh →ₐ[R] B)
    (h : (k.comp g.toRingHom).comp (algebraMap R Hh) = (k.comp g'.toRingHom).comp (algebraMap R Hh)) :
    convR (k.comp g.toRingHom) (k.comp g'.toRingHom) h = k.comp (cmul g g').toRingHom := by
  ext x
  letI : Algebra R E := ((k.comp g.toRingHom).comp (algebraMap R Hh)).toAlgebra
  simp only [convR, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  induction (Coalgebra.comul x : Hh ⊗[R] Hh) using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
  | tmul y z =>
    rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_mul]
    rfl

lemma one_comp {B E : Type u} [CommRing B] [Algebra R B] [CommRing E] (k : B →+* E) :
    k.comp (WithConv.ofConv (1 : WithConv (Hh →ₐ[R] B))).toRingHom = unitR Hh (k.comp (algebraMap R B)) := by
  ext x
  simp [unitR]

/-- `g₁ g₂ = 1` gives `(g₁)_W ∘ (g₂)_W = id`. -/
lemma GAct.act_cancel {W : Scheme.{u}} {πW : W ⟶ Spec (CommRingCat.of R)} (α : GAct R Hh W πW)
    {B E : Type u} [CommRing B] [Algebra R B] [CommRing E] (k : B →+* E) (g₁ g₂ : Hh →ₐ[R] B)
    (h12 : WithConv.toConv g₁ * WithConv.toConv g₂ = 1)
    (z : Spec (CommRingCat.of E) ⟶ W) (hz : z ≫ πW = sp (k.comp (algebraMap R B)))
    (h₁ : z ≫ πW = sp ((k.comp g₂.toRingHom).comp (algebraMap R Hh)))
    (h₂ : α.act (k.comp g₂.toRingHom) z h₁ ≫ πW = sp ((k.comp g₁.toRingHom).comp (algebraMap R Hh))) :
    α.act (k.comp g₁.toRingHom) (α.act (k.comp g₂.toRingHom) z h₁) h₂ = z := by
  have hh : (k.comp g₁.toRingHom).comp (algebraMap R Hh) = (k.comp g₂.toRingHom).comp (algebraMap R Hh) := by
    rw [comp_alg, comp_alg]
  rw [← α.mul _ _ hh z (by rw [convR_comp, comp_alg]; exact hz)]
  have e : convR (k.comp g₁.toRingHom) (k.comp g₂.toRingHom) hh = unitR Hh (k.comp (algebraMap R B)) := by
    rw [convR_comp, ← one_comp, cmul, h12]
  rw [α.act_congr e rfl _ (by rw [unitR_alg]; exact hz), α.one]

/-! ### The data -/

variable {A₁ A : Type u} [CommRing A₁] [CommRing A] [Algebra R A₁] [Algebra R A] {φ : A₁ →ₐ[R] A}
  [IsThick φ]
  {Y Z : Scheme.{u}} {f : Y ⟶ Z} {a : Spec (CommRingCat.of A) ⟶ Y} {b : Spec (CommRingCat.of A₁) ⟶ Z}
  (c₁ : Coact (R := R) Hh A₁) (c₀ : Coact (R := R) Hh A)
  (hφρ : (Algebra.TensorProduct.map (AlgHom.id R Hh) φ).comp c₁.ρ = c₀.ρ.comp φ)
  {πZ : Z ⟶ Spec (CommRingCat.of R)}
  (αY : GAct R Hh Y (f ≫ πZ)) (αZ : GAct R Hh Z πZ)
  (hf : ∀ {E : Type u} [CommRing E] (g : Hh →+* E) (z : Spec (CommRingCat.of E) ⟶ Y)
    (hz : z ≫ f ≫ πZ = sp (g.comp (algebraMap R Hh))) (hz' : (z ≫ f) ≫ πZ = sp (g.comp (algebraMap R Hh))),
    αY.act g z hz ≫ f = αZ.act g (z ≫ f) hz')
  (hbS : b ≫ πZ = sp (algebraMap R A₁))
  (w : a ≫ f = sp φ.toRingHom ≫ b)
  (haE : ∀ {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B)
    (hz : aB (R := R) (B := B) a ≫ f ≫ πZ =
      sp (((includeLeft (R := R) (S := R) (A := B) (B := A)).toRingHom.comp g.toRingHom).comp (algebraMap R Hh))),
    sp (tau c₀ g).toRingHom ≫ aB (R := R) a =
      αY.act ((includeLeft (R := R) (S := R) (A := B) (B := A)).toRingHom.comp g.toRingHom) (aB a) hz)
  (hbE : ∀ {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B)
    (hz : bB (R := R) (B := B) b ≫ πZ = sp ((pt₁ (A₁ := A₁) g).comp (algebraMap R Hh))),
    sp (tau c₁ g).toRingHom ≫ bB (R := R) b = αZ.act (pt₁ g) (bB b) hz)

include hbS in
lemma bB_over {B : Type u} [CommRing B] [Algebra R B] :
    bB (R := R) (B := B) b ≫ πZ =
      sp ((includeLeft (R := R) (S := R) (A := B) (B := A₁)).toRingHom.comp (algebraMap R B)) := by
  rw [Category.assoc, hbS, ← sp_comp]
  congr 1
  exact RingHom.ext fun r => by simp

include hbS w in
lemma aB_over {B : Type u} [CommRing B] [Algebra R B] :
    aB (R := R) (B := B) a ≫ f ≫ πZ =
      sp ((includeLeft (R := R) (S := R) (A := B) (B := A)).toRingHom.comp (algebraMap R B)) := by
  rw [← Category.assoc, wB f a b w, Category.assoc, bB_over hbS, ← sp_comp]
  congr 1
  exact RingHom.ext fun r => by simp [phB]

include haE hbS w in
lemma haI {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) hz :
    αY.act ((psB φ B).comp (pt₁ g)) (sp (tau c₀ (ginv g)).toRingHom ≫ aB (R := R) a) hz = aB a := by
  have h₀ := aB_over hbS w (B := B)
  refine (αY.act_congr (g' := (includeLeft (R := R) (S := R) (A := B) (B := A)).toRingHom.comp g.toRingHom)
    (RingHom.ext fun h => by simp [phB])
    (haE (ginv g) (by rw [h₀, comp_alg])) hz ?_).trans ?_
  · rw [αY.over, comp_alg, comp_alg]
  · exact αY.act_cancel _ g (ginv g) (mul_ginv g) _ h₀ _ _

include hbE hbS in
lemma hbI {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) hz :
    αZ.act (pt₁ g) (sp (tau c₁ (ginv g)).toRingHom ≫ bB (R := R) b) hz = bB b := by
  have h₀ := bB_over hbS (B := B)
  refine (αZ.act_congr rfl (hbE (ginv g) (by rw [h₀, comp_alg])) hz ?_).trans ?_
  · rw [αZ.over, comp_alg, comp_alg]
  · exact αZ.act_cancel _ g (ginv g) (mul_ginv g) _ h₀ _ _

/-- **`g · a' = g_Y ∘ a' ∘ g⁻¹_{X'}`**, the action of `G(T)` on `P(T)`. -/
noncomputable def gact {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) (x : PB φ B f a b) :
    PB φ B f a b :=
  gact' c₁ c₀ hφρ αY αZ hf hbS w g (ginv g) (haI c₀ αY hbS w haE g) (hbI c₁ αZ hbS hbE g) x

/-- The action of `G(T)` on `F(T)`. -/
noncomputable def gactF {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) (x : FB φ B f a) :
    FB φ B f a :=
  gactF' c₁ c₀ hφρ αY αZ hf hbS w g (ginv g) (haI c₀ αY hbS w haE g) x

theorem diffB_gact {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) (x y : PB φ B f a b) :
    diffB B w (gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE g x) (gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE g y) =
      gactF c₁ c₀ hφρ αY αZ hf hbS w haE g (diffB B w x y) :=
  diffB_act c₁ c₀ hφρ αY αZ hf hbS w g (ginv g) _ _ x y

lemma gactF_add {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) (x y : FB φ B f a) :
    gactF c₁ c₀ hφρ αY αZ hf hbS w haE g (x + y) =
      gactF c₁ c₀ hφρ αY αZ hf hbS w haE g x + gactF c₁ c₀ hφρ αY αZ hf hbS w haE g y := by
  unfold gactF gactF'
  rw [L.pull_add, L.post_add, L.cast_add]

lemma Pl.cast_val {A₁ A : Type u} [CommRing A₁] [CommRing A] {φ : A₁ →+* A} {Y Z : Scheme.{u}} {f : Y ⟶ Z}
    {a a' : Spec (CommRingCat.of A) ⟶ Y} {b b' : Spec (CommRingCat.of A₁) ⟶ Z} {P : Type u} [AddCommGroup P]
    (ha : a = a') (hb : b = b') (x : Pl φ f a b P) : (Pl.cast ha hb x).1 = x.1 := rfl

/-! ### Pullback along `T' → T` -/

section Pull

variable {B B' B'' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] [CommRing B'']
  [Algebra R B'']

/-- `e ⊗ 1`. -/
noncomputable abbrev eT (A₁ : Type u) [CommRing A₁] [Algebra R A₁] (e : B →ₐ[R] B') :
    B ⊗[R] A₁ →+* B' ⊗[R] A₁ :=
  (Algebra.TensorProduct.map e (AlgHom.id R A₁)).toRingHom

lemma eT_comp (e : B →ₐ[R] B') (e' : B' →ₐ[R] B'') :
    (eT A₁ e').comp (eT A₁ e) = eT A₁ (e'.comp e) := by
  have : (Algebra.TensorProduct.map e' (AlgHom.id R A₁)).comp (Algebra.TensorProduct.map e (AlgHom.id R A₁)) =
      Algebra.TensorProduct.map (e'.comp e) (AlgHom.id R A₁) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  exact congrArg AlgHom.toRingHom this

lemma eT_ps (e : B →ₐ[R] B') : (psB φ B').comp (eT A₁ e) = (eT A e).comp (psB φ B) := by
  have : (phB B' φ).comp (Algebra.TensorProduct.map e (AlgHom.id R A₁)) =
      (Algebra.TensorProduct.map e (AlgHom.id R A)).comp (phB B φ) := by
    refine Algebra.TensorProduct.ext ?_ ?_ <;> ext <;> simp [phB]
  exact congrArg AlgHom.toRingHom this

lemma eT_iR (A₁ : Type u) [CommRing A₁] [Algebra R A₁] (e : B →ₐ[R] B') :
    (eT A₁ e).comp (includeRight (R := R) (A := B) (B := A₁)).toRingHom =
      (includeRight (R := R) (A := B') (B := A₁)).toRingHom :=
  RingHom.ext fun x => by simp

lemma eT_a (e : B →ₐ[R] B') : sp (eT A e) ≫ aB (R := R) (B := B) a = aB (R := R) (B := B') a := by
  rw [← Category.assoc, ← sp_comp, eT_iR]

lemma eT_b (e : B →ₐ[R] B') : sp (eT A₁ e) ≫ bB (R := R) (B := B) b = bB (R := R) (B := B') b := by
  rw [← Category.assoc, ← sp_comp, eT_iR]

/-- `P(T) → P(T')`. -/
noncomputable def pullP (e : B →ₐ[R] B') (x : PB φ B f a b) : PB φ B' f a b :=
  Pl.pull (eT_ps e) (eT_a e) (eT_b e) x

/-- `F(T) → F(T')`. -/
noncomputable def pullF (e : B →ₐ[R] B') (x : FB φ B f a) : FB φ B' f a :=
  L.pull (eT_a e) (kσ (eT_ps e)) (kσ_smul (psB_surj φ B) (psB_N φ B) (psB_N φ B') (eT_ps e)) x

lemma pullF_add (e : B →ₐ[R] B') (x y : FB φ B f a) : pullF e (x + y) = pullF e x + pullF e y :=
  L.pull_add _ _ _ x y

include w in
theorem diffB_pull (e : B →ₐ[R] B') (x y : PB φ B f a b) :
    diffB B' w (pullP e x) (pullP e y) = pullF e (diffB B w x y) :=
  diffL_pull (psB_surj φ B) (psB_surj φ B') (psB_N φ B) (psB_sq φ B) (psB_N φ B') (psB_sq φ B')
    (eT_ps e) (eT_a e) (eT_b e) (wB f a b w) (wB f a b w) x y

lemma pullP_comp (e : B →ₐ[R] B') (e' : B' →ₐ[R] B'') (x : PB φ B f a b) :
    pullP e' (pullP e x) = pullP (e'.comp e) x := by
  refine Pl.ext' ?_
  change sp (mr _ (eT A₁ e')) ≫ sp (mr _ (eT A₁ e)) ≫ x.1 = sp (mr _ (eT A₁ (e'.comp e))) ≫ x.1
  rw [sp_mr_assoc, eT_comp]

lemma pullF_comp (e : B →ₐ[R] B') (e' : B' →ₐ[R] B'') (x : FB φ B f a) :
    pullF e' (pullF e x) = pullF (e'.comp e) x := by
  refine L.ext' ?_
  change sp (mr _ (sqM _ _ _)) ≫ sp (mr _ (sqM _ _ _)) ≫ x.1 = sp (mr _ (sqM _ _ _)) ≫ x.1
  rw [sp_mr_assoc]
  congr 3
  refine RingHom.ext fun z => sq_ext ?_ ?_
  · simp only [RingHom.comp_apply, sqM_fst]
    rw [← RingHom.comp_apply (eT A e'), eT_comp]
  · refine Subtype.ext ?_
    simp only [RingHom.comp_apply, sqM_snd]
    change eT A₁ e' (eT A₁ e z.snd) = eT A₁ (e'.comp e) z.snd
    rw [← RingHom.comp_apply (eT A₁ e'), eT_comp]

lemma pullP_id (x : PB φ B f a b) : pullP (AlgHom.id R B) x = x := by
  refine Pl.ext' ?_
  change sp (mr _ (eT A₁ (AlgHom.id R B))) ≫ x.1 = x.1
  have : eT A₁ (AlgHom.id R B) = RingHom.id _ := by
    rw [eT, Algebra.TensorProduct.map_id]; rfl
  rw [this, mr_id, sp_id', Category.id_comp]

end Pull

/-! ### Naturality and multiplicativity of the action -/

lemma tau_eT (c : Coact (R := R) Hh A₁) {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B']
    [Algebra R B'] (e : B →ₐ[R] B') (t : Hh →ₐ[R] B) :
    (eT A₁ e).comp (tau c t).toRingHom = (tau c (e.comp t)).toRingHom.comp (eT A₁ e) := by
  suffices h : (Algebra.TensorProduct.map e (AlgHom.id R A₁)).comp (tau c t) =
      (tau c (e.comp t)).comp (Algebra.TensorProduct.map e (AlgHom.id R A₁)) from congrArg AlgHom.toRingHom h
  refine Algebra.TensorProduct.ext ?_ ?_
  · ext x; simp [Prop101General.tau_tmul]
  · ext x
    simp only [AlgHom.restrictScalars_apply, AlgHom.comp_apply, includeRight_apply,
      Prop101General.tau_tmul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    rw [kap, kap, AlgHom.comp_apply, AlgHom.comp_apply, ← Algebra.TensorProduct.one_def, one_mul, ← Algebra.TensorProduct.one_def, one_mul,
      ← AlgHom.comp_apply (Algebra.TensorProduct.map e (AlgHom.id R A₁)),
      ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

lemma tau_left_rh (c : Coact (R := R) Hh A₁) {B : Type u} [CommRing B] [Algebra R B] (t : Hh →ₐ[R] B) :
    (tau c t).toRingHom.comp (includeLeft (R := R) (S := R) (A := B) (B := A₁)).toRingHom =
      (includeLeft (R := R) (S := R) (A := B) (B := A₁)).toRingHom :=
  congrArg AlgHom.toRingHom (tau_left c t)

/-- **The action is natural in `T`**: `(g · a')|_{T'} = g|_{T'} · a'|_{T'}`. -/
theorem pullP_gact {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (e : B →ₐ[R] B') (g : Hh →ₐ[R] B) (x : PB φ B f a b) :
    pullP e (gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE g x) =
      gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE (e.comp g) (pullP e x) := by
  refine Pl.ext' ?_
  simp only [pullP, gact, gact', Pl.pull_val, Pl.cast_val, Pl.post_val]
  rw [αY.nat']
  refine αY.act_congr ?_ ?_ _ _
  · rw [← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc]
    congr 1
  · rw [sp_mr_assoc, sp_mr_assoc, tau_eT]
    rfl

/-- `g_W ∘ g'_W = (g g')_W` on points through `k`. -/
lemma GAct.mul_comp {W : Scheme.{u}} {πW : W ⟶ Spec (CommRingCat.of R)} (α : GAct R Hh W πW)
    {B E E₀ : Type u} [CommRing B] [Algebra R B] [CommRing E] [CommRing E₀] (k : E₀ →+* E) (k' : B →+* E₀)
    (g g' : Hh →ₐ[R] B) (z : Spec (CommRingCat.of E) ⟶ W)
    (hz : z ≫ πW = sp ((k.comp k').comp (algebraMap R B)))
    (h₁ : z ≫ πW = sp ((k.comp (k'.comp g'.toRingHom)).comp (algebraMap R Hh)))
    (h₂ : α.act (k.comp (k'.comp g'.toRingHom)) z h₁ ≫ πW =
      sp ((k.comp (k'.comp g.toRingHom)).comp (algebraMap R Hh))) :
    α.act (k.comp (k'.comp g.toRingHom)) (α.act (k.comp (k'.comp g'.toRingHom)) z h₁) h₂ =
      α.act (k.comp (k'.comp (cmul g g').toRingHom)) z (by
        rw [← RingHom.comp_assoc, comp_alg]; exact hz) := by
  have hh : ((k.comp k').comp g.toRingHom).comp (algebraMap R Hh) =
      ((k.comp k').comp g'.toRingHom).comp (algebraMap R Hh) := by rw [comp_alg, comp_alg]
  have hc : convR (k.comp (k'.comp g.toRingHom)) (k.comp (k'.comp g'.toRingHom)) hh =
      k.comp (k'.comp (cmul g g').toRingHom) := convR_comp (k.comp k') g g' hh
  rw [← α.mul (k.comp (k'.comp g.toRingHom)) (k.comp (k'.comp g'.toRingHom)) hh z
    (by rw [hc, ← RingHom.comp_assoc, comp_alg]; exact hz) h₁ h₂]
  exact α.act_congr hc rfl _ _

include hbS in
lemma PB_over {B : Type u} [CommRing B] [Algebra R B] (r : B ⊗[R] A₁ →ₐ[R] B ⊗[R] A₁)
    (hr : r.toRingHom.comp (includeLeft (R := R) (S := R) (A := B) (B := A₁)).toRingHom =
      (includeLeft (R := R) (S := R) (A := B) (B := A₁)).toRingHom) (x : PB φ B f a b) :
    (sp (mr PUnit.{u + 1} r.toRingHom) ≫ x.1) ≫ f ≫ πZ =
      sp (((cs (B ⊗[R] A₁) PUnit.{u + 1}).comp (includeLeft (R := R) (S := R) (A := B) (B := A₁)).toRingHom).comp
        (algebraMap R B)) := by
  rw [Category.assoc, ← Category.assoc x.1, x.2.2, Category.assoc, bB_over hbS, ← sp_comp, ← sp_comp]
  congr 1
  refine RingHom.ext fun t => ?_
  have h1 := RingHom.congr_fun hr (algebraMap R B t)
  simp only [RingHom.comp_apply] at h1 ⊢
  rw [← RingHom.comp_apply (mr _ _), mr_cs, RingHom.comp_apply, h1]

lemma tau_ginv_mul {B : Type u} [CommRing B] [Algebra R B] (g g' : Hh →ₐ[R] B) :
    (tau c₁ (ginv g)).toRingHom.comp (tau c₁ (ginv g')).toRingHom = (tau c₁ (ginv (cmul g g'))).toRingHom := by
  rw [ginv_cmul, tau_mul]
  rfl

/-- **The action is an action**: `(g g') · a' = g · (g' · a')`. -/
theorem gact_mul {B : Type u} [CommRing B] [Algebra R B] (g g' : Hh →ₐ[R] B) (x : PB φ B f a b) :
    gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE (cmul g g') x =
      gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE g (gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE g' x) := by
  refine Pl.ext' ?_
  have hc : (mr PUnit.{u + 1} (tau c₁ (ginv g)).toRingHom).comp ((cs (B ⊗[R] A₁) PUnit.{u + 1}).comp (pt₁ g')) =
      (cs (B ⊗[R] A₁) PUnit.{u + 1}).comp (pt₁ g') := by
    rw [← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc]
    congr 1
    ext h
    simp only [pt₁, RingHom.comp_apply]
    exact RingHom.congr_fun (tau_left_rh c₁ (ginv g)) _
  simp only [gact, gact', Pl.cast_val, Pl.post_val, Pl.pull_val, αY.nat', hc]
  rw [αY.mul_comp (cs (B ⊗[R] A₁) PUnit.{u + 1}) (includeLeft (R := R) (S := R) (A := B) (B := A₁)).toRingHom
    g g' _ (by
      rw [sp_mr_assoc, Category.assoc]
      exact PB_over hbS (B := B) ((tau c₁ (ginv g)).comp (tau c₁ (ginv g'))) (by
        have e : ((tau c₁ (ginv g)).comp (tau c₁ (ginv g'))).comp
            (includeLeft (R := R) (S := R) (A := B) (B := A₁)) = includeLeft := by
          rw [AlgHom.comp_assoc, tau_left, tau_left]
        exact congrArg AlgHom.toRingHom e) x)]
  refine αY.act_congr rfl ?_ _ _
  rw [← tau_ginv_mul]
  try rw [sp_mr_assoc]


end AlgMag.Sec10Printed
