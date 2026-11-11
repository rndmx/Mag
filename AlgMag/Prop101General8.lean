/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Prop101General7

/-!
# Proposition 10.1 for a general affine flat `G` (with `X'` affine)

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Proposition 10.1 (p. 168), with the agreed
erratum `X'` affine, and `S = Spec R` affine. `G = Spec H` for a commutative Hopf `R`-algebra `H`
(flatness of `H` is only used to identify `F(T)` with `p_* Hom(a^*Ω, C)(T)` for `T = H, H ⊗ H`,
`incB_injective`; the proof does not need it). The actions: `ρ₁ : A₁ → H ⊗ A₁`, `ρ₀ : A → H ⊗ A`
(comodule algebras, `φ` equivariant), and `S`-actions of `G` on `Y`, `Z` on points; `f`, `a`, `b`
equivariant. The non equivariant lift `α` exists since `Y → Z` is formally smooth and `X'` is affine.
Under `H¹(G, F) = 0` (Hochschild form) there is a `G`-equivariant lift.
-/

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts AlgMag.Prop101General Algebra.TensorProduct

attribute [local instance] Stacks.Smooth.moduleMulOpposite

variable {R : Type u} [CommRing R] {Hh : Type u} [CommRing Hh] [HopfAlgebra R Hh]
  {A₁ A : Type u} [CommRing A₁] [CommRing A] [Algebra R A₁] [Algebra R A] {φ : A₁ →ₐ[R] A}
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

/-- `(R ⊗ A₁)[0] → A₁`. -/
noncomputable abbrev kR (A₁ : Type u) [CommRing A₁] [Algebra R A₁] :
    AddMonoidAlgebra (R ⊗[R] A₁) PUnit.{u + 1} →+* A₁ :=
  ((Algebra.TensorProduct.lid R A₁).toAlgHom.toRingHom).comp (aug _ PUnit.{u + 1})

lemma kR_cs_iR (A₁ : Type u) [CommRing A₁] [Algebra R A₁] :
    (kR (R := R) A₁).comp ((cs _ PUnit.{u + 1}).comp (includeRight (R := R) (A := R) (B := A₁)).toRingHom) =
      RingHom.id A₁ := by
  refine RingHom.ext fun x => ?_
  have h : ∀ y, (aug (R ⊗[R] A₁) PUnit.{u + 1}) ((cs (R ⊗[R] A₁) PUnit.{u + 1}) y) = y :=
    fun y => RingHom.congr_fun aug_cs y
  simp only [RingHom.comp_apply, RingHom.id_apply, h]
  simp

lemma φ_kR : φ.toRingHom.comp (kR (R := R) A₁) = (kR (R := R) A).comp (mr PUnit.{u + 1} (psB φ R)) := by
  rw [kR, kR, RingHom.comp_assoc, aug_mr, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  | tmul r y => simp [phB, Algebra.smul_def]

lemma iR_kR {B : Type u} [CommRing B] [Algebra R B] :
    (includeRight (R := R) (A := B) (B := A₁)).toRingHom.comp (kR (R := R) A₁) =
      (eT A₁ (Algebra.ofId R B)).comp (aug _ PUnit.{u + 1}) := by
  rw [kR, ← RingHom.comp_assoc]
  congr 1
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  | tmul r y =>
    simp only [RingHom.comp_apply]
    simp [Algebra.smul_def]
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

include hbE in
/-- **Proposition 10.1** (printed statement, with `X'` affine and `S` affine), for a general affine
`G = Spec H`: if `Y → Z` has a lift `α` of the square (it exists, `Y → Z` being formally smooth and
`X'` affine) and `H¹(G, p_* Hom(a^*Ω_{Y/Z}, C_{X/X'})) = 0`, there is a `G`-equivariant lift `l`:
`l ∘ i = a`, `f ∘ l = ϕ`, and `l ∘ g_{X'} = g_Y ∘ l` on `T`-points for every `T = Spec B`, `g ∈ G(T)`. -/
theorem prop101_general (hH1 : HochschildH1Vanish c₁ c₀ hφρ αY αZ hf hbS w haE)
    (α : Spec (CommRingCat.of A₁) ⟶ Y) (hα₁ : sp φ.toRingHom ≫ α = a) (hα₂ : α ≫ f = b) :
    ∃ l : Spec (CommRingCat.of A₁) ⟶ Y, sp φ.toRingHom ≫ l = a ∧ l ≫ f = b ∧
      ∀ {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B)
        (hz : (sp (includeRight (R := R) (A := B) (B := A₁)).toRingHom ≫ l) ≫ f ≫ πZ =
          sp ((pt₁ g).comp (algebraMap R Hh))),
        sp (tau c₁ g).toRingHom ≫ sp (includeRight (R := R) (A := B) (B := A₁)).toRingHom ≫ l =
          αY.act (pt₁ g) (sp (includeRight (R := R) (A := B) (B := A₁)).toRingHom ≫ l) hz := by
  let iR₁ := (includeRight (R := R) (A := R) (B := A₁)).toRingHom
  let αP : PB φ R f a b := ⟨sp ((cs _ PUnit.{u + 1}).comp iR₁) ≫ α, by
      rw [← Category.assoc, ← sp_comp, ← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc]
      have : (psB φ R).comp iR₁ = (includeRight (R := R) (A := R) (B := A)).toRingHom.comp φ.toRingHom :=
        RingHom.ext fun x => by simp [iR₁, phB]
      rw [this, sp_comp, sp_comp, Category.assoc, Category.assoc, hα₁], by
      rw [Category.assoc, hα₂, sp_comp, Category.assoc]⟩
  obtain ⟨⟨βv, hβ1, hβ2⟩, hβ⟩ := exists_invariant_PB c₁ c₀ hφρ αY αZ hf hbS w haE hbE hH1 αP
  refine ⟨sp (kR A₁) ≫ βv, ?_, ?_, ?_⟩
  · rw [← Category.assoc, ← sp_comp, φ_kR, sp_comp (mr PUnit.{u + 1} (psB φ R)) (kR A), Category.assoc, hβ1, ← Category.assoc, ← sp_comp,
      ← Category.assoc, ← sp_comp, RingHom.comp_assoc, kR_cs_iR, sp_id', Category.id_comp]
  · rw [Category.assoc, hβ2, ← Category.assoc, ← sp_comp, ← Category.assoc, ← sp_comp, RingHom.comp_assoc,
      kR_cs_iR, sp_id', Category.id_comp]
  · intro B _ _ g hz
    let βB : PB φ B f a b := pullP (Algebra.ofId R B) ⟨βv, hβ1, hβ2⟩
    have hval := congrArg Subtype.val (hβ g)
    simp only [gact, gact', Pl.cast_val, Pl.post_val, Pl.pull_val] at hval
    have hτ : (tau c₁ g).toRingHom.comp (tau c₁ (ginv g)).toRingHom = RingHom.id _ := by
      have e : (tau c₁ g).comp (tau c₁ (ginv g)) = AlgHom.id R _ := by
        rw [← tau_mul, ginv_mul, tau_one]
      exact congrArg AlgHom.toRingHom e
    have hstd : sp (mr PUnit.{u + 1} (tau c₁ g).toRingHom) ≫ βB.1 =
        αY.act ((cs _ PUnit.{u + 1}).comp (pt₁ g)) βB.1
          (by rw [← Category.assoc βB.1, βB.2.2, Category.assoc, bB_over hbS, ← sp_comp]
              congr 1
              exact RingHom.ext fun r => by simp) := by
      conv_lhs => rw [← hval]
      rw [αY.nat']
      refine αY.act_congr ?_ ?_ _ _
      · rw [← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc]
        congr 1
        ext h
        simp only [pt₁, RingHom.comp_apply]
        exact RingHom.congr_fun (tau_left_rh c₁ g) _
      · rw [sp_mr_assoc, hτ, mr_id, sp_id', Category.id_comp]
    have hl : sp (includeRight (R := R) (A := B) (B := A₁)).toRingHom ≫ sp (kR A₁) ≫ βv =
        sp (aug _ PUnit.{u + 1}) ≫ βB.1 := by
      change _ = sp (aug _ PUnit.{u + 1}) ≫ sp (mr PUnit.{u + 1} (eT A₁ (Algebra.ofId R B))) ≫ βv
      rw [← Category.assoc, ← Category.assoc, ← sp_comp, ← sp_comp, iR_kR, aug_mr]
    refine (congrArg (sp (tau c₁ g).toRingHom ≫ ·) hl).trans ?_
    refine Eq.trans ?_ (αY.act_congr rfl hl.symm (hl ▸ hz) hz)
    rw [← Category.assoc, ← sp_comp, ← aug_mr, sp_comp, Category.assoc, hstd, αY.nat']
    exact αY.act_congr (by rw [← RingHom.comp_assoc, aug_cs, RingHom.id_comp]) rfl _ _


end AlgMag.Sec10Printed
