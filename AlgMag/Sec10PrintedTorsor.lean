/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedAct

/-!
# The torsor of lifts

Mayeux, *Algebraic Magnetism*, proof of Proposition 10.1. Let `φ : A₁ → A` be surjective with square
zero kernel `N`. On the test objects `D(P)`, the lifts `Pl` of the square form a torsor under `L f a N P`
(`Tag 061C` of the printed proof), compatibly with `g · a = g a g⁻¹` (`Tag 0618`). The difference of
`b, c` is read on the Milnor square `A₁ ×_A A₁`, the sum on `A₁ ×_A A[N]`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts

attribute [local instance] Stacks.Smooth.moduleMulOpposite

section LiftM

variable {X R' B C D : Type u} [CommRing X] [CommRing R'] [CommRing B] [CommRing C] [CommRing D]
  {p : R' →+* B} {q : R' →+* C} {i : B →+* D} {j : C →+* D}

lemma uniqM (H : MilnorData p q i j) {z z' : R'} (h₁ : p z = p z') (h₂ : q z = q z') : z = z' :=
  sub_eq_zero.1 (H.inj _ (by simp [h₁]) (by simp [h₂]))

/-- The universal property of a Milnor square, for rings. -/
noncomputable def liftM (H : MilnorData p q i j) (α : X →+* B) (β : X →+* C)
    (h : ∀ x, i (α x) = j (β x)) : X →+* R' :=
  have s₁ : ∀ x, p (H.ex _ _ (h x)).choose = α x := fun x => (H.ex _ _ (h x)).choose_spec.1
  have s₂ : ∀ x, q (H.ex _ _ (h x)).choose = β x := fun x => (H.ex _ _ (h x)).choose_spec.2
  { toFun := fun x => (H.ex _ _ (h x)).choose
    map_one' := uniqM H (by rw [s₁, map_one, map_one]) (by rw [s₂, map_one, map_one])
    map_zero' := uniqM H (by rw [s₁, map_zero, map_zero]) (by rw [s₂, map_zero, map_zero])
    map_add' := fun x y => uniqM H (by rw [s₁, map_add, map_add, s₁, s₁])
      (by rw [s₂, map_add, map_add, s₂, s₂])
    map_mul' := fun x y => uniqM H (by rw [s₁, map_mul, map_mul, s₁, s₁])
      (by rw [s₂, map_mul, map_mul, s₂, s₂]) }

lemma liftM_p (H : MilnorData p q i j) (α : X →+* B) (β : X →+* C) (h : ∀ x, i (α x) = j (β x)) :
    p.comp (liftM H α β h) = α :=
  RingHom.ext fun x => (H.ex _ _ (h x)).choose_spec.1

lemma liftM_q (H : MilnorData p q i j) (α : X →+* B) (β : X →+* C) (h : ∀ x, i (α x) = j (β x)) :
    q.comp (liftM H α β h) = β :=
  RingHom.ext fun x => (H.ex _ _ (h x)).choose_spec.2

lemma rh_milnor (H : MilnorData p q i j) {r s : X →+* R'} (h₁ : p.comp r = p.comp s)
    (h₂ : q.comp r = q.comp s) : r = s :=
  RingHom.ext fun x => uniqM H (RingHom.congr_fun h₁ x) (RingHom.congr_fun h₂ x)

end LiftM

section Rings

variable {A₁ A : Type u} [CommRing A₁] [CommRing A] (φ : A₁ →+* A)

/-- `A₁ ×_A A₁`. -/
noncomputable abbrev Dd : Subring (A₁ × A₁) :=
  RingHom.eqLocus (φ.comp (RingHom.fst _ _)) (φ.comp (RingHom.snd _ _))

/-- First projection. -/
noncomputable def d₁ : Dd φ →+* A₁ := (RingHom.fst _ _).comp (Dd φ).subtype
/-- Second projection. -/
noncomputable def d₂ : Dd φ →+* A₁ := (RingHom.snd _ _).comp (Dd φ).subtype
/-- The diagonal. -/
noncomputable def dΔ : A₁ →+* Dd φ :=
  RingHom.codRestrict ((RingHom.id A₁).prod (RingHom.id A₁)) (Dd φ) (fun _ => rfl)

lemma d₁_Δ : (d₁ φ).comp (dΔ φ) = RingHom.id _ := rfl
lemma d₂_Δ : (d₂ φ).comp (dΔ φ) = RingHom.id _ := rfl

theorem milnor_D (hs : Function.Surjective φ) : MilnorData (d₁ φ) (d₂ φ) φ φ where
  comm z := z.2
  surj := hs
  inj z h₁ h₂ := Subtype.ext (Prod.ext h₁ h₂)
  ex x y h := ⟨⟨(x, y), h⟩, rfl, rfl⟩

lemma d₂_surj : Function.Surjective (d₂ φ) := fun x => ⟨dΔ φ x, rfl⟩
lemma d₁_surj : Function.Surjective (d₁ φ) := fun x => ⟨dΔ φ x, rfl⟩

variable {φ}
variable [Module A (RingHom.ker φ)]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)

/-- The kernel part of an element of `A₁ ×_A A₁`. -/
noncomputable def kk (z : Dd φ) : RingHom.ker φ :=
  ⟨d₁ φ z - d₂ φ z, by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact z.2⟩

lemma kk_val (z : Dd φ) : (kk z : A₁) = d₁ φ z - d₂ φ z := rfl

include hN hq in
/-- `(x, y) ↦ (φ x, x - y)`. -/
noncomputable def qq : Dd φ →+* Sq A (RingHom.ker φ) := by
  refine { toFun := fun z => TrivSqZeroExt.inl (φ (d₁ φ z)) + TrivSqZeroExt.inr (kk z), map_one' := ?_,
           map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }
  · refine sq_ext ?_ (Subtype.ext ?_)
    · simp
    · simp [kk_val]
  · intro x y
    refine sq_ext (by simp) (Subtype.ext ?_)
    have e₁ : (x * y : Dd φ) = x * y := rfl
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      add_zero, Submodule.coe_add, op_smul_eq_smul, kk_val, map_mul]
    have h₃ : ((φ (d₁ φ x) • kk y : RingHom.ker φ) : A₁) = d₁ φ x * (d₁ φ y - d₂ φ y) := hN _ _
    have h₄ : ((φ (d₁ φ y) • kk x : RingHom.ker φ) : A₁) = d₁ φ y * (d₁ φ x - d₂ φ x) := hN _ _
    have h₅ := hq (d₁ φ x - d₂ φ x) (d₁ φ y - d₂ φ y)
      (by rw [map_sub, sub_eq_zero]; exact x.2) (by rw [map_sub, sub_eq_zero]; exact y.2)
    have e : ((φ (d₁ φ x) • kk y + φ (d₁ φ y) • kk x : RingHom.ker φ) : A₁) =
        d₁ φ x * (d₁ φ y - d₂ φ y) + d₁ φ y * (d₁ φ x - d₂ φ x) := by
      rw [Submodule.coe_add, h₃, h₄]
    refine Eq.trans ?_ e.symm
    linear_combination -h₅
  · exact sq_ext (by simp) (Subtype.ext (by simp [kk_val]))
  · intro x y
    refine sq_ext (by simp) (Subtype.ext ?_)
    simp [kk_val]
    ring

lemma qq_fst (z : Dd φ) : (qq hN hq z).fst = φ (d₁ φ z) := by simp [qq]
lemma qq_snd (z : Dd φ) : (qq hN hq z).snd = kk z := by simp [qq]

lemma qq_surj (hs : Function.Surjective φ) : Function.Surjective (qq hN hq) := by
  intro t
  obtain ⟨x, hx⟩ := hs t.fst
  refine ⟨⟨(x, x - t.snd), ?_⟩, sq_ext ?_ (Subtype.ext ?_)⟩
  · change φ x = φ (x - t.snd)
    rw [map_sub, RingHom.mem_ker.1 t.snd.2, sub_zero]
  · rw [qq_fst]; exact hx
  · rw [qq_snd]
    change x - (x - (t.snd : A₁)) = _
    ring

lemma sFst_qq : (sFst (RingHom.ker φ)).comp (qq hN hq) = φ.comp (d₁ φ) :=
  RingHom.ext fun z => qq_fst hN hq z

lemma qq_Δ : (qq hN hq).comp (dΔ φ) = (sInl (RingHom.ker φ)).comp φ :=
  RingHom.ext fun x => sq_ext (qq_fst hN hq _) (by
    refine (qq_snd hN hq _).trans (Subtype.ext ?_)
    change x - x = 0
    exact sub_self x)

/-- `A₁ ×_A A[N]`. -/
noncomputable abbrev Da : Subring (A₁ × Sq A (RingHom.ker φ)) :=
  RingHom.eqLocus (φ.comp (RingHom.fst _ _)) ((sFst (RingHom.ker φ)).comp (RingHom.snd _ _))

/-- First projection. -/
noncomputable def a₁ : Da (φ := φ) →+* A₁ := (RingHom.fst _ _).comp (Da (φ := φ)).subtype
/-- Second projection. -/
noncomputable def a₂ : Da (φ := φ) →+* Sq A (RingHom.ker φ) := (RingHom.snd _ _).comp (Da (φ := φ)).subtype

theorem milnor_a (hs : Function.Surjective φ) : MilnorData (a₁ (φ := φ)) (a₂ (φ := φ)) φ (sFst _) where
  comm z := z.2
  surj := hs
  inj z h₁ h₂ := Subtype.ext (Prod.ext h₁ h₂)
  ex x y h := ⟨⟨(x, y), h⟩, rfl, rfl⟩

lemma a₂_surj (hs : Function.Surjective φ) : Function.Surjective (a₂ (φ := φ)) := fun t => by
  obtain ⟨x, hx⟩ := hs t.fst
  exact ⟨⟨(x, t), hx⟩, rfl⟩

include hN hq in
/-- `(x, (φ x, j)) ↦ x + j`. -/
noncomputable def ss : Da (φ := φ) →+* A₁ := by
  refine { toFun := fun z => a₁ z + ((a₂ z).snd : A₁), map_one' := ?_,
           map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }
  · simp [a₁, a₂]
  · intro x y
    have hx : φ (a₁ x) = (a₂ x).fst := x.2
    have hy : φ (a₁ y) = (a₂ y).fst := y.2
    have h₃ := hN (a₁ x) (a₂ y).snd
    have h₄ := hN (a₁ y) (a₂ x).snd
    rw [hx] at h₃
    rw [hy] at h₄
    have h₅ := hq _ _ (a₂ x).snd.2 (a₂ y).snd.2
    have e : ((a₂ (x * y)).snd : A₁) = a₁ x * (a₂ y).snd + a₁ y * (a₂ x).snd := by
      rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, Submodule.coe_add, h₃]
      exact congrArg _ (by
        rw [show (TrivSqZeroExt.fst (a₂ y)) = _ from rfl]
        exact h₄)
    rw [e, map_mul]
    linear_combination -h₅
  · simp
  · intro x y
    simp only [map_add, TrivSqZeroExt.snd_add, Submodule.coe_add]
    ring

lemma ss_apply (z : Da (φ := φ)) : ss hN hq z = a₁ z + ((a₂ z).snd : A₁) := rfl

lemma φ_ss : φ.comp (ss hN hq) = φ.comp (a₁ (φ := φ)) := by
  refine RingHom.ext fun z => ?_
  simp only [RingHom.comp_apply, ss_apply, map_add, RingHom.mem_ker.1 (a₂ z).snd.2, add_zero]

/-- `(x, y) ↦ (y, q(x, y))`. -/
noncomputable def nn : Dd φ →+* Da (φ := φ) :=
  RingHom.codRestrict ((d₂ φ).prod (qq hN hq)) _ (fun z => by
    change φ (d₂ φ z) = (qq hN hq z).fst
    rw [qq_fst]
    exact z.2.symm)

/-- `(x, (φ x, j)) ↦ (x + j, x)`. -/
noncomputable def mm : Da (φ := φ) →+* Dd φ :=
  RingHom.codRestrict ((ss hN hq).prod a₁) _ (fun z => RingHom.congr_fun (φ_ss hN hq) z)

lemma a₁_nn : (a₁ (φ := φ)).comp (nn hN hq) = d₂ φ := rfl
lemma a₂_nn : (a₂ (φ := φ)).comp (nn hN hq) = qq hN hq := rfl
lemma d₁_mm : (d₁ φ).comp (mm hN hq) = ss hN hq := rfl
lemma d₂_mm : (d₂ φ).comp (mm hN hq) = a₁ := rfl

lemma ss_nn : (ss hN hq).comp (nn hN hq) = d₁ φ := by
  refine RingHom.ext fun z => ?_
  change d₂ φ z + ((qq hN hq z).snd : A₁) = _
  rw [qq_snd, kk_val]
  ring

lemma qq_mm : (qq hN hq).comp (mm hN hq) = a₂ := by
  refine RingHom.ext fun z => sq_ext ?_ (Subtype.ext ?_)
  · change (qq hN hq (mm hN hq z)).fst = (a₂ z).fst
    rw [qq_fst]
    refine (RingHom.congr_fun (φ_ss hN hq) z).trans z.2
  · change ((qq hN hq (mm hN hq z)).snd : A₁) = _
    rw [qq_snd, kk_val]
    change ss hN hq z - a₁ z = _
    rw [ss_apply]
    ring

/-- `A₁ ×_A A₁ ×_A A₁`. -/
noncomputable abbrev Dt : Subring (Dd φ × Dd φ) :=
  RingHom.eqLocus ((d₂ φ).comp (RingHom.fst _ _)) ((d₁ φ).comp (RingHom.snd _ _))

/-- `(x,y,z) ↦ (x,y)`. -/
noncomputable def t₁ : Dt (φ := φ) →+* Dd φ := (RingHom.fst _ _).comp (Dt (φ := φ)).subtype
/-- `(x,y,z) ↦ (y,z)`. -/
noncomputable def t₂ : Dt (φ := φ) →+* Dd φ := (RingHom.snd _ _).comp (Dt (φ := φ)).subtype

theorem milnor_t : MilnorData (t₁ (φ := φ)) (t₂ (φ := φ)) (d₂ φ) (d₁ φ) where
  comm z := z.2
  surj := d₂_surj φ
  inj z h₁ h₂ := Subtype.ext (Prod.ext h₁ h₂)
  ex x y h := ⟨⟨(x, y), h⟩, rfl, rfl⟩

lemma t₂_surj : Function.Surjective (t₂ (φ := φ)) := fun y =>
  ⟨⟨(⟨(d₁ φ y, d₁ φ y), rfl⟩, y), rfl⟩, rfl⟩

/-- `(x,y,z) ↦ (x,z)`. -/
noncomputable def tt : Dt (φ := φ) →+* Dd φ :=
  RingHom.codRestrict (((d₁ φ).comp t₁).prod ((d₂ φ).comp t₂)) _ (fun z => by
    have h₁ := (t₁ z).2
    have h₂ := (t₂ z).2
    have h₃ : d₂ φ (t₁ z) = d₁ φ (t₂ z) := z.2
    change φ (d₁ φ (t₁ z)) = φ (d₂ φ (t₂ z))
    refine Eq.trans h₁ ?_
    change φ (d₂ φ (t₁ z)) = _
    rw [h₃]
    exact h₂)

lemma d₁_tt : (d₁ φ).comp (tt (φ := φ)) = (d₁ φ).comp t₁ := rfl
lemma d₂_tt : (d₂ φ).comp (tt (φ := φ)) = (d₂ φ).comp t₂ := rfl

/-- `(x,y,z) ↦ (φ x, (x - y, y - z))`. -/
noncomputable def q₃ : Dt (φ := φ) →+* Sq A (RingHom.ker φ × RingHom.ker φ) :=
  liftM milnor_prod ((qq hN hq).comp t₁) ((qq hN hq).comp t₂) (fun z => by
    change (qq hN hq (t₁ z)).fst = (qq hN hq (t₂ z)).fst
    rw [qq_fst, qq_fst]
    refine Eq.trans (t₁ z).2 ?_
    change φ (d₂ φ (t₁ z)) = _
    rw [show d₂ φ (t₁ z) = d₁ φ (t₂ z) from z.2])

lemma fst_q₃ : (sMap (LinearMap.fst A _ _)).comp (q₃ hN hq) = (qq hN hq).comp t₁ := liftM_p _ _ _ _
lemma snd_q₃ : (sMap (LinearMap.snd A _ _)).comp (q₃ hN hq) = (qq hN hq).comp t₂ := liftM_q _ _ _ _

lemma add_q₃ : (sMap (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ) + LinearMap.snd A _ _)).comp (q₃ hN hq) =
    (qq hN hq).comp tt := by
  refine RingHom.ext fun z => sq_ext ?_ (Subtype.ext ?_)
  · simp only [RingHom.comp_apply, sMap_fst]
    have := congrArg TrivSqZeroExt.fst (RingHom.congr_fun (fst_q₃ hN hq) z)
    simp only [RingHom.comp_apply, sMap_fst] at this
    rw [this, qq_fst, qq_fst]
    rfl
  · have h₁ := congrArg TrivSqZeroExt.snd (RingHom.congr_fun (fst_q₃ hN hq) z)
    have h₂ := congrArg TrivSqZeroExt.snd (RingHom.congr_fun (snd_q₃ hN hq) z)
    simp only [RingHom.comp_apply, sMap_snd, qq_snd] at h₁ h₂
    simp only [RingHom.comp_apply, sMap_snd, qq_snd, LinearMap.add_apply, Submodule.coe_add]
    rw [h₁, h₂, kk_val, kk_val, kk_val, show d₂ φ (t₁ z) = d₁ φ (t₂ z) from z.2]
    change _ = d₁ φ (t₁ z) - d₂ φ (t₂ z)
    ring

end Rings

end AlgMag.Sec10Printed
