/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Data.ZMod.Basic

/-!
# `R[Z] → R[M]` for `Z ⊆ M` of finite index, `[M : Z]` invertible in `R`

Ring input of Remarks 6.5 and 6.6 of *Algebraic Magnetism*: the morphism `D(M) → D(Z)` is étale when
`[M : Z]` is invertible (`formallyEtale_incl`), whereas `D(ℤ/2) → Spec ℤ` is not
(`not_formallyUnramified_int_zmod2`).
-/

open scoped Pointwise

universe u

namespace AlgMag.Leftover

section Root

variable {B : Type*} [CommRing B] (I : Ideal B) (hI : I ^ 2 = ⊥)

include hI in
lemma mul_eq_zero_of_mem {s t : B} (hs : s ∈ I) (ht : t ∈ I) : s * t = 0 := by
  have : s * t ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hs ht
  rwa [hI, Ideal.mem_bot] at this

include hI in
lemma add_pow_succ_of_mem (u : B) {t : B} (ht : t ∈ I) (m : ℕ) :
    (u + t) ^ (m + 1) = u ^ (m + 1) + (m + 1 : ℕ) * u ^ m * t := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have h0 := mul_eq_zero_of_mem I hI ht ht
    push_cast
    linear_combination ((k + 1 : B) * u ^ k) * h0

include hI in
/-- Unique `n`-th root lifting: if `n` is invertible, `b` is a unit and `b ≡ x^n` modulo the
square-zero ideal `I`, there is exactly one lift `v` of `x` with `v^n = b`. -/
theorem existsUnique_root (m : ℕ) (hn : IsUnit ((m + 1 : ℕ) : B)) {b : B} (hb : IsUnit b)
    (x : B ⧸ I) (hx : Ideal.Quotient.mk I b = x ^ (m + 1)) :
    ∃! v : B, Ideal.Quotient.mk I v = x ∧ v ^ (m + 1) = b := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hd : u ^ (m + 1) - b ∈ I := by
    rw [← Ideal.Quotient.eq, map_pow, hx]
  have hu : IsUnit u := by
    have h1 : IsUnit (u ^ (m + 1)) := by
      have e : u ^ (m + 1) = (u ^ (m + 1) - b) + b := by ring
      rw [e]
      refine IsNilpotent.isUnit_add_right_of_commute ?_ hb (Commute.all _ _)
      exact ⟨2, by rw [pow_two]; exact mul_eq_zero_of_mem I hI hd hd⟩
    exact (isUnit_pow_succ_iff).1 h1
  obtain ⟨c, hc⟩ : IsUnit (((m + 1 : ℕ) : B) * u ^ m) := hn.mul (hu.pow m)
  have hcc : ((m + 1 : ℕ) : B) * u ^ m * (↑c⁻¹ : B) = 1 := by rw [← hc]; simp
  have hneg : b - u ^ (m + 1) ∈ I := by simpa using I.neg_mem hd
  have ht : (b - u ^ (m + 1)) * (↑c⁻¹ : B) ∈ I := I.mul_mem_right _ hneg
  refine ⟨u + (b - u ^ (m + 1)) * ↑c⁻¹, ⟨?_, ?_⟩, ?_⟩
  · rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ht, add_zero]
  · rw [add_pow_succ_of_mem I hI u ht m]
    linear_combination (b - u ^ (m + 1)) * hcc
  · rintro v ⟨hv, hvn⟩
    have ht' : v - u ∈ I := Ideal.Quotient.eq.1 hv
    have e := add_pow_succ_of_mem I hI u ht' m
    rw [add_sub_cancel, hvn] at e
    have e' : (b - u ^ (m + 1)) = ((m + 1 : ℕ) : B) * u ^ m * (v - u) := by
      rw [e]; ring
    have : v - u = (b - u ^ (m + 1)) * ↑c⁻¹ := by
      rw [e', mul_comm (((m + 1 : ℕ) : B) * u ^ m), mul_assoc, hcc, mul_one]
    linear_combination this

end Root

variable (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] (Z : AddSubgroup M)

/-- The ring map `R[Z] → R[M]`. -/
noncomputable def incl : AddMonoidAlgebra R Z →+* AddMonoidAlgebra R M :=
  AddMonoidAlgebra.mapDomainRingHom R Z.subtype

@[simp] lemma incl_single (z : Z) (r : R) :
    incl R Z (AddMonoidAlgebra.single z r) = AddMonoidAlgebra.single (z : M) r := by
  simp [incl]

/-- `incl`, as an algebra structure. -/
@[reducible] noncomputable def inclAlg : Algebra (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) :=
  (incl R Z).toAlgebra

lemma isUnit_single {G : Type*} [AddCommGroup G] {A : Type*} [CommRing A] (g : G) :
    IsUnit (AddMonoidAlgebra.single g (1 : A)) :=
  IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-g) (1 : A)) (by
    rw [AddMonoidAlgebra.single_mul_single, one_mul, add_neg_cancel, AddMonoidAlgebra.one_def])

lemma single_nsmul {G : Type*} [AddCommMonoid G] {A : Type*} [CommRing A] (g : G) (n : ℕ) :
    (AddMonoidAlgebra.single g (1 : A)) ^ n = AddMonoidAlgebra.single (n • g) (1 : A) := by
  rw [AddMonoidAlgebra.single_pow, one_pow]

section Lift

variable {R Z}
variable {B : Type u} [CommRing B] [Algebra (AddMonoidAlgebra R Z) B]

variable (R) in
/-- The value of `R[Z] → B` on `z`. -/
noncomputable def phi (B : Type u) [CommRing B] [Algebra (AddMonoidAlgebra R Z) B] (z : Z) : B :=
  algebraMap (AddMonoidAlgebra R Z) B (AddMonoidAlgebra.single z 1)

lemma phi_add (z z' : Z) : (phi R B (z + z') : B) = phi R B z * phi R B z' := by
  simp only [phi, ← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]

lemma phi_zero : (phi R B (0 : Z) : B) = 1 := by
  simp only [phi]
  rw [← AddMonoidAlgebra.one_def, map_one]

lemma phi_isUnit (z : Z) : IsUnit (phi R B z : B) := (isUnit_single z).map _

lemma phi_nsmul (n : ℕ) (z : Z) : (phi R B (n • z) : B) = phi R B z ^ n := by
  simp only [phi, ← map_pow, single_nsmul]

end Lift

/-- **Ring input of Remark 6.6 (corrected).** If `[M : Z]` is finite and invertible in `R`, then
`R[Z] → R[M]` is formally étale. A lift to a square-zero extension is determined by
`v(m)^n = φ(n m)`, `n = [M : Z]`, which has one solution by `existsUnique_root`. -/
theorem formallyEtale_incl (hfin : Z.FiniteIndex) (hn : IsUnit ((Z.index : ℕ) : R)) :
    letI := inclAlg R Z
    Algebra.FormallyEtale (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) := by
  letI := inclAlg R Z
  refine Algebra.FormallyEtale.iff_comp_bijective.mpr ?_
  intro B _ _ I hI
  obtain ⟨m, hm⟩ : ∃ m, Z.index = m + 1 := Nat.exists_eq_succ_of_ne_zero hfin.index_ne_zero
  let ρ : R →+* B := (algebraMap (AddMonoidAlgebra R Z) B).comp AddMonoidAlgebra.singleZeroRingHom
  have hnB : IsUnit ((m + 1 : ℕ) : B) := by
    have := hn.map ρ
    rwa [map_natCast, hm] at this
  have hmem : ∀ x : M, (m + 1) • x ∈ Z := fun x => by
    rw [← hm]
    exact AddSubgroup.nsmul_index_mem Z x
  have halg : ∀ (g : AddMonoidAlgebra R M →ₐ[AddMonoidAlgebra R Z] B) (z : Z),
      g (AddMonoidAlgebra.single (z : M) 1) = phi R B z := by
    intro g z
    have := g.commutes (AddMonoidAlgebra.single z 1)
    rw [show algebraMap (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) _ =
      incl R Z (AddMonoidAlgebra.single z 1) from rfl, incl_single] at this
    exact this
  have hquot : ∀ (f : AddMonoidAlgebra R M →ₐ[AddMonoidAlgebra R Z] B ⧸ I) (x : M),
      Ideal.Quotient.mk I (phi R B ⟨(m + 1) • x, hmem x⟩) =
        (f (AddMonoidAlgebra.single x 1)) ^ (m + 1) := by
    intro f x
    rw [← map_pow, single_nsmul]
    have := f.commutes (AddMonoidAlgebra.single (⟨(m + 1) • x, hmem x⟩ : Z) 1)
    rw [show algebraMap (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) _ =
      incl R Z (AddMonoidAlgebra.single _ 1) from rfl, incl_single] at this
    exact this.symm
  have hconst : ∀ r : R, (AddMonoidAlgebra.single (0 : M) r) =
      algebraMap (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M)
        (AddMonoidAlgebra.single (0 : Z) r) := by
    intro r
    rw [show algebraMap (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) _ =
      incl R Z (AddMonoidAlgebra.single _ r) from rfl, incl_single]
    rfl
  constructor
  · intro g g' hgg
    have hval : ∀ x : M, g (AddMonoidAlgebra.single x 1) = g' (AddMonoidAlgebra.single x 1) := by
      intro x
      let f := (Ideal.Quotient.mkₐ (AddMonoidAlgebra R Z) I).comp g
      have hu := existsUnique_root I hI m hnB (phi_isUnit (R := R) (B := B) ⟨(m + 1) • x, hmem x⟩)
        (f (AddMonoidAlgebra.single x 1)) (hquot f x)
      refine hu.unique ⟨rfl, ?_⟩ ⟨?_, ?_⟩
      · rw [← map_pow, single_nsmul]; exact halg g ⟨_, hmem x⟩
      · exact (congrArg (fun k => k (AddMonoidAlgebra.single x 1)) hgg).symm
      · rw [← map_pow, single_nsmul]; exact halg g' ⟨_, hmem x⟩
    apply AlgHom.coe_ringHom_injective
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun x => ?_)
    · change g _ = g' _
      rw [hconst, g.commutes, g'.commutes]
    · exact hval x
  · intro f
    have hu := fun x : M => existsUnique_root I hI m hnB
      (phi_isUnit (R := R) (B := B) ⟨(m + 1) • x, hmem x⟩) (f (AddMonoidAlgebra.single x 1))
      (hquot f x)
    choose v hv huniq using hu
    have hv1 := fun x => (hv x).1
    have hv2 := fun x => (hv x).2
    have vadd : ∀ x y, v (x + y) = v x * v y := by
      intro x y
      symm
      refine huniq (x + y) _ ⟨?_, ?_⟩
      · rw [map_mul, hv1, hv1, ← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
      · rw [mul_pow, hv2, hv2, ← phi_add]
        congr 1
        exact Subtype.ext (by simp [smul_add])
    have vzero : v 0 = 1 := by
      symm
      refine huniq 0 _ ⟨?_, ?_⟩
      · rw [map_one, ← AddMonoidAlgebra.one_def, map_one]
      · rw [one_pow]
        have : (⟨(m + 1) • (0 : M), hmem 0⟩ : Z) = 0 := Subtype.ext (by simp)
        rw [this, phi_zero]
    have vZ : ∀ z : Z, v z = phi R B z := by
      intro z
      symm
      refine huniq z _ ⟨?_, ?_⟩
      · have := f.commutes (AddMonoidAlgebra.single z 1)
        rw [show algebraMap (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) _ =
          incl R Z (AddMonoidAlgebra.single z 1) from rfl, incl_single] at this
        rw [this]; rfl
      · rw [← phi_nsmul]
        congr 1
    let ψ : Multiplicative M →* B :=
      { toFun := fun x => v (Multiplicative.toAdd x)
        map_one' := vzero
        map_mul' := fun x y => vadd _ _ }
    let G : AddMonoidAlgebra R M →+* B :=
      AddMonoidAlgebra.liftNCRingHom ρ ψ (fun _ _ => Commute.all _ _)
    have Gs : ∀ x (r : R), G (AddMonoidAlgebra.single x r) = ρ r * v x := by
      intro x r
      simp [G, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single, ψ]
    have Gc : ∀ a : AddMonoidAlgebra R Z, G (incl R Z a) = algebraMap _ B a := by
      intro a
      have : G.comp (incl R Z) = algebraMap (AddMonoidAlgebra R Z) B := by
        refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun z => ?_)
        · change G (incl R Z (AddMonoidAlgebra.single 0 r)) = _
          rw [incl_single, Gs]
          have : ((0 : Z) : M) = 0 := rfl
          rw [this, vzero, mul_one]
          rfl
        · change G (incl R Z (AddMonoidAlgebra.single z 1)) = _
          rw [incl_single, Gs, vZ, map_one, one_mul]
          rfl
      exact congrArg (fun k => k a) this
    refine ⟨{ G with commutes' := Gc }, ?_⟩
    apply AlgHom.coe_ringHom_injective
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun x => ?_)
    · change Ideal.Quotient.mk I (G _) = f _
      rw [hconst, f.commutes, show algebraMap (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) _ =
          incl R Z (AddMonoidAlgebra.single _ r) from rfl, Gc]
      rfl
    · change Ideal.Quotient.mk I (G _) = f _
      rw [Gs, map_one, one_mul]
      exact hv1 x

/-- `incl` is injective. -/
theorem incl_injective : Function.Injective (incl R Z) :=
  AddMonoidAlgebra.mapDomain_injective Z.subtype_injective

/-- `R[M]` is integral over `R[Z]` for `Z` of finite index. -/
theorem isIntegral_incl (hfin : Z.FiniteIndex) :
    letI := inclAlg R Z
    Algebra.IsIntegral (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) := by
  letI := inclAlg R Z
  have hsing : ∀ (x : M) (r : R), IsIntegral (AddMonoidAlgebra R Z)
      (AddMonoidAlgebra.single x r : AddMonoidAlgebra R M) := by
    intro x r
    have hx : IsIntegral (AddMonoidAlgebra R Z) (AddMonoidAlgebra.single x 1 : AddMonoidAlgebra R M) := by
      have hpos : 0 < Z.index := Nat.pos_of_ne_zero hfin.index_ne_zero
      refine IsIntegral.of_pow hpos ?_
      rw [single_nsmul]
      have := isIntegral_algebraMap (R := AddMonoidAlgebra R Z) (A := AddMonoidAlgebra R M)
        (x := AddMonoidAlgebra.single (⟨Z.index • x, AddSubgroup.nsmul_index_mem Z x⟩ : Z) 1)
      rwa [show algebraMap (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) _ =
        incl R Z (AddMonoidAlgebra.single _ 1) from rfl, incl_single] at this
    have hr := isIntegral_algebraMap (R := AddMonoidAlgebra R Z) (A := AddMonoidAlgebra R M)
      (x := AddMonoidAlgebra.single (0 : Z) r)
    rw [show algebraMap (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) _ =
      incl R Z (AddMonoidAlgebra.single _ r) from rfl, incl_single] at hr
    have := hr.mul hx
    rwa [AddMonoidAlgebra.single_mul_single, mul_one, show ((0 : Z) : M) = 0 from rfl, zero_add] at this
  refine ⟨fun a => ?_⟩
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => exact isIntegral_zero
  | add f g hf hg => exact hf.add hg
  | single x r => exact hsing x r

/-- **The printed example of Remark 6.5 is not étale over `ℤ`.** `ℤ[ℤ/2]` is not formally unramified
over `ℤ`, so `D(ℤ/2)_ℤ → Spec ℤ` is not étale: the two ring maps to `𝔽₂[ε]` with `g ↦ 1`,
`g ↦ 1 + ε` agree modulo `ε`. -/
theorem not_formallyUnramified_int_zmod2 :
    ¬ Algebra.FormallyUnramified ℤ (AddMonoidAlgebra ℤ (ZMod 2)) := by
  intro h
  let B := DualNumber (ZMod 2)
  let eps : B := DualNumber.eps
  let I : Ideal B := Ideal.span {eps}
  have heps : eps * eps = 0 := DualNumber.eps_mul_eps
  have hI : I ^ 2 = ⊥ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, pow_two]
    exact heps
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h2B : (1 : B) + 1 = 0 := by
    have : (1 : B) + 1 = TrivSqZeroExt.inl ((1 : ZMod 2) + 1) := by
      rw [TrivSqZeroExt.inl_add, TrivSqZeroExt.inl_one]
    rw [this, h11, TrivSqZeroExt.inl_zero]
  have hu : ((1 : B) + eps) * ((1 : B) + eps) = 1 := by
    linear_combination heps + eps * h2B
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  let χ₁ : Multiplicative (ZMod 2) →* B := 1
  let χ₂ : Multiplicative (ZMod 2) →* B :=
    { toFun := fun x => if Multiplicative.toAdd x = 0 then 1 else 1 + eps
      map_one' := by simp
      map_mul' := by
        intro x y
        have hall : ∀ a b : ZMod 2, (if a + b = 0 then (1 : B) else 1 + eps) =
            (if a = 0 then 1 else 1 + eps) * (if b = 0 then 1 else 1 + eps) := by
          intro a b
          rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl <;>
            simp only [add_zero, zero_add, h11, h10, if_true, if_false, one_mul, mul_one, hu]
        exact hall (Multiplicative.toAdd x) (Multiplicative.toAdd y) }
  let g₁ : AddMonoidAlgebra ℤ (ZMod 2) →ₐ[ℤ] B := AddMonoidAlgebra.lift ℤ B (ZMod 2) χ₁
  let g₂ : AddMonoidAlgebra ℤ (ZMod 2) →ₐ[ℤ] B := AddMonoidAlgebra.lift ℤ B (ZMod 2) χ₂
  have hg₁ : ∀ x, g₁ (AddMonoidAlgebra.single x 1) = χ₁ (Multiplicative.ofAdd x) := by
    intro x; simp only [g₁, AddMonoidAlgebra.lift_single, one_zsmul]
  have hg₂ : ∀ x, g₂ (AddMonoidAlgebra.single x 1) = χ₂ (Multiplicative.ofAdd x) := by
    intro x; simp only [g₂, AddMonoidAlgebra.lift_single, one_zsmul]
  have heq : (Ideal.Quotient.mkₐ ℤ I).comp g₁ = (Ideal.Quotient.mkₐ ℤ I).comp g₂ := by
    apply AlgHom.coe_ringHom_injective
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun x => ?_)
    · have e : ∀ (g : AddMonoidAlgebra ℤ (ZMod 2) →ₐ[ℤ] B ⧸ I),
          g (AddMonoidAlgebra.single 0 r) = algebraMap ℤ _ r := by
        intro g
        rw [show (AddMonoidAlgebra.single (0 : ZMod 2) r : AddMonoidAlgebra ℤ (ZMod 2)) =
          algebraMap ℤ _ r from rfl, g.commutes]
      exact (e ((Ideal.Quotient.mkₐ ℤ I).comp g₁)).trans (e ((Ideal.Quotient.mkₐ ℤ I).comp g₂)).symm
    · change Ideal.Quotient.mk I (g₁ _) = Ideal.Quotient.mk I (g₂ _)
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, hg₁, hg₂]
      by_cases hx : x = 0
      · simp [χ₁, χ₂, hx]
      · have e2 : χ₂ (Multiplicative.ofAdd x) = 1 + eps := by simp [χ₂, hx]
        rw [e2]
        exact ⟨-1, by simp [χ₁]; ring⟩
  have := Algebra.FormallyUnramified.comp_injective I hI heq
  have h1 := DFunLike.congr_fun this (AddMonoidAlgebra.single (1 : ZMod 2) 1)
  rw [hg₁, hg₂] at h1
  have e2 : χ₂ (Multiplicative.ofAdd (1 : ZMod 2)) = 1 + eps := by simp [χ₂, h10]
  rw [e2] at h1
  have h0 : eps = 0 := by
    have : χ₁ (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := rfl
    rw [this] at h1
    linear_combination -h1
  have h3 := congrArg TrivSqZeroExt.snd h0
  rw [show TrivSqZeroExt.snd eps = (1 : ZMod 2) from DualNumber.snd_eps, TrivSqZeroExt.snd_zero] at h3
  exact h10 h3

end AlgMag.Leftover
