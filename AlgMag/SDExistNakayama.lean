/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3SchemeQuotient

/-!
# Lemma D, Step 3 (v): a finite flat graded algebra with a section on the closed orbit

Step 3 (v) of the proof of Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`,
at finite level (no henselization): `B → D` graded, finite, flat, an isomorphism modulo the closed orbit `I`.
Then `B → D` is bijective after inverting an invariant outside `q`. The note argues with the rank; here the two halves
are graded Nakayama and the equational criterion of flatness.
-/

universe u

namespace AlgMag.SD

open AlgMag.SQ

variable {R B D Γ : Type u} [CommRing R] [CommRing B] [CommRing D] [AddCommGroup Γ]
  {cB : Coact B Γ} {cD : Coact D Γ} {ι : R →+* B} [Algebra B D]

/-- `B → D` is graded. -/
def SDExist_IsGraded (cB : Coact B Γ) (cD : Coact D Γ) [Algebra B D] : Prop :=
  ∀ (d : Γ) (b : B), cD.comp d (algebraMap B D b) = algebraMap B D (cB.comp d b)

/-- A homogeneous ideal not contained in the closed orbit contains an invariant outside `q`. -/
theorem SDExist_exists_inv_mem (hι : cB.IsInv ι) {q : Ideal R} {I J : Ideal B} (hI : cB.IsHomIdeal I)
    (hIq : ∀ a, ι a ∈ I → a ∈ q) (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q)
    (hJ : cB.IsHomIdeal J) {r : B} (hr : r ∈ J) (hrI : r ∉ I) : ∃ h, h ∉ q ∧ ι h ∈ J := by
  obtain ⟨d, hd⟩ : ∃ d, cB.comp d r ∉ I := by
    by_contra hcon
    push Not at hcon
    exact hrI (cB.mem_of_comp_mem I r hcon)
  obtain ⟨h, hh, b, hb⟩ := exists_inv_of_homog hι hI hIq hmax (cB.comp_isHom d r) hd
  exact ⟨h, hh, hb ▸ J.mul_mem_right _ (hJ r hr d)⟩

variable (hg : SDExist_IsGraded cB cD)

include hg in
/-- The conductor of `B → D` is homogeneous. -/
theorem SDExist_conductor_hom :
    cB.IsHomIdeal
      { carrier := {b | ∀ y : D, ∃ b', algebraMap B D b * y = algebraMap B D b'}
        add_mem' := fun {a b} ha hb y => by
          obtain ⟨a', ha'⟩ := ha y
          obtain ⟨b', hb'⟩ := hb y
          exact ⟨a' + b', by rw [map_add, add_mul, ha', hb', map_add]⟩
        zero_mem' := fun y => ⟨0, by simp⟩
        smul_mem' := fun c {a} ha y => by
          obtain ⟨a', ha'⟩ := ha y
          exact ⟨c * a', by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, ha']⟩ } := by
  intro b hb d y
  induction y using cD.induction with
  | h0 => exact ⟨0, by simp⟩
  | hadd y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨c, hc⟩ := hz
    exact ⟨a + c, by rw [mul_add, ha, hc, map_add]⟩
  | hh e y hy =>
    obtain ⟨b', hb'⟩ := hb y
    refine ⟨cB.comp (d + e) b', ?_⟩
    rw [← hg d b, ← hg (d + e) b', ← hb', mul_comm (algebraMap B D b), cD.comp_mul_of_isHom hy, add_sub_cancel_right, mul_comm]

include hg in
/-- **Surjectivity** (graded Nakayama): if `B → D` is finite and onto modulo `I`, it is onto after inverting an invariant
outside `q`. -/
theorem SDExist_surj [Module.Finite B D] (hι : cB.IsInv ι) {q : Ideal R} [q.IsPrime] {I : Ideal B}
    (hI : cB.IsHomIdeal I) (hIq : ∀ a, ι a ∈ I → a ∈ q)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q)
    (H1 : ∀ y : D, ∃ b, y - algebraMap B D b ∈ I.map (algebraMap B D)) :
    ∃ h, h ∉ q ∧ ∀ y : D, ∃ b, algebraMap B D (ι h) * y = algebraMap B D b := by
  let L : Submodule B D := LinearMap.range (Algebra.linearMap B D)
  have htop : (⊤ : Submodule B (D ⧸ L)) ≤ I • ⊤ := by
    rintro x -
    obtain ⟨y, rfl⟩ := L.mkQ_surjective x
    obtain ⟨b, hb⟩ := H1 y
    have hz : y - algebraMap B D b ∈ (I • ⊤ : Submodule B D) := by
      rw [Ideal.smul_top_eq_map]
      exact hb
    have h2 := Submodule.mem_map_of_mem (f := L.mkQ) hz
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h2
    have h3 : L.mkQ (algebraMap B D b) = 0 := (Submodule.Quotient.mk_eq_zero L).2 ⟨b, rfl⟩
    rw [map_sub, h3, sub_zero] at h2
    exact h2
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
    Module.Finite.fg_top htop
  have h1I : (1 : B) ∉ I := fun h => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one q).2
    (hIq 1 (by rw [map_one]; exact h)))
  have hrI : r ∉ I := fun h => h1I (by simpa using I.sub_mem h hr1)
  have hrJ : ∀ y : D, ∃ b', algebraMap B D r * y = algebraMap B D b' := by
    intro y
    have h0 := hr (L.mkQ y) trivial
    rw [← map_smul] at h0
    obtain ⟨b', hb'⟩ := (Submodule.Quotient.mk_eq_zero L).1 h0
    exact ⟨b', by rw [← Algebra.smul_def]; exact hb'.symm⟩
  obtain ⟨h, hh, hJ⟩ := SDExist_exists_inv_mem hι hI hIq hmax (SDExist_conductor_hom hg) (r := r) hrJ hrI
  exact ⟨h, hh, hJ⟩

include hg in
/-- **Injectivity** on one element: flatness gives an annihilator outside the closed orbit. -/
theorem SDExist_inj_one [Module.Flat B D] (hι : cB.IsInv ι) {q : Ideal R} [q.IsPrime] {I : Ideal B}
    (hI : cB.IsHomIdeal I) (hIq : ∀ a, ι a ∈ I → a ∈ q)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q)
    {h₁ : R} (hh₁ : h₁ ∉ q) (hS : ∀ y : D, ∃ b, algebraMap B D (ι h₁) * y = algebraMap B D b)
    (𝔯 : Ideal D) [𝔯.IsPrime] (h𝔯 : ∀ a, algebraMap B D (ι a) ∈ 𝔯 → a ∈ q)
    {b : B} (hb : algebraMap B D b = 0) : ∃ h, h ∉ q ∧ ι h * b = 0 := by
  classical
  -- the kernel is contained in `I`
  have hK : RingHom.ker (algebraMap B D) ≤ I := by
    by_contra hcon
    have hlt : I < I ⊔ RingHom.ker (algebraMap B D) := lt_of_le_of_ne le_sup_left fun e => hcon (e ▸ le_sup_right)
    have hhomK : cB.IsHomIdeal (RingHom.ker (algebraMap B D)) := fun y hy d => by
      rw [RingHom.mem_ker] at hy ⊢
      rw [← hg, hy]
      simp [Coact.comp]
    obtain ⟨a, ha, haq⟩ := hmax _ (fun y hy d => by
      obtain ⟨i, hi, k, hk, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Coact.comp_add]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (hI i hi d)) (Ideal.mem_sup_right (hhomK k hk d))) hlt
    obtain ⟨i, hi, k, hk, hik⟩ := Submodule.mem_sup.1 ha
    apply haq
    have e0 : cB.comp 0 (ι a) = ι a := cB.comp_self_of_isHom ((hι.range _).2 ⟨a, rfl⟩)
    have e1 : ι a = ι (hι.r i) + ι (hι.r k) := by
      rw [hι.ι_r, hι.ι_r, ← Coact.comp_add, hik, e0]
    have e2 : a = hι.r i + hι.r k := hι.inj (by rw [map_add]; exact e1)
    rw [e2]
    refine q.add_mem (hIq _ (by rw [hι.ι_r]; exact hI i hi 0)) (h𝔯 _ ?_)
    rw [hι.ι_r]
    have : cB.comp 0 k ∈ RingHom.ker (algebraMap B D) := hhomK k hk 0
    rw [RingHom.mem_ker] at this
    rw [this]
    exact 𝔯.zero_mem
  -- reduce to homogeneous `b`
  have hom : ∀ (e : Γ) (b : B), cB.IsHom e b → algebraMap B D b = 0 → ∃ h, h ∉ q ∧ ι h * b = 0 := by
    intro e b hbe hb0
    obtain ⟨k, a, y, hy, hab⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := B) (M := D)
      (f := ![b]) (x := ![(1 : D)]) (by simp [Algebra.smul_def, hb0])
    choose c hc using fun j => hS (y j)
    let a₀ : B := ∑ j, a 0 j * c j
    have hb₀ : b * a₀ = 0 := by
      simp only [a₀, Finset.mul_sum, ← mul_assoc]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := hab j
      simp at this
      rw [this, zero_mul]
    have hg₀ : algebraMap B D a₀ = algebraMap B D (ι h₁) := by
      have h1 := hy 0
      simp only [Matrix.cons_val_zero] at h1
      have := congrArg (algebraMap B D (ι h₁) * ·) h1
      simp only [mul_one, Finset.mul_sum] at this
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← hc j, Algebra.smul_def]
      ring
    have ha₀ : a₀ ∉ I := fun hm => hh₁ (hIq _ (by
      have : ι h₁ - a₀ ∈ I := hK (by rw [RingHom.mem_ker, map_sub, hg₀, sub_self])
      simpa using I.add_mem this hm))
    let J : Ideal B :=
      { carrier := {x | x * b = 0}
        add_mem' := fun {x z} hx hz => by simp only [Set.mem_setOf_eq] at *; rw [add_mul, hx, hz, zero_add]
        zero_mem' := by simp
        smul_mem' := fun c {x} hx => by simp only [Set.mem_setOf_eq, smul_eq_mul] at *; rw [mul_assoc, hx, mul_zero] }
    have hJ : cB.IsHomIdeal J := by
      intro x hx d
      change cB.comp d x * b = 0
      have hx' : x * b = 0 := hx
      have := cB.comp_mul_of_isHom hbe x (d + e)
      rw [mul_comm b x, hx', add_sub_cancel_right] at this
      rw [mul_comm]
      simpa [Coact.comp] using this.symm
    obtain ⟨h, hh, hm⟩ := SDExist_exists_inv_mem hι hI hIq hmax hJ (r := a₀) (by
      change a₀ * b = 0
      rwa [mul_comm]) ha₀
    exact ⟨h, hh, hm⟩
  have hprod : ∀ s : Finset Γ, ∃ h, h ∉ q ∧ ∀ d ∈ s, ι h * cB.comp d b = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, (Ideal.ne_top_iff_one q).1 (Ideal.IsPrime.ne_top ‹_›), by simp⟩
    | insert d s _ ih =>
      obtain ⟨h, hh, hs⟩ := ih
      obtain ⟨h', hh', hd⟩ := hom d _ (cB.comp_isHom d b) (by rw [← hg, hb]; simp [Coact.comp])
      refine ⟨h * h', fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hh hh', fun e he => ?_⟩
      rw [map_mul]
      obtain rfl | he := Finset.mem_insert.1 he
      · rw [mul_assoc, hd, mul_zero]
      · rw [mul_right_comm, hs e he, zero_mul]
  obtain ⟨h, hh, hs⟩ := hprod (cB.σ b).coeff.support
  refine ⟨h, hh, ?_⟩
  rw [← cB.sum_eq b, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun d hd => hs d hd

end AlgMag.SD

#print axioms AlgMag.SD.SDExist_surj
#print axioms AlgMag.SD.SDExist_inj_one
