/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDExistNakayama
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Lemma D, Step 3 (v): the uniform invariant `h`, and the section

Step 3 (v) of the proof of Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, at
finite level. If `B → D` is graded, finite, flat, finitely presented and onto modulo the closed orbit, then a single
invariant `h ∉ q` makes `B_h → D_h` bijective. Hence a section `D → B_h`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

variable {R B D Γ : Type u} [CommRing R] [CommRing B] [CommRing D] [AddCommGroup Γ]
  {cB : Coact B Γ} {cD : Coact D Γ} {ι : R →+* B} [Algebra B D]

/-- Step 3 (v), elementwise: one invariant `h ∉ q` handles both the cokernel and the kernel of `B → D`. -/
theorem SDLocA_uniform [Module.Finite B D] [Module.Flat B D] [Algebra.FinitePresentation B D]
    (hg : SDExist_IsGraded cB cD) (hι : cB.IsInv ι) {q : Ideal R} [q.IsPrime] {I : Ideal B}
    (hI : cB.IsHomIdeal I) (hIq : ∀ a, ι a ∈ I → a ∈ q)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q)
    (H1 : ∀ y : D, ∃ b, y - algebraMap B D b ∈ I.map (algebraMap B D))
    (𝔯 : Ideal D) [𝔯.IsPrime] (h𝔯 : ∀ a, algebraMap B D (ι a) ∈ 𝔯 → a ∈ q) :
    ∃ h, h ∉ q ∧ (∀ y : D, ∃ b, algebraMap B D (ι h) * y = algebraMap B D b) ∧
      ∀ b : B, algebraMap B D b = 0 → ∃ n : ℕ, ι h ^ n * b = 0 := by
  classical
  obtain ⟨h₁, hh₁, hS⟩ := SDExist_surj hg hι hI hIq hmax H1
  let S := Localization.Away (ι h₁)
  let f : S →ₐ[S] S ⊗[B] D := Algebra.ofId S (S ⊗[B] D)
  have hf0 : ∀ x : S, f x = x ⊗ₜ[B] (1 : D) := fun x => rfl
  have hsw : ∀ (x : S) (b : B) (y : D), (x * algebraMap B S b) ⊗ₜ[B] y = x ⊗ₜ[B] (algebraMap B D b * y) := by
    intro x b y
    rw [mul_comm x, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
  have hfa : ∀ b : B, f (algebraMap B S b) = (1 : S) ⊗ₜ[B] algebraMap B D b := fun b => by
    rw [hf0, ← one_mul (algebraMap B S b), hsw, mul_one]
  obtain ⟨v, hv⟩ : ∃ v : S, v * algebraMap B S (ι h₁) = 1 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := S) (ι h₁)).exists_left_inv)
  have hf : Function.Surjective f := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero f⟩
    | add a c ha hc =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨c', rfl⟩ := hc
      exact ⟨a' + c', map_add f _ _⟩
    | tmul s y =>
      obtain ⟨b, hb⟩ := hS y
      refine ⟨s * v * algebraMap B S b, ?_⟩
      rw [hf0, hsw, mul_one, ← hb, ← hsw, mul_assoc, hv, mul_one]
  have hker : (RingHom.ker f.toRingHom).FG := Algebra.FinitePresentation.ker_fG_of_surjective f hf
  obtain ⟨t, ht⟩ := hker
  have hloc : IsLocalizedModule (Submonoid.powers (ι h₁)) (TensorProduct.mk B S D 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers (ι h₁)) S _).2 (TensorProduct.isBaseChange B D S)
  have hone : ∀ s ∈ t, ∃ h', h' ∉ q ∧ algebraMap B S (ι h') * s = 0 := by
    intro s hs
    have hsk : f s = 0 := by
      have : s ∈ RingHom.ker f.toRingHom := ht ▸ Ideal.subset_span hs
      exact this
    obtain ⟨⟨g, m⟩, hgm⟩ := IsLocalization.surj (Submonoid.powers (ι h₁)) s
    simp only at hgm
    have h1 : (1 : S) ⊗ₜ[B] algebraMap B D g = 0 := by
      rw [← hfa, ← hgm, map_mul, hsk, zero_mul]
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (ι h₁)) (TensorProduct.mk B S D 1)).1 h1
    have hc' : algebraMap B D ((c : B) * g) = 0 := by
      rw [map_mul, ← Algebra.smul_def]
      exact hc
    obtain ⟨h', hh', hz⟩ := SDExist_inj_one hg hι hI hIq hmax hh₁ hS 𝔯 h𝔯 hc'
    refine ⟨h', hh', ?_⟩
    have hum := IsLocalization.map_units S m
    have huc := IsLocalization.map_units S c
    have h2 : algebraMap B S (ι h') * s * algebraMap B S m * algebraMap B S c = 0 := by
      have : algebraMap B S (ι h' * ((c : B) * g)) = 0 := by rw [hz, map_zero]
      rw [map_mul, map_mul, ← hgm] at this
      rw [← this]
      ring
    exact hum.mul_left_eq_zero.1 (huc.mul_left_eq_zero.1 h2)
  have hall : ∀ t' : Finset S, (∀ s ∈ t', ∃ h', h' ∉ q ∧ algebraMap B S (ι h') * s = 0) →
      ∃ H, H ∉ q ∧ ∀ s ∈ t', algebraMap B S (ι H) * s = 0 := by
    intro t'
    induction t' using Finset.induction_on with
    | empty => exact fun _ => ⟨1, (Ideal.ne_top_iff_one q).1 (Ideal.IsPrime.ne_top ‹_›), by simp⟩
    | insert a t' _ ih =>
      intro hh
      obtain ⟨H, hH, hs0⟩ := ih fun s hs => hh s (Finset.mem_insert_of_mem hs)
      obtain ⟨h', hh', ha⟩ := hh a (Finset.mem_insert_self _ _)
      refine ⟨H * h', fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hH hh', fun s hs => ?_⟩
      rw [map_mul, map_mul]
      obtain rfl | hs' := Finset.mem_insert.1 hs
      · rw [mul_assoc, ha, mul_zero]
      · rw [mul_right_comm, hs0 s hs', zero_mul]
  obtain ⟨H, hH, hs⟩ := hall t hone
  have hspan : ∀ s : S, f s = 0 → algebraMap B S (ι H) * s = 0 := by
    intro s hfs
    have hm : s ∈ Ideal.span (t : Set S) := by
      rw [ht]
      exact hfs
    clear hfs
    induction hm using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact mul_zero _
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  refine ⟨h₁ * H, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hh₁ hH, fun y => ?_, fun b hb => ?_⟩
  · obtain ⟨b, hb⟩ := hS y
    refine ⟨ι H * b, ?_⟩
    rw [map_mul, map_mul, map_mul, ← hb]
    ring
  · have h3 : algebraMap B S (ι H * b) = 0 := by
      rw [map_mul]
      apply hspan
      rw [hfa, hb, TensorProduct.tmul_zero]
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (ι h₁)) S _).1 h3
    obtain ⟨m, hm⟩ := c.2
    refine ⟨m + 1, ?_⟩
    have hc' : ι h₁ ^ m * (ι H * b) = 0 := by
      have hm' : ι h₁ ^ m = (c : B) := hm
      rw [hm']
      exact hc
    calc ι (h₁ * H) ^ (m + 1) * b = ι H ^ m * ι h₁ * (ι h₁ ^ m * (ι H * b)) := by rw [map_mul]; ring
      _ = 0 := by rw [hc', mul_zero]

/-- Step 3 (v): `B_h → D_h` is bijective, for the `h` of `SDLocA_uniform`. -/
theorem SDLocA_bijective {h : B} (hsurj : ∀ y : D, ∃ b, algebraMap B D h * y = algebraMap B D b)
    (hinj : ∀ b : B, algebraMap B D b = 0 → ∃ n : ℕ, h ^ n * b = 0) :
    Function.Bijective (IsLocalization.Away.map (Localization.Away h)
      (Localization.Away (algebraMap B D h)) (algebraMap B D) h) := by
  set φ := IsLocalization.Away.map (Localization.Away h) (Localization.Away (algebraMap B D h)) (algebraMap B D) h
  have hφ : ∀ b : B, φ (algebraMap B _ b) = algebraMap D _ (algebraMap B D b) := fun b =>
    IsLocalization.map_eq _ b
  have huB : IsUnit (algebraMap B (Localization.Away h) h) := IsLocalization.Away.algebraMap_isUnit h
  have huD : IsUnit (algebraMap D (Localization.Away (algebraMap B D h)) (algebraMap B D h)) :=
    IsLocalization.Away.algebraMap_isUnit _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨b, m⟩, hbm⟩ := IsLocalization.surj (Submonoid.powers h) x
    simp only at hbm
    have h0 : algebraMap D (Localization.Away (algebraMap B D h)) (algebraMap B D b) = 0 := by
      rw [← hφ, ← hbm, map_mul, hx, zero_mul]
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap B D h)) _ _).1 h0
    obtain ⟨k, hk⟩ := c.2
    have h1 : algebraMap B D (h ^ k * b) = 0 := by
      have hk' : algebraMap B D h ^ k = (c : D) := hk
      rw [map_mul, map_pow, hk']
      exact hc
    obtain ⟨n, hn⟩ := hinj _ h1
    have h2 : algebraMap B (Localization.Away h) b = 0 :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers h) _ _).2
        ⟨⟨h ^ n * h ^ k, ⟨n + k, pow_add _ _ _⟩⟩, by simpa [mul_assoc] using hn⟩
    rw [h2] at hbm
    exact ((IsLocalization.map_units _ m).mul_left_eq_zero).1 hbm
  · intro z
    obtain ⟨⟨y, m⟩, hym⟩ := IsLocalization.surj (Submonoid.powers (algebraMap B D h)) z
    simp only at hym
    obtain ⟨k, hk⟩ := m.2
    obtain ⟨b, hb⟩ := hsurj y
    obtain ⟨w, hw⟩ := huB.exists_left_inv
    refine ⟨algebraMap B _ b * w ^ (k + 1), ?_⟩
    have hφw : φ w * algebraMap D _ (algebraMap B D h) = 1 := by
      rw [← hφ, ← map_mul, hw, map_one]
    have e : algebraMap D (Localization.Away (algebraMap B D h)) (algebraMap B D h) ^ (k + 1) * φ w ^ (k + 1) = 1 := by
      rw [← mul_pow, mul_comm, hφw, one_pow]
    rw [map_mul, map_pow, hφ, ← hb, map_mul]
    have hym' : z * algebraMap D _ (algebraMap B D h) ^ k = algebraMap D _ y := by
      have hk' : algebraMap B D h ^ k = (m : D) := hk
      rw [← map_pow, hk']
      exact hym
    rw [← hym']
    calc _ = z * (algebraMap D (Localization.Away (algebraMap B D h)) (algebraMap B D h) ^ (k + 1) * φ w ^ (k + 1)) := by ring
      _ = z := by rw [e, mul_one]

/-- Step 3 (v), the **section**: a ring map `D → B_h` under `B`. It replaces "rank 1, so `B ≅ D`" of the note. -/
theorem SDLocA_section {h : B} (hsurj : ∀ y : D, ∃ b, algebraMap B D h * y = algebraMap B D b)
    (hinj : ∀ b : B, algebraMap B D b = 0 → ∃ n : ℕ, h ^ n * b = 0) :
    ∃ s : D →+* Localization.Away h, ∀ b : B, s (algebraMap B D b) = algebraMap B _ b := by
  let E := RingEquiv.ofBijective _ (SDLocA_bijective hsurj hinj)
  refine ⟨E.symm.toRingHom.comp (algebraMap D (Localization.Away (algebraMap B D h))), fun b => ?_⟩
  change E.symm _ = _
  rw [RingEquiv.symm_apply_eq]
  change _ = IsLocalization.Away.map (Localization.Away h) (Localization.Away (algebraMap B D h)) (algebraMap B D) h
    (algebraMap B _ b)
  exact (IsLocalization.map_eq _ b).symm

end AlgMag.SD

#print axioms AlgMag.SD.SDLocA_uniform
#print axioms AlgMag.SD.SDLocA_bijective
#print axioms AlgMag.SD.SDLocA_section
