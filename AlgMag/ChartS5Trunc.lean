/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartAlgebraize
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.IdempotentFG

/-!
# Truncations at maximal ideals: the étale part of the Artin approximation step of the chart lemma

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

Pure commutative algebra.

* `quot_pow_bijective_of_etale`: an étale map with trivial residue extension at maximal ideals is
  bijective on truncations.
* `exists_lift_completion`, `ker_evalₐ_eq_pow`: lifting to the completion; its truncations.
* `quot_pow_transfer`: transfer of truncations from a bijection `A/IA ≃ B/IB`.
* `QA_trunc`: truncations of `P ⊗ A` against `P ⊗ P̂₀`.
* `quotient_trunc_equiv`: truncations of `(P ⊗ A)/(F)` inside `Ξ = (P ⊗ P̂₀)_𝔫`.
* `exists_N₀_isEtaleAt`, `span_syzygies_localization`: the étale conclusion of the Artin approximation step.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000

namespace AlgMag.ChartS5

open Ideal

/-- A power of a maximal ideal is primary, in the form used below. -/
lemma mem_pow_of_mul_mem {R : Type*} [CommRing R] (𝔞 : Ideal R) [h𝔞 : 𝔞.IsMaximal] (j : ℕ) {c x : R}
    (hc : c ∉ 𝔞) (h : c * x ∈ 𝔞 ^ j) : x ∈ 𝔞 ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hrad : (𝔞 ^ j).radical = 𝔞 := by
    rw [Ideal.radical_pow _ hj.ne', h𝔞.isPrime.radical]
  have hp : (𝔞 ^ j).IsPrimary := isPrimary_of_isMaximal_radical (by rw [hrad]; exact h𝔞)
  rw [mul_comm] at h
  rcases (isPrimary_iff.1 hp).2 h with h | h
  · exact h
  · rw [hrad] at h; exact absurd h hc

section T1

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Flatness: `x·v ∈ 𝔞^j B`, `v ∉ 𝔟` over `𝔞` implies `x ∈ 𝔞^j`. -/
lemma mem_of_flat_mul_mem [Module.Flat A B] (𝔞 : Ideal A) [𝔞.IsMaximal] (𝔟 : Ideal B)
    (h : 𝔟.comap (algebraMap A B) = 𝔞) (j : ℕ) {x : A} {v : B} (hv : v ∉ 𝔟)
    (hx : algebraMap A B x * v ∈ (𝔞 ^ j).map (algebraMap A B)) : x ∈ 𝔞 ^ j := by
  classical
  obtain ⟨c, t, ht, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.1 hx
  have hpre : ∀ y : t, ∃ a ∈ 𝔞 ^ j, algebraMap A B a = (y : B) := fun y => by
    obtain ⟨a, ha, hay⟩ := ht y.2
    exact ⟨a, ha, hay⟩
  choose a ha hay using hpre
  let f : Option t → A := fun o => o.elim x a
  let w : Option t → B := fun o => o.elim v (fun y => - c y)
  have hrel : ∑ o, f o • w o = 0 := by
    rw [Fintype.sum_option]
    simp only [f, w, Option.elim, Algebra.smul_def, hay]
    have : ∑ y : t, (y : B) * (- c y) = - ∑ y ∈ t, c y • y := by
      rw [← Finset.sum_coe_sort t, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [mul_comm]
    rw [this, hsum]; ring
  obtain ⟨k, M, z, hw, hM⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := B) (f := f) (x := w) hrel
  by_contra hxn
  apply hv
  have hv' : v = ∑ i, M none i • z i := hw none
  rw [hv']
  refine Ideal.sum_mem _ fun i _ => ?_
  have hMi : M none i ∈ 𝔞 := by
    by_contra hni
    apply hxn
    apply mem_pow_of_mul_mem 𝔞 j hni
    have h0 := hM i
    rw [Fintype.sum_option] at h0
    have h1 : M none i * x = - ∑ y : t, a y * M (some y) i := by
      have h2 : x * M none i + ∑ y : t, a y * M (some y) i = 0 := h0
      linear_combination h2
    rw [h1]
    exact neg_mem (Ideal.sum_mem _ fun y _ => Ideal.mul_mem_right _ _ (ha y))
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_right
  have : M none i ∈ 𝔟.comap (algebraMap A B) := h ▸ hMi
  exact this

/-- Formally unramified with trivial residue extension: `𝔟 = 𝔞B + 𝔟²`. -/
lemma le_map_sup_sq [Algebra.FormallyUnramified A B] (𝔞 : Ideal A) [𝔞.IsMaximal] (𝔟 : Ideal B)
    [𝔟.IsMaximal] (h : 𝔟.comap (algebraMap A B) = 𝔞)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔟).comp (algebraMap A B))) :
    𝔟 ≤ 𝔞.map (algebraMap A B) ⊔ 𝔟 ^ 2 := by
  set J := 𝔞.map (algebraMap A B) ⊔ 𝔟 ^ 2 with hJ
  have ha𝔟 : ∀ a ∈ 𝔞, algebraMap A B a ∈ 𝔟 := fun a ha => by
    have : a ∈ 𝔟.comap (algebraMap A B) := h ▸ ha
    exact this
  let e : (A ⧸ 𝔞) →ₐ[A] (B ⧸ 𝔟) := Ideal.Quotient.liftₐ 𝔞
    ((Ideal.Quotient.mkₐ A 𝔟).comp (Algebra.ofId A B))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (ha𝔟 a ha))
  have he : ∀ a, e (Ideal.Quotient.mk 𝔞 a) = Ideal.Quotient.mk 𝔟 (algebraMap A B a) := fun _ => rfl
  have hbij : Function.Bijective e := by
    constructor
    · refine (injective_iff_map_eq_zero e).2 fun y hy => ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [he, Ideal.Quotient.eq_zero_iff_mem] at hy
      have : a ∈ 𝔟.comap (algebraMap A B) := hy
      rw [h] at this
      exact Ideal.Quotient.eq_zero_iff_mem.2 this
    · intro y
      obtain ⟨a, ha⟩ := hres y
      exact ⟨Ideal.Quotient.mk 𝔞 a, by rw [he]; exact ha⟩
  let t : (A ⧸ 𝔞) →ₐ[A] (B ⧸ J) := Ideal.Quotient.liftₐ 𝔞
    ((Ideal.Quotient.mkₐ A J).comp (Algebra.ofId A B))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2
      ((show 𝔞.map (algebraMap A B) ≤ J from le_sup_left) (Ideal.mem_map_of_mem _ ha)))
  have ht : ∀ a, t (Ideal.Quotient.mk 𝔞 a) = Ideal.Quotient.mk J (algebraMap A B a) := fun _ => rfl
  let E := AlgEquiv.ofBijective e hbij
  let g₂ : B →ₐ[A] B ⧸ J := t.comp (E.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A 𝔟))
  have hg₂ : ∀ (a : A) (b : B), b - algebraMap A B a ∈ 𝔟 →
      g₂ b = Ideal.Quotient.mk J (algebraMap A B a) := by
    intro a b hb
    have : E.symm (Ideal.Quotient.mk 𝔟 b) = Ideal.Quotient.mk 𝔞 a := by
      rw [AlgEquiv.symm_apply_eq]
      rw [show E (Ideal.Quotient.mk 𝔞 a) = Ideal.Quotient.mk 𝔟 (algebraMap A B a) from he a]
      exact Ideal.Quotient.eq.2 hb
    change t (E.symm (Ideal.Quotient.mk 𝔟 b)) = _
    rw [this, ht]
  have hnil : IsNilpotent (𝔟.map (Ideal.Quotient.mk J)) :=
    ⟨2, by
      rw [← Ideal.map_pow]
      exact Ideal.map_mk_eq_bot_of_le le_sup_right⟩
  have hext : Ideal.Quotient.mkₐ A J = g₂ := by
    refine Algebra.FormallyUnramified.ext _ hnil fun x => ?_
    obtain ⟨a, ha⟩ := hres (Ideal.Quotient.mk 𝔟 x)
    have hd : x - algebraMap A B a ∈ 𝔟 := by
      have := Ideal.Quotient.eq.1 ha
      rw [← neg_sub]; exact neg_mem this
    rw [hg₂ a x hd, Ideal.Quotient.eq]
    change Ideal.Quotient.mk J x - _ ∈ _
    rw [← map_sub]
    exact Ideal.mem_map_of_mem _ hd
  intro b hb
  have h0 : g₂ b = 0 := by
    have := hg₂ 0 b (by simpa using hb)
    simpa using this
  rw [← hext] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

/-- Unramified locally at `𝔟`: there is `u ∉ 𝔟` with `u 𝔟 ⊆ 𝔞 B`. -/
lemma exists_mul_mem_map [Algebra.FormallyUnramified A B] [Algebra.FiniteType A B] (𝔞 : Ideal A)
    [h𝔞 : 𝔞.IsMaximal] (𝔟 : Ideal B) [h𝔟 : 𝔟.IsMaximal] (h : 𝔟.comap (algebraMap A B) = 𝔞)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔟).comp (algebraMap A B))) :
    ∃ u : B, u ∉ 𝔟 ∧ ∀ b ∈ 𝔟, u * b ∈ 𝔞.map (algebraMap A B) := by
  set 𝔠 := 𝔞.map (algebraMap A B) with h𝔠
  have h𝔠𝔟 : 𝔠 ≤ 𝔟 := Ideal.map_le_iff_le_comap.2 h.ge
  let _ : Field (A ⧸ 𝔞) := Ideal.Quotient.field 𝔞
  let _ : Algebra (A ⧸ 𝔞) (B ⧸ 𝔠) :=
    (Ideal.quotientMap 𝔠 (algebraMap A B) Ideal.le_comap_map).toAlgebra
  have : IsScalarTower A (A ⧸ 𝔞) (B ⧸ 𝔠) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType (A ⧸ 𝔞) (B ⧸ 𝔠) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A _ _
  have : IsNoetherianRing (B ⧸ 𝔠) := Algebra.FiniteType.isNoetherianRing (A ⧸ 𝔞) _
  set 𝔟' := 𝔟.map (Ideal.Quotient.mk 𝔠) with h𝔟'
  have hidem : IsIdempotentElem 𝔟' := by
    refine le_antisymm Ideal.mul_le_left ?_
    have h1 := Ideal.map_mono (f := Ideal.Quotient.mk 𝔠) (le_map_sup_sq 𝔞 𝔟 h hres)
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow, pow_two] at h1
    exact h1
  obtain ⟨e, he, hspan⟩ := (Ideal.isIdempotentElem_iff_of_fg 𝔟' (IsNoetherian.noetherian _)).1 hidem
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (1 - e)
  have hmem : ∀ y : B, Ideal.Quotient.mk 𝔠 y ∈ 𝔟' → y ∈ 𝔟 := by
    intro y hy
    obtain ⟨y', hy', hyy⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
    have := Ideal.Quotient.eq.1 hyy
    have h3 := 𝔟.sub_mem hy' (h𝔠𝔟 this)
    simpa using h3
  have heb : e ∈ 𝔟' := by rw [hspan]; exact Submodule.mem_span_singleton_self e
  refine ⟨u, fun hub => ?_, fun b hb => ?_⟩
  · apply h𝔟.ne_top
    rw [Ideal.eq_top_iff_one]
    apply hmem
    rw [map_one]
    have : (1 - e) ∈ 𝔟' := hu ▸ Ideal.mem_map_of_mem _ hub
    have h3 := 𝔟'.add_mem this heb
    simpa using h3
  · have hb' : Ideal.Quotient.mk 𝔠 b ∈ 𝔟' := Ideal.mem_map_of_mem _ hb
    rw [hspan] at hb'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hb'
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hu, ← hc, smul_eq_mul]
    have he2 : e * e = e := he
    linear_combination (-c) * he2

/-- `𝔟^j ⊆ 𝔞^j B + 𝔟^(j+1)`. -/
lemma pow_le_map_sup [Algebra.FormallyUnramified A B] (𝔞 : Ideal A) [𝔞.IsMaximal] (𝔟 : Ideal B)
    [𝔟.IsMaximal] (h : 𝔟.comap (algebraMap A B) = 𝔞)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔟).comp (algebraMap A B))) (j : ℕ) :
    𝔟 ^ j ≤ (𝔞 ^ j).map (algebraMap A B) ⊔ 𝔟 ^ (j + 1) := by
  have h𝔠𝔟 : 𝔞.map (algebraMap A B) ≤ 𝔟 := Ideal.map_le_iff_le_comap.2 h.ge
  induction j with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, Ideal.one_eq_top, Ideal.map_top]; simp
  | succ j ih =>
    have h1 := le_map_sup_sq 𝔞 𝔟 h hres
    rw [Ideal.map_pow] at ih ⊢
    rw [pow_succ 𝔟 j]
    refine (Ideal.mul_mono ih h1).trans ?_
    set 𝔠 := 𝔞.map (algebraMap A B)
    have hcj : 𝔠 ^ j ≤ 𝔟 ^ j := Ideal.pow_right_mono h𝔠𝔟 j
    rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact le_sup_of_le_left (by rw [pow_succ])
    · refine le_sup_of_le_right ?_
      calc 𝔠 ^ j * 𝔟 ^ 2 ≤ 𝔟 ^ j * 𝔟 ^ 2 := Ideal.mul_mono_left hcj
        _ = 𝔟 ^ (j + 1 + 1) := by ring
    · refine le_sup_of_le_right ?_
      calc 𝔟 ^ (j + 1) * 𝔠 ≤ 𝔟 ^ (j + 1) * 𝔟 := Ideal.mul_mono_right h𝔠𝔟
        _ = 𝔟 ^ (j + 1 + 1) := by ring
    · refine le_sup_of_le_right ?_
      rw [show 𝔟 ^ (j + 1) * 𝔟 ^ 2 = 𝔟 ^ (j + 1 + 1) * 𝔟 by ring]
      exact Ideal.mul_le_left

/-- Elements of `I B`, modulo `𝔟 K`, are images of elements of `I`, when `A → B/𝔟` is onto. -/
lemma exists_of_mem_map (𝔟 K : Ideal B) (I : Ideal A) (hIK : I.map (algebraMap A B) ≤ K)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔟).comp (algebraMap A B)))
    {w : B} (hw : w ∈ I.map (algebraMap A B)) :
    ∃ a ∈ I, w - algebraMap A B a ∈ 𝔟 * K := by
  refine Submodule.span_induction (p := fun w _ => ∃ a ∈ I, w - algebraMap A B a ∈ 𝔟 * K)
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, by simp⟩
  · exact ⟨0, I.zero_mem, by simp⟩
  · rintro x y - - ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
    refine ⟨a + b, I.add_mem ha hb, ?_⟩
    have := (𝔟 * K).add_mem hxa hyb
    rw [map_add]
    convert this using 1
    ring
  · rintro c x hx ⟨a, ha, hxa⟩
    obtain ⟨c₀, hc₀⟩ := hres (Ideal.Quotient.mk 𝔟 c)
    have hd : c - algebraMap A B c₀ ∈ 𝔟 := by
      have := Ideal.Quotient.eq.1 hc₀
      rw [← neg_sub]; exact neg_mem this
    refine ⟨c₀ * a, I.mul_mem_left _ ha, ?_⟩
    have h1 : (c - algebraMap A B c₀) * x ∈ 𝔟 * K := Ideal.mul_mem_mul hd (hIK hx)
    have h2 := (𝔟 * K).mul_mem_left (algebraMap A B c₀) hxa
    have := (𝔟 * K).add_mem h1 h2
    rw [smul_eq_mul, map_mul]
    convert this using 1
    ring

/-- **T1.** An étale map, at maximal ideals with trivial residue extension, is bijective on
truncations. No noetherian hypothesis. -/
theorem quot_pow_bijective_of_etale {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (𝔞 : Ideal A) [𝔞.IsMaximal] (𝔟 : Ideal B) [h𝔟 : 𝔟.IsMaximal]
    (h : 𝔟.comap (algebraMap A B) = 𝔞)
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔟).comp (algebraMap A B))) (j : ℕ) :
    (𝔟 ^ j).comap (algebraMap A B) = 𝔞 ^ j ∧
      Function.Surjective ((Ideal.Quotient.mk (𝔟 ^ j)).comp (algebraMap A B)) := by
  have h𝔠𝔟 : 𝔞.map (algebraMap A B) ≤ 𝔟 := Ideal.map_le_iff_le_comap.2 h.ge
  constructor
  · refine le_antisymm ?_ ?_
    · intro a ha
      obtain ⟨u, hu, hub⟩ := exists_mul_mem_map 𝔞 𝔟 h hres
      refine mem_of_flat_mul_mem 𝔞 𝔟 h j (v := u ^ j) (fun hc => hu (h𝔟.isPrime.mem_of_pow_mem _ hc)) ?_
      rw [Ideal.map_pow]
      have h1 : Ideal.span {u} * 𝔟 ≤ 𝔞.map (algebraMap A B) := by
        rw [Ideal.span_singleton_mul_le_iff]
        exact hub
      have h2 := Ideal.pow_right_mono h1 j
      rw [mul_pow, Ideal.span_singleton_pow] at h2
      have h3 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (u ^ j)) ha
      rw [mul_comm]
      exact h2 h3
    · rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono h𝔠𝔟 j
  · induction j with
    | zero =>
      intro y
      have : Subsingleton (B ⧸ 𝔟 ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
      exact ⟨0, Subsingleton.elim _ _⟩
    | succ j ih =>
      intro y
      obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨a, ha⟩ := ih (Ideal.Quotient.mk _ y₀)
      have hd : y₀ - algebraMap A B a ∈ 𝔟 ^ j := by
        have := Ideal.Quotient.eq.1 ha
        rw [← neg_sub]; exact neg_mem this
      obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.1 (pow_le_map_sup 𝔞 𝔟 h hres j hd)
      have hle : (𝔞 ^ j).map (algebraMap A B) ≤ 𝔟 ^ j := by
        rw [Ideal.map_pow]; exact Ideal.pow_right_mono h𝔠𝔟 j
      obtain ⟨a', ha', hw'⟩ := exists_of_mem_map 𝔟 (𝔟 ^ j) (𝔞 ^ j) hle hres hw
      refine ⟨a + a', ?_⟩
      refine (Ideal.Quotient.eq.2 ?_)
      have h1 : 𝔟 * 𝔟 ^ j = 𝔟 ^ (j + 1) := by ring
      rw [h1] at hw'
      have := (𝔟 ^ (j + 1)).add_mem hw' hz
      rw [map_add]
      have h2 := neg_mem this
      convert h2 using 1
      linear_combination hwz

end T1

section T3

/-- **T3.** Transfer of truncations: if `A/IA → B/IB` is bijective, `IB = IA B`, `IA ⊆ 𝔞^j`,
`IB ⊆ 𝔟^j`, then `A → B/𝔟^j` is onto with kernel `𝔞^j`. -/
theorem quot_pow_transfer {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B)
    (𝔞 : Ideal A) (𝔟 : Ideal B) (h : 𝔟.comap g = 𝔞) (j : ℕ) (IA : Ideal A) (IB : Ideal B)
    (hIA : IA ≤ 𝔞 ^ j) (hIB : IB ≤ 𝔟 ^ j) (hmap : IB = IA.map g) (hker : IB.comap g = IA)
    (hsurj : ∀ b : B, ∃ a : A, b - g a ∈ IB) :
    (𝔟 ^ j).comap g = 𝔞 ^ j ∧ Function.Surjective ((Ideal.Quotient.mk (𝔟 ^ j)).comp g) := by
  have hS : Function.Surjective ((Ideal.Quotient.mk (𝔟 ^ j)).comp g) := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hsurj b
    refine ⟨a, ?_⟩
    have := hIB ha
    exact (Ideal.Quotient.eq.2 this).symm
  refine ⟨?_, hS⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hIA1 : IA ≤ 𝔞 := hIA.trans (Ideal.pow_le_self hj.ne')
  have hIB1 : IB ≤ 𝔟 := hIB.trans (Ideal.pow_le_self hj.ne')
  have hbmap : 𝔟 = 𝔞.map g := by
    refine le_antisymm (fun b hb => ?_) (Ideal.map_le_iff_le_comap.2 h.ge)
    obtain ⟨a, ha⟩ := hsurj b
    have hga : g a ∈ 𝔟 := by
      have := 𝔟.sub_mem hb (hIB1 ha)
      simpa using this
    have ha𝔞 : a ∈ 𝔞 := h ▸ hga
    have : b = g a + (b - g a) := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mem_map_of_mem _ ha𝔞) ?_
    rw [hmap] at ha
    exact Ideal.map_mono hIA1 ha
  refine le_antisymm (fun a ha => ?_) ?_
  · have ha' : g a ∈ (𝔞 ^ j).map g := by
      rw [Ideal.map_pow, ← hbmap]; exact ha
    have key : ∀ w ∈ (𝔞 ^ j).map g, ∃ a ∈ 𝔞 ^ j, w - g a ∈ IB := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => ∃ a ∈ 𝔞 ^ j, w - g a ∈ IB) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨a, ha, by simp⟩
      · exact ⟨0, zero_mem _, by simp⟩
      · rintro x y - - ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
        refine ⟨a + b, add_mem ha hb, ?_⟩
        have := IB.add_mem hxa hyb
        rw [map_add]
        convert this using 1
        ring
      · rintro c x - ⟨a, ha, hxa⟩
        obtain ⟨c₀, hc₀⟩ := hsurj c
        obtain ⟨d, hd, hgd⟩ : ∃ d ∈ IA, True := ⟨0, IA.zero_mem, trivial⟩
        refine ⟨c₀ * a, (𝔞 ^ j).mul_mem_left _ ha, ?_⟩
        have hga : g a ∈ (𝔞 ^ j).map g := Ideal.mem_map_of_mem _ ha
        have hx : x ∈ (𝔞 ^ j).map g := by
          have : x = (x - g a) + g a := by ring
          rw [this]
          refine Ideal.add_mem _ ?_ hga
          rw [hmap] at hxa
          exact Ideal.map_mono hIA hxa
        have h1 : (c - g c₀) * g a ∈ IB := IB.mul_mem_right _ hc₀
        have h2 := IB.mul_mem_left c hxa
        have h3 := IB.add_mem h1 h2
        rw [smul_eq_mul, map_mul]
        convert h3 using 1
        ring
    obtain ⟨a₀, ha₀, hd⟩ := key _ ha'
    rw [← map_sub] at hd
    have hd' : a - a₀ ∈ IA := hker ▸ hd
    have : a = (a - a₀) + a₀ := by ring
    rw [this]
    exact add_mem (hIA hd') ha₀
  · rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 h.ge) j

end T3

section T2

universe u

/-- One lifting step along `P₀/𝔭^(m+1) → P₀/𝔭^m`, `m ≥ 1`. -/
lemma exists_lift_step {P₀ A' : Type u} [CommRing P₀] [CommRing A'] [Algebra P₀ A']
    [Algebra.FormallyEtale P₀ A'] (𝔭 : Ideal P₀) {m : ℕ} (hm : 1 ≤ m) (τ : A' →ₐ[P₀] P₀ ⧸ 𝔭 ^ m) :
    ∃ τ' : A' →ₐ[P₀] P₀ ⧸ 𝔭 ^ (m + 1),
      (Ideal.Quotient.factorₐ P₀ (Ideal.pow_le_pow_right (Nat.le_succ m))).comp τ' = τ := by
  let g : (P₀ ⧸ 𝔭 ^ (m + 1)) →ₐ[P₀] P₀ ⧸ 𝔭 ^ m :=
    Ideal.Quotient.factorₐ P₀ (Ideal.pow_le_pow_right (Nat.le_succ m))
  have hg : Function.Surjective g :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ m))
  have hk : IsNilpotent (RingHom.ker (g : (P₀ ⧸ 𝔭 ^ (m + 1)) →+* P₀ ⧸ 𝔭 ^ m)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
    intro z hz
    refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hx' : x ∈ 𝔭 ^ m := Ideal.Quotient.eq_zero_iff_mem.1 hx
      have hy' : y ∈ 𝔭 ^ m := Ideal.Quotient.eq_zero_iff_mem.1 hy
      have : x * y ∈ 𝔭 ^ (m + 1) :=
        Ideal.pow_le_pow_right (by omega : m + 1 ≤ m + m) (by
          rw [pow_add]; exact Ideal.mul_mem_mul hx' hy')
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem.2 this]
      exact zero_mem _
    · exact add_mem hx hy
  exact ⟨Algebra.FormallySmooth.liftOfSurjective τ g hg hk,
    Algebra.FormallySmooth.comp_liftOfSurjective τ g hg hk⟩

/-- **T2.** A `P₀`-map from an étale algebra to a truncation lifts to the completion. -/
theorem exists_lift_completion {P₀ A' : Type u} [CommRing P₀] [CommRing A'] [Algebra P₀ A']
    [Algebra.Etale P₀ A'] (𝔭 : Ideal P₀) [𝔭.IsMaximal] {N : ℕ} (hN : 1 ≤ N)
    (σ : A' →ₐ[P₀] P₀ ⧸ 𝔭 ^ N) :
    ∃ θ : A' →ₐ[P₀] AdicCompletion 𝔭 P₀, ∀ a, AdicCompletion.evalₐ 𝔭 N (θ a) = σ a := by
  have step : ∀ (m : ℕ), ∀ (τ : A' →ₐ[P₀] P₀ ⧸ 𝔭 ^ (N + m)), ∃ τ' : A' →ₐ[P₀] P₀ ⧸ 𝔭 ^ (N + m + 1),
      (Ideal.Quotient.factorₐ P₀ (Ideal.pow_le_pow_right (Nat.le_succ (N + m)))).comp τ' = τ :=
    fun m τ => exists_lift_step 𝔭 (by omega) τ
  choose s hs using step
  let τ : ∀ n, A' →ₐ[P₀] P₀ ⧸ 𝔭 ^ (N + n) := fun n =>
    Nat.rec (motive := fun n => A' →ₐ[P₀] P₀ ⧸ 𝔭 ^ (N + n)) σ (fun n t => s n t) n
  have hτ : ∀ n x, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (N + n)))
      (τ (n + 1) x) = τ n x := fun n x => AlgHom.congr_fun (hs n (τ n)) x
  have hchain : ∀ m n (hmn : m ≤ n) x, Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_left hmn N)) (τ n x) = τ m x := by
    intro m n hmn x
    induction n, hmn using Nat.le_induction with
    | base =>
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (τ m x)
      rw [← hy]; rfl
    | succ n hmn ih =>
      rw [← ih, ← hτ n x]
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (τ (n + 1) x)
      rw [← hy]; rfl
  let f : ∀ n, A' →ₐ[P₀] P₀ ⧸ 𝔭 ^ n := fun n =>
    (Ideal.Quotient.factorₐ P₀ (Ideal.pow_le_pow_right (Nat.le_add_left n N))).comp (τ n)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ P₀ (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    intro m n hle
    ext x
    change Ideal.Quotient.factor (Ideal.pow_le_pow_right hle)
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left n N)) (τ n x)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left m N)) (τ m x)
    rw [← hchain m n hle x]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (τ n x)
    rw [← hy]; rfl
  refine ⟨AdicCompletion.liftAlgHom 𝔭 f hf, fun a => ?_⟩
  rw [AdicCompletion.evalₐ_liftAlgHom]
  have h0 := hchain 0 N (Nat.zero_le N) a
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_left N N)) (τ N a) = σ a
  exact h0

/-- The kernel of `evalₐ` is the extended power. -/
lemma ker_evalₐ_eq_map {P₀ : Type u} [CommRing P₀] (𝔭 : Ideal P₀) (fg : 𝔭.FG) (j : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ 𝔭 j) =
      (𝔭 ^ j).map (algebraMap P₀ (AdicCompletion 𝔭 P₀)) := by
  ext x
  trans x ∈ (AdicCompletion.eval 𝔭 P₀ j).ker
  · have eq : 𝔭 ^ j • (⊤ : Ideal P₀) = 𝔭 ^ j := by simp
    have hinj : Function.Injective (Ideal.Quotient.factor (le_of_eq eq)) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le (le_of_eq eq.symm)
    rw [RingHom.mem_ker, LinearMap.mem_ker, ← AdicCompletion.factor_eval_eq_evalₐ 𝔭 x (le_of_eq eq)]
    exact map_eq_zero_iff _ hinj
  · rw [← AdicCompletion.pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map]
    rfl

/-- `ph := ker (evalₐ 𝔭 1)` is `𝔭 P̂₀`. -/
lemma ker_evalₐ_one_eq_map {P₀ : Type u} [CommRing P₀] (𝔭 : Ideal P₀) (fg : 𝔭.FG) :
    RingHom.ker (AdicCompletion.evalₐ 𝔭 1) = 𝔭.map (algebraMap P₀ (AdicCompletion 𝔭 P₀)) := by
  rw [ker_evalₐ_eq_map 𝔭 fg 1, pow_one]

/-- **T2.** The truncations of the completion: `evalₐ 𝔭 j` (surjective, by
`AdicCompletion.surjective_evalₐ`) has kernel `ph^j`. -/
theorem ker_evalₐ_eq_pow {P₀ : Type u} [CommRing P₀] [IsNoetherianRing P₀] (𝔭 : Ideal P₀) (j : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ 𝔭 j) = RingHom.ker (AdicCompletion.evalₐ 𝔭 1) ^ j := by
  have fg : 𝔭.FG := IsNoetherian.noetherian 𝔭
  rw [ker_evalₐ_eq_map 𝔭 fg j, ker_evalₐ_one_eq_map 𝔭 fg, Ideal.map_pow]

end T2

section T4

open TensorProduct

universe u₀ u₁ u₂ u₃

/-- The map `P ⊗ A → P ⊗ R` induced by `θ : A → R`, as a ring homomorphism. -/
noncomputable abbrev gQ {P₀ : Type u₀} {P : Type u₁} {A : Type u₂} {Rh : Type u₃} [CommRing P₀]
    [CommRing P] [CommRing A] [CommRing Rh] [Algebra P₀ P] [Algebra P₀ A] [Algebra P₀ Rh]
    (θ : A →ₐ[P₀] Rh) : P ⊗[P₀] A →+* P ⊗[P₀] Rh :=
  (Algebra.TensorProduct.map (AlgHom.id P₀ P) θ).toRingHom

variable {P₀ : Type u₀} {P : Type u₁} {A : Type u₂} {Rh : Type u₃} [CommRing P₀]
    [CommRing P] [CommRing A] [CommRing Rh] [Algebra P₀ P] [Algebra P₀ A] [Algebra P₀ Rh]

lemma map_id_surjective {X Y : Type*} [CommRing X] [CommRing Y] [Algebra P₀ X] [Algebra P₀ Y]
    (g : X →ₐ[P₀] Y) (hg : Function.Surjective g) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id P₀ P) g) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul p z =>
    obtain ⟨a, rfl⟩ := hg z
    exact ⟨p ⊗ₜ a, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/-- The preimage of a maximal ideal under a map onto the residue field is maximal. -/
lemma comap_isMaximal_of_surj {X Y : Type*} [CommRing X] [CommRing Y] (g : X →+* Y) (𝔫 : Ideal Y)
    [h𝔫 : 𝔫.IsMaximal] (hs : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp g)) :
    (𝔫.comap g).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => h𝔫.ne_top ?_, fun J x hle hx hxJ => ?_⟩
  · rw [Ideal.eq_top_iff_one]
    simpa using h1
  · obtain ⟨y, i, hi, hyi⟩ := h𝔫.exists_inv (show g x ∉ 𝔫 from hx)
    obtain ⟨y₀, hy₀⟩ := hs (Ideal.Quotient.mk 𝔫 y)
    have hd : g y₀ - y ∈ 𝔫 := Ideal.Quotient.eq.1 hy₀
    have h1 : (1 : X) - y₀ * x ∈ 𝔫.comap g := by
      rw [Ideal.mem_comap, map_sub, map_one, map_mul]
      have : 1 - g y₀ * g x = i - (g y₀ - y) * g x := by linear_combination -hyi
      rw [this]
      exact 𝔫.sub_mem hi (𝔫.mul_mem_right _ hd)
    have := J.add_mem (hle h1) (J.mul_mem_left y₀ hxJ)
    simpa using this

/-- Abstract form of `QA_trunc`: `ph` is any ideal of `Rh` with `ph ⊆ (θ⁻¹ ph) Rh`. -/
theorem QA_trunc_aux (θ : A →ₐ[P₀] Rh) (ph : Ideal Rh)
    (hph : ph ≤ (ph.comap θ).map θ)
    (hA : ∀ j, (ph ^ j).comap θ = (ph.comap θ) ^ j ∧
      Function.Surjective ((Ideal.Quotient.mk (ph ^ j)).comp (θ : A →+* Rh)))
    (𝔫 : Ideal (P ⊗[P₀] Rh)) [𝔫.IsMaximal]
    (hn : ph.map (Algebra.TensorProduct.includeRight : Rh →ₐ[P₀] P ⊗[P₀] Rh) ≤ 𝔫) :
    (𝔫.comap (gQ (P := P) θ)).IsMaximal ∧ ∀ j,
      (𝔫 ^ j).comap (gQ (P := P) θ) = (𝔫.comap (gQ (P := P) θ)) ^ j ∧
      Function.Surjective ((Ideal.Quotient.mk (𝔫 ^ j)).comp (gQ (P := P) θ)) := by
  set 𝔮 := ph.comap θ with h𝔮
  let incA : A →+* P ⊗[P₀] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[P₀] P ⊗[P₀] A).toRingHom
  let incR : Rh →+* P ⊗[P₀] Rh :=
    (Algebra.TensorProduct.includeRight : Rh →ₐ[P₀] P ⊗[P₀] Rh).toRingHom
  have hcomm : (gQ (P := P) θ).comp incA = incR.comp (θ : A →+* Rh) := by
    ext x
    simp [incA, incR, gQ]
  have hqmap : 𝔮.map (θ : A →+* Rh) = ph :=
    le_antisymm (Ideal.map_le_iff_le_comap.2 le_rfl) hph
  have hn' : ph.map incR ≤ 𝔫 := hn
  have key : ∀ j, (𝔮 ^ j).map incA ≤ (𝔫.comap (gQ (P := P) θ)) ^ j ∧ (ph ^ j).map incR ≤ 𝔫 ^ j ∧
      (ph ^ j).map incR = ((𝔮 ^ j).map incA).map (gQ (P := P) θ) ∧
      ((ph ^ j).map incR).comap (gQ (P := P) θ) = (𝔮 ^ j).map incA ∧
      ∀ b, ∃ a, b - gQ (P := P) θ a ∈ (ph ^ j).map incR := by
    intro j
    let πR : Rh →ₐ[P₀] Rh ⧸ ph ^ j := Ideal.Quotient.mkₐ P₀ (ph ^ j)
    let πA : A →ₐ[P₀] Rh ⧸ ph ^ j := πR.comp θ
    have hπR : Function.Surjective πR := Ideal.Quotient.mkₐ_surjective _ _
    have hπA : Function.Surjective πA := (hA j).2
    have kR : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id P₀ P) πR) = (ph ^ j).map incR := by
      have h1 := Algebra.TensorProduct.lTensor_ker (A := P) πR hπR
      have h2 : RingHom.ker πR = ph ^ j := Ideal.Quotient.mkₐ_ker P₀ (ph ^ j)
      rw [h1, h2]; rfl
    have kA : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id P₀ P) πA) = (𝔮 ^ j).map incA := by
      have h1 := Algebra.TensorProduct.lTensor_ker (A := P) πA hπA
      have h2 : RingHom.ker πA = 𝔮 ^ j := by
        rw [← (hA j).1]
        ext x
        rw [RingHom.mem_ker]
        exact Ideal.Quotient.eq_zero_iff_mem
      rw [h1, h2]; rfl
    have hcompat : ∀ y, Algebra.TensorProduct.map (AlgHom.id P₀ P) πA y =
        Algebra.TensorProduct.map (AlgHom.id P₀ P) πR (gQ (P := P) θ y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul p z => simp [gQ, πA]
      | add x y hx hy => simp only [map_add, hx, hy]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ j
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : gQ (P := P) θ (incA x) = incR (θ x) := RingHom.congr_fun hcomm x
      change gQ (P := P) θ (incA x) ∈ 𝔫
      rw [h1]
      exact hn' (Ideal.mem_map_of_mem _ hx)
    · rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hn' j
    · rw [Ideal.map_map, hcomm, ← Ideal.map_map]
      congr 1
      rw [Ideal.map_pow, hqmap]
    · ext y
      rw [Ideal.mem_comap, ← kR, ← kA, RingHom.mem_ker, RingHom.mem_ker, hcompat]
    · intro b
      obtain ⟨a, ha⟩ := map_id_surjective (P := P) πA hπA
        (Algebra.TensorProduct.map (AlgHom.id P₀ P) πR b)
      refine ⟨a, ?_⟩
      rw [← kR, RingHom.mem_ker, map_sub, ← hcompat, ha, sub_self]
  have hsurj1 : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (gQ (P := P) θ)) := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := (key 1).2.2.2.2 b
    refine ⟨a, (Ideal.Quotient.eq.2 ?_).symm⟩
    have := (key 1).2.1 ha
    rwa [pow_one] at this
  refine ⟨?_, fun j => ?_⟩
  · exact comap_isMaximal_of_surj _ 𝔫 hsurj1
  · obtain ⟨h1, h2, h3, h4, h5⟩ := key j
    exact quot_pow_transfer (gQ (P := P) θ) (𝔫.comap (gQ (P := P) θ)) 𝔫 rfl j _ _ h1 h2 h3 h4 h5

/-- **T4 (the QR step).** `Q_A = P ⊗ A`, `Q = P ⊗ P̂₀`, `𝔫 ⊂ Q` maximal over `ph`, `θ : A → P̂₀` with
`A → P̂₀/ph^j` onto with kernel `(θ⁻¹ ph)^j`. Then `𝔫_A = gQ⁻¹ 𝔫` is maximal and `Q_A → Q/𝔫^j` is onto
with kernel `𝔫_A^j`. -/
theorem QA_trunc {P₀ : Type u₀} {P : Type u₁} {A : Type u₂} [CommRing P₀] [IsNoetherianRing P₀]
    [CommRing P] [CommRing A] [Algebra P₀ P] [Algebra P₀ A] (𝔭 : Ideal P₀)
    (θ : A →ₐ[P₀] AdicCompletion 𝔭 P₀)
    (hA : ∀ j, (RingHom.ker (AdicCompletion.evalₐ 𝔭 1) ^ j).comap θ =
        ((RingHom.ker (AdicCompletion.evalₐ 𝔭 1)).comap θ) ^ j ∧
      Function.Surjective ((Ideal.Quotient.mk (RingHom.ker (AdicCompletion.evalₐ 𝔭 1) ^ j)).comp
        (θ : A →+* AdicCompletion 𝔭 P₀)))
    (𝔫 : Ideal (P ⊗[P₀] AdicCompletion 𝔭 P₀)) [𝔫.IsMaximal]
    (hn : (RingHom.ker (AdicCompletion.evalₐ 𝔭 1)).map (Algebra.TensorProduct.includeRight :
      AdicCompletion 𝔭 P₀ →ₐ[P₀] P ⊗[P₀] AdicCompletion 𝔭 P₀) ≤ 𝔫) :
    (𝔫.comap (gQ (P := P) θ)).IsMaximal ∧ ∀ j,
      (𝔫 ^ j).comap (gQ (P := P) θ) = (𝔫.comap (gQ (P := P) θ)) ^ j ∧
      Function.Surjective ((Ideal.Quotient.mk (𝔫 ^ j)).comp (gQ (P := P) θ)) := by
  refine QA_trunc_aux θ _ ?_ hA 𝔫 hn
  have fg : 𝔭.FG := IsNoetherian.noetherian 𝔭
  conv_lhs => rw [ker_evalₐ_one_eq_map 𝔭 fg]
  rw [Ideal.map_le_iff_le_comap]
  intro p hp
  have hmem : algebraMap P₀ (AdicCompletion 𝔭 P₀) p ∈ RingHom.ker (AdicCompletion.evalₐ 𝔭 1) := by
    rw [ker_evalₐ_one_eq_map 𝔭 fg]; exact Ideal.mem_map_of_mem _ hp
  have h1 : θ (algebraMap P₀ A p) = algebraMap P₀ _ p := θ.commutes p
  rw [Ideal.mem_comap, ← h1]
  refine Ideal.mem_map_of_mem _ ?_
  change θ (algebraMap P₀ A p) ∈ RingHom.ker (AdicCompletion.evalₐ 𝔭 1)
  rw [h1]; exact hmem

end T4

section Trunc

variable {C D : Type*} [CommRing C] [CommRing D]

/-- A ring map bijective on truncations gives an isomorphism of truncations. -/
noncomputable def truncEquiv (φ : C →+* D) (𝔞 : Ideal C) (𝔪 : Ideal D) (j : ℕ)
    (hc : (𝔪 ^ j).comap φ = 𝔞 ^ j) (hs : Function.Surjective ((Ideal.Quotient.mk (𝔪 ^ j)).comp φ)) :
    (C ⧸ 𝔞 ^ j) ≃+* D ⧸ 𝔪 ^ j :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift (𝔞 ^ j) ((Ideal.Quotient.mk (𝔪 ^ j)).comp φ) (fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (by
        have : a ∈ (𝔪 ^ j).comap φ := hc ▸ ha
        exact this)))
    (by
      constructor
      · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
        have h1 : Ideal.Quotient.mk (𝔪 ^ j) (φ a) = 0 := hy
        have h0 : φ a ∈ 𝔪 ^ j := Ideal.Quotient.eq_zero_iff_mem.1 h1
        have h2 : a ∈ (𝔪 ^ j).comap φ := h0
        rw [hc] at h2
        exact Ideal.Quotient.eq_zero_iff_mem.2 h2
      · intro y
        obtain ⟨a, ha⟩ := hs y
        exact ⟨Ideal.Quotient.mk _ a, ha⟩)

@[simp] lemma truncEquiv_mk (φ : C →+* D) (𝔞 : Ideal C) (𝔪 : Ideal D) (j : ℕ)
    (hc : (𝔪 ^ j).comap φ = 𝔞 ^ j) (hs : Function.Surjective ((Ideal.Quotient.mk (𝔪 ^ j)).comp φ))
    (y : C) : truncEquiv φ 𝔞 𝔪 j hc hs (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (φ y) := rfl

/-- `y` maps into `(φ F) + 𝔪^j` iff `y ∈ (F) + 𝔞^j`. -/
lemma mem_sup_of_map_mem {s : ℕ} (φ : C →+* D) (𝔞 : Ideal C) (𝔪 : Ideal D) (F : Fin s → C) (j : ℕ)
    (hc : (𝔪 ^ j).comap φ = 𝔞 ^ j) (hs : Function.Surjective ((Ideal.Quotient.mk (𝔪 ^ j)).comp φ))
    {y : C} (hy : φ y ∈ Ideal.span (Set.range fun ℓ => φ (F ℓ)) ⊔ 𝔪 ^ j) :
    y ∈ Ideal.span (Set.range F) ⊔ 𝔞 ^ j := by
  obtain ⟨w, hw, m, hm, hwm⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hw
  have hlift : ∀ ℓ, ∃ d : C, c ℓ - φ d ∈ 𝔪 ^ j := fun ℓ => by
    obtain ⟨d, hd⟩ := hs (Ideal.Quotient.mk _ (c ℓ))
    exact ⟨d, Ideal.Quotient.eq.1 hd.symm⟩
  choose d hd using hlift
  have h1 : y - ∑ ℓ, d ℓ * F ℓ ∈ 𝔞 ^ j := by
    rw [← hc, Ideal.mem_comap, map_sub, map_sum]
    have : φ y - ∑ ℓ, φ (d ℓ * F ℓ) = ∑ ℓ, (c ℓ - φ (d ℓ)) * φ (F ℓ) + m := by
      rw [← hwm]
      simp only [map_mul, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [this]
    exact add_mem (Ideal.sum_mem _ fun ℓ _ => Ideal.mul_mem_right _ _ (hd ℓ)) hm
  have h2 : ∑ ℓ, d ℓ * F ℓ ∈ Ideal.span (Set.range F) :=
    Ideal.sum_mem _ fun ℓ _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨ℓ, rfl⟩)
  have : y = ∑ ℓ, d ℓ * F ℓ + (y - ∑ ℓ, d ℓ * F ℓ) := by ring
  rw [this]
  exact Submodule.add_mem_sup h2 h1

/-- The truncations of `C/(F)` are those of `D/(φ F)`, when `φ` is bijective on truncations. -/
noncomputable def truncQuotEquiv {s : ℕ} (φ : C →+* D) (𝔞 : Ideal C) (𝔪 : Ideal D) (F : Fin s → C)
    (j : ℕ) (hc : (𝔪 ^ j).comap φ = 𝔞 ^ j)
    (hs : Function.Surjective ((Ideal.Quotient.mk (𝔪 ^ j)).comp φ)) :
    ((C ⧸ Ideal.span (Set.range F)) ⧸ (𝔞.map (Ideal.Quotient.mk (Ideal.span (Set.range F)))) ^ j) ≃+*
      D ⧸ (Ideal.span (Set.range fun ℓ => φ (F ℓ)) ⊔ 𝔪 ^ j) :=
  have hmem : ∀ a, a ∈ Ideal.span (Set.range F) →
      φ a ∈ Ideal.span (Set.range fun ℓ => φ (F ℓ)) ⊔ 𝔪 ^ j := fun a ha =>
    Ideal.mem_sup_left (by
      have h : Ideal.span (Set.range F) ≤
          (Ideal.span (Set.range fun ℓ => φ (F ℓ))).comap φ := by
        rw [Ideal.span_le]
        rintro _ ⟨ℓ, rfl⟩
        exact Ideal.subset_span ⟨ℓ, rfl⟩
      exact h ha)
  let ψ₀ : (C ⧸ Ideal.span (Set.range F)) →+* D ⧸ (Ideal.span (Set.range fun ℓ => φ (F ℓ)) ⊔ 𝔪 ^ j) :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp φ)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hmem a ha))
  have hψ₀ : ∀ a ∈ 𝔞 ^ j, ψ₀ (Ideal.Quotient.mk _ a) = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (by
      have : a ∈ (𝔪 ^ j).comap φ := hc ▸ ha
      exact this))
  RingEquiv.ofBijective
    (Ideal.Quotient.lift _ ψ₀ (fun z hz => by
      rw [← Ideal.map_pow] at hz
      obtain ⟨a, ha, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hz
      exact hψ₀ a ha))
    (by
      constructor
      · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        have h1 : Ideal.Quotient.mk (Ideal.span (Set.range fun ℓ => φ (F ℓ)) ⊔ 𝔪 ^ j) (φ y) = 0 := hy
        have h2 := mem_sup_of_map_mem φ 𝔞 𝔪 F j hc hs (Ideal.Quotient.eq_zero_iff_mem.1 h1)
        obtain ⟨i, hi, a, ha, rfl⟩ := Submodule.mem_sup.1 h2
        rw [Ideal.Quotient.eq_zero_iff_mem, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hi, zero_add,
          ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ ha
      · intro y
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨a, ha⟩ := hs (Ideal.Quotient.mk _ y)
        refine ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a), ?_⟩
        have h1 : y - φ a ∈ 𝔪 ^ j := Ideal.Quotient.eq.1 ha.symm
        exact (Ideal.Quotient.eq.2 (Ideal.mem_sup_right h1)).symm)

@[simp] lemma truncQuotEquiv_mk {s : ℕ} (φ : C →+* D) (𝔞 : Ideal C) (𝔪 : Ideal D) (F : Fin s → C)
    (j : ℕ) (hc : (𝔪 ^ j).comap φ = 𝔞 ^ j)
    (hs : Function.Surjective ((Ideal.Quotient.mk (𝔪 ^ j)).comp φ)) (y : C) :
    truncQuotEquiv φ 𝔞 𝔪 F j hc hs (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ y)) =
      Ideal.Quotient.mk _ (φ y) := rfl

section Localization

variable {Q : Type*} [CommRing Q] (𝔫 : Ideal Q) [h𝔫 : 𝔫.IsMaximal]

/-- `Q → Q_𝔫/𝔪^j` has kernel `𝔫^j`. -/
lemma comap_localization_pow (j : ℕ) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j).comap
      (algebraMap Q (Localization.AtPrime 𝔫)) = 𝔫 ^ j := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [Ideal.mem_comap, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
      IsLocalization.mem_map_algebraMap_iff 𝔫.primeCompl] at hx
    obtain ⟨⟨a, s⟩, hx⟩ := hx
    rw [← map_mul] at hx
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔫.primeCompl _).1 hx
    have hcs : (c : Q) * (s : Q) ∉ 𝔫 := fun h => (h𝔫.isPrime.mem_or_mem h).elim c.2 s.2
    refine mem_pow_of_mul_mem 𝔫 j hcs ?_
    have h1 : (c : Q) * s * x = (c : Q) * (a : Q) := by
      linear_combination hc
    rw [h1]
    exact Ideal.mul_mem_left _ _ a.2
  · rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]

/-- `Q → Q_𝔫/𝔪^j` is onto. -/
lemma surjective_localization_pow (j : ℕ) : Function.Surjective
    ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j)).comp
      (algebraMap Q (Localization.AtPrime 𝔫))) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, u, rfl⟩ := IsLocalization.exists_mk'_eq 𝔫.primeCompl z
  obtain ⟨v, i, hi, hvi⟩ := h𝔫.exists_inv (show (u : Q) ∉ 𝔫 from u.2)
  have hcop : IsCoprime (u : Q) (i ^ j) :=
    IsCoprime.pow_right ⟨v, 1, by linear_combination hvi⟩
  obtain ⟨p, q, hpq⟩ := hcop
  refine ⟨a * p, ?_⟩
  symm
  refine Ideal.Quotient.eq.2 ?_
  set z := IsLocalization.mk' (Localization.AtPrime 𝔫) a u with hz
  have hzu : z * algebraMap Q _ (u : Q) = algebraMap Q _ a := IsLocalization.mk'_spec _ _ _
  have h1 : z - algebraMap Q (Localization.AtPrime 𝔫) (a * p) =
      z * algebraMap Q _ q * (algebraMap Q _ i) ^ j := by
    have h2 := congrArg (algebraMap Q (Localization.AtPrime 𝔫)) hpq
    simp only [map_add, map_mul, map_pow, map_one] at h2
    rw [map_mul, ← hzu]
    linear_combination (-z) * h2
  rw [h1]
  apply Ideal.mul_mem_left
  apply Ideal.pow_mem_pow
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ 𝔫 _).2 hi

end Localization

end Trunc

section T5

open TensorProduct

variable {P₀ P A Rh : Type*} [CommRing P₀] [CommRing P] [CommRing A] [CommRing Rh] [Algebra P₀ P]
  [Algebra P₀ A] [Algebra P₀ Rh]

/-- The natural map `Q_A → Ξ = Q_𝔫`. -/
noncomputable abbrev toΞ (θ : A →ₐ[P₀] Rh) (𝔫 : Ideal (P ⊗[P₀] Rh)) [𝔫.IsMaximal] :
    P ⊗[P₀] A →+* Localization.AtPrime 𝔫 :=
  (algebraMap (P ⊗[P₀] Rh) (Localization.AtPrime 𝔫)).comp (gQ θ)

lemma toΞ_comap (θ : A →ₐ[P₀] Rh) (𝔫 : Ideal (P ⊗[P₀] Rh)) [𝔫.IsMaximal] (j : ℕ)
    (h : (𝔫 ^ j).comap (gQ (P := P) θ) = (𝔫.comap (gQ (P := P) θ)) ^ j) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j).comap (toΞ θ 𝔫) =
      (𝔫.comap (gQ (P := P) θ)) ^ j := by
  rw [← h, ← comap_localization_pow 𝔫 j, Ideal.comap_comap]

lemma toΞ_surjective (θ : A →ₐ[P₀] Rh) (𝔫 : Ideal (P ⊗[P₀] Rh)) [𝔫.IsMaximal] (j : ℕ)
    (hs : Function.Surjective ((Ideal.Quotient.mk (𝔫 ^ j)).comp (gQ (P := P) θ))) :
    Function.Surjective ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j)).comp (toΞ θ 𝔫)) := by
  intro y
  obtain ⟨b, hb⟩ := surjective_localization_pow 𝔫 j y
  obtain ⟨a, ha⟩ := hs (Ideal.Quotient.mk _ b)
  refine ⟨a, ?_⟩
  rw [← hb]
  have h1 : gQ (P := P) θ a - b ∈ 𝔫 ^ j := Ideal.Quotient.eq.1 ha
  refine Ideal.Quotient.eq.2 ?_
  have h2 := (comap_localization_pow 𝔫 j).ge h1
  rw [Ideal.mem_comap, map_sub] at h2
  exact h2

/-- **T5.** `G = Q_A/(F)`, `𝔴` the image of `𝔫_A`, `Ξ = Q_𝔫`, `F'` the image of `F` in `Ξ`:
`G/𝔴^j ≃ Ξ/((F') + 𝔪^j)`. The hypotheses `h`, `hs` are the conclusions of `QA_trunc`. -/
noncomputable def quotient_trunc_equiv {s : ℕ} (θ : A →ₐ[P₀] Rh) (𝔫 : Ideal (P ⊗[P₀] Rh))
    [𝔫.IsMaximal] (F : Fin s → P ⊗[P₀] A) (j : ℕ)
    (h : (𝔫 ^ j).comap (gQ (P := P) θ) = (𝔫.comap (gQ (P := P) θ)) ^ j)
    (hs : Function.Surjective ((Ideal.Quotient.mk (𝔫 ^ j)).comp (gQ (P := P) θ))) :
    ((P ⊗[P₀] A ⧸ Ideal.span (Set.range F)) ⧸
        ((𝔫.comap (gQ (P := P) θ)).map (Ideal.Quotient.mk (Ideal.span (Set.range F)))) ^ j) ≃+*
      Localization.AtPrime 𝔫 ⧸
        (Ideal.span (Set.range fun ℓ => algebraMap (P ⊗[P₀] Rh) (Localization.AtPrime 𝔫)
            (gQ θ (F ℓ))) ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) ^ j) :=
  truncQuotEquiv (toΞ θ 𝔫) _ _ F j (toΞ_comap θ 𝔫 j h) (toΞ_surjective θ 𝔫 j hs)

/-- **T5.** `quotient_trunc_equiv` sends the class of `y : Q_A` to the class of its image in `Ξ`. -/
lemma quotient_trunc_equiv_mk {s : ℕ} (θ : A →ₐ[P₀] Rh) (𝔫 : Ideal (P ⊗[P₀] Rh))
    [𝔫.IsMaximal] (F : Fin s → P ⊗[P₀] A) (j : ℕ)
    (h : (𝔫 ^ j).comap (gQ (P := P) θ) = (𝔫.comap (gQ (P := P) θ)) ^ j)
    (hs : Function.Surjective ((Ideal.Quotient.mk (𝔫 ^ j)).comp (gQ (P := P) θ)))
    (y : P ⊗[P₀] A) :
    quotient_trunc_equiv θ 𝔫 F j h hs (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ y)) =
      Ideal.Quotient.mk _ (algebraMap (P ⊗[P₀] Rh) (Localization.AtPrime 𝔫) (gQ θ y)) := rfl

/-- `𝔴` is maximal when `F` lies in `𝔫_A`. -/
lemma isMaximal_map_quot {C : Type*} [CommRing C] {s : ℕ} (𝔞 : Ideal C) [h𝔞 : 𝔞.IsMaximal]
    (F : Fin s → C) (hF : ∀ ℓ, F ℓ ∈ 𝔞) :
    (𝔞.map (Ideal.Quotient.mk (Ideal.span (Set.range F)))).IsMaximal := by
  have hle : Ideal.span (Set.range F) ≤ 𝔞 := by
    rw [Ideal.span_le]; rintro _ ⟨ℓ, rfl⟩; exact hF ℓ
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span (Set.range F)))
    Ideal.Quotient.mk_surjective h𝔞 with h | h
  · exfalso
    have h1 : (1 : C ⧸ Ideal.span (Set.range F)) ∈ 𝔞.map (Ideal.Quotient.mk (Ideal.span (Set.range F))) := by
      rw [h]; trivial
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h1
    rw [← map_one (Ideal.Quotient.mk (Ideal.span (Set.range F)))] at hy1
    have h2 := hle (Ideal.Quotient.eq.1 hy1)
    have h3 := 𝔞.sub_mem hy h2
    apply h𝔞.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using h3
  · exact h

end T5

section Syzygies

/-- Syzygies localize: if `r` generates the syzygies of `f` over `Q`, the images generate the
syzygies of the image of `f` over `Q_𝔫`. -/
theorem span_syzygies_localization {Q : Type*} [CommRing Q] (𝔫 : Ideal Q) [h𝔫 : 𝔫.IsPrime] {s t : ℕ}
    (f : Fin s → Q) (r : Fin t → Fin s → Q)
    (hr : Submodule.span Q (Set.range r) = LinearMap.ker (Fintype.linearCombination Q f)) :
    Submodule.span (Localization.AtPrime 𝔫)
        (Set.range fun j ℓ => algebraMap Q (Localization.AtPrime 𝔫) (r j ℓ)) =
      LinearMap.ker (Fintype.linearCombination (Localization.AtPrime 𝔫)
        fun ℓ => algebraMap Q (Localization.AtPrime 𝔫) (f ℓ)) := by
  classical
  set φ := algebraMap Q (Localization.AtPrime 𝔫) with hφ
  have hker : ∀ a : Fin s → Q, a ∈ Submodule.span Q (Set.range r) ↔ ∑ ℓ, a ℓ * f ℓ = 0 := by
    intro a
    rw [hr, LinearMap.mem_ker, Fintype.linearCombination_apply]
    simp
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h0 := (hker (r j)).1 (Submodule.subset_span ⟨j, rfl⟩)
    change _ ∈ LinearMap.ker _
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    have := congrArg φ h0
    simpa [map_sum] using this
  · intro a ha
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at ha
    obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples_of_finite 𝔫.primeCompl a
    choose b hb using hu
    have hb' : ∀ ℓ, φ (b ℓ) = φ (u : Q) * a ℓ := fun ℓ => by
      rw [hb ℓ, Algebra.smul_def]
    have h1 : φ (∑ ℓ, b ℓ * f ℓ) = 0 := by
      rw [map_sum]
      have : ∑ ℓ, φ (b ℓ * f ℓ) = φ (u : Q) * ∑ ℓ, a ℓ • φ (f ℓ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [map_mul, hb', smul_eq_mul]; ring
      rw [this, ha, mul_zero]
    obtain ⟨v, hv⟩ := (IsLocalization.map_eq_zero_iff 𝔫.primeCompl _ _).1 h1
    have h2 : (fun ℓ => (v : Q) * b ℓ) ∈ Submodule.span Q (Set.range r) := by
      rw [hker]
      rw [Finset.mul_sum] at hv
      rw [← hv]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
    obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun Q).1 h2
    have hunit : IsUnit (φ ((v : Q) * u)) :=
      IsLocalization.map_units (Localization.AtPrime 𝔫)
        (⟨(v : Q) * u, (𝔫.primeCompl).mul_mem v.2 u.2⟩ : 𝔫.primeCompl)
    obtain ⟨w, hw⟩ := hunit.exists_left_inv
    have hval : a = w • ∑ j, φ (e j) •
        (fun ℓ => φ (r j ℓ)) := by
      funext ℓ
      have h3 := congrFun he ℓ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      have h4 : ∑ j, φ (e j) * φ (r j ℓ) = φ ((v : Q) * u) * a ℓ := by
        simp only [← map_mul]
        rw [← map_sum, h3, map_mul, hb', map_mul]; ring
      rw [h4, ← mul_assoc, hw, one_mul]
    rw [hval]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨j, rfl⟩

end Syzygies

section T6

universe v w

/-- **T6.** The étale step of the Artin approximation, with `N₀` chosen before `R`, `S`: it depends on `f`, `r` only.
Truncations of `R` at `p` are those of `Ξ/(f)`, truncations of `S` at `q` those of `Ξ/(f')`, and the
two presentations agree modulo `𝔫²`. Then `S` is étale over `R` at `q`. -/
theorem exists_N₀_isEtaleAt {Ξ : Type v} [CommRing Ξ] [IsNoetherianRing Ξ] (𝔫 : Ideal Ξ)
    [𝔫.IsMaximal] {s t : ℕ} (f : Fin s → Ξ) (r : Fin t → Fin s → Ξ)
    (hr : Submodule.span Ξ (Set.range r) = LinearMap.ker (Fintype.linearCombination Ξ f)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (f' : Fin s → Ξ) (r' : Fin t → Fin s → Ξ),
      (∀ ℓ, f' ℓ - f ℓ ∈ 𝔫 ^ (N + 1)) → (∀ j ℓ, r' j ℓ - r j ℓ ∈ 𝔫 ^ (N + 1)) →
      (∀ j, ∑ ℓ, r' j ℓ * f' ℓ = 0) →
      ∀ {R S : Type w} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
        [IsNoetherianRing R] [IsNoetherianRing S] (p : Ideal R) [p.IsMaximal] (q : Ideal S)
        [q.IsMaximal] (_hq : q.comap (algebraMap R S) = p)
        (eA : ∀ j, (R ⧸ p ^ j) ≃+* Ξ ⧸ (Ideal.span (Set.range f) ⊔ 𝔫 ^ j))
        (eB : ∀ j, (S ⧸ q ^ j) ≃+* Ξ ⧸ (Ideal.span (Set.range f') ⊔ 𝔫 ^ j)),
        (∀ (a : R) (ξ : Ξ), eA 2 (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ξ →
          eB 2 (Ideal.Quotient.mk _ (algebraMap R S a)) = Ideal.Quotient.mk _ ξ) →
        Algebra.IsEtaleAt R q := by
  obtain ⟨N₀, hN₀⟩ := ChartAlg.lemma51_initial 𝔫 f r hr
  refine ⟨N₀, fun N hN f' r' hf hr' hs => ?_⟩
  intro R S _ _ _ _ _ _ p _ q _ hq eA eB hcompat
  have hin := hN₀ N hN f' r' hf hr' hs
  have : q.LiesOver p := ⟨hq.symm⟩
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have hL : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  have : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [hL.algebraMap_eq]; infer_instance
  have hscal : ∀ a : R, algebraMap (Localization.AtPrime p) (Localization.AtPrime q)
      (algebraMap R _ a) = algebraMap S _ (algebraMap R S a) := by
    intro a
    rw [hL.algebraMap_eq, Localization.localRingHom_to_map]
  let bA : ∀ j, (R ⧸ p ^ j) ≃+* Localization.AtPrime p ⧸ _ := fun j =>
    truncEquiv (algebraMap R (Localization.AtPrime p)) p _ j (comap_localization_pow p j)
      (surjective_localization_pow p j)
  let bB : ∀ j, (S ⧸ q ^ j) ≃+* Localization.AtPrime q ⧸ _ := fun j =>
    truncEquiv (algebraMap S (Localization.AtPrime q)) q _ j (comap_localization_pow q j)
      (surjective_localization_pow q j)
  let eA' := fun j => (bA j).symm.trans (eA j)
  let eB' := fun j => (bB j).symm.trans (eB j)
  have hT := ChartAlg.truncationsBijective_of_presentations 𝔫 _ _ hin eA' eB' (by
    intro a ξ hξ
    obtain ⟨a₀, ha₀⟩ := surjective_localization_pow p 2 (Ideal.Quotient.mk _ a)
    have ha₀' : (bA 2) (Ideal.Quotient.mk _ a₀) = Ideal.Quotient.mk _ a := ha₀
    have h1 : eA 2 (Ideal.Quotient.mk _ a₀) = Ideal.Quotient.mk _ ξ := by
      rw [← hξ]
      change _ = eA 2 ((bA 2).symm _)
      rw [← ha₀', RingEquiv.symm_apply_apply]
    have h2 := hcompat a₀ ξ h1
    rw [← h2]
    change eB 2 ((bB 2).symm _) = _
    congr 1
    rw [RingEquiv.symm_apply_eq]
    change _ = Ideal.Quotient.mk _ (algebraMap S (Localization.AtPrime q) (algebraMap R S a₀))
    rw [← hscal]
    refine Ideal.Quotient.eq.2 ?_
    have h3 : a - algebraMap R _ a₀ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ 2 :=
      Ideal.Quotient.eq.1 ha₀.symm
    have h4 : IsLocalRing.maximalIdeal (Localization.AtPrime p) ≤
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)).comap
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
      fun x hx => map_nonunit (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) x hx
    have h5 := Ideal.le_comap_pow _ 2 (Ideal.pow_right_mono h4 2 h3)
    rw [Ideal.mem_comap, map_sub] at h5
    exact h5)
  exact ChartAlg.isEtaleAt_of_truncationsBijective p q hT (ChartAlg.map_eq_of_truncationsBijective hT)

end T6

end AlgMag.ChartS5
