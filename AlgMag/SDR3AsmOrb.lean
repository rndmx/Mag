/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmIso
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Lemma D, Steps 7-9: closed orbit above a homogeneous ideal, section in degree `0`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

section Orbit

variable {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ] {ι : A₀ →+* A}

/-- The closed orbit of the fibre over `q`, above a homogeneous ideal `J₀` with invariants in `q`
(`exists_maximal_homIdeal` is the case `J₀ = 0`). -/
lemma SDR3Asm_orbit_above (c : Coact A Γ) (q : Ideal A₀) (J₀ : Ideal A) (hJ₀ : c.IsHomIdeal J₀)
    (hq : ∀ a, ι a ∈ J₀ → a ∈ q) :
    ∃ I : Ideal A, J₀ ≤ I ∧ c.IsHomIdeal I ∧ (∀ a, ι a ∈ I → a ∈ q) ∧
      ∀ J, c.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q := by
  let s : Set (Ideal A) := {I | c.IsHomIdeal I ∧ ∀ a, ι a ∈ I → a ∈ q}
  obtain ⟨I, hle, hI⟩ := zorn_le_nonempty₀ s (fun C hC hch y hy => by
    have hne : C.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) C := hch.directedOn
    refine ⟨sSup C, ⟨fun z hz d => ?_, fun a ha => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨K, hK, hzK⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hz
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨K, hK, (hC hK).1 z hzK d⟩
    · obtain ⟨K, hK, hzK⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 ha
      exact (hC hK).2 a hzK) J₀ ⟨hJ₀, hq⟩
  refine ⟨I, hle, hI.prop.1, hI.prop.2, fun J hJ hlt => ?_⟩
  by_contra hcon
  push Not at hcon
  exact absurd (hI.le_of_ge ⟨hJ, hcon⟩ hlt.le) (not_le_of_gt hlt)

end Orbit

section Base

variable {R B Γ : Type u} (R₂ : Type u) [CommRing R] [CommRing B] [CommRing R₂] [AddCommGroup Γ]
  [Algebra R B] [Algebra R R₂] (cB : Coact B Γ)
  (hcB : ∀ r : R, cB.σ (algebraMap R B r) = AddMonoidAlgebra.single 0 (algebraMap R B r))

/-- The generators of `J₀ = P₂(R₂ ⊗ B) + (R₂ ⊗ I)`. -/
def SDR3Asm_gen (P₂ : Ideal R₂) (I : Ideal B) : Set (R₂ ⊗[R] B) :=
  {y | (∃ p ∈ P₂, ∃ b, y = p ⊗ₜ[R] b) ∨ (∃ r, ∃ i ∈ I, y = r ⊗ₜ[R] i)}

/-- `J₀ = P₂(R₂ ⊗ B) + (R₂ ⊗ I)`. -/
def SDR3Asm_J₀ (P₂ : Ideal R₂) (I : Ideal B) : Ideal (R₂ ⊗[R] B) := Ideal.span (SDR3Asm_gen R₂ P₂ I)

variable {R₂}

lemma SDR3Asm_J₀_induct (P₂ : Ideal R₂) (I : Ideal B) {p : R₂ ⊗[R] B → Prop} (h0 : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b)) (hg : ∀ y ∈ SDR3Asm_gen R₂ P₂ I, p y) {y : R₂ ⊗[R] B}
    (hy : y ∈ SDR3Asm_J₀ R₂ P₂ I) : p y := by
  have hm : ∀ (a : R₂ ⊗[R] B), ∀ y ∈ SDR3Asm_gen R₂ P₂ I, p (a * y) := by
    intro a y hy
    induction a using TensorProduct.induction_on with
    | zero => simpa using h0
    | add a c ha hc =>
      rw [add_mul]
      exact hadd _ _ ha hc
    | tmul r b =>
      refine hg _ ?_
      rcases hy with ⟨q, hq, b', rfl⟩ | ⟨r', i, hi, rfl⟩
      · left
        exact ⟨r * q, P₂.mul_mem_left _ hq, b * b', by rw [Algebra.TensorProduct.tmul_mul_tmul]⟩
      · right
        exact ⟨r * r', b * i, I.mul_mem_left _ hi, by rw [Algebra.TensorProduct.tmul_mul_tmul]⟩
  have key : ∀ a : R₂ ⊗[R] B, p (a * y) := by
    induction hy using Submodule.span_induction with
    | mem x hx => exact fun a => hm a x hx
    | zero => exact fun a => by simpa using h0
    | add x z _ _ hx hz =>
      intro a
      rw [mul_add]
      exact hadd _ _ (hx a) (hz a)
    | smul b x _ hx =>
      intro a
      rw [smul_eq_mul, ← mul_assoc]
      exact hx _
  simpa using key 1

lemma SDR3Asm_J₀_hom (P₂ : Ideal R₂) (I : Ideal B) (hI : cB.IsHomIdeal I) :
    (SDExist_bc R₂ cB hcB).IsHomIdeal (SDR3Asm_J₀ R₂ P₂ I) := by
  intro y hy d
  refine SDR3Asm_J₀_induct P₂ I (p := fun y => (SDExist_bc R₂ cB hcB).comp d y ∈ SDR3Asm_J₀ R₂ P₂ I)
    ?_ ?_ ?_ hy
  · simp [Coact.comp]
  · intro a b ha hb
    rw [Coact.comp_add]
    exact Ideal.add_mem _ ha hb
  · rintro y (⟨p, hp, b, rfl⟩ | ⟨r, i, hi, rfl⟩)
    · rw [SDExist_bc_comp]
      exact Ideal.subset_span (Or.inl ⟨p, hp, _, rfl⟩)
    · rw [SDExist_bc_comp]
      exact Ideal.subset_span (Or.inr ⟨r, _, hI i hi d, rfl⟩)

include hcB in
lemma SDR3Asm_J₀_inv (hι : cB.IsInv (algebraMap R B)) (P₂ : Ideal R₂) (I : Ideal B) (hI : cB.IsHomIdeal I) (P : Ideal R)
    (hIq : ∀ a, algebraMap R B a ∈ I → a ∈ P) (hP : ∀ a ∈ P, algebraMap R R₂ a ∈ P₂) (a : R₂)
    (ha : a ⊗ₜ[R] (1 : B) ∈ SDR3Asm_J₀ R₂ P₂ I) : a ∈ P₂ := by
  have hι' := SDExist_bc_isInv R₂ cB hcB hι
  have hr1 : ∀ x : R₂, hι'.r (x ⊗ₜ[R] (1 : B)) = x := fun x => hι'.inj (by
    rw [hι'.ι_r]
    exact (SDExist_bc R₂ cB hcB).comp_self_of_isHom ((hι'.range _).2 ⟨x, rfl⟩))
  have key : hι'.r (a ⊗ₜ[R] (1 : B)) ∈ P₂ := by
    refine SDR3Asm_J₀_induct P₂ I (p := fun y => hι'.r y ∈ P₂) ?_ ?_ ?_ ha
    · have : hι'.r 0 = 0 := hι'.inj (by
        rw [hι'.ι_r, map_zero]
        simp [Coact.comp])
      rw [this]
      exact P₂.zero_mem
    · intro x y hx hy
      rw [hι'.r_add]
      exact P₂.add_mem hx hy
    · have hform : ∀ (r : R₂) (b : B), hι'.r (r ⊗ₜ[R] b) = r * algebraMap R R₂ (hι.r b) := by
        intro r b
        apply hι'.inj
        rw [hι'.ι_r, SDExist_bc_comp, ← hι.ι_r]
        change r ⊗ₜ[R] (algebraMap R B (hι.r b)) = (r * algebraMap R R₂ (hι.r b)) ⊗ₜ[R] (1 : B)
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          Algebra.smul_def, mul_comm]
      rintro y (⟨p, hp, b, rfl⟩ | ⟨r, i, hi, rfl⟩)
      · rw [hform]
        exact P₂.mul_mem_right _ hp
      · rw [hform]
        refine P₂.mul_mem_left _ (hP _ (hIq _ ?_))
        rw [hι.ι_r]
        exact hI i hi 0
  rwa [hr1] at key

end Base

section Finite

variable {R B D Γ : Type u} [CommRing R] [CommRing B] [CommRing D] [Algebra B D] {ι : R →+* B}

/-- From elementwise to uniform in G1: finitely many generators. -/
theorem SDR3Asm_uniform_H1 [Module.Finite B D] {q : Ideal R} [q.IsPrime] {J : Ideal D}
    (H : ∀ y : D, ∃ s, s ∉ q ∧ ∃ b, algebraMap B D (ι s) * y - algebraMap B D b ∈ J) :
    ∃ s, s ∉ q ∧ ∀ y : D, ∃ b, algebraMap B D (ι s) * y - algebraMap B D b ∈ J := by
  classical
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule B D).FG)
  have hall : ∀ t' : Finset D, ∃ s, s ∉ q ∧ ∀ y ∈ t', ∃ b, algebraMap B D (ι s) * y - algebraMap B D b ∈ J := by
    intro t'
    induction t' using Finset.induction_on with
    | empty => exact ⟨1, (Ideal.ne_top_iff_one q).1 (Ideal.IsPrime.ne_top ‹_›), by simp⟩
    | insert a t' _ ih =>
      obtain ⟨s, hs, hS⟩ := ih
      obtain ⟨s', hs', b', hb'⟩ := H a
      refine ⟨s * s', fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hs hs', fun y hy => ?_⟩
      obtain rfl | hy' := Finset.mem_insert.1 hy
      · refine ⟨ι s * b', ?_⟩
        have := J.mul_mem_left (algebraMap B D (ι s)) hb'
        convert this using 1
        simp only [map_mul]
        ring
      · obtain ⟨b, hb⟩ := hS y hy'
        refine ⟨ι s' * b, ?_⟩
        have := J.mul_mem_left (algebraMap B D (ι s')) hb
        convert this using 1
        simp only [map_mul]
        ring
  obtain ⟨s, hs, hS⟩ := hall t
  refine ⟨s, hs, fun y => ?_⟩
  have hy : y ∈ Submodule.span B (t : Set D) := by
    rw [ht]
    trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hz
    refine ⟨a + c, ?_⟩
    have := J.add_mem ha hc
    convert this using 1
    rw [map_add]
    ring
  | smul b x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨b * a, ?_⟩
    have := J.mul_mem_left (algebraMap B D b) ha
    convert this using 1
    rw [Algebra.smul_def, map_mul]
    ring

end Finite

section Section

variable {R B D Γ : Type u} [CommRing R] [CommRing B] [CommRing D] [AddCommGroup Γ] [Algebra B D]
  {cB : Coact B Γ} {cD : Coact D Γ} {ι : R →+* B}

/-- **Step 9**: on an element `y` of degree `0` of `D`, the value of the section is invariant. -/
theorem SDR3Asm_section_zero (hg : SDExist_IsGraded cB cD) (hι : cB.IsInv ι) {h : R} {b : B} {y : D}
    (hinj : ∀ b : B, algebraMap B D b = 0 → ∃ n : ℕ, ι h ^ n * b = 0)
    (hy : cD.IsHom 0 y) (hb : algebraMap B D (ι h) * y = algebraMap B D b) :
    ∃ (N : ℕ) (r : R), ι h ^ N * b = ι r := by
  classical
  have hcomp : ∀ d, d ≠ 0 → ∃ n : ℕ, ι h ^ n * cB.comp d b = 0 := by
    intro d hd
    apply hinj
    rw [← hg, ← hb, ← mul_comm y]
    rw [cD.comp_mul_of_isHom hy, sub_zero]
    have h1 : cD.IsHom 0 (algebraMap B D (ι h)) := by
      have h0 : cB.IsHom 0 (ι h) := (hι.range _).2 ⟨h, rfl⟩
      have h2 := hg 0 (ι h)
      rw [cB.comp_self_of_isHom h0] at h2
      rw [← h2]
      exact cD.comp_isHom 0 _
    have h3 : cD.comp d (algebraMap B D (ι h)) = 0 := by
      have : cD.σ (algebraMap B D (ι h)) = AddMonoidAlgebra.single 0 (algebraMap B D (ι h)) := h1
      rw [Coact.comp, this, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hd)]
    rw [h3, mul_zero]
  have hfin : ∀ s : Finset Γ, ∃ N : ℕ, ∀ d ∈ s, d ≠ 0 → ι h ^ N * cB.comp d b = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a s _ ih =>
      obtain ⟨N, hN⟩ := ih
      by_cases ha : a = 0
      · refine ⟨N, fun d hd hd0 => ?_⟩
        obtain rfl | hd' := Finset.mem_insert.1 hd
        · exact absurd ha hd0
        · exact hN d hd' hd0
      · obtain ⟨n, hn⟩ := hcomp a ha
        refine ⟨N + n, fun d hd hd0 => ?_⟩
        obtain rfl | hd' := Finset.mem_insert.1 hd
        · rw [pow_add, mul_assoc, hn, mul_zero]
        · rw [pow_add, mul_right_comm, hN d hd' hd0, zero_mul]
  obtain ⟨N, hN⟩ := hfin (cB.σ b).coeff.support
  refine ⟨N, h ^ N * hι.r b, ?_⟩
  rw [map_mul, map_pow, hι.ι_r]
  conv_lhs => rw [← cB.sum_eq b]
  rw [Finsupp.sum, Finset.mul_sum]
  by_cases h0 : (0 : Γ) ∈ (cB.σ b).coeff.support
  · rw [Finset.sum_eq_single (0 : Γ)]
    · rfl
    · intro d hd hd0
      exact hN d hd hd0
    · exact fun hn => absurd h0 hn
  · have hz : cB.comp 0 b = 0 := Finsupp.notMem_support_iff.1 h0
    rw [hz, mul_zero]
    exact Finset.sum_eq_zero fun d hd => hN d hd (fun e => h0 (e ▸ hd))

end Section

section Tensor

variable {R R₂ C : Type u} [CommRing R] [CommRing R₂] [CommRing C] [Algebra R R₂] [Algebra R C]

/-- A prime of `R₂ ⊗ C` over two primes with the same contraction to `R`. -/
theorem SDR3Asm_exists_prime (P : Ideal R) [P.IsPrime] (P₂ : Ideal R₂) [P₂.IsPrime] [P₂.LiesOver P]
    (𝔫 : Ideal C) [𝔫.IsPrime] [𝔫.LiesOver P] :
    ∃ Q : Ideal (R₂ ⊗[R] C), Q.IsPrime ∧ Q.comap (Algebra.TensorProduct.includeLeftRingHom : R₂ →+* _) = P₂ ∧
      Q.comap (Algebra.TensorProduct.includeRight : C →ₐ[R] R₂ ⊗[R] C).toRingHom = 𝔫 := by
  let K₀ := P.ResidueField
  let K₁ := P₂.ResidueField
  let K₂ := 𝔫.ResidueField
  letI : Algebra K₀ K₁ := (Ideal.ResidueField.map P P₂ (algebraMap R R₂)
    (Ideal.LiesOver.over (P := P₂) (p := P))).toAlgebra
  letI : Algebra K₀ K₂ := (Ideal.ResidueField.map P 𝔫 (algebraMap R C)
    (Ideal.LiesOver.over (P := 𝔫) (p := P))).toAlgebra
  let T := K₁ ⊗[K₀] K₂
  have : Nontrivial T := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  let L := T ⧸ m
  let g₁ : K₁ →+* L := (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom : K₁ →+* T)
  let g₂ : K₂ →+* L := (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : K₂ →ₐ[K₀] T).toRingHom
  let f₁ : R₂ →+* L := g₁.comp (algebraMap R₂ K₁)
  let f₂ : C →+* L := g₂.comp (algebraMap C K₂)
  have hcomp : ∀ r : R, f₁ (algebraMap R R₂ r) = f₂ (algebraMap R C r) := by
    intro r
    have e1 : algebraMap R₂ K₁ (algebraMap R R₂ r) = algebraMap K₀ K₁ (algebraMap R K₀ r) :=
      (Ideal.ResidueField.map_algebraMap P P₂ (algebraMap R R₂) _ r).symm
    have e2 : algebraMap C K₂ (algebraMap R C r) = algebraMap K₀ K₂ (algebraMap R K₀ r) :=
      (Ideal.ResidueField.map_algebraMap P 𝔫 (algebraMap R C) _ r).symm
    change Ideal.Quotient.mk m ((algebraMap R₂ K₁ (algebraMap R R₂ r)) ⊗ₜ[K₀] (1 : K₂)) =
      Ideal.Quotient.mk m ((1 : K₁) ⊗ₜ[K₀] (algebraMap C K₂ (algebraMap R C r)))
    rw [e1, e2]
    generalize algebraMap R K₀ r = k
    rw [Algebra.algebraMap_eq_smul_one k, Algebra.algebraMap_eq_smul_one k, TensorProduct.smul_tmul]
  letI : Algebra R L := (f₁.comp (algebraMap R R₂)).toAlgebra
  let F₁ : R₂ →ₐ[R] L := { f₁ with commutes' := fun _ => rfl }
  let F₂ : C →ₐ[R] L := { f₂ with commutes' := fun r => (hcomp r).symm }
  let Φ := Algebra.TensorProduct.productMap F₁ F₂
  have hk₁ : RingHom.ker f₁ = P₂ := by
    rw [RingHom.ker_comp_of_injective _ g₁.injective]
    exact Ideal.ker_algebraMap_residueField P₂
  have hk₂ : RingHom.ker f₂ = 𝔫 := by
    rw [RingHom.ker_comp_of_injective _ g₂.injective]
    exact Ideal.ker_algebraMap_residueField 𝔫
  refine ⟨RingHom.ker Φ.toRingHom, RingHom.ker_isPrime _, ?_, ?_⟩
  · refine Eq.trans ?_ hk₁
    ext x
    simp [Ideal.mem_comap, RingHom.mem_ker, Φ, F₁, F₂]
  · refine Eq.trans ?_ hk₂
    ext x
    simp [Ideal.mem_comap, RingHom.mem_ker, Φ, F₁, F₂]

end Tensor

end AlgMag.SD
