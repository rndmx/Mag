/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDLocAMain

/-!
# Lemma D, surjectivity modulo the closed orbit, up to a denominator

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`. The hypothesis `H1` of
`SDExist_surj` is weakened to `∃ s ∉ q, ∀ y, ∃ b, ι s · y - b ∈ I D`; Cayley-Hamilton on `D / B` recovers an annihilator
outside `I`. `SDR3Orbit_uniform` and `SDR3Orbit_main` are `SDLocA_uniform`, `SDLocA_main` under that hypothesis.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

section Surj

variable {R B D Γ : Type u} [CommRing R] [CommRing B] [CommRing D] [AddCommGroup Γ]
  {cB : Coact B Γ} {cD : Coact D Γ} {ι : R →+* B} [Algebra B D]

/-- G1: **surjectivity** (graded Nakayama) when `D` is onto modulo `I` only up to a denominator `s ∉ q`. -/
theorem SDR3Orbit_surj [Module.Finite B D] (hg : SDExist_IsGraded cB cD) (hι : cB.IsInv ι) {q : Ideal R} [q.IsPrime]
    {I : Ideal B} (hI : cB.IsHomIdeal I) (hIq : ∀ a, ι a ∈ I → a ∈ q)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q)
    (H1 : ∃ s, s ∉ q ∧ ∀ y : D, ∃ b, algebraMap B D (ι s) * y - algebraMap B D b ∈ I.map (algebraMap B D)) :
    ∃ h, h ∉ q ∧ ∀ y : D, ∃ b, algebraMap B D (ι h) * y = algebraMap B D b := by
  obtain ⟨s, hs, H1⟩ := H1
  let L : Submodule B D := LinearMap.range (Algebra.linearMap B D)
  let f : Module.End B (D ⧸ L) := algebraMap B (Module.End B (D ⧸ L)) (ι s)
  have hf : ∀ m, f m = ι s • m := fun _ => rfl
  have hrange : LinearMap.range f ≤ I • ⊤ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := L.mkQ_surjective x
    obtain ⟨b, hb⟩ := H1 y
    have hz : algebraMap B D (ι s) * y - algebraMap B D b ∈ (I • ⊤ : Submodule B D) := by
      rw [Ideal.smul_top_eq_map]
      exact hb
    have h2 := Submodule.mem_map_of_mem (f := L.mkQ) hz
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h2
    have h3 : L.mkQ (algebraMap B D b) = 0 := (Submodule.Quotient.mk_eq_zero L).2 ⟨b, rfl⟩
    rw [map_sub, h3, sub_zero, ← Algebra.smul_def, map_smul] at h2
    rw [hf]
    exact h2
  obtain ⟨p, hp, -, hc, hae⟩ := LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (R := B) (M := D ⧸ L) f I hrange
  let r : B := Polynomial.aeval (ι s) p
  have hr0 : ∀ m : D ⧸ L, r • m = 0 := by
    intro m
    have e : Polynomial.aeval f p = algebraMap B (Module.End B (D ⧸ L)) r :=
      Polynomial.aeval_algebraMap_apply (Module.End B (D ⧸ L)) (ι s) p
    have := LinearMap.congr_fun (e.symm.trans hae) m
    exact this
  have hrI : r - ι s ^ p.natDegree ∈ I := by
    have e : r = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • ι s ^ k := Polynomial.aeval_eq_sum_range _
    rw [e, Finset.sum_range_succ, hp.coeff_natDegree, one_smul, add_sub_cancel_right]
    refine Ideal.sum_mem _ fun k hk => ?_
    rw [smul_eq_mul]
    have hk' := Finset.mem_range.1 hk
    refine Ideal.mul_mem_right _ _ (Ideal.pow_le_self ?_ (hc k))
    omega
  have hsI : ι s ^ p.natDegree ∉ I := by
    intro hm
    have hm' : ι (s ^ p.natDegree) ∈ I := by rwa [map_pow]
    exact hs (Ideal.IsPrime.mem_of_pow_mem ‹_› _ (hIq _ hm'))
  have hrnI : r ∉ I := fun h => hsI (by simpa using I.sub_mem h hrI)
  have hrJ : ∀ y : D, ∃ b', algebraMap B D r * y = algebraMap B D b' := by
    intro y
    have h0 := hr0 (L.mkQ y)
    rw [← map_smul] at h0
    obtain ⟨b', hb'⟩ := (Submodule.Quotient.mk_eq_zero L).1 h0
    exact ⟨b', by rw [← Algebra.smul_def]; exact hb'.symm⟩
  obtain ⟨h, hh, hJ⟩ := SDExist_exists_inv_mem hι hI hIq hmax (SDExist_conductor_hom hg) (r := r) hrJ hrnI
  exact ⟨h, hh, hJ⟩

/-- `SDLocA_uniform` under the weakened hypothesis G1. -/
theorem SDR3Orbit_uniform [Module.Finite B D] [Module.Flat B D] [Algebra.FinitePresentation B D]
    (hg : SDExist_IsGraded cB cD) (hι : cB.IsInv ι) {q : Ideal R} [q.IsPrime] {I : Ideal B}
    (hI : cB.IsHomIdeal I) (hIq : ∀ a, ι a ∈ I → a ∈ q)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q)
    (H1 : ∃ s, s ∉ q ∧ ∀ y : D, ∃ b, algebraMap B D (ι s) * y - algebraMap B D b ∈ I.map (algebraMap B D))
    (𝔯 : Ideal D) [𝔯.IsPrime] (h𝔯 : ∀ a, algebraMap B D (ι a) ∈ 𝔯 → a ∈ q) :
    ∃ h, h ∉ q ∧ (∀ y : D, ∃ b, algebraMap B D (ι h) * y = algebraMap B D b) ∧
      ∀ b : B, algebraMap B D b = 0 → ∃ n : ℕ, ι h ^ n * b = 0 := by
  classical
  obtain ⟨h₁, hh₁, hS⟩ := SDR3Orbit_surj hg hι hI hIq hmax H1
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

end Surj

variable {R B C Γ : Type u} (R'' : Type u) [CommRing R] [CommRing B] [CommRing C] [CommRing R''] [AddCommGroup Γ]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] [Algebra R R'']
  (cB : Coact B Γ) (cC : Coact C Γ)
  (hcB : ∀ r : R, cB.σ (algebraMap R B r) = AddMonoidAlgebra.single 0 (algebraMap R B r))
  (hcC : ∀ r : R, cC.σ (algebraMap R C r) = AddMonoidAlgebra.single 0 (algebraMap R C r))

set_option maxHeartbeats 2000000 in
/-- `SDLocA_main` under the weakened hypothesis G1. `B → C` graded, `C` integral over `B`, `C_d` étale over `B`, and
`e` an idempotent of degree zero of `R'' ⊗ C`, with `1 ⊗ d` a unit on its corner. Put `D = (R'' ⊗ C)/(1-e)`. If `D` is onto
modulo the closed orbit `I` and has a prime `𝔯` over `q`, one invariant `h ∉ q` gives the section `D → (R'' ⊗ B)_h`,
together with the bijection `(R'' ⊗ B)_h → D_h`. -/
theorem SDR3Orbit_main (hBC : ∀ (d : Γ) (b : B), cC.comp d (algebraMap B C b) = algebraMap B C (cB.comp d b))
    (hιB : cB.IsInv (algebraMap R B)) [Algebra.IsIntegral B C] (x : C) [Algebra.Etale B (Localization.Away x)]
    {e : R'' ⊗[R] C} (he : IsIdempotentElem e) (hu : ∃ u, e = u * ((1 : R'') ⊗ₜ[R] x) * e)
    (he0 : (SDExist_bc R'' cC hcC).IsHom 0 e)
    {q : Ideal R''} [q.IsPrime] {I : Ideal (R'' ⊗[R] B)}
    (hI : (SDExist_bc R'' cB hcB).IsHomIdeal I)
    (hIq : ∀ a : R'', a ⊗ₜ[R] (1 : B) ∈ I → a ∈ q)
    (hmax : ∀ J, (SDExist_bc R'' cB hcB).IsHomIdeal J → I < J → ∃ a : R'', a ⊗ₜ[R] (1 : B) ∈ J ∧ a ∉ q) :
    letI := SDLocA_alg R B C R''
    ∀ (H1 : ∃ s : R'', s ∉ q ∧ ∀ y : (R'' ⊗[R] C) ⧸ Ideal.span {1 - e}, ∃ b,
        algebraMap (R'' ⊗[R] B) _ (s ⊗ₜ[R] (1 : B)) * y - algebraMap (R'' ⊗[R] B) _ b ∈
          I.map (algebraMap (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e})))
      (𝔯 : Ideal ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e})) (_ : 𝔯.IsPrime)
      (_ : ∀ a : R'', algebraMap (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e}) (a ⊗ₜ[R] (1 : B)) ∈ 𝔯 → a ∈ q),
      ∃ h : R'', h ∉ q ∧
        (∀ y : (R'' ⊗[R] C) ⧸ Ideal.span {1 - e}, ∃ b,
          algebraMap (R'' ⊗[R] B) _ (h ⊗ₜ[R] (1 : B)) * y = algebraMap (R'' ⊗[R] B) _ b) ∧
        (∀ b : R'' ⊗[R] B, algebraMap (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e}) b = 0 →
          ∃ n : ℕ, (h ⊗ₜ[R] (1 : B)) ^ n * b = 0) ∧
        ∃ s : (R'' ⊗[R] C) ⧸ Ideal.span {1 - e} →+* Localization.Away (h ⊗ₜ[R] (1 : B) : R'' ⊗[R] B),
          ∀ b : R'' ⊗[R] B, s (algebraMap (R'' ⊗[R] B) _ b) = algebraMap (R'' ⊗[R] B) _ b := by
  letI := SDLocA_alg R B C R''
  intro H1 𝔯 h𝔯P h𝔯
  obtain ⟨hE, hF, hFl, hP⟩ := SDLocA_finite R B R'' C x he hu
  let cT := SDExist_bc R'' cC hcC
  let cD := SDLocA_quot cT (Ideal.span {1 - e}) (SDLocA_span_hom cT he0)
  have hg : SDExist_IsGraded (SDExist_bc R'' cB hcB) cD := by
    intro d b
    induction b using TensorProduct.induction_on with
    | zero => simp [Coact.comp]
    | add a c ha hc => rw [map_add, Coact.comp_add, ha, hc, Coact.comp_add, map_add]
    | tmul r b =>
      change cD.comp d (Ideal.Quotient.mk _ (r ⊗ₜ[R] algebraMap B C b)) =
        Ideal.Quotient.mk _ _
      rw [SDLocA_quot_comp, SDExist_bc_comp, SDExist_bc_comp, hBC]
      rfl
  have hι := SDExist_bc_isInv R'' cB hcB hιB
  obtain ⟨h, hh, hs, hi⟩ := SDR3Orbit_uniform (ι := Algebra.TensorProduct.includeLeftRingHom) hg hι hI hIq hmax H1 𝔯 h𝔯
  exact ⟨h, hh, hs, hi, SDLocA_section hs hi⟩

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Orbit_surj
#print axioms AlgMag.SD.SDR3Orbit_uniform
#print axioms AlgMag.SD.SDR3Orbit_main
