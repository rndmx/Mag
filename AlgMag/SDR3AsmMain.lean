/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmOrb
import AlgMag.SDR3OrbitNakayama
import AlgMag.SDR3OrbitClopen

/-!
# Lemma D, Steps 5-9, algebraic form

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`. From the graded
`B → C` integral, a homogeneous prime `𝔫` over the closed orbit, a homogeneous `a ∉ 𝔫` with `C_a` étale over `B`, and the
idempotent of G3 (`d'/s'`, in the form `hJ`), one gets an étale neighbourhood `R₃` of `P` and a `B`-map
`C_d → R₃ ⊗ B`, with `d` a multiple of `a`, sending degree `0` into `R₃`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

variable {R B C Γ : Type u} [CommRing R] [CommRing B] [CommRing C] [AddCommGroup Γ] [UniqueSums Γ]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

/-- **Step 9**: from the section `s₀` of `SDR3Orbit_main`, the map `κ : C_d → R₃ ⊗ B`, with `R₃ = (R₂)_{h₃}`. -/
theorem SDR3Asm_finish (R₂ : Type u) [CommRing R₂] [Algebra R R₂] (cB : Coact B Γ) (cC : Coact C Γ)
    (hcB : ∀ r : R, cB.σ (algebraMap R B r) = AddMonoidAlgebra.single 0 (algebraMap R B r))
    (hcC : ∀ r : R, cC.σ (algebraMap R C r) = AddMonoidAlgebra.single 0 (algebraMap R C r))
    (hBC : ∀ (d : Γ) (b : B), cC.comp d (algebraMap B C b) = algebraMap B C (cB.comp d b))
    (hιB : cB.IsInv (algebraMap R B)) (d : C) (hd0 : cC.IsHom 0 d) {e : R₂ ⊗[R] C}
    (he0 : (SDExist_bc R₂ cC hcC).IsHom 0 e) (hu : ∃ u, e = u * ((1 : R₂) ⊗ₜ[R] d) * e) (h₃ : R₂) :
    letI := SDLocA_alg R B C R₂
    ∀ (_ : ∀ y : (R₂ ⊗[R] C) ⧸ Ideal.span {1 - e}, ∃ b,
          algebraMap (R₂ ⊗[R] B) _ (h₃ ⊗ₜ[R] (1 : B)) * y = algebraMap (R₂ ⊗[R] B) _ b)
      (_ : ∀ b : R₂ ⊗[R] B, algebraMap (R₂ ⊗[R] B) ((R₂ ⊗[R] C) ⧸ Ideal.span {1 - e}) b = 0 →
          ∃ n : ℕ, (h₃ ⊗ₜ[R] (1 : B)) ^ n * b = 0)
      (s₀ : (R₂ ⊗[R] C) ⧸ Ideal.span {1 - e} →+* Localization.Away (h₃ ⊗ₜ[R] (1 : B) : R₂ ⊗[R] B))
      (_ : ∀ b : R₂ ⊗[R] B, s₀ (algebraMap (R₂ ⊗[R] B) _ b) = algebraMap (R₂ ⊗[R] B) _ b),
      ∃ κ : Localization.Away d →+* Localization.Away h₃ ⊗[R] B,
      (∀ b, κ (algebraMap C _ (algebraMap B C b)) = (1 : Localization.Away h₃) ⊗ₜ[R] b) ∧
      ∀ (y : C) (k : ℕ) (v : Localization.Away d), cC.IsHom 0 y → v * algebraMap C _ d ^ k = algebraMap C _ y →
        ∃ r : Localization.Away h₃, κ v = r ⊗ₜ[R] (1 : B) := by
  letI := SDLocA_alg R B C R₂
  intro hsurj hinj s₀ hs₀
  let cT := SDExist_bc R₂ cC hcC
  let Jd : Ideal (R₂ ⊗[R] C) := Ideal.span {1 - e}
  let D := (R₂ ⊗[R] C) ⧸ Jd
  let mk : (R₂ ⊗[R] C) →+* D := Ideal.Quotient.mk Jd
  let ρ : C →ₐ[R] R₂ ⊗[R] C := Algebra.TensorProduct.includeRight
  let R₃ := Localization.Away h₃
  let g₃ : R₂ ⊗[R] B →+* R₃ ⊗[R] B :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R₂ R₃) (AlgHom.id R B)).toRingHom
  let L₃ : R₃ →+* R₃ ⊗[R] B := Algebra.TensorProduct.includeLeftRingHom
  have hg₃ : ∀ (r : R₂) (b : B), g₃ (r ⊗ₜ[R] b) = algebraMap R₂ R₃ r ⊗ₜ[R] b := fun r b => by
    simp [g₃]
  obtain ⟨i₃, hi₃⟩ := (IsLocalization.Away.algebraMap_isUnit (S := R₃) h₃).exists_left_inv
  have hu₃ : IsUnit (g₃ (h₃ ⊗ₜ[R] (1 : B))) := by
    rw [hg₃]
    exact (IsLocalization.Away.algebraMap_isUnit (S := R₃) h₃).map L₃
  let lam : Localization.Away (h₃ ⊗ₜ[R] (1 : B) : R₂ ⊗[R] B) →+* R₃ ⊗[R] B := IsLocalization.Away.lift _ hu₃
  have hlam : ∀ b, lam (algebraMap _ _ b) = g₃ b := fun b => IsLocalization.Away.lift_eq _ hu₃ b
  obtain ⟨u', hu'⟩ := hu
  have hρu : IsUnit (mk (ρ d)) := by
    have h1 : mk e = 1 := by
      have : mk (1 - e) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
      rw [map_sub, map_one, sub_eq_zero] at this
      exact this.symm
    refine IsUnit.of_mul_eq_one (mk u') ?_
    have := congrArg mk hu'
    rw [map_mul, map_mul, h1, mul_one] at this
    rw [mul_comm]
    exact this.symm
  let κ₀ : Localization.Away d →+* D := IsLocalization.Away.lift d (g := mk.comp ρ.toRingHom) hρu
  have hκ₀ : ∀ y, κ₀ (algebraMap C _ y) = mk (ρ y) := fun y => IsLocalization.Away.lift_eq d hρu y
  let κ : Localization.Away d →+* R₃ ⊗[R] B := lam.comp (s₀.comp κ₀)
  have hκ : ∀ y, κ (algebraMap C _ y) = lam (s₀ (mk (ρ y))) := fun y => by
    change lam (s₀ (κ₀ _)) = _
    rw [hκ₀]
  let cD : Coact D Γ := SDLocA_quot cT Jd (SDLocA_span_hom cT he0)
  let cB₂ := SDExist_bc R₂ cB hcB
  have hgD : SDExist_IsGraded cB₂ cD := by
    intro d b
    induction b using TensorProduct.induction_on with
    | zero => simp [Coact.comp]
    | add a c ha hc => rw [map_add, Coact.comp_add, ha, hc, Coact.comp_add, map_add]
    | tmul r b =>
      change cD.comp d (Ideal.Quotient.mk _ (r ⊗ₜ[R] algebraMap B C b)) =
        Ideal.Quotient.mk _ _
      rw [SDLocA_quot_comp, SDExist_bc_comp, SDExist_bc_comp, hBC]
      rfl
  have hιB₂ : cB₂.IsInv (Algebra.TensorProduct.includeLeftRingHom : R₂ →+* R₂ ⊗[R] B) := SDExist_bc_isInv R₂ cB hcB hιB
  have hρ0 : ∀ y, cC.IsHom 0 y → cD.IsHom 0 (mk (ρ y)) := by
    intro y hy
    have h1 : cT.comp 0 ((1 : R₂) ⊗ₜ[R] y) = (1 : R₂) ⊗ₜ[R] y := by
      rw [SDExist_bc_comp, cC.comp_self_of_isHom hy]
    have h2 := cD.comp_isHom 0 (mk (ρ y))
    have h3 : cD.comp 0 (mk (ρ y)) = mk (ρ y) := by
      refine (SDLocA_quot_comp cT Jd (SDLocA_span_hom cT he0) 0 _).trans ?_
      exact congrArg mk h1
    rwa [h3] at h2
  have hL₃h : L₃ i₃ * g₃ (h₃ ⊗ₜ[R] (1 : B)) = 1 := by
    rw [hg₃]
    change L₃ i₃ * L₃ (algebraMap R₂ R₃ h₃) = 1
    rw [← map_mul, hi₃, map_one]
  have hzero : ∀ y, cC.IsHom 0 y → ∃ r : R₃, lam (s₀ (mk (ρ y))) = L₃ r := by
    intro y hy
    obtain ⟨b, hb⟩ := hsurj (mk (ρ y))
    obtain ⟨N, r, hr⟩ := SDR3Asm_section_zero hgD hιB₂ (h := h₃) hinj (hρ0 y hy) hb
    have hr' : (h₃ ⊗ₜ[R] (1 : B)) ^ N * b = r ⊗ₜ[R] (1 : B) := hr
    have h1 : g₃ (h₃ ⊗ₜ[R] (1 : B)) * lam (s₀ (mk (ρ y))) = g₃ b := by
      rw [← hlam, ← hlam, ← map_mul, ← hs₀, ← hs₀, ← map_mul]
      exact congrArg (fun z => lam (s₀ z)) hb
    have h2 := congrArg g₃ hr'
    rw [map_mul, map_pow, hg₃ r] at h2
    refine ⟨i₃ ^ (N + 1) * algebraMap R₂ R₃ r, ?_⟩
    have h3 : L₃ (algebraMap R₂ R₃ r) = g₃ (h₃ ⊗ₜ[R] (1 : B)) ^ N * (g₃ (h₃ ⊗ₜ[R] (1 : B)) * lam (s₀ (mk (ρ y)))) := by
      rw [h1]
      exact h2.symm
    rw [map_mul, map_pow, h3]
    calc lam (s₀ (mk (ρ y))) = (L₃ i₃ * g₃ (h₃ ⊗ₜ[R] (1 : B))) ^ (N + 1) * lam (s₀ (mk (ρ y))) := by rw [hL₃h, one_pow, one_mul]
      _ = _ := by ring
  have hι₃ : (SDExist_bc R₃ cB hcB).IsInv L₃ := SDExist_bc_isInv R₃ cB hcB hιB
  refine ⟨κ, fun b => ?_, ?_⟩
  · rw [hκ]
    have e1 : mk (ρ (algebraMap B C b)) = algebraMap (R₂ ⊗[R] B) D ((1 : R₂) ⊗ₜ[R] b) := rfl
    rw [e1, hs₀, hlam, hg₃, map_one]
  · intro y k v hy hv
    obtain ⟨r, hr⟩ := hzero y hy
    obtain ⟨r₀, hr₀⟩ := hzero d hd0
    have hud : IsUnit (κ (algebraMap C _ d)) := (IsLocalization.Away.algebraMap_isUnit d).map κ
    rw [hκ, hr₀] at hud
    obtain ⟨w, hw⟩ := hud.exists_right_inv
    -- the inverse of `L₃ r₀` is in `R₃`
    have h1 := congrArg ((SDExist_bc R₃ cB hcB).comp 0) hw
    rw [hι₃.comp_ι, ← hι₃.ι_r, ← map_mul] at h1
    have h1' : (SDExist_bc R₃ cB hcB).comp 0 (1 : R₃ ⊗[R] B) = 1 :=
      (SDExist_bc R₃ cB hcB).comp_self_of_isHom (map_one (SDExist_bc R₃ cB hcB).σ)
    rw [h1'] at h1
    have hv' := congrArg κ hv
    rw [map_mul, map_pow, hκ, hκ, hr₀, hr] at hv'
    refine ⟨r * (hι₃.r w) ^ k, ?_⟩
    change κ v = L₃ _
    rw [map_mul, ← hv', map_pow, mul_assoc, ← mul_pow, ← map_mul, h1, one_pow, mul_one]

set_option maxHeartbeats 2000000 in
/-- **Steps 5-9**, algebraic form. -/
theorem SDR3Asm_alg (cB : Coact B Γ) (cC : Coact C Γ)
    (hcB : ∀ r : R, cB.σ (algebraMap R B r) = AddMonoidAlgebra.single 0 (algebraMap R B r))
    (hcC : ∀ r : R, cC.σ (algebraMap R C r) = AddMonoidAlgebra.single 0 (algebraMap R C r))
    (hBC : ∀ (d : Γ) (b : B), cC.comp d (algebraMap B C b) = algebraMap B C (cB.comp d b))
    (hιB : cB.IsInv (algebraMap R B)) [Algebra.IsIntegral B C]
    (P : Ideal R) [P.IsPrime] {I : Ideal B} (hI : cB.IsHomIdeal I) (hIq : ∀ a, algebraMap R B a ∈ I → a ∈ P)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, algebraMap R B a ∈ J ∧ a ∉ P)
    (𝔫 : Ideal C) [𝔫.IsPrime] (h𝔫 : cC.IsHomIdeal 𝔫) (h𝔫I : ∀ b, b ∈ I → algebraMap B C b ∈ 𝔫)
    (h𝔫R : ∀ s, algebraMap R C s ∈ 𝔫 ↔ s ∈ P)
    (hfib : ∀ y : C, ∃ s, s ∉ P ∧ ∃ β, algebraMap R C s * y - algebraMap B C β ∈ 𝔫)
    {e : Γ} {a : C} (ha : cC.IsHom e a) (ha𝔫 : a ∉ 𝔫) [Algebra.Etale B (Localization.Away a)]
    {d' : C} {s' : R} (hd'0 : cC.IsHom 0 d') (hs' : s' ∉ P) (hd'𝔫 : d' - algebraMap R C s' ∈ 𝔫)
    (hJ : ∀ j ∈ 𝔫, ∃ t, t ∉ P ∧ algebraMap R C t * d' * j ∈ I.map (algebraMap B C)) :
    ∃ (R₃ : Type u) (_ : CommRing R₃) (_ : Algebra R R₃) (_ : Algebra.Etale R R₃) (P₃ : Ideal R₃) (_ : P₃.IsPrime)
      (_ : P₃.LiesOver P) (d b₁ : C) (_ : d = a * b₁) (_ : cC.IsHom 0 d) (κ : Localization.Away d →+* R₃ ⊗[R] B),
      (∀ b, κ (algebraMap C _ (algebraMap B C b)) = (1 : R₃) ⊗ₜ[R] b) ∧
      ∀ (y : C) (k : ℕ) (v : Localization.Away d), cC.IsHom 0 y → v * algebraMap C _ d ^ k = algebraMap C _ y →
        ∃ r : R₃, κ v = r ⊗ₜ[R] (1 : B) := by
  have hg : SDExist_IsGraded cB cC := hBC
  have htw : ∀ s : R, algebraMap B C (algebraMap R B s) = algebraMap R C s := fun s =>
    (IsScalarTower.algebraMap_apply R B C s).symm
  obtain ⟨x, b₀, hxa, hx0, h, hh, hxh⟩ := SDR3Asm_d₀ (ι := algebraMap R B) hg hιB hI hIq hmax 𝔫 h𝔫 h𝔫I
    (fun s hs => (h𝔫R s).1 (by rwa [htw] at hs))
    (fun y => by
      obtain ⟨s, hs, β, hβ⟩ := hfib y
      exact ⟨s, hs, β, by rwa [htw]⟩) ha ha𝔫
  rw [htw] at hxh
  obtain ⟨d, hd⟩ : ∃ d, d = x * d' := ⟨_, rfl⟩
  have hd0 : cC.IsHom 0 d := by
    rw [hd]
    simpa using hx0.mul hd'0
  have hc𝔫 : d - algebraMap R C (h * s') ∈ 𝔫 := by
    have := 𝔫.add_mem (𝔫.mul_mem_left d' hxh) (𝔫.mul_mem_left (algebraMap R C h) hd'𝔫)
    convert this using 1
    rw [hd, map_mul]
    ring
  have hcP : h * s' ∉ P := fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hh hs'
  have hdint : IsIntegral R d := by
    have h1 := SDR3Asm_integral_zero hg hιB hd0 (Algebra.IsIntegral.isIntegral (R := B) d)
    rwa [← IsScalarTower.algebraMap_eq R B C] at h1
  have h𝔯 : 𝔫.comap (algebraMap R C) = P := by
    ext s
    exact h𝔫R s
  have hdE : d ∈ Algebra.adjoin R {d} := Algebra.self_mem_adjoin_singleton R d
  obtain ⟨R'', _, _, _, P'', _, hP'', e₀, he₀, P', _, hP', heP', hd1', huniq, w, hw, u, hu⟩ :=
    SDR3Asm_isolate hdint P 𝔫 h𝔯 hcP hc𝔫
  have hdisj : Disjoint (Submonoid.powers w : Set R'') (P'' : Set R'') := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hm
    exact hw ((Ideal.IsPrime.mem_of_pow_mem ‹_› n) hm)
  let R₂ := Localization.Away w
  let P₂ : Ideal R₂ := P''.map (algebraMap R'' R₂)
  haveI hP₂ : P₂.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers w) R₂ P'' ‹_› hdisj
  have hP₂c : P₂.comap (algebraMap R'' R₂) = P'' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers w) R₂ ‹_› hdisj
  have hRP'' : ∀ s : R, algebraMap R R'' s ∈ P'' ↔ s ∈ P := fun s => by
    rw [hP''.over]
    rfl
  have hRP₂ : ∀ s : R, algebraMap R R₂ s ∈ P₂ ↔ s ∈ P := fun s => by
    rw [← hRP'', ← hP₂c, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
  haveI hP₂o : P₂.LiesOver P := ⟨by
    ext s
    exact (hRP₂ s).symm⟩
  let φ : R'' ⊗[R] Algebra.adjoin R {d} →ₐ[R] R₂ ⊗[R] C :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R'' R₂) (Algebra.adjoin R {d}).val
  obtain ⟨heI, u', hu'⟩ := SDLocA_of_isolate d hdE e₀ he₀ w u hu
  change IsIdempotentElem (φ e₀) at heI
  change φ e₀ = u' * ((1 : R₂) ⊗ₜ[R] d) * φ e₀ at hu'
  have he0 := SDR3Orbit_idem_deg0 (SDExist_bc R₂ cC hcC) heI
  haveI : Algebra.Etale B (Localization.Away d) := by
    have : d = a * (b₀ * d') := by rw [hd, hxa]; ring
    rw [this]
    exact SDR3Asm_etale_mul a (b₀ * d')
  letI := SDLocA_alg R B C R₂
  obtain ⟨-, hFin, -, -⟩ := SDLocA_finite R B R₂ C d heI ⟨u', hu'⟩
  obtain ⟨I₂, hJ₀I, hI₂, hI₂q, hI₂max⟩ := SDR3Asm_orbit_above (ι := (Algebra.TensorProduct.includeLeftRingHom : R₂ →+* R₂ ⊗[R] B))
    (SDExist_bc R₂ cB hcB) P₂ (SDR3Asm_J₀ R₂ P₂ I) (SDR3Asm_J₀_hom cB hcB P₂ I hI)
    (fun a ha => SDR3Asm_J₀_inv cB hcB hιB P₂ I hI P hIq (fun s hs => (hRP₂ s).2 hs) a ha)
  let ρ : C →ₐ[R] R₂ ⊗[R] C := Algebra.TensorProduct.includeRight
  let L : R₂ →+* R₂ ⊗[R] C := Algebra.TensorProduct.includeLeftRingHom
  have hρL : ∀ s : R, ρ (algebraMap R C s) = L (algebraMap R R₂ s) := fun s => by
    rw [AlgHom.commutes]
    rfl
  have hLρ : ∀ (r : R₂) (c : C), r ⊗ₜ[R] c = L r * ρ c := fun r c => by
    simp [L, ρ]
  let WW : Submonoid (R₂ ⊗[R] C) := (P₂.primeCompl).map L
  let 𝔍 : Ideal (R₂ ⊗[R] C) := I₂.map (algebraMap (R₂ ⊗[R] B) (R₂ ⊗[R] C))
  have halg : ∀ (r : R₂) (b : B), algebraMap (R₂ ⊗[R] B) (R₂ ⊗[R] C) (r ⊗ₜ[R] b) = r ⊗ₜ[R] algebraMap B C b := fun r b => by
    change (Algebra.TensorProduct.map (AlgHom.id R R₂) (IsScalarTower.toAlgHom R B C)) (r ⊗ₜ[R] b) = _
    simp
  have hI𝔍 : I.map (algebraMap B C) ≤ 𝔍.comap ρ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    change ρ (algebraMap B C i) ∈ 𝔍
    have h1 : (1 : R₂) ⊗ₜ[R] i ∈ I₂ := hJ₀I (Ideal.subset_span (Or.inr ⟨1, i, hi, rfl⟩))
    have h2 := Ideal.mem_map_of_mem (algebraMap (R₂ ⊗[R] B) (R₂ ⊗[R] C)) h1
    rwa [halg] at h2
  have hP𝔍 : ∀ p ∈ P₂, L p ∈ 𝔍 := by
    intro p hp
    have h1 : p ⊗ₜ[R] (1 : B) ∈ I₂ := hJ₀I (Ideal.subset_span (Or.inl ⟨p, hp, 1, rfl⟩))
    have h2 := Ideal.mem_map_of_mem (algebraMap (R₂ ⊗[R] B) (R₂ ⊗[R] C)) h1
    rw [halg, map_one] at h2
    exact h2
  have hQc : ∀ Q : Ideal (R₂ ⊗[R] C), 𝔍 ≤ Q → Disjoint (Q : Set (R₂ ⊗[R] C)) (WW : Set (R₂ ⊗[R] C)) →
      Q.comap L = P₂ := by
    intro Q hle hd
    ext p
    constructor
    · intro hp
      by_contra hn
      exact Set.disjoint_left.1 hd hp ⟨p, hn, rfl⟩
    · exact fun hp => hle (hP𝔍 p hp)
  -- comparison with `R'' ⊗ R[d]`
  have hφL : ∀ r : R'', φ (r ⊗ₜ[R] 1) = L (algebraMap R'' R₂ r) := fun r => by
    simp [φ, L]
  let dE : Algebra.adjoin R {d} := ⟨d, hdE⟩
  have hφd : φ ((1 : R'') ⊗ₜ[R] dE) = ρ d := by
    simp [φ, ρ, dE]
  have hφc : φ (algebraMap R (R'' ⊗[R] Algebra.adjoin R {d}) (h * s')) = ρ (algebraMap R C (h * s')) := by
    rw [AlgHom.commutes, AlgHom.commutes]
  have hQ₀ : ∀ Q : Ideal (R₂ ⊗[R] C), Q.IsPrime → Q.comap L = P₂ →
      (Q.comap φ.toRingHom).IsPrime ∧ (Q.comap φ.toRingHom).LiesOver P'' := by
    intro Q hQ hc
    refine ⟨Ideal.comap_isPrime _ _, ⟨?_⟩⟩
    ext r
    change r ∈ P'' ↔ φ (r ⊗ₜ[R] 1) ∈ Q
    rw [hφL, ← hP₂c, Ideal.mem_comap, ← hc]
    rfl
  have U1 : ∀ Q : Ideal (R₂ ⊗[R] C), Q.IsPrime → Q.comap L = P₂ → φ e₀ ∉ Q → ρ d - ρ (algebraMap R C (h * s')) ∈ Q := by
    intro Q hQ hc he
    obtain ⟨h1, h2⟩ := hQ₀ Q hQ hc
    have h3 := huniq _ h1 h2 he
    have h4 : (1 : R'') ⊗ₜ[R] dE - algebraMap R (R'' ⊗[R] Algebra.adjoin R {d}) (h * s') ∈ Q.comap φ.toRingHom := by
      rw [h3]
      exact hd1'
    have h5 : φ ((1 : R'') ⊗ₜ[R] dE - algebraMap R (R'' ⊗[R] Algebra.adjoin R {d}) (h * s')) ∈ Q := h4
    rwa [map_sub, hφd, hφc] at h5
  have U2 : ∀ Q : Ideal (R₂ ⊗[R] C), Q.IsPrime → Q.comap L = P₂ → ρ d - ρ (algebraMap R C (h * s')) ∈ Q → φ e₀ ∉ Q := by
    intro Q hQ hc hm
    obtain ⟨h1, h2⟩ := hQ₀ Q hQ hc
    have hmem : (1 : R'') ⊗ₜ[R] dE - algebraMap R (R'' ⊗[R] Algebra.adjoin R {d}) (h * s') ∈ Q.comap φ.toRingHom := by
      change φ _ ∈ Q
      rwa [map_sub, hφd, hφc]
    have hspan₁ : Ideal.span {(1 : R'') ⊗ₜ[R] dE - algebraMap R (R'' ⊗[R] Algebra.adjoin R {d}) (h * s')} ≤
        Q.comap φ.toRingHom := (Ideal.span_singleton_le_iff_mem _).2 hmem
    have hspan₂ : Ideal.span {(1 : R'') ⊗ₜ[R] dE - algebraMap R (R'' ⊗[R] Algebra.adjoin R {d}) (h * s')} ≤ P' :=
      (Ideal.span_singleton_le_iff_mem _).2 hd1'
    have hlo : ∀ r : R'', r ⊗ₜ[R] (1 : Algebra.adjoin R {d}) ∈ Q.comap φ.toRingHom ↔ r ∈ P'' := by
      intro r
      rw [h2.over]
      rfl
    have hlo' : ∀ r : R'', r ⊗ₜ[R] (1 : Algebra.adjoin R {d}) ∈ P' ↔ r ∈ P'' := by
      intro r
      rw [hP'.over]
      rfl
    have heq : Q.comap φ.toRingHom = P' := by
      ext w
      obtain ⟨r, hr⟩ := SDR3Asm_generated (R' := R'') d (h * s') w
      constructor
      · intro hw'
        have h3 := Ideal.sub_mem _ hw' (hspan₁ hr)
        rw [sub_sub_cancel] at h3
        have h4 := P'.add_mem ((hlo' r).2 ((hlo r).1 h3)) (hspan₂ hr)
        rwa [add_sub_cancel] at h4
      · intro hw'
        have h3 := P'.sub_mem hw' (hspan₂ hr)
        rw [sub_sub_cancel] at h3
        have h4 := Ideal.add_mem _ ((hlo r).2 ((hlo' r).1 h3)) (hspan₁ hr)
        rwa [add_sub_cancel] at h4
    intro hin
    exact heP' (heq ▸ hin)
  -- the star
  have hτW : ∀ t : R, t ∉ P → L (algebraMap R R₂ t) ∈ WW := fun t ht =>
    ⟨algebraMap R R₂ t, fun hm => ht ((hRP₂ t).1 hm), rfl⟩
  have hJ' : ∀ j ∈ 𝔫, ∃ t, t ∉ P ∧ L (algebraMap R R₂ t) * ρ d' * ρ j ∈ 𝔍 := by
    intro j hj
    obtain ⟨t, ht, hm⟩ := hJ j hj
    refine ⟨t, ht, ?_⟩
    have := hI𝔍 hm
    change ρ (algebraMap R C t * d' * j) ∈ 𝔍 at this
    rwa [map_mul, map_mul, hρL] at this
  obtain ⟨t, ⟨τ, hτ, rfl⟩, htS⟩ : ∃ t ∈ WW, t * (L (algebraMap R R₂ s') * φ e₀ - ρ d') ∈ 𝔍 := by
    refine SDR3Asm_star WW 𝔍 (h := L (algebraMap R R₂ h)) heI (hτW h hh) (hτW s' hs') (Dt := ρ d) ?_ ?_ ?_ ?_
    · obtain ⟨t, ht, hm⟩ := hJ' _ hxh
      refine ⟨_, hτW t ht, ?_⟩
      convert hm using 1
      rw [hd, map_sub, map_mul, hρL]
      ring
    · obtain ⟨t, ht, hm⟩ := hJ' _ hd'𝔫
      refine ⟨_, hτW t ht, ?_⟩
      convert hm using 1
      rw [map_sub, hρL]
      ring
    · intro Q hQ hle hd' he
      have := U1 Q hQ (hQc Q hle hd') he
      rwa [map_mul, map_mul, hρL, hρL] at this
    · intro Q hQ hle hd' hm
      refine U2 Q hQ (hQc Q hle hd') ?_
      rwa [map_mul, map_mul, hρL, hρL]
  -- `H1`, elementwise
  let cT := SDExist_bc R₂ cC hcC
  let Jd : Ideal (R₂ ⊗[R] C) := Ideal.span {1 - φ e₀}
  let D := (R₂ ⊗[R] C) ⧸ Jd
  let mk : (R₂ ⊗[R] C) →+* D := Ideal.Quotient.mk Jd
  have hmk𝔍 : ∀ z ∈ 𝔍 ⊔ Jd, mk z ∈ I₂.map (algebraMap (R₂ ⊗[R] B) D) := by
    intro z hz
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hz
    have h0 : mk j = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hj
    rw [map_add, h0, add_zero]
    have h1 : I₂.map (algebraMap (R₂ ⊗[R] B) D) = (𝔍.map mk) := by
      rw [Ideal.map_map]
      rfl
    rw [h1]
    exact Ideal.mem_map_of_mem _ hi
  have hH : ∀ y : D, ∃ s, s ∉ P₂ ∧ ∃ b, algebraMap (R₂ ⊗[R] B) D
      ((Algebra.TensorProduct.includeLeftRingHom : R₂ →+* R₂ ⊗[R] B) s) * y - algebraMap (R₂ ⊗[R] B) D b ∈
        I₂.map (algebraMap (R₂ ⊗[R] B) D) := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, (Ideal.ne_top_iff_one P₂).1 hP₂.ne_top, 0, by simp⟩
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨s₁, hs₁, b₁, hb₁⟩ := h₁
      obtain ⟨s₂, hs₂, b₂, hb₂⟩ := h₂
      refine ⟨s₁ * s₂, fun hm => (hP₂.mem_or_mem hm).elim hs₁ hs₂,
        (Algebra.TensorProduct.includeLeftRingHom : R₂ →+* R₂ ⊗[R] B) s₂ * b₁ +
          (Algebra.TensorProduct.includeLeftRingHom : R₂ →+* R₂ ⊗[R] B) s₁ * b₂, ?_⟩
      have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap (R₂ ⊗[R] B) D
        ((Algebra.TensorProduct.includeLeftRingHom : R₂ →+* R₂ ⊗[R] B) s₂)) hb₁)
        (Ideal.mul_mem_left _ (algebraMap (R₂ ⊗[R] B) D
        ((Algebra.TensorProduct.includeLeftRingHom : R₂ →+* R₂ ⊗[R] B) s₁)) hb₂)
      convert this using 1
      simp only [map_add, map_mul]
      ring
    | tmul r z' =>
      obtain ⟨s₁, hs₁, β, hβ⟩ := hfib z'
      obtain ⟨τ₁, hτ₁, hm⟩ := hJ' _ hβ
      let τ₁' := algebraMap R R₂ τ₁
      let s₁' := algebraMap R R₂ s₁
      let s'' := algebraMap R R₂ s'
      refine ⟨τ * s'' * τ₁' * s₁', ?_, (r * τ * s'' * τ₁') ⊗ₜ[R] β, ?_⟩
      · intro hmem
        refine ((hP₂.mem_or_mem hmem).elim (fun h3 => (hP₂.mem_or_mem h3).elim (fun h4 =>
          (hP₂.mem_or_mem h4).elim hτ fun h5 => hs' ((hRP₂ s').1 h5)) fun h4 => hτ₁ ((hRP₂ τ₁).1 h4))
          fun h3 => hs₁ ((hRP₂ s₁).1 h3))
      · let j := algebraMap R C s₁ * z' - algebraMap B C β
        have hexpr : L r * L τ * L τ₁' * L s'' * ρ j ∈ 𝔍 ⊔ Jd := by
          have h1 := 𝔍.mul_mem_left (L r * L τ₁' * ρ j) htS
          have h2 := 𝔍.mul_mem_left (L r * L τ) hm
          have h3 : L r * L τ * L τ₁' * L s'' * ρ j * (1 - φ e₀) ∈ Jd :=
            Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
          have h4 := Ideal.add_mem (𝔍 ⊔ Jd) (Ideal.mem_sup_left (𝔍.add_mem h1 h2)) (Ideal.mem_sup_right h3)
          convert h4 using 1
          ring
        have := hmk𝔍 _ hexpr
        convert this using 1
        change mk (((τ * s'' * τ₁' * s₁') ⊗ₜ[R] (1 : B) : R₂ ⊗[R] B) |> algebraMap (R₂ ⊗[R] B) (R₂ ⊗[R] C)) * mk (r ⊗ₜ[R] z') -
          mk (algebraMap (R₂ ⊗[R] B) (R₂ ⊗[R] C) ((r * τ * s'' * τ₁') ⊗ₜ[R] β)) = _
        rw [← map_mul, ← map_sub]
        congr 1
        rw [halg, halg, map_one, hLρ, hLρ, hLρ]
        simp only [map_mul, j, map_sub, hρL, map_one, mul_one]
        ring
  obtain ⟨sU, hsU, hSU⟩ := SDR3Asm_uniform_H1 (ι := (Algebra.TensorProduct.includeLeftRingHom : R₂ →+* R₂ ⊗[R] B))
    (D := D) (q := P₂) hH
  -- the prime `𝔯`
  haveI h𝔫o : 𝔫.LiesOver P := ⟨h𝔯.symm⟩
  obtain ⟨Q, hQ, hQL, hQρ⟩ := SDR3Asm_exists_prime P P₂ 𝔫
  have hQe : φ e₀ ∉ Q := by
    refine U2 Q hQ hQL ?_
    rw [← map_sub]
    have : d - algebraMap R C (h * s') ∈ Q.comap ρ.toRingHom := by
      rw [hQρ]
      exact hc𝔫
    exact this
  have h1e : 1 - φ e₀ ∈ Q := by
    have h6 : φ e₀ * (1 - φ e₀) ∈ Q := by
      rw [mul_sub, mul_one, heI.eq, sub_self]
      exact Q.zero_mem
    exact (hQ.mem_or_mem h6).resolve_left hQe
  have hkQ : Jd ≤ Q := (Ideal.span_singleton_le_iff_mem _).2 h1e
  let 𝔯 : Ideal D := Q.map mk
  have h𝔯P : 𝔯.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
    rw [Ideal.mk_ker]
    exact hkQ)
  have h𝔯q : ∀ a : R₂, algebraMap (R₂ ⊗[R] B) D (a ⊗ₜ[R] (1 : B)) ∈ 𝔯 → a ∈ P₂ := by
    intro a ha
    have h2 : mk (L a) ∈ Q.map mk := by
      have e1 : algebraMap (R₂ ⊗[R] B) D (a ⊗ₜ[R] (1 : B)) = mk (L a) := by
        change mk (algebraMap (R₂ ⊗[R] B) (R₂ ⊗[R] C) (a ⊗ₜ[R] (1 : B))) = _
        rw [halg, map_one]
        rfl
      rwa [e1] at ha
    have h3 := (Ideal.mem_quotient_iff_mem hkQ).1 h2
    rw [← hQL]
    exact h3
  obtain ⟨h₃, hh₃, hsurj, hinj, s₀, hs₀⟩ := SDR3Orbit_main R₂ cB cC hcB hcC hBC hιB d heI ⟨u', hu'⟩ he0 hI₂
    hI₂q hI₂max ⟨sU, hsU, hSU⟩ 𝔯 h𝔯P h𝔯q
  obtain ⟨κ, hκ1, hκ2⟩ := SDR3Asm_finish R₂ cB cC hcB hcC hBC hιB d hd0 he0 ⟨u', hu'⟩ h₃ hsurj hinj s₀ hs₀
  let R₃ := Localization.Away h₃
  have hP₃d : Disjoint (Submonoid.powers h₃ : Set R₂) (P₂ : Set R₂) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hm
    exact hh₃ ((Ideal.IsPrime.mem_of_pow_mem ‹_› n) hm)
  let P₃ : Ideal R₃ := P₂.map (algebraMap R₂ R₃)
  haveI hP₃ : P₃.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers h₃) R₃ P₂ ‹_› hP₃d
  have hP₃c : P₃.comap (algebraMap R₂ R₃) = P₂ :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers h₃) R₃ ‹_› hP₃d
  haveI hP₃o : P₃.LiesOver P := ⟨by
    ext s
    change s ∈ P ↔ algebraMap R R₃ s ∈ P₃
    rw [IsScalarTower.algebraMap_apply R R₂ R₃, ← Ideal.mem_comap, hP₃c, hRP₂]⟩
  haveI : Algebra.Etale R'' R₂ := Algebra.Etale.of_isLocalizationAway w
  haveI : Algebra.Etale R R₂ := Algebra.Etale.comp R R'' R₂
  haveI : Algebra.Etale R₂ R₃ := Algebra.Etale.of_isLocalizationAway h₃
  haveI : Algebra.Etale R R₃ := Algebra.Etale.comp R R₂ R₃
  exact ⟨R₃, inferInstance, inferInstance, inferInstance, P₃, hP₃, hP₃o, d, b₀ * d', by rw [hd, hxa]; ring, hd0, κ, hκ1, hκ2⟩

end AlgMag.SD
