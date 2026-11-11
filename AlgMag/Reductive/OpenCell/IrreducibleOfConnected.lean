/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.

Compiled; no sorry.
-/
import AlgMag.Reductive.OpenCell.TensorDomain
import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# A connected affine group over `k̄` is irreducible

`K` algebraically closed, `H` a commutative Hopf `K`-algebra of finite type (no smoothness, no
reducedness needed). If `Spec H` is connected, it is irreducible.

Proof.
1. (`minimalPrime_unique_le_augmentation`) At most one minimal prime lies in `ker ε`: if `p₁, p₂`
   are minimal and `≤ ker ε`, let `ρ : H → H/p₁ ⊗ H/p₂` be `Δ` followed by the quotients
   (the multiplication `X₁ × X₂ → G` of the two components). The target is a domain
   (`isDomain_tensorProduct_of_isAlgClosed`), so `q = ker ρ` is prime. Composing with
   `id ⊗ ε̄` (resp. `ε̄ ⊗ id`) gives the quotient map to `H/p₁` (resp. `H/p₂`) by the counit
   axiom, so `q ≤ p₁` and `q ≤ p₂`; minimality gives `p₁ = q = p₂`.
2. (`minimalPrime_unique_le_ker`) Right translation `R_g` by a `K`-point `g` is an algebra
   automorphism with `ε ∘ R_g = g`, so it moves minimal primes inside `ker g` to minimal primes
   inside `ker ε`: at most one minimal prime lies in each `ker g`, hence (Nullstellensatz) in each
   maximal ideal.
3. Distinct minimal primes are therefore comaximal. If there were two, `p` and
   `J = ⨅ (other minimal primes)` would be comaximal with `p ⊓ J = nilradical`, so `V(p)` would be
   a proper nonempty clopen subset of `Spec H`. Hence `minimalPrimes H = {p}`, the nilradical
   is prime, and `Spec H` is irreducible.
-/

namespace AlgMag.OpenCellNotes

open scoped TensorProduct
open TauCeti.HopfAlgebra WithConv

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {H : Type u} [CommRing H] [HopfAlgebra K H] [Algebra.FiniteType K H]

local notation "ε" => Bialgebra.counitAlgHom K H

omit [IsAlgClosed K] [Algebra.FiniteType K H] in
/-- Counit axiom, right form: `(id ⊗ ε) ∘ Δ = id` (after `H ⊗ K ≅ H`). -/
lemma rid_map_counit_comul (x : H) :
    Algebra.TensorProduct.rid K K H
      (Algebra.TensorProduct.map (R := K) (S := K) (AlgHom.id K H) ε (Bialgebra.comulAlgHom K H x)) = x := by
  have h := Coalgebra.lTensor_counit_comul (R := K) x
  have e : Algebra.TensorProduct.map (R := K) (S := K) (AlgHom.id K H) ε (Bialgebra.comulAlgHom K H x) =
      (Coalgebra.counit (R := K) (A := H)).lTensor H (Coalgebra.comul x) := rfl
  rw [e, h]
  simp

omit [IsAlgClosed K] [Algebra.FiniteType K H] in
/-- Counit axiom, left form: `(ε ⊗ id) ∘ Δ = id`. -/
lemma lid_map_counit_comul (x : H) :
    Algebra.TensorProduct.lid K H
      (Algebra.TensorProduct.map (R := K) (S := K) ε (AlgHom.id K H) (Bialgebra.comulAlgHom K H x)) = x := by
  have h := Coalgebra.rTensor_counit_comul (R := K) x
  have e : Algebra.TensorProduct.map (R := K) (S := K) ε (AlgHom.id K H) (Bialgebra.comulAlgHom K H x) =
      (Coalgebra.counit (R := K) (A := H)).rTensor H (Coalgebra.comul x) := rfl
  rw [e, h]
  simp

/-- A ring automorphism carries minimal primes to minimal primes. -/
lemma minimal_comap_ringEquiv (e : H ≃+* H) {p : Ideal H} (hp : Minimal Ideal.IsPrime p) :
    Minimal Ideal.IsPrime (p.comap (e : H →+* H)) := by
  have := hp.1
  refine ⟨Ideal.comap_isPrime (e : H →+* H) p, fun r hr hle => ?_⟩
  have := hr
  have hcomp : ∀ q : Ideal H, (q.comap (e : H →+* H)).comap (e.symm : H →+* H) = q := by
    intro q
    rw [Ideal.comap_comap]
    simp [RingEquiv.comp_symm, Ideal.comap_id]
  have hcomp' : ∀ q : Ideal H, (q.comap (e.symm : H →+* H)).comap (e : H →+* H) = q := by
    intro q
    rw [Ideal.comap_comap]
    simp [RingEquiv.symm_comp, Ideal.comap_id]
  have h1 : r.comap (e.symm : H →+* H) ≤ p := by
    simpa [hcomp p] using Ideal.comap_mono (f := (e.symm : H →+* H)) hle
  have h2 : p ≤ r.comap (e.symm : H →+* H) :=
    hp.2 (Ideal.comap_isPrime (e.symm : H →+* H) r) h1
  have h3 := Ideal.comap_mono (f := (e : H →+* H)) h2
  rwa [hcomp'] at h3

variable (K) in
/-- The product map `ρ : H → H/p₁ ⊗ H/p₂` of two components. -/
noncomputable def componentProduct (p₁ p₂ : Ideal H) : H →ₐ[K] (H ⧸ p₁) ⊗[K] (H ⧸ p₂) :=
  (Algebra.TensorProduct.map (R := K) (S := K) (Ideal.Quotient.mkₐ K p₁) (Ideal.Quotient.mkₐ K p₂)).comp
    (Bialgebra.comulAlgHom K H)

/-- `ker ρ ≤ p₁` when `p₂ ≤ ker ε`. -/
lemma ker_componentProduct_le_left (p₁ p₂ : Ideal H) (h₂ : p₂ ≤ RingHom.ker ε) :
    RingHom.ker (componentProduct K p₁ p₂) ≤ p₁ := by
  let ε₂ : H ⧸ p₂ →ₐ[K] K := Ideal.Quotient.liftₐ p₂ ε fun x hx => h₂ hx
  let π : (H ⧸ p₁) ⊗[K] (H ⧸ p₂) →ₐ[K] H ⧸ p₁ :=
    (Algebra.TensorProduct.rid K K (H ⧸ p₁)).toAlgHom.comp
      (Algebra.TensorProduct.map (R := K) (S := K) (AlgHom.id K _) ε₂)
  -- `π ∘ (mk₁ ⊗ mk₂) = mk₁ ∘ rid ∘ (id ⊗ ε)` on `H ⊗ H`.
  have hsq : π.comp (Algebra.TensorProduct.map (R := K) (S := K) (Ideal.Quotient.mkₐ K p₁)
      (Ideal.Quotient.mkₐ K p₂)) = (Ideal.Quotient.mkₐ K p₁).comp
        ((Algebra.TensorProduct.rid K K H).toAlgHom.comp
          (Algebra.TensorProduct.map (R := K) (S := K) (AlgHom.id K H) ε)) := by
    apply Algebra.TensorProduct.ext
    · ext a; simp [π]
    · ext b; simp [π, ε₂, Algebra.smul_def]; rfl
  have hπ : ∀ x, π (componentProduct K p₁ p₂ x) = Ideal.Quotient.mk p₁ x := by
    intro x
    have := DFunLike.congr_fun hsq (Bialgebra.comulAlgHom K H x)
    simp only [AlgHom.comp_apply] at this
    rw [show componentProduct K p₁ p₂ x = Algebra.TensorProduct.map (R := K) (S := K) (Ideal.Quotient.mkₐ K p₁)
      (Ideal.Quotient.mkₐ K p₂) (Bialgebra.comulAlgHom K H x) from rfl, this]
    exact congrArg (Ideal.Quotient.mk p₁) (rid_map_counit_comul x)
  intro x hx
  rw [RingHom.mem_ker] at hx
  have h0 := hπ x
  rw [hx, map_zero] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0.symm

/-- `ker ρ ≤ p₂` when `p₁ ≤ ker ε`. -/
lemma ker_componentProduct_le_right (p₁ p₂ : Ideal H) (h₁ : p₁ ≤ RingHom.ker ε) :
    RingHom.ker (componentProduct K p₁ p₂) ≤ p₂ := by
  let ε₁ : H ⧸ p₁ →ₐ[K] K := Ideal.Quotient.liftₐ p₁ ε fun x hx => h₁ hx
  let π : (H ⧸ p₁) ⊗[K] (H ⧸ p₂) →ₐ[K] H ⧸ p₂ :=
    (Algebra.TensorProduct.lid K (H ⧸ p₂)).toAlgHom.comp
      (Algebra.TensorProduct.map (R := K) (S := K) ε₁ (AlgHom.id K _))
  have hsq : π.comp (Algebra.TensorProduct.map (R := K) (S := K) (Ideal.Quotient.mkₐ K p₁)
      (Ideal.Quotient.mkₐ K p₂)) = (Ideal.Quotient.mkₐ K p₂).comp
        ((Algebra.TensorProduct.lid K H).toAlgHom.comp
          (Algebra.TensorProduct.map (R := K) (S := K) ε (AlgHom.id K H))) := by
    apply Algebra.TensorProduct.ext
    · ext a; simp [π, ε₁, Algebra.smul_def]; rfl
    · ext b; simp [π]
  have hπ : ∀ x, π (componentProduct K p₁ p₂ x) = Ideal.Quotient.mk p₂ x := by
    intro x
    have := DFunLike.congr_fun hsq (Bialgebra.comulAlgHom K H x)
    simp only [AlgHom.comp_apply] at this
    rw [show componentProduct K p₁ p₂ x = Algebra.TensorProduct.map (R := K) (S := K) (Ideal.Quotient.mkₐ K p₁)
      (Ideal.Quotient.mkₐ K p₂) (Bialgebra.comulAlgHom K H x) from rfl, this]
    exact congrArg (Ideal.Quotient.mk p₂) (lid_map_counit_comul x)
  intro x hx
  rw [RingHom.mem_ker] at hx
  have h0 := hπ x
  rw [hx, map_zero] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0.symm

/-- **Step 1.** At most one minimal prime lies in the augmentation ideal. -/
theorem minimalPrime_unique_le_augmentation {p₁ p₂ : Ideal H}
    (hp₁ : Minimal Ideal.IsPrime p₁) (hp₂ : Minimal Ideal.IsPrime p₂)
    (h₁ : p₁ ≤ RingHom.ker ε) (h₂ : p₂ ≤ RingHom.ker ε) : p₁ = p₂ := by
  have := hp₁.1
  have := hp₂.1
  have : Algebra.FiniteType K (H ⧸ p₁) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K p₁)
      (Ideal.Quotient.mkₐ_surjective K p₁)
  have : IsDomain ((H ⧸ p₁) ⊗[K] (H ⧸ p₂)) := isDomain_tensorProduct_of_isAlgClosed
  have hq : (RingHom.ker (componentProduct K p₁ p₂)).IsPrime := RingHom.ker_isPrime _
  have hle₁ := ker_componentProduct_le_left p₁ p₂ h₂
  have hle₂ := ker_componentProduct_le_right p₁ p₂ h₁
  have e₁ : p₁ ≤ RingHom.ker (componentProduct K p₁ p₂) := hp₁.2 hq hle₁
  have e₂ : p₂ ≤ RingHom.ker (componentProduct K p₁ p₂) := hp₂.2 hq hle₂
  exact le_antisymm (e₁.trans hle₂) (e₂.trans hle₁)

/-- **Step 2.** At most one minimal prime lies in the kernel of any `K`-point. -/
theorem minimalPrime_unique_le_ker (g : H →ₐ[K] K) {p₁ p₂ : Ideal H}
    (hp₁ : Minimal Ideal.IsPrime p₁) (hp₂ : Minimal Ideal.IsPrime p₂)
    (h₁ : p₁ ≤ RingHom.ker g) (h₂ : p₂ ≤ RingHom.ker g) : p₁ = p₂ := by
  let σ : H ≃ₐ[K] H := rightTranslationAlgEquiv (toConv g)
  let e : H ≃+* H := σ.symm.toRingEquiv
  have hεσ : ∀ x, ε (σ x) = g x := by
    intro x
    have h := DFunLike.congr_fun (counitAlgHom_comp_rightTranslationAlgHom (k := K) (H := H)
      (toConv g)) x
    rw [AlgHom.comp_apply] at h
    exact h
  have hle : ∀ p : Ideal H, p ≤ RingHom.ker g → p.comap (e : H →+* H) ≤ RingHom.ker ε := by
    intro p hp x hx
    rw [Ideal.mem_comap] at hx
    have h' := hp hx
    rw [RingHom.mem_ker] at h' ⊢
    rw [← hεσ] at h'
    -- `e x = σ.symm x`, `σ (σ.symm x) = x`.
    simpa [e] using h'
  have := minimalPrime_unique_le_augmentation (minimal_comap_ringEquiv e hp₁)
    (minimal_comap_ringEquiv e hp₂) (hle p₁ h₁) (hle p₂ h₂)
  exact Ideal.comap_injective_of_surjective (e : H →+* H) e.surjective this

variable (K) in
include K in
/-- **Step 3a.** Distinct minimal primes are comaximal. -/
theorem sup_eq_top_of_minimal {p₁ p₂ : Ideal H}
    (hp₁ : Minimal Ideal.IsPrime p₁) (hp₂ : Minimal Ideal.IsPrime p₂) (hne : p₁ ≠ p₂) :
    p₁ ⊔ p₂ = ⊤ := by
  by_contra htop
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ htop
  obtain ⟨g, hg⟩ := exists_algHom_ker_eq (K := K) m
  exact hne (minimalPrime_unique_le_ker g hp₁ hp₂ (hg ▸ le_sup_left.trans hle)
    (hg ▸ le_sup_right.trans hle))

variable (K) in
include K in
/-- **A connected affine group of finite type over an algebraically closed field is
irreducible.** -/
theorem irreducibleSpace_of_connectedSpace [ConnectedSpace (PrimeSpectrum H)] :
    IrreducibleSpace (PrimeSpectrum H) := by
  classical
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing K H
  have hfin : (minimalPrimes H).Finite := minimalPrimes.finite_of_isNoetherianRing H
  have hmin : ∀ {q : Ideal H}, q ∈ minimalPrimes H → Minimal Ideal.IsPrime q := fun hq => by
    rw [minimalPrimes_eq_minimals] at hq
    exact hq
  have : (RingHom.ker ε).IsPrime := RingHom.ker_isPrime _
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal H)) (J := RingHom.ker ε)
    bot_le
  have hpmin : Minimal Ideal.IsPrime p := hmin hp
  have hall : ∀ p' ∈ minimalPrimes H, p' = p := by
    intro p' hp'
    have hp'min : Minimal Ideal.IsPrime p' := hmin hp'
    by_contra hne
    let s : Finset (Ideal H) := hfin.toFinset.erase p
    let J : Ideal H := ⨅ r ∈ s, r
    have hJ : p ⊔ J = ⊤ := by
      refine Ideal.sup_iInf_eq_top fun r hr => ?_
      simp only [s, Finset.mem_erase, Set.Finite.mem_toFinset] at hr
      exact sup_eq_top_of_minimal K hpmin (hmin hr.2) (Ne.symm hr.1)
    have hinf : p ⊓ J = nilradical H := by
      have hS : hfin.toFinset = insert p s := by
        rw [Finset.insert_erase (hfin.mem_toFinset.mpr hp)]
      have h2 : nilradical H = ⨅ r ∈ minimalPrimes H, r := by
        rw [nilradical, ← Ideal.sInf_minimalPrimes, sInf_eq_iInf]
        rfl
      have h3 : (⨅ r ∈ hfin.toFinset, r) = ⨅ r ∈ minimalPrimes H, r := by
        simp only [Set.Finite.mem_toFinset]
      rw [h2, ← h3, hS, Finset.iInf_insert]
    have hU : PrimeSpectrum.zeroLocus (p : Set H) ∪ PrimeSpectrum.zeroLocus (J : Set H) =
        Set.univ := by
      rw [← PrimeSpectrum.zeroLocus_inf, hinf, nilradical, PrimeSpectrum.zeroLocus_radical]
      exact PrimeSpectrum.zeroLocus_bot
    have hI : PrimeSpectrum.zeroLocus (p : Set H) ∩ PrimeSpectrum.zeroLocus (J : Set H) = ∅ := by
      rw [← PrimeSpectrum.zeroLocus_sup, hJ]
      exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr rfl
    have hcompl : (PrimeSpectrum.zeroLocus (p : Set H))ᶜ = PrimeSpectrum.zeroLocus (J : Set H) := by
      ext x
      constructor
      · intro hx
        have hxU : x ∈ (Set.univ : Set (PrimeSpectrum H)) := trivial
        rw [← hU] at hxU
        exact hxU.resolve_left hx
      · intro hx hx'
        have : x ∈ (∅ : Set (PrimeSpectrum H)) := hI ▸ ⟨hx', hx⟩
        exact this
    have hcl : IsClopen (PrimeSpectrum.zeroLocus (p : Set H)) := by
      refine ⟨PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
      rw [← isClosed_compl_iff, hcompl]
      exact PrimeSpectrum.isClosed_zeroLocus _
    rcases isClopen_iff.mp hcl with h0 | h1
    · have hmem : (⟨p, hpmin.1⟩ : PrimeSpectrum H) ∈ PrimeSpectrum.zeroLocus (p : Set H) :=
        (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl
      rw [h0] at hmem
      exact hmem
    · have hp's : p' ∈ s := by
        simp only [s, Finset.mem_erase, Set.Finite.mem_toFinset]
        exact ⟨hne, hp'⟩
      have hp'J : (⟨p', hp'min.1⟩ : PrimeSpectrum H) ∈ PrimeSpectrum.zeroLocus (J : Set H) :=
        (PrimeSpectrum.mem_zeroLocus _ _).mpr (iInf₂_le p' hp's : J ≤ p')
      have hp'p : (⟨p', hp'min.1⟩ : PrimeSpectrum H) ∈ PrimeSpectrum.zeroLocus (p : Set H) := by
        rw [h1]; trivial
      have : (⟨p', hp'min.1⟩ : PrimeSpectrum H) ∈ (∅ : Set (PrimeSpectrum H)) :=
        hI ▸ ⟨hp'p, hp'J⟩
      exact this
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  have hnil : nilradical H = p := by
    have hset : (⊥ : Ideal H).minimalPrimes = {p} := by
      ext q
      constructor
      · intro hq; exact hall q hq
      · rintro rfl; exact hp
    rw [nilradical, ← Ideal.sInf_minimalPrimes]
    change sInf ((⊥ : Ideal H).minimalPrimes) = p
    rw [hset, sInf_singleton]
  rw [hnil]
  exact hpmin.1

end AlgMag.OpenCellNotes
