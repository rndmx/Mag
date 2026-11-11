/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Data.Finsupp.PWO
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Order.WellFoundedSet
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import StacksFrontier.RingTheory.Etale.Basic.FirstProperties

/-!
# Algebraization of the chart: §§5–6 of the chart-lemma proof

All of this is the commutative algebra of Steps (4) and "shrink" of the proof of AHR Cor. 10.2 for
`D(M)`, in magnet language: gradings, no cocharacters.

* `graded_coordinates`: homogeneous coordinates `x_i`, with `ℤ[x_i] → C/m^k` onto.
* `P0`, `Pd`, `P0_finiteType`, `Pd_fg`: **Lemma 3.1** for the graded polynomial ring `P`.
* `Qring`, `Qmap`, `Qmap_surjective`, `Qmap_ker_homogeneous`: `Q = P ⊗_{P₀} P̂₀ → C` is onto with
  homogeneously generated kernel.
* `lemma51_initial`, `length_le_of_initial`: **Lemma 5.1**.
* `flat_of_truncationsBijective`, `isEtaleAt_of_truncationsBijective`: **EGA IV 17.6.3**, proved.
* `truncationsBijective_of_presentations`, `isEtaleAt_of_presentations`: étaleness at `w`.
* `shrinking`, `etale_chart`: the **Shrinking Lemma** and the affine chart `D(h)`.

Artin approximation itself is `AlgMag.ChartArtin.artinApprox_of_finiteType_int`; nothing here
assumes it.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000
set_option linter.style.haveILetI false

section PartK
open CategoryTheory
namespace AlgMag.ChartAlg
/-- König for sequences: an inverse sequence of nonempty finite types has a compatible section. -/
lemma exists_section_of_finite {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]
    (π : ∀ n, X (n + 1) → X n) : ∃ s : ∀ n, X n, ∀ n, π n (s (n + 1)) = s n := by
  let F : ℕᵒᵖ ⥤ Type _ := Functor.ofOpSequence (fun n => TypeCat.ofHom (π n))
  have : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => by
    change Finite (X j.unop); infer_instance
  have : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => by
    change Nonempty (X j.unop); infer_instance
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => s (Opposite.op n), fun n => ?_⟩
  have := hs (homOfLE (Nat.le_succ n)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at this
  exact this
end AlgMag.ChartAlg

end PartK

section PartP1
namespace AlgMag.ChartAlg

section Lemma51

variable {Ξ : Type*} [CommRing Ξ]

lemma mem_smul_top_pi {ι : Type*} [Finite ι] (I : Ideal Ξ) (a : ι → Ξ) :
    a ∈ (I • ⊤ : Submodule Ξ (ι → Ξ)) ↔ ∀ ℓ, a ℓ ∈ I := by
  classical
  have := Fintype.ofFinite ι
  constructor
  · intro h
    refine Submodule.smul_induction_on h (fun r hr x _ ℓ => ?_) (fun x y hx hy ℓ => ?_)
    · simpa using I.mul_mem_right _ hr
    · simpa using I.add_mem (hx ℓ) (hy ℓ)
  · intro h
    have : a = ∑ ℓ, a ℓ • (Pi.single ℓ (1 : Ξ) : ι → Ξ) := by
      funext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun ℓ _ => Submodule.smul_mem_smul (h ℓ) trivial

/-- Elements of `I • (range L)`, for `L` on a finite free module, are `L` of a vector with entries
in `I`. -/
lemma exists_of_mem_smul_range {ι X : Type*} [Finite ι] [AddCommGroup X] [Module Ξ X]
    (L : (ι → Ξ) →ₗ[Ξ] X) (I : Ideal Ξ) {x : X} (hx : x ∈ I • LinearMap.range L) :
    ∃ c : ι → Ξ, (∀ j, c j ∈ I) ∧ L c = x := by
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨c, (mem_smul_top_pi I c).1 hc, rfl⟩

variable (𝔫 : Ideal Ξ)

lemma sum_smul_mem_pow {ι : Type*} [Fintype ι] {a b : ι → Ξ} {p q : ℕ} (ha : ∀ ℓ, a ℓ ∈ 𝔫 ^ p)
    (hb : ∀ ℓ, b ℓ ∈ 𝔫 ^ q) : ∑ ℓ, a ℓ * b ℓ ∈ 𝔫 ^ (p + q) :=
  Ideal.sum_mem _ fun ℓ _ => by rw [pow_add]; exact Ideal.mul_mem_mul (ha ℓ) (hb ℓ)

set_option maxHeartbeats 1000000 in
/-- **Lemma 5.1**, first part, of the note `ahr-specialized-proof.md` (the case of AHR20 A.17(6)):
if `f̃ ≡ f` and `r̃ ≡ r` modulo `𝔫^(N+1)`, with `r` generating the syzygies of `f`, `r̃` syzygies of
`f̃`, and `N` at least the Artin–Rees constants (depending on `f`, `r` only), then
`in(f̃) ⊆ in(f)`: an element of `(f̃)` of order `n` is an element of `(f)` of order `n` modulo
`𝔫^(n+1)`. -/
theorem lemma51_initial [IsNoetherianRing Ξ] {s t : ℕ} (f : Fin s → Ξ) (r : Fin t → Fin s → Ξ)
    (hr : Submodule.span Ξ (Set.range r) = LinearMap.ker (Fintype.linearCombination Ξ f)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (f' : Fin s → Ξ) (r' : Fin t → Fin s → Ξ),
      (∀ ℓ, f' ℓ - f ℓ ∈ 𝔫 ^ (N + 1)) → (∀ j ℓ, r' j ℓ - r j ℓ ∈ 𝔫 ^ (N + 1)) →
      (∀ j, ∑ ℓ, r' j ℓ * f' ℓ = 0) →
      ∀ (n : ℕ) (v : Ξ), v ∈ Ideal.span (Set.range f') → v ∈ 𝔫 ^ n →
        v ∈ (Ideal.span (Set.range f) ⊓ 𝔫 ^ n) ⊔ 𝔫 ^ (n + 1) := by
  classical
  set θ := Fintype.linearCombination Ξ f with hθ
  have θapp : ∀ a, θ a = ∑ ℓ, a ℓ * f ℓ := fun a => by
    simp [hθ, Fintype.linearCombination_apply]
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔫 (LinearMap.range θ)
  obtain ⟨c₂, hc₂⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔫 (LinearMap.ker θ)
  refine ⟨max c c₂, fun N hN f' r' hf hr' hrs n v hv hvn => ?_⟩
  have hNc : c ≤ N := (le_max_left _ _).trans hN
  have hNc₂ : c₂ ≤ N := (le_max_right _ _).trans hN
  -- Artin–Rees for `θ`
  have AR1 : ∀ (m : ℕ) (a : Fin s → Ξ), θ a ∈ 𝔫 ^ (m + c) →
      ∃ b : Fin s → Ξ, (∀ ℓ, b ℓ ∈ 𝔫 ^ m) ∧ θ b = θ a := by
    intro m a ha
    have h1 : θ a ∈ (𝔫 ^ (m + c) • ⊤ : Submodule Ξ Ξ) ⊓ LinearMap.range θ :=
      ⟨by simpa using ha, ⟨a, rfl⟩⟩
    rw [hc (m + c) (by omega), Nat.add_sub_cancel] at h1
    exact exists_of_mem_smul_range θ _ (Submodule.smul_mono le_rfl inf_le_right h1)
  -- Artin–Rees for the syzygies
  have AR2 : ∀ (m : ℕ) (ρ : Fin s → Ξ), (∀ ℓ, ρ ℓ ∈ 𝔫 ^ m) → θ ρ = 0 →
      ∃ e : Fin t → Ξ, (∀ j, e j ∈ 𝔫 ^ (m - c₂)) ∧ ∑ j, e j • r j = ρ := by
    intro m ρ hρ h0
    have hker : (LinearMap.ker θ) = LinearMap.range (Fintype.linearCombination Ξ r) := by
      rw [Fintype.range_linearCombination, hr]
    have h2 : ρ ∈ (𝔫 ^ (m - c₂)) • LinearMap.ker θ := by
      by_cases hm : c₂ ≤ m
      · have h1 : ρ ∈ (𝔫 ^ m • ⊤ : Submodule Ξ (Fin s → Ξ)) ⊓ LinearMap.ker θ :=
          ⟨(mem_smul_top_pi _ _).2 hρ, h0⟩
        rw [hc₂ m hm] at h1
        exact Submodule.smul_mono le_rfl inf_le_right h1
      · have : m - c₂ = 0 := by omega
        rw [this, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        exact h0
    rw [hker] at h2
    obtain ⟨e, he, hee⟩ := exists_of_mem_smul_range _ _ h2
    exact ⟨e, he, by simpa [Fintype.linearCombination_apply] using hee⟩
  -- `v` is `θ̃ a`
  have hv' : ∃ a : Fin s → Ξ, ∑ ℓ, a ℓ * f' ℓ = v := by
    have : v ∈ LinearMap.range (Fintype.linearCombination Ξ f') := by
      rw [Fintype.range_linearCombination]; exact hv
    obtain ⟨a, rfl⟩ := this
    exact ⟨a, by simp [Fintype.linearCombination_apply]⟩
  -- the induction
  have key : ∀ u, u + c ≤ n → ∃ a : Fin s → Ξ, (∀ ℓ, a ℓ ∈ 𝔫 ^ u) ∧ ∑ ℓ, a ℓ * f' ℓ = v := by
    intro u
    induction u with
    | zero =>
      intro _
      obtain ⟨a, ha⟩ := hv'
      exact ⟨a, by simp, ha⟩
    | succ u ih =>
      intro hu
      obtain ⟨a, ha, hav⟩ := ih (by omega)
      have hdiff : θ a - v ∈ 𝔫 ^ (u + 1 + c) := by
        have : θ a - v = ∑ ℓ, a ℓ * (f ℓ - f' ℓ) := by
          rw [θapp, ← hav, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun ℓ _ => by ring
        rw [this]
        refine Ideal.pow_le_pow_right (n := u + (N + 1)) (by omega) (sum_smul_mem_pow 𝔫 ha ?_)
        intro ℓ
        rw [← neg_sub]; exact neg_mem (hf ℓ)
      have hθa : θ a ∈ 𝔫 ^ (u + 1 + c) := by
        have := add_mem hdiff (Ideal.pow_le_pow_right hu hvn)
        rwa [sub_add_cancel] at this
      obtain ⟨b, hb, hbθ⟩ := AR1 (u + 1) a hθa
      have hρ : ∀ ℓ, (a - b) ℓ ∈ 𝔫 ^ u := fun ℓ =>
        sub_mem (ha ℓ) (Ideal.pow_le_pow_right (by omega) (hb ℓ))
      obtain ⟨e, he, hee⟩ := AR2 u (a - b) hρ (by simp [hbθ])
      refine ⟨b + ∑ j, e j • (r j - r' j), fun ℓ => ?_, ?_⟩
      · refine add_mem (hb ℓ) ?_
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        refine Ideal.sum_mem _ fun j _ => ?_
        refine Ideal.pow_le_pow_right (n := (u - c₂) + (N + 1)) (by omega) ?_
        rw [pow_add]
        refine Ideal.mul_mem_mul (he j) ?_
        rw [← neg_sub]; exact neg_mem (hr' j ℓ)
      · have ha' : b + ∑ j, e j • (r j - r' j) = a - ∑ j, e j • r' j := by
          have : a = b + ∑ j, e j • r j := by rw [hee]; abel
          simp only [smul_sub, Finset.sum_sub_distrib]
          rw [eq_sub_iff_add_eq]
          conv_rhs => rw [this]
          abel
        rw [ha']
        have hz : ∑ ℓ, (∑ j, e j • r' j) ℓ * f' ℓ = 0 := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_eq_zero fun j _ => ?_
          simp only [mul_assoc, ← Finset.mul_sum, hrs j, mul_zero]
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hav, hz, sub_zero]
  have hfin : ∃ a : Fin s → Ξ, (∀ ℓ, a ℓ ∈ 𝔫 ^ (n - c)) ∧ ∑ ℓ, a ℓ * f' ℓ = v := by
    by_cases h : c ≤ n
    · exact key (n - c) (by omega)
    · obtain ⟨a, ha⟩ := hv'
      exact ⟨a, by simp [show n - c = 0 by omega], ha⟩
  obtain ⟨a, ha, hav⟩ := hfin
  have hd : v - θ a ∈ 𝔫 ^ (n + 1) := by
    have : v - θ a = ∑ ℓ, a ℓ * (f' ℓ - f ℓ) := by
      rw [θapp, ← hav, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
    rw [this]
    exact Ideal.pow_le_pow_right (n := (n - c) + (N + 1)) (by omega) (sum_smul_mem_pow 𝔫 ha hf)
  have hθn : θ a ∈ 𝔫 ^ n := by
    have := sub_mem hvn (Ideal.pow_le_pow_right (Nat.le_succ n) hd)
    rwa [sub_sub_cancel] at this
  have hθf : θ a ∈ Ideal.span (Set.range f) := by
    rw [θapp]
    exact Ideal.sum_mem _ fun ℓ _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨ℓ, rfl⟩)
  have : v = θ a + (v - θ a) := by ring
  rw [this]
  exact Submodule.add_mem_sup ⟨hθf, hθn⟩ hd

end Lemma51
end AlgMag.ChartAlg

end PartP1

section PartP2
namespace AlgMag.ChartAlg

section Hilbert

variable {Ξ : Type*} [CommRing Ξ] (𝔫 : Ideal Ξ)

/-- The degree `j` graded piece of the Hilbert function of `Ξ/I`. -/
abbrev HilbertPiece (I : Ideal Ξ) (j : ℕ) : Type _ :=
  ↥(𝔫 ^ j) ⧸ (Submodule.comap (𝔫 ^ j).subtype (I ⊔ 𝔫 ^ (j + 1)))

lemma length_succ (I : Ideal Ξ) (j : ℕ) :
    Module.length Ξ (Ξ ⧸ (I ⊔ 𝔫 ^ (j + 1))) =
      Module.length Ξ (HilbertPiece 𝔫 I j) + Module.length Ξ (Ξ ⧸ (I ⊔ 𝔫 ^ j)) := by
  have hle : I ⊔ 𝔫 ^ (j + 1) ≤ I ⊔ 𝔫 ^ j := sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ j)) _
  let u : HilbertPiece 𝔫 I j →ₗ[Ξ] (Ξ ⧸ (I ⊔ 𝔫 ^ (j + 1))) :=
    Submodule.mapQ _ _ (𝔫 ^ j).subtype le_rfl
  let w : (Ξ ⧸ (I ⊔ 𝔫 ^ (j + 1))) →ₗ[Ξ] (Ξ ⧸ (I ⊔ 𝔫 ^ j)) := Submodule.factor hle
  refine Module.length_eq_add_of_exact u w ?_ (Submodule.factor_surjective hle) ?_
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    intro hx
    have : (x : Ξ) ∈ I ⊔ 𝔫 ^ (j + 1) :=
       Ideal.Quotient.eq_zero_iff_mem.1 (by simpa [u] using hx)
    exact (Submodule.Quotient.mk_eq_zero _).2 this
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    constructor
    · intro hy
      have hy' : y ∈ I ⊔ 𝔫 ^ j := by
        exact Ideal.Quotient.eq_zero_iff_mem.1 hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
      refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
      simp only [u, Submodule.mapQ_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      have : b - (a + b) = -a := by ring
      rw [this]
      exact neg_mem (Submodule.mem_sup_left ha)
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← hx]
      simp only [u, w, Submodule.mapQ_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_sup_right x.2)

/-- **Lemma 5.1**, second part, of the note: `in(I') ⊆ in(I)` implies
`length Ξ/(I + 𝔫^j) ≤ length Ξ/(I' + 𝔫^j)` for all `j`. -/
theorem length_le_of_initial (I I' : Ideal Ξ)
    (h : ∀ (n : ℕ) (v : Ξ), v ∈ I' → v ∈ 𝔫 ^ n → v ∈ (I ⊓ 𝔫 ^ n) ⊔ 𝔫 ^ (n + 1)) (j : ℕ) :
    Module.length Ξ (Ξ ⧸ (I ⊔ 𝔫 ^ j)) ≤ Module.length Ξ (Ξ ⧸ (I' ⊔ 𝔫 ^ j)) := by
  induction j with
  | zero =>
    have : Subsingleton (Ξ ⧸ (I ⊔ 𝔫 ^ 0)) := by
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
      exact Submodule.Quotient.subsingleton_iff.2 rfl
    rw [Module.length_eq_zero]; exact zero_le
  | succ j ih =>
    rw [length_succ, length_succ]
    refine add_le_add ?_ ih
    have hc : Submodule.comap (𝔫 ^ j).subtype (I' ⊔ 𝔫 ^ (j + 1)) ≤
        Submodule.comap (𝔫 ^ j).subtype (I ⊔ 𝔫 ^ (j + 1)) := by
      rintro ⟨x, hx⟩ hx'
      obtain ⟨u, hu, y, hy, huy⟩ := Submodule.mem_sup.1 (show x ∈ I' ⊔ 𝔫 ^ (j + 1) from hx')
      have hun : u ∈ 𝔫 ^ j := by
        have : u = x - y := by rw [← huy]; ring
        rw [this]
        exact sub_mem hx (Ideal.pow_le_pow_right (Nat.le_succ j) hy)
      have h1 := h j u hu hun
      have h20 : (I ⊓ 𝔫 ^ j) ⊔ 𝔫 ^ (j + 1) ≤ I ⊔ 𝔫 ^ (j + 1) := sup_le_sup_right inf_le_left _
      have h2 : u ∈ I ⊔ 𝔫 ^ (j + 1) := h20 h1
      show x ∈ I ⊔ 𝔫 ^ (j + 1)
      rw [← huy]
      exact add_mem h2 (Submodule.mem_sup_right hy)
    exact Module.length_le_of_surjective (Submodule.factor hc) (Submodule.factor_surjective hc)

/-- Length of `Ξ/J` over `Ξ` is its length over itself. -/
lemma length_quotient_self (J : Ideal Ξ) :
    Module.length Ξ (Ξ ⧸ J) = Module.length (Ξ ⧸ J) (Ξ ⧸ J) :=
  Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

/-- A surjective ring map from a ring of finite length, whose self-length is at least that of the
source, is injective. -/
lemma injective_of_surjective_of_length_le {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (hg : Function.Surjective g) (hfin : Module.length R R ≠ ⊤)
    (hle : Module.length R R ≤ Module.length S S) : Function.Injective g := by
  let := g.toAlgebra
  have e : Module.length R S = Module.length S S :=
    Module.length_eq_of_surjective (S := R) (R := S) hg
  let gl : R →ₗ[R] S := Algebra.linearMap R S
  have hgl : Function.Surjective gl := hg
  have ex := Module.length_eq_add_of_exact (LinearMap.ker gl).subtype gl
    (Submodule.subtype_injective _) hgl (LinearMap.exact_subtype_ker_map gl)
  rw [e] at ex
  have hS : Module.length S S ≠ ⊤ := fun h => hfin (by rw [ex, h]; simp)
  have h0 : Module.length R (LinearMap.ker gl) = 0 := by
    have h3 : Module.length R (LinearMap.ker gl) + Module.length S S ≤ 0 + Module.length S S := by
      rw [← ex, zero_add]; exact hle
    exact le_antisymm (WithTop.le_of_add_le_add_right hS h3) (zero_le)
  have hsub := Module.length_eq_zero_iff.1 h0
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : (⟨a, ha⟩ : LinearMap.ker gl) = 0 := Subsingleton.elim _ _
  exact congrArg Subtype.val this

end Hilbert
end AlgMag.ChartAlg

end PartP2

section PartP3
open IsLocalRing TensorProduct

namespace AlgMag.ChartAlg

lemma length_quotient_ne_top {Ξ : Type*} [CommRing Ξ] [IsNoetherianRing Ξ] (𝔫 : Ideal Ξ)
    [𝔫.IsMaximal] (J : Ideal Ξ) {j : ℕ} (h : 𝔫 ^ j ≤ J) :
    Module.length (Ξ ⧸ J) (Ξ ⧸ J) ≠ ⊤ := by
  have : Ring.KrullDimLE 0 (Ξ ⧸ J) := Ring.krullDimLE_zero_iff.mpr fun P hP => by
    have hc : (P.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
    have hJ : J ≤ P.comap (Ideal.Quotient.mk J) := fun x hx => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact zero_mem _
    have hn : 𝔫 ≤ P.comap (Ideal.Quotient.mk J) := fun x hx =>
      hc.mem_of_pow_mem j (hJ (h (Ideal.pow_mem_pow hx j)))
    have hne : P.comap (Ideal.Quotient.mk J) ≠ ⊤ := hc.ne_top
    have hmax : (P.comap (Ideal.Quotient.mk J)).IsMaximal := by
      rw [← ‹𝔫.IsMaximal›.eq_of_le hne hn]; infer_instance
    have hs : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
    have hm := Ideal.map_comap_of_surjective _ hs P
    rcases (P.comap (Ideal.Quotient.mk J)).map_eq_top_or_isMaximal_of_surjective _ hs hmax with h1 | h1
    · rw [hm] at h1; exact absurd h1 hP.ne_top
    · rwa [hm] at h1
  have : IsArtinianRing (Ξ ⧸ J) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact Module.length_ne_top

section EGA

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

/-- Nakayama on cotangent spaces. -/
lemma map_maximalIdeal_eq_of_cotangent [IsNoetherianRing B]
    (h : maximalIdeal B ≤ (maximalIdeal A).map (algebraMap A B) ⊔ maximalIdeal B ^ 2) :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    by_contra hc
    exact (mem_maximalIdeal x).1 hx (isUnit_of_map_unit (algebraMap A B) x
      (by simpa [mem_maximalIdeal, mem_nonunits_iff] using hc))
  · refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
    simpa [pow_two, smul_eq_mul] using h

/-- The map on truncations. -/
noncomputable def truncMap (j : ℕ) : A →+* B ⧸ (maximalIdeal B) ^ j :=
  (Ideal.Quotient.mk _).comp (algebraMap A B)

/-- Truncations bijective: `A → B/𝔫^j` is onto with kernel `𝔪^j`. This is the form in which the
completed local map `Â → B̂` is an isomorphism. -/
structure TruncationsBijective (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [Algebra A B] : Prop where
  surj : ∀ j, Function.Surjective ((Ideal.Quotient.mk ((maximalIdeal B) ^ j)).comp (algebraMap A B))
  ker : ∀ j, (maximalIdeal B ^ j).comap (algebraMap A B) = maximalIdeal A ^ j

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- The completed map `Â → B̂`, as a bijection. -/
lemma exists_completion_equiv (h : TruncationsBijective A B) :
    Nonempty (AdicCompletion (maximalIdeal A) A ≃ₗ[A] AdicCompletion (maximalIdeal B) B) := by
  classical
  set 𝔪 := maximalIdeal A
  set 𝔫 := maximalIdeal B
  -- levelwise maps `Â → B/𝔫^j`
  let q : ∀ j, A ⧸ 𝔪 ^ j →+* B ⧸ 𝔫 ^ j := fun j =>
    Ideal.quotientMap _ (algebraMap A B) (le_of_eq (h.ker j).symm)
  have hq : ∀ j x, q j (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A B x) := fun _ _ => rfl
  have hqinj : ∀ j, Function.Injective (q j) := by
    intro j
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hq, Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ← h.ker j]
    exact hx
  let F : ∀ j, AdicCompletion 𝔪 A →+* B ⧸ 𝔫 ^ j := fun j =>
    (q j).comp (AdicCompletion.evalₐ 𝔪 j).toRingHom
  have hF : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow 𝔫 hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective 𝔪 A x
    simp only [F, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AdicCompletion.evalₐ_mk, hq]
    simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.eq, ← map_sub]
    have := c.2 hle
    rw [SModEq.sub_mem] at this
    have h3 : c.1 m - c.1 n ∈ 𝔪 ^ m := by simpa using this
    have h3' := neg_mem h3
    rw [neg_sub] at h3'
    exact (h.ker m).ge h3'
  let G : AdicCompletion 𝔪 A →+* AdicCompletion 𝔫 B := AdicCompletion.liftRingHom 𝔫 F hF
  have hG : ∀ j x, AdicCompletion.evalₐ 𝔫 j (G x) = F j x := by
    intro j x
    exact AdicCompletion.evalₐ_liftRingHom 𝔫 F hF j x
  have Gmap : ∀ (a : A) x, G (a • x) = a • G x := by
    intro a x
    apply AdicCompletion.ext_evalₐ
    intro j
    rw [hG, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, hG]
    congr 1
  have Ginj : Function.Injective G := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply AdicCompletion.ext_evalₐ
    intro j
    apply hqinj j
    have := hG j x
    rw [hx, map_zero] at this
    simpa [F] using this.symm
  have Gsurj : Function.Surjective G := by
    intro y
    obtain ⟨b, rfl⟩ := AdicCompletion.mk_surjective 𝔫 B y
    choose a ha using fun j => h.surj j (AdicCompletion.evalₐ 𝔫 j (AdicCompletion.mk 𝔫 B b))
    have hab : ∀ j, algebraMap A B (a j) - b.1 j ∈ 𝔫 ^ j := fun j => by
      have := ha j
      rw [AdicCompletion.evalₐ_mk] at this
      exact Ideal.Quotient.eq.1 this
    let c : AdicCompletion.AdicCauchySequence 𝔪 A := AdicCompletion.AdicCauchySequence.mk 𝔪 A a (by
      intro n
      rw [SModEq.sub_mem]
      have : a n - a (n + 1) ∈ (𝔫 ^ n).comap (algebraMap A B) := by
        rw [Ideal.mem_comap, map_sub]
        have h1 := b.2 (Nat.le_succ n)
        rw [SModEq.sub_mem] at h1
        have h1' : b.1 n - b.1 (n + 1) ∈ 𝔫 ^ n := by simpa using h1
        have h2 := Ideal.pow_le_pow_right (Nat.le_succ n) (hab (n + 1))
        have := add_mem (add_mem (hab n) h1') (neg_mem h2)
        convert this using 1
        ring
      rw [h.ker n] at this
      simpa using this)
    refine ⟨AdicCompletion.mk 𝔪 A c, ?_⟩
    apply AdicCompletion.ext_evalₐ
    intro j
    rw [hG]
    simp only [F, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AdicCompletion.evalₐ_mk, hq]
    exact ha j
  exact ⟨LinearEquiv.ofBijective { toFun := G, map_add' := map_add G, map_smul' := Gmap } ⟨Ginj, Gsurj⟩⟩

/-- **EGA IV 17.6.3**, flatness: if `Â → B̂` is an isomorphism, then `B` is flat over `A`.
`Â → B̂ ≅ Â` flat over `A`, and `B → B̂` is faithfully flat. -/
theorem flat_of_truncationsBijective (h : TruncationsBijective A B) : Module.Flat A B := by
  obtain ⟨e⟩ := exists_completion_equiv h
  set C := AdicCompletion (maximalIdeal B) B
  have hAC : Module.Flat A C := Module.Flat.of_linearEquiv e.symm
  have hloc : IsLocalHom (algebraMap B C) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hc
    have hxm : x ∈ maximalIdeal B := (mem_maximalIdeal x).2 hc
    have h1 := hx.map (AdicCompletion.evalₐ (maximalIdeal B) 1)
    have h2 : AdicCompletion.evalₐ (maximalIdeal B) 1 (algebraMap B C x) = 0 := by
      have : AdicCompletion.evalₐ (maximalIdeal B) 1 (algebraMap B C x) =
          Ideal.Quotient.mk _ x := AlgHom.commutes _ x
      rw [this, Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact hxm
    rw [h2] at h1
    have : Nontrivial (B ⧸ maximalIdeal B ^ 1) := by
      rw [pow_one]; exact Ideal.Quotient.nontrivial_iff.2 (maximalIdeal.isMaximal B).ne_top
    exact not_isUnit_zero h1
  have hFF : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  have hC : Function.Injective (f.lTensor C) := Module.Flat.lTensor_preserves_injective_linearMap f hf
  let f' : B ⊗[A] N →ₗ[B] B ⊗[A] P := f.baseChange B
  have hf' : Function.Injective f' := by
    rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective B C f']
    let e1 := TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C N
    let e2 := TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C P
    have hcomm : ∀ x, e2 (f'.lTensor C x) = f.lTensor C (e1 x) := by
      intro x
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul c z =>
        induction z with
        | zero => simp
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
        | tmul b n => simp [f', e1, e2]
    intro x y hxy
    apply e1.injective
    apply hC
    rw [← hcomm, ← hcomm, hxy]
  exact hf'

lemma length_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  let := e.toRingHom.toAlgebra
  have h1 : Module.length R S = Module.length S S :=
    Module.length_eq_of_surjective (S := R) (R := S) e.surjective
  let l : R ≃ₗ[R] S := LinearEquiv.ofBijective (Algebra.linearMap R S) e.bijective
  rw [← h1]
  exact l.length_eq

/-- From cotangent surjectivity, residue surjectivity and `length A/𝔪^j ≤ length B/𝔫^j`, the
truncations are bijective. -/
theorem truncationsBijective_of_length
    (hcot : maximalIdeal B ≤ (maximalIdeal A).map (algebraMap A B) ⊔ maximalIdeal B ^ 2)
    (hres : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B)
    (hlen : ∀ j, Module.length (A ⧸ maximalIdeal A ^ j) (A ⧸ maximalIdeal A ^ j) ≤
      Module.length (B ⧸ maximalIdeal B ^ j) (B ⧸ maximalIdeal B ^ j)) :
    TruncationsBijective A B := by
  have hmap := map_maximalIdeal_eq_of_cotangent (A := A) hcot
  have hsurj : ∀ (j : ℕ) (b : B), ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B ^ j := by
    intro j
    induction j with
    | zero => intro b; exact ⟨0, by simp⟩
    | succ j ih =>
      intro b
      obtain ⟨a, ha⟩ := ih b
      have hj : maximalIdeal B ^ j = ((maximalIdeal A) ^ j).map (algebraMap A B) := by
        rw [Ideal.map_pow, hmap]
      rw [hj] at ha
      have key : ∀ y ∈ ((maximalIdeal A) ^ j).map (algebraMap A B),
          ∃ a' ∈ (maximalIdeal A) ^ j, y - algebraMap A B a' ∈ maximalIdeal B ^ (j + 1) := by
        intro y hy
        refine Submodule.span_induction ?_ ⟨0, zero_mem _, ?_⟩ ?_ ?_ hy
        · rintro _ ⟨x, hx, rfl⟩
          exact ⟨x, hx, by simp⟩
        · simp
        · rintro u v _ _ ⟨p, hp, hp'⟩ ⟨q, hq, hq'⟩
          refine ⟨p + q, add_mem hp hq, ?_⟩
          have := add_mem hp' hq'
          convert this using 1
          rw [map_add]; ring
        · rintro c u _ ⟨p, hp, hp'⟩
          obtain ⟨d, hd⟩ := hres c
          refine ⟨d * p, Ideal.mul_mem_left _ _ hp, ?_⟩
          have h1 : (c - algebraMap A B d) * algebraMap A B p ∈ maximalIdeal B ^ (j + 1) := by
            rw [pow_succ', ]
            refine Ideal.mul_mem_mul hd ?_
            have : (maximalIdeal A ^ j).map (algebraMap A B) ≤ maximalIdeal B ^ j := hj.ge
            exact this (Ideal.mem_map_of_mem _ hp)
          have h2 := Ideal.mul_mem_left _ c hp'
          have := add_mem h2 h1
          convert this using 1
          rw [map_mul, smul_eq_mul]; ring
      obtain ⟨a', _, ha'⟩ := key _ ha
      refine ⟨a + a', ?_⟩
      convert ha' using 1
      rw [map_add]; ring
  have hsurj' : ∀ j, Function.Surjective
      ((Ideal.Quotient.mk ((maximalIdeal B) ^ j)).comp (algebraMap A B)) := by
    intro j y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hsurj j b
    exact ⟨a, (Ideal.Quotient.eq.2 ha).symm⟩
  refine ⟨hsurj', fun j => ?_⟩
  have hle : maximalIdeal A ^ j ≤ (maximalIdeal B ^ j).comap (algebraMap A B) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, hmap]
  let q : A ⧸ maximalIdeal A ^ j →+* B ⧸ maximalIdeal B ^ j :=
    Ideal.quotientMap _ (algebraMap A B) hle
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨a, ha⟩ := hsurj' j y
    exact ⟨Ideal.Quotient.mk _ a, ha⟩
  have hinj := injective_of_surjective_of_length_le q hq
    (length_quotient_ne_top (maximalIdeal A) _ le_rfl) (hlen j)
  refine le_antisymm (fun a ha => ?_) hle
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hinj
  rw [map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.2 ha

/-- The étale step of §5 of the note, ring-theoretically. `A = 𝒪_{X,x}`, `B = 𝒪_{W,w}`, with
truncations of `A` given by `Ξ/(f)` and those of `B` by `Ξ/(f̃)`; the data agree modulo `𝔫²` (the
note's `N ≥ 1`), and `f̃ ≡ f`, `r̃ ≡ r` modulo `𝔫^(N+1)`, `N` above the Artin–Rees constants. Then
`Â → B̂` is an isomorphism. -/
theorem truncationsBijective_of_presentations {Ξ : Type*} [CommRing Ξ] [IsNoetherianRing Ξ]
    (𝔫' : Ideal Ξ) [𝔫'.IsMaximal] (I I' : Ideal Ξ)
    (hin : ∀ (n : ℕ) (v : Ξ), v ∈ I' → v ∈ 𝔫' ^ n → v ∈ (I ⊓ 𝔫' ^ n) ⊔ 𝔫' ^ (n + 1))
    (eA : ∀ j, (A ⧸ maximalIdeal A ^ j) ≃+* Ξ ⧸ (I ⊔ 𝔫' ^ j))
    (eB : ∀ j, (B ⧸ maximalIdeal B ^ j) ≃+* Ξ ⧸ (I' ⊔ 𝔫' ^ j))
    (hcompat : ∀ (a : A) (ξ : Ξ), eA 2 (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ξ →
      eB 2 (Ideal.Quotient.mk _ (algebraMap A B a)) = Ideal.Quotient.mk _ ξ) :
    TruncationsBijective A B := by
  have hmod2 : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B ^ 2 := by
    intro b
    obtain ⟨ξ, hξ⟩ := Ideal.Quotient.mk_surjective (eB 2 (Ideal.Quotient.mk _ b))
    obtain ⟨y, hy⟩ := (eA 2).surjective (Ideal.Quotient.mk _ ξ)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨a, ?_⟩
    have h1 := hcompat a ξ hy
    rw [hξ] at h1
    exact Ideal.Quotient.eq.1 ((eB 2).injective h1).symm
  refine truncationsBijective_of_length ?_ ?_ ?_
  · intro b hb
    obtain ⟨a, ha⟩ := hmod2 b
    have hla : algebraMap A B a ∈ maximalIdeal B := by
      have h2 : maximalIdeal B ^ 2 ≤ maximalIdeal B := Ideal.pow_le_self (by norm_num)
      have := sub_mem hb (h2 ha)
      rwa [sub_sub_cancel] at this
    have ham : a ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff] at hla ⊢
      exact fun hu => hla (hu.map _)
    have : b = algebraMap A B a + (b - algebraMap A B a) := by ring
    rw [this]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ ham) ha
  · intro b
    obtain ⟨a, ha⟩ := hmod2 b
    exact ⟨a, Ideal.pow_le_self (by norm_num) ha⟩
  · intro j
    have l1 : Module.length (A ⧸ maximalIdeal A ^ j) (A ⧸ maximalIdeal A ^ j) =
        Module.length (Ξ ⧸ (I ⊔ 𝔫' ^ j)) (Ξ ⧸ (I ⊔ 𝔫' ^ j)) := length_eq_of_ringEquiv (eA j)
    have l2 : Module.length (B ⧸ maximalIdeal B ^ j) (B ⧸ maximalIdeal B ^ j) =
        Module.length (Ξ ⧸ (I' ⊔ 𝔫' ^ j)) (Ξ ⧸ (I' ⊔ 𝔫' ^ j)) := length_eq_of_ringEquiv (eB j)
    rw [l1, l2, ← length_quotient_self, ← length_quotient_self]
    exact length_le_of_initial 𝔫' I I' hin j

end EGA

/-- **EGA IV 17.6.3**, in the form used at §5 of the note: if `R → S` is of finite presentation, `q`
lies over `p`, the localizations are noetherian and the map on truncations `R_p/𝔪^j → S_q/𝔫^j` is
bijective for all `j` (i.e. the completed local map is an isomorphism, which includes trivial
residue extension), then `S` is étale over `R` at `q`. -/
theorem isEtaleAt_of_truncationsBijective {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    [IsNoetherianRing (Localization.AtPrime p)] [IsNoetherianRing (Localization.AtPrime q)]
    [IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))]
    (h : TruncationsBijective (Localization.AtPrime p) (Localization.AtPrime q))
    (hmap : (maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
        maximalIdeal (Localization.AtPrime q)) :
    Algebra.IsEtaleAt R q := by
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    flat_of_truncationsBijective h
  have hsurj : Function.Surjective (algebraMap p.ResidueField q.ResidueField) := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := h.surj 1 (Ideal.Quotient.mk _ b)
    refine ⟨IsLocalRing.residue _ a, ?_⟩
    have h3 : IsLocalRing.residue (Localization.AtPrime q)
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q) a) =
        IsLocalRing.residue (Localization.AtPrime q) b := by
      have ha' := Ideal.Quotient.eq.1 ha
      rw [pow_one] at ha'
      exact Ideal.Quotient.eq.2 ha'
    rw [← h3]
    exact IsLocalRing.ResidueField.algebraMap_residue _
  have hbij : Function.Bijective (algebraMap p.ResidueField q.ResidueField) :=
    ⟨(algebraMap p.ResidueField q.ResidueField).injective, hsurj⟩
  let E : p.ResidueField ≃ₐ[p.ResidueField] q.ResidueField := AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
  have : Module.Finite p.ResidueField q.ResidueField := Module.Finite.equiv E.toLinearEquiv
  have : Algebra.IsSeparable p.ResidueField q.ResidueField :=
    Algebra.IsSeparable.of_algHom _ _ E.symm.toAlgHom
  refine Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal p q ?_
  rw [← hmap, ← Localization.AtPrime.map_eq_maximalIdeal (I := p), Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]
end AlgMag.ChartAlg

end PartP3

section PartP4
open MvPolynomial

namespace AlgMag.ChartAlg

section Gordan

variable {ι M : Type*} [Finite ι] [AddCommGroup M] (w : ι → M)

/-- Dickson: a set of exponents has a finite set of minimal elements below all its members. -/
lemma exists_finite_minimal (S : Set (ι →₀ ℕ)) :
    ∃ F : Finset (ι →₀ ℕ), (F : Set _) ⊆ S ∧ ∀ a ∈ S, ∃ b ∈ F, b ≤ a := by
  classical
  have hanti : IsAntichain (· ≤ ·) {a | Minimal (· ∈ S) a} := setOfPred_minimal_antichain _
  have hpwo : Set.IsPWO {a : ι →₀ ℕ | Minimal (· ∈ S) a} := Set.isPWO_of_wellQuasiOrderedLE _
  have hfin : Set.Finite {a | Minimal (· ∈ S) a} :=
    hanti.finite_of_partiallyWellOrderedOn hpwo
  refine ⟨hfin.toFinset, ?_, fun a ha => ?_⟩
  · intro b hb
    exact (hfin.mem_toFinset.1 hb).1
  · obtain ⟨b, hba, hb⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ S) a ha
    exact ⟨b, hfin.mem_toFinset.2 hb, hba⟩

variable (R : Type*) [CommRing R]

/-- `P₀`, the degree zero subalgebra of the `M`-graded polynomial ring. -/
def P0 : Subalgebra R (MvPolynomial ι R) where
  carrier := {p | IsWeightedHomogeneous w p 0}
  mul_mem' {a b} ha hb := by simpa using ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' r := by
    simpa [algebraMap_eq] using isWeightedHomogeneous_C w r

lemma mem_P0 {p : MvPolynomial ι R} : p ∈ P0 w R ↔ IsWeightedHomogeneous w p 0 := Iff.rfl

/-- `P_d`, as a `P₀`-submodule. -/
def Pd (d : M) : Submodule (P0 w R) (MvPolynomial ι R) where
  carrier := {p | IsWeightedHomogeneous w p d}
  add_mem' ha hb := ha.add hb
  zero_mem' := isWeightedHomogeneous_zero _ _ _
  smul_mem' c p hp := by
    have := c.2.mul hp
    rw [zero_add] at this
    exact this

lemma mem_Pd {d : M} {p : MvPolynomial ι R} : p ∈ Pd w R d ↔ IsWeightedHomogeneous w p d := Iff.rfl

/-- **Lemma 3.1** (Gordan/Dickson) of the note, polynomial case: `P_d` is finite over `P₀`. -/
theorem Pd_fg (d : M) : (Pd w R d).FG := by
  classical
  obtain ⟨F, hFS, hF⟩ := exists_finite_minimal {a : ι →₀ ℕ | Finsupp.weight w a = d}
  refine ⟨F.image fun b => monomial b (1 : R), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro p hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    exact isWeightedHomogeneous_monomial w b 1 (hFS hb)
  · intro p hp
    rw [p.as_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have hwa : Finsupp.weight w a = d := hp (mem_support_iff.1 ha)
    obtain ⟨b, hb, hba⟩ := hF a hwa
    have hb' : Finsupp.weight w b = d := hFS hb
    have hzero : Finsupp.weight w (a - b) = 0 := by
      have : a = b + (a - b) := (add_tsub_cancel_of_le hba).symm
      have h2 := congrArg (Finsupp.weight w) this
      rw [map_add, hwa, hb'] at h2
      simpa using h2.symm
    let c : P0 w R := ⟨monomial (a - b) (coeff a p), isWeightedHomogeneous_monomial w _ _ hzero⟩
    have : monomial a (coeff a p) = c • monomial b (1 : R) := by
      change _ = monomial (a - b) (coeff a p) * monomial b 1
      rw [monomial_mul_monomial, mul_one, tsub_add_cancel_of_le hba]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb)))

/-- **Lemma 3.1** of the note, polynomial case: `P₀` is of finite type. -/
theorem P0_finiteType : Algebra.FiniteType R (P0 w R) := by
  classical
  have := Fintype.ofFinite ι
  rw [← Subalgebra.fg_iff_finiteType]
  obtain ⟨F, hFS, hF⟩ := exists_finite_minimal
    {a : ι →₀ ℕ | Finsupp.weight w a = 0 ∧ a ≠ 0}
  refine ⟨F.image fun b => monomial b (1 : R), le_antisymm ?_ ?_⟩
  · rw [Algebra.adjoin_le_iff]
    intro p hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    exact isWeightedHomogeneous_monomial w b 1 (hFS hb).1
  · set S := Algebra.adjoin R ((F.image fun b => monomial b (1 : R) : Finset _) : Set (MvPolynomial ι R))
    have hmon : ∀ (n : ℕ) (a : ι →₀ ℕ), (a.sum fun _ e => e) = n → Finsupp.weight w a = 0 →
        monomial a (1 : R) ∈ S := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro a hn hwa
        by_cases ha0 : a = 0
        · subst ha0
          simp
        obtain ⟨b, hb, hba⟩ := hF a ⟨hwa, ha0⟩
        have hb' := hFS hb
        have hzero : Finsupp.weight w (a - b) = 0 := by
          have : a = b + (a - b) := (add_tsub_cancel_of_le hba).symm
          have h2 := congrArg (Finsupp.weight w) this
          rw [map_add, hwa, hb'.1] at h2
          simpa using h2.symm
        have hdeg : ((a - b).sum fun _ e => e) < n := by
          have hab : a = b + (a - b) := (add_tsub_cancel_of_le hba).symm
          have hbpos : 0 < (b.sum fun _ e => e) := by
            obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hb'.2
            refine lt_of_lt_of_le (Nat.pos_of_ne_zero (by simpa using hi)) ?_
            exact Finset.single_le_sum (f := fun j => b j) (fun _ _ => Nat.zero_le _)
              (Finsupp.mem_support_iff.2 (by simpa using hi))
          have hsum : (a.sum fun _ e => e) = (b.sum fun _ e => e) + ((a - b).sum fun _ e => e) := by
            conv_lhs => rw [hab]
            exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
          omega
        have h1 := ih _ hdeg (a - b) rfl hzero
        have h2 : monomial b (1 : R) ∈ S :=
          Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))
        have h3 := S.mul_mem h2 h1
        rwa [monomial_mul_monomial, mul_one, add_tsub_cancel_of_le hba] at h3
    intro p hp
    rw [p.as_sum]
    refine S.sum_mem fun a ha => ?_
    have hwa : Finsupp.weight w a = 0 := hp (mem_support_iff.1 ha)
    have := S.smul_mem (hmon _ a rfl hwa) (coeff a p)
    rwa [smul_monomial, smul_eq_mul, mul_one] at this

end Gordan
end AlgMag.ChartAlg

end PartP4

section PartP5
open DirectSum

namespace AlgMag.ChartAlg

section Shrink

variable {A M σ : Type*} [CommRing A] [AddCommGroup M] [DecidableEq M]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : M → σ) [GradedRing 𝒜]

/-- `V(I)` is `D(M)`-stable, in coefficients: for `g ∈ I`, the coaction `Σ g_d e^d` of `g` is
nilpotent modulo `I · A[M]`, i.e. all homogeneous components of some power of `g` lie in `I`.
This is the first sentence of the proof of the Shrinking Lemma of the note. -/
def IsStableClosed (I : Ideal A) : Prop :=
  ∀ g ∈ I, ∃ e : ℕ, ∀ d, ((decompose 𝒜 (g ^ e) d : 𝒜 d) : A) ∈ I

/-- **Shrinking Lemma** (§6 of the note): `Y = Spec A` with `D(M)`-action, `V(I)` a stable closed,
`O = V(I_O)` closed stable disjoint from `V(I)`. Then there is `h ∈ A₀` with `O ⊆ D(h)` (indeed
`1 - h ∈ I_O`) and `D(h) ∩ V(I) = ∅` (indeed `h ∈ I`). -/
theorem shrinking {I IO : Ideal A} (hI : IsStableClosed 𝒜 I) (hO : IO.IsHomogeneous 𝒜)
    (hdisj : IO ⊔ I = ⊤) : ∃ h ∈ 𝒜 0, h ∈ I ∧ 1 - h ∈ IO := by
  classical
  choose! e he using hI
  let gens : Set A := {x | ∃ g ∈ I, ∃ d, x = ((decompose 𝒜 (g ^ e g) d : 𝒜 d) : A)}
  let J : Ideal A := Ideal.span gens
  have hJI : J ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨g, hg, d, rfl⟩
    exact he g hg d
  have hJhom : J.IsHomogeneous 𝒜 := by
    refine Ideal.homogeneous_span 𝒜 gens ?_
    rintro _ ⟨g, hg, d, rfl⟩
    exact ⟨d, SetLike.coe_mem _⟩
  have hrad : I ≤ J.radical := by
    intro g hg
    refine ⟨e g, ?_⟩
    rw [← DirectSum.sum_support_decompose 𝒜 (g ^ e g)]
    exact Ideal.sum_mem _ fun d _ => Ideal.subset_span ⟨g, hg, d, rfl⟩
  have htop : IO ⊔ J = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : J ≤ P := le_sup_right.trans hle
    have h2 : I ≤ P := hrad.trans (hP.isPrime.radical_le_iff.2 h1)
    have h3 : IO ≤ P := le_sup_left.trans hle
    exact hP.ne_top (top_le_iff.1 (hdisj ▸ sup_le h3 h2))
  obtain ⟨u, hu, j, hj, huj⟩ := Submodule.mem_sup.1 (show (1 : A) ∈ IO ⊔ J by rw [htop]; trivial)
  have h0 := congrArg (fun x => ((decompose 𝒜 x 0 : 𝒜 0) : A)) huj
  simp only [decompose_add, DirectSum.add_apply, AddMemClass.coe_add] at h0
  have hone : ((decompose 𝒜 (1 : A) 0 : 𝒜 0) : A) = 1 :=
    DirectSum.decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem
  rw [hone] at h0
  refine ⟨_, SetLike.coe_mem (decompose 𝒜 j 0), hJI (hJhom 0 hj), ?_⟩
  rw [← h0, add_sub_cancel_right]
  exact hO 0 hu

/-- **§6, conclusion**, ring form. Let `Ω = D(I)` be a `D(M)`-stable open of `Spec A` contained in
the étale locus over `R`, containing the closed stable `O = V(I_O)`. Then there is `h ∈ A₀` with
`O ⊆ D(h)` and `A_h` étale over `R`; `U := Spec A_h` is the affine chart. -/
theorem etale_chart {R : Type*} [CommRing R] [Algebra R A] [Algebra.FinitePresentation R A]
    {I IO : Ideal A} (hI : IsStableClosed 𝒜 I) (hO : IO.IsHomogeneous 𝒜) (hdisj : IO ⊔ I = ⊤)
    (hΩ : (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ⊆ Algebra.etaleLocus R A) :
    ∃ h ∈ 𝒜 0, 1 - h ∈ IO ∧ Algebra.Etale R (Localization.Away h) := by
  obtain ⟨h, h0, hmem, h1⟩ := shrinking 𝒜 hI hO hdisj
  refine ⟨h, h0, h1, ?_⟩
  refine (Algebra.basicOpen_subset_etaleLocus_iff_etale).1 (Set.Subset.trans ?_ hΩ)
  intro p hp hz
  exact hp (hz hmem)

end Shrink
end AlgMag.ChartAlg

end PartP5

section PartP6
open DirectSum MvPolynomial TensorProduct

namespace AlgMag.ChartAlg

section Coordinates

variable {C M : Type*} [CommRing C] [AddCommGroup M] [DecidableEq M]
  (𝒞 : M → AddSubgroup C) [GradedRing 𝒞] (m : Ideal C)

/-- A **complete pair** (Conventions of the note): `C_d → lim (C/m^n)_d` is bijective for all `d`,
in sequence form. Noetherianity is assumed separately where it is used. -/
structure CompletePair : Prop where
  hom : m.IsHomogeneous 𝒞
  sep : ∀ d, ∀ c ∈ 𝒞 d, (∀ n, c ∈ m ^ n) → c = 0
  lim : ∀ d (c : ℕ → C), (∀ n, c n ∈ 𝒞 d) → (∀ n, c (n + 1) - c n ∈ m ^ n) →
    ∃ l ∈ 𝒞 d, ∀ n, l - c n ∈ m ^ n

variable {𝒞 m}

/-- **Coordinates** (§5 of the note): if `C/m` is generated as a ring by the images of finitely many
homogeneous elements `T` (for `C/m = k[Z₀]`: lifts of a generator of `k`, of generators of `Z₀` and
their inverses), and `C` is noetherian, there are finitely many homogeneous `x_i ∈ C` such that
`ℤ[x_i] → C/m^k` is onto for all `k`. -/
theorem graded_coordinates [IsNoetherianRing C] (hm : m.IsHomogeneous 𝒞) (T : Finset C)
    (hT : ∀ t ∈ T, ∃ d, t ∈ 𝒞 d)
    (hgen : ∀ c : C, ∃ p ∈ Algebra.adjoin ℤ (T : Set C), c - p ∈ m) :
    ∃ (n : ℕ) (x : Fin n → C) (w : Fin n → M), (∀ i, x i ∈ 𝒞 (w i)) ∧
      ∀ (c : C) (k : ℕ), ∃ p : MvPolynomial (Fin n) ℤ, c - aeval x p ∈ m ^ k := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian m : m.FG)
  -- homogeneous generators of `m`
  let S : Finset C := s.biUnion fun g => (decompose 𝒞 g).support.image fun d => (decompose 𝒞 g d : C)
  have hSm : (S : Set C) ⊆ m := by
    intro y hy
    obtain ⟨g, hg, hy⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hy)
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.1 hy
    exact hm d (by rw [← hs]; exact Ideal.subset_span hg)
  have hSspan : m ≤ Ideal.span (S : Set C) := by
    rw [← hs, Ideal.span_le]
    intro g hg
    rw [← DirectSum.sum_support_decompose 𝒞 g]
    exact Ideal.sum_mem _ fun d hd => Ideal.subset_span
      (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_image_of_mem _ hd⟩))
  have hShom : ∀ y ∈ S, ∃ d, y ∈ 𝒞 d := by
    intro y hy
    obtain ⟨g, hg, hy⟩ := Finset.mem_biUnion.1 hy
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨d, SetLike.coe_mem _⟩
  let X : Finset C := T ∪ S
  have hX : ∀ y ∈ X, ∃ d, y ∈ 𝒞 d := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · exact hT y h
    · exact hShom y h
  let e := X.equivFin
  let x : Fin X.card → C := fun i => (e.symm i : C)
  have hxmem : ∀ y (hy : y ∈ X), x (e ⟨y, hy⟩) = y := fun y hy => by simp [x]
  choose! dg hdg using hX
  refine ⟨X.card, x, fun i => dg (x i), fun i => hdg _ (e.symm i).2, ?_⟩
  set φ : MvPolynomial (Fin X.card) ℤ →ₐ[ℤ] C := aeval x with hφ
  have hrange : ∀ y ∈ X, ∃ p, φ p = y := fun y hy => ⟨MvPolynomial.X (e ⟨y, hy⟩), by
    simp [hφ, hxmem]⟩
  have hadj : ∀ y ∈ Algebra.adjoin ℤ (T : Set C), ∃ p, φ p = y := by
    intro y hy
    have : Algebra.adjoin ℤ (T : Set C) ≤ φ.range := by
      rw [Algebra.adjoin_le_iff]
      intro t ht
      obtain ⟨p, hp⟩ := hrange t (Finset.mem_union_left _ (Finset.mem_coe.1 ht))
      exact ⟨p, hp⟩
    obtain ⟨p, hp⟩ := this hy
    exact ⟨p, hp⟩
  -- one step
  have step : ∀ k, ∀ y ∈ m ^ k, ∃ p, y - φ p ∈ m ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro y _
      obtain ⟨q, hq, hyq⟩ := hgen y
      obtain ⟨p, rfl⟩ := hadj q hq
      exact ⟨p, by simpa using hyq⟩
    | succ k ih =>
      intro y hy
      rw [pow_succ] at hy
      have key : ∀ b ∈ Ideal.span (S : Set C), ∀ a ∈ m ^ k, ∃ p, a * b - φ p ∈ m ^ (k + 1 + 1) := by
        intro b hb
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
        · intro s' hs' a ha
          obtain ⟨p, hp⟩ := ih a ha
          obtain ⟨q, hq⟩ := hrange s' (Finset.mem_union_right _ (Finset.mem_coe.1 hs'))
          refine ⟨p * q, ?_⟩
          rw [map_mul, hq, ← sub_mul, pow_succ _ (k + 1)]
          exact Ideal.mul_mem_mul hp (hSm hs')
        · intro a _
          exact ⟨0, by simp⟩
        · intro u v _ _ hu hv a ha
          obtain ⟨p, hp⟩ := hu a ha
          obtain ⟨q, hq⟩ := hv a ha
          refine ⟨p + q, ?_⟩
          have := add_mem hp hq
          convert this using 1
          rw [map_add]; ring
        · intro r u _ hu a ha
          obtain ⟨p, hp⟩ := hu (a * r) (Ideal.mul_mem_right _ _ ha)
          refine ⟨p, ?_⟩
          convert hp using 2
          rw [smul_eq_mul]; ring
      have hle : (m ^ k * m : Ideal C) ≤ m ^ k * Ideal.span (S : Set C) :=
        Ideal.mul_mono_right hSspan
      refine Submodule.mul_induction_on (hle hy) (fun a ha b hb => key b hb a ha) ?_
      rintro u v ⟨p, hp⟩ ⟨q, hq⟩
      refine ⟨p + q, ?_⟩
      have := add_mem hp hq
      convert this using 1
      rw [map_add]; ring
  intro c k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := step k _ hp
    refine ⟨p + q, ?_⟩
    convert hq using 1
    rw [map_add]; ring

end Coordinates
end AlgMag.ChartAlg

end PartP6

section PartP7
open DirectSum MvPolynomial TensorProduct


namespace AlgMag.ChartAlg

section Surj

variable {C M ι : Type*} [CommRing C] [AddCommGroup M] [DecidableEq M] [Finite ι]
  {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {m : Ideal C}
  {w : ι → M} {x : ι → C}

lemma isHomogeneous_pow {I : Ideal C} (h : I.IsHomogeneous 𝒞) (n : ℕ) :
    (I ^ n).IsHomogeneous 𝒞 := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact fun _ _ _ => trivial
  | succ n ih => rw [pow_succ]; exact ih.mul h

/-- The map `P → C` is graded. -/
lemma aeval_mem_of_homog (hx : ∀ i, x i ∈ 𝒞 (w i)) {d : M} {p : MvPolynomial ι ℤ}
    (hp : IsWeightedHomogeneous w p d) : aeval x p ∈ 𝒞 d := by
  classical
  have := Fintype.ofFinite ι
  rw [p.as_sum, map_sum]
  refine sum_mem fun a ha => ?_
  have hwa : Finsupp.weight w a = d := hp (mem_support_iff.1 ha)
  rw [aeval_monomial]
  have h1 : (a.prod fun i e => x i ^ e) ∈ 𝒞 d := by
    have h2 := SetLike.prod_pow_mem_graded 𝒞 w x a (F := a.support) (fun i _ => hx i)
    rw [← hwa, Finsupp.weight_apply]
    simpa [Finsupp.prod, Finsupp.sum] using h2
  have h3 : algebraMap ℤ C (coeff a p) * (a.prod fun i e => x i ^ e) =
      (coeff a p) • (a.prod fun i e => x i ^ e) := by simp [zsmul_eq_mul]
  rw [h3]
  exact zsmul_mem h1 _

/-- The ring map `P₀ → C`. -/
noncomputable def phi0 (w : ι → M) (x : ι → C) : P0 w ℤ →+* C :=
  (aeval x : MvPolynomial ι ℤ →ₐ[ℤ] C).toRingHom.comp (P0 w ℤ).val.toRingHom

/-- `𝔭₀ = ker(P₀ → C₀/m₀)`. -/
noncomputable def p0 (w : ι → M) (x : ι → C) (m : Ideal C) : Ideal (P0 w ℤ) := m.comap (phi0 w x)

/-- `P̂₀`. -/
abbrev P0hat (w : ι → M) (x : ι → C) (m : Ideal C) : Type _ := AdicCompletion (p0 w x m) (P0 w ℤ)

lemma phi0_mem (hx : ∀ i, x i ∈ 𝒞 (w i)) (a : P0 w ℤ) : phi0 w x a ∈ 𝒞 0 :=
  aeval_mem_of_homog hx a.2

lemma phi0_pow_mem {a : P0 w ℤ} {n : ℕ} (ha : a ∈ p0 w x m ^ n) : phi0 w x a ∈ m ^ n := by
  have : (p0 w x m ^ n).map (phi0 w x) ≤ m ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono Ideal.map_comap_le n
  exact this (Ideal.mem_map_of_mem _ ha)

/-- `c` is the limit in `C₀` of `y ∈ P̂₀`. -/
def IsLimOf (x' : ι → C) (w' : ι → M) (𝒞' : M → AddSubgroup C) (m' : Ideal C)
    (y : P0hat w' x' m') (c : C) : Prop :=
  c ∈ 𝒞' 0 ∧ ∀ (n : ℕ) (b : P0 w' ℤ),
    AdicCompletion.evalₐ (p0 w' x' m') n y = Ideal.Quotient.mk _ b → c - phi0 w' x' b ∈ m' ^ n

lemma IsLimOf.unique (hC : CompletePair 𝒞 m) {y : P0hat w x m} {c c' : C}
    (h : IsLimOf x w 𝒞 m y c) (h' : IsLimOf x w 𝒞 m y c') : c = c' := by
  refine sub_eq_zero.1 (hC.sep 0 _ (sub_mem h.1 h'.1) fun n => ?_)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (p0 w x m) n y)
  have := sub_mem (h.2 n b hb.symm) (h'.2 n b hb.symm)
  simpa using this

lemma exists_isLimOf (hx : ∀ i, x i ∈ 𝒞 (w i)) (hC : CompletePair 𝒞 m) (y : P0hat w x m) :
    ∃ c, IsLimOf x w 𝒞 m y c := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective (p0 w x m) (P0 w ℤ) y
  have hcau : ∀ {k l : ℕ}, k ≤ l → a.1 k - a.1 l ∈ p0 w x m ^ k := fun {k l} h => by
    have := a.2 h
    rw [SModEq.sub_mem] at this
    simpa using this
  obtain ⟨l, hl, hl'⟩ := hC.lim 0 (fun n => phi0 w x (a.1 n)) (fun n => phi0_mem hx _) (fun n => by
    have := phi0_pow_mem (neg_mem (hcau (Nat.le_succ n)))
    rw [neg_sub, map_sub] at this
    exact this)
  refine ⟨l, hl, fun n b hb => ?_⟩
  rw [AdicCompletion.evalₐ_mk] at hb
  have h1 : a.1 n - b ∈ p0 w x m ^ n := Ideal.Quotient.eq.1 hb
  have h2 := add_mem (hl' n) (phi0_pow_mem h1)
  rw [map_sub] at h2
  convert h2 using 1
  ring

variable (hx : ∀ i, x i ∈ 𝒞 (w i)) (hC : CompletePair 𝒞 m)

include hx hC in
/-- The ring map `P̂₀ → C₀ ⊂ C`, the continuous extension of `P₀ → C₀`. -/
noncomputable def phiHat : P0hat w x m →+* C where
  toFun y := Classical.choose (exists_isLimOf hx hC y)
  map_one' := by
    refine IsLimOf.unique hC (Classical.choose_spec (exists_isLimOf hx hC _)) ⟨SetLike.GradedOne.one_mem, ?_⟩
    intro n b hb
    have h1 : (1 : P0 w ℤ) - b ∈ p0 w x m ^ n := by
      refine Ideal.Quotient.eq.1 ?_
      rw [← hb, map_one, map_one]
    have := phi0_pow_mem h1
    simpa using this
  map_zero' := by
    refine IsLimOf.unique hC (Classical.choose_spec (exists_isLimOf hx hC _)) ⟨zero_mem _, ?_⟩
    intro n b hb
    have h1 : (0 : P0 w ℤ) - b ∈ p0 w x m ^ n := by
      refine Ideal.Quotient.eq.1 ?_
      rw [← hb, map_zero, map_zero]
    have := phi0_pow_mem h1
    simpa using this
  map_add' y z := by
    have hy := Classical.choose_spec (exists_isLimOf hx hC y)
    have hz := Classical.choose_spec (exists_isLimOf hx hC z)
    refine IsLimOf.unique hC (Classical.choose_spec (exists_isLimOf hx hC _)) ⟨add_mem hy.1 hz.1, ?_⟩
    intro n b hb
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (p0 w x m) n y)
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (p0 w x m) n z)
    have h1 : (u + v) - b ∈ p0 w x m ^ n := by
      refine Ideal.Quotient.eq.1 ?_
      rw [← hb, map_add, map_add, hu, hv]
    have h2 := add_mem (add_mem (hy.2 n u hu.symm) (hz.2 n v hv.symm)) (phi0_pow_mem h1)
    convert h2 using 1
    simp only [map_sub, map_add]; ring
  map_mul' y z := by
    have hy := Classical.choose_spec (exists_isLimOf hx hC y)
    have hz := Classical.choose_spec (exists_isLimOf hx hC z)
    refine IsLimOf.unique hC (Classical.choose_spec (exists_isLimOf hx hC _))
      ⟨by simpa using SetLike.GradedMul.mul_mem hy.1 hz.1, ?_⟩
    intro n b hb
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (p0 w x m) n y)
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (p0 w x m) n z)
    have h1 : (u * v) - b ∈ p0 w x m ^ n := by
      refine Ideal.Quotient.eq.1 ?_
      rw [← hb, map_mul, map_mul, hu, hv]
    have h2 := add_mem (add_mem (Ideal.mul_mem_right (Classical.choose (exists_isLimOf hx hC z)) _ (hy.2 n u hu.symm))
      (Ideal.mul_mem_left _ (phi0 w x u) (hz.2 n v hv.symm))) (phi0_pow_mem h1)
    convert h2 using 1
    simp only [map_sub, map_mul]; ring

lemma phiHat_isLim (y : P0hat w x m) : IsLimOf x w 𝒞 m y (phiHat hx hC y) :=
  Classical.choose_spec (exists_isLimOf hx hC y)

lemma phiHat_algebraMap (a : P0 w ℤ) :
    phiHat hx hC (algebraMap _ _ a) = phi0 w x a := by
  refine IsLimOf.unique hC (phiHat_isLim hx hC _) ⟨phi0_mem hx a, fun n b hb => ?_⟩
  have h1 : a - b ∈ p0 w x m ^ n := by
    refine Ideal.Quotient.eq.1 ?_
    rw [← hb]
    exact (AlgHom.commutes (AdicCompletion.evalₐ (p0 w x m) n) a).symm
  have := phi0_pow_mem h1
  rwa [map_sub] at this

include hx in
lemma proj_aeval (d : M) (p : MvPolynomial ι ℤ) :
    ((decompose 𝒞 (aeval x p) d : 𝒞 d) : C) = aeval x (weightedHomogeneousComponent w d p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    have hm : IsWeightedHomogeneous w (monomial a c) (Finsupp.weight w a) :=
      isWeightedHomogeneous_monomial w a c rfl
    have hmem := aeval_mem_of_homog hx hm
    by_cases h : Finsupp.weight w a = d
    · subst h
      rw [hm.weightedHomogeneousComponent_same]
      exact DirectSum.decompose_of_mem_same 𝒞 hmem
    · rw [hm.weightedHomogeneousComponent_ne d (Ne.symm h), map_zero]
      exact DirectSum.decompose_of_mem_ne 𝒞 hmem h
  | add p q hp hq =>
    rw [map_add, decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hp, hq, map_add,
      map_add]

/-- `Q := P ⊗_{P₀} P̂₀` of §5 of the note. -/
abbrev Qring (w : ι → M) (x : ι → C) (m : Ideal C) : Type _ :=
  MvPolynomial ι ℤ ⊗[P0 w ℤ] P0hat w x m

/-- The ring map `Q → C` of §5 of the note. -/
noncomputable def Qmap : Qring w x m →+* C :=
  letI : Algebra (P0 w ℤ) C := (phi0 w x).toAlgebra
  let f : MvPolynomial ι ℤ →ₐ[P0 w ℤ] C :=
    { (aeval x : MvPolynomial ι ℤ →ₐ[ℤ] C).toRingHom with commutes' := fun _ => rfl }
  let g : P0hat w x m →ₐ[P0 w ℤ] C :=
    { phiHat hx hC with commutes' := fun a => phiHat_algebraMap hx hC a }
  (Algebra.TensorProduct.productMap f g).toRingHom

@[simp] lemma Qmap_tmul (p : MvPolynomial ι ℤ) (y : P0hat w x m) :
    Qmap hx hC (p ⊗ₜ y) = aeval x p * phiHat hx hC y := by
  let : Algebra (P0 w ℤ) C := (phi0 w x).toAlgebra
  simp [Qmap, Algebra.TensorProduct.productMap_apply_tmul]

/-- **`Q → C` is surjective** (§5 of the note). The note's compactness argument is carried out with
König's lemma for the finite sets `P₀/𝔭₀ⁿ`-points, which is where `k` finite is used. -/
theorem Qmap_surjective (happ : ∀ (c : C) (k : ℕ), ∃ p : MvPolynomial ι ℤ, c - aeval x p ∈ m ^ k)
    [Finite (P0 w ℤ ⧸ p0 w x m)] : Function.Surjective (Qmap hx hC) := by
  classical
  have hnoeth : IsNoetherianRing (P0 w ℤ) := by
    have := P0_finiteType w ℤ
    exact Algebra.FiniteType.isNoetherianRing ℤ _
  have hfinq : ∀ n, Finite (P0 w ℤ ⧸ p0 w x m ^ n) := fun n =>
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  have homog : ∀ d, ∀ c ∈ 𝒞 d, c ∈ (Qmap hx hC).range := by
    intro d c hc
    obtain ⟨s, hs⟩ := Pd_fg w ℤ d
    -- the finite sets
    let X : ℕ → Type _ := fun n => {ā : s → P0 w ℤ ⧸ p0 w x m ^ n // ∃ a : s → P0 w ℤ,
      (∀ i, Ideal.Quotient.mk _ (a i) = ā i) ∧
        c - ∑ i : s, phi0 w x (a i) * aeval x (i : MvPolynomial ι ℤ) ∈ m ^ n}
    have hXfin : ∀ n, Finite (X n) := fun n => by
      have := hfinq n; exact Subtype.finite
    have hXne : ∀ n, Nonempty (X n) := by
      intro n
      obtain ⟨p, hp⟩ := happ c n
      let pd := weightedHomogeneousComponent w d p
      have hpd : pd ∈ Pd w ℤ d := weightedHomogeneousComponent_isWeightedHomogeneous d p
      have hcpd : c - aeval x pd ∈ m ^ n := by
        have h2 : ((decompose 𝒞 (c - aeval x p) d : 𝒞 d) : C) = c - aeval x pd := by
          rw [decompose_sub, DirectSum.sub_apply, AddSubgroupClass.coe_sub,
            DirectSum.decompose_of_mem_same 𝒞 hc]
          congr 1
          exact proj_aeval hx d p
        rw [← h2]
        exact (isHomogeneous_pow hC.hom n) d hp
      rw [← hs] at hpd
      obtain ⟨f, hf⟩ := Submodule.mem_span_finset'.1 hpd
      refine ⟨⟨fun i => Ideal.Quotient.mk _ (f i), f, fun _ => rfl, ?_⟩⟩
      rw [← hf, map_sum] at hcpd
      convert hcpd using 3 with i
      simp [phi0, Subalgebra.smul_def]
    let π : ∀ n, X (n + 1) → X n := fun n ā => ⟨fun i =>
      Ideal.Quotient.factorPow (p0 w x m) (Nat.le_succ n) (ā.1 i), by
        obtain ⟨a, ha, hc'⟩ := ā.2
        refine ⟨a, fun i => ?_, Ideal.pow_le_pow_right (Nat.le_succ n) hc'⟩
        show Ideal.Quotient.mk _ (a i) = Ideal.Quotient.factorPow _ _ (ā.1 i)
        rw [← ha i]; rfl⟩
    obtain ⟨σ, hσ⟩ := exists_section_of_finite π
    choose a ha hca using fun n => (σ n).2
    have hau : ∀ n i, a n i - a (n + 1) i ∈ p0 w x m ^ n := by
      intro n i
      refine Ideal.Quotient.eq.1 ?_
      rw [ha n i, ← hσ n]
      show _ = Ideal.Quotient.mk _ (a (n + 1) i)
      change Ideal.Quotient.factorPow (p0 w x m) (Nat.le_succ n) ((σ (n + 1)).1 i) = _
      rw [← ha (n + 1) i]; rfl
    let y : s → P0hat w x m := fun i => AdicCompletion.mk _ _
      (AdicCompletion.AdicCauchySequence.mk _ _ (fun n => a n i) (fun n => by
        rw [SModEq.sub_mem]; simpa using hau n i))
    have hy : ∀ n i, phiHat hx hC (y i) - phi0 w x (a n i) ∈ m ^ n := fun n i =>
      (phiHat_isLim hx hC (y i)).2 n _ (by simp [y, AdicCompletion.evalₐ_mk])
    let q : Qring w x m := ∑ i : s, (i : MvPolynomial ι ℤ) ⊗ₜ y i
    refine ⟨q, ?_⟩
    have hq : Qmap hx hC q = ∑ i : s, aeval x (i : MvPolynomial ι ℤ) * phiHat hx hC (y i) := by
      have : Qmap hx hC q = (Qmap hx hC).toAddMonoidHom q := rfl
      rw [this, map_sum]
      exact Finset.sum_congr rfl fun i _ => Qmap_tmul hx hC _ _
    have hmem : ∀ i : s, aeval x (i : MvPolynomial ι ℤ) ∈ 𝒞 d := fun i => by
      have : (i : MvPolynomial ι ℤ) ∈ Pd w ℤ d := by
        rw [← hs]; exact Submodule.subset_span i.2
      exact aeval_mem_of_homog hx this
    refine sub_eq_zero.1 (hC.sep d _ (sub_mem ?_ hc) fun n => ?_)
    · rw [hq]
      refine sum_mem fun i _ => ?_
      simpa using SetLike.GradedMul.mul_mem (hmem i) (phiHat_isLim hx hC (y i)).1
    · rw [hq]
      have h1 := hca n
      have h2 : ∑ i : s, aeval x (i : MvPolynomial ι ℤ) * (phiHat hx hC (y i) - phi0 w x (a n i)) ∈ m ^ n :=
        Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hy n i)
      have := sub_mem h2 h1
      convert this using 1
      simp only [mul_sub, Finset.sum_sub_distrib]
      have : ∑ i : s, aeval x (i : MvPolynomial ι ℤ) * phi0 w x (a n i) =
          ∑ i : s, phi0 w x (a n i) * aeval x (i : MvPolynomial ι ℤ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [this]; ring
  intro c
  rw [← DirectSum.sum_support_decompose 𝒞 c]
  exact sum_mem fun d _ => homog d _ (SetLike.coe_mem _)

end Surj
end AlgMag.ChartAlg

end PartP7

section PartP8
open DirectSum MvPolynomial TensorProduct


namespace AlgMag.ChartAlg

section Kernel

variable {C M ι : Type*} [CommRing C] [AddCommGroup M] [DecidableEq M] [Finite ι]
  {𝒞 : M → AddSubgroup C} [GradedRing 𝒞] {m : Ideal C}
  {w : ι → M} {x : ι → C}

lemma decompose_mul_zero {u c : C} (hc : c ∈ 𝒞 0) (d : M) :
    ((decompose 𝒞 (u * c) d : 𝒞 d) : C) = (decompose 𝒞 u d : 𝒞 d) * c := by
  classical
  induction u using DirectSum.Decomposition.inductionOn 𝒞 with
  | zero => simp
  | @homogeneous e u =>
    have h : (u : C) * c ∈ 𝒞 e := by simpa using SetLike.GradedMul.mul_mem u.2 hc
    by_cases hd : e = d
    · subst hd
      rw [DirectSum.decompose_of_mem_same 𝒞 h, DirectSum.decompose_of_mem_same 𝒞 u.2]
    · rw [DirectSum.decompose_of_mem_ne 𝒞 h hd, DirectSum.decompose_of_mem_ne 𝒞 u.2 hd, zero_mul]
  | add u v hu hv =>
    rw [add_mul, decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hu, hv, decompose_add,
      DirectSum.add_apply, AddMemClass.coe_add, add_mul]

/-- The projection `P → P_d` is `P₀`-linear. -/
noncomputable def piP (w : ι → M) (d : M) : MvPolynomial ι ℤ →ₗ[P0 w ℤ] MvPolynomial ι ℤ where
  toFun := weightedHomogeneousComponent w d
  map_add' := map_add _
  map_smul' a p := by
    classical
    ext b
    simp only [RingHom.id_apply, Subalgebra.smul_def, smul_eq_mul]
    rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
    have term : ∀ uv ∈ Finset.antidiagonal b, (if Finsupp.weight w b = d then
        coeff uv.1 (a : MvPolynomial ι ℤ) * coeff uv.2 p else 0) =
        coeff uv.1 (a : MvPolynomial ι ℤ) * coeff uv.2 (weightedHomogeneousComponent w d p) := by
      rintro ⟨u, v⟩ huv
      rw [coeff_weightedHomogeneousComponent]
      by_cases ha : coeff u (a : MvPolynomial ι ℤ) = 0
      · simp [ha]
      · have hu : Finsupp.weight w u = 0 := a.2 ha
        have hb : Finsupp.weight w b = Finsupp.weight w v := by
          rw [← Finset.mem_antidiagonal.1 huv, map_add, hu, zero_add]
        simp only [hb]
        split_ifs <;> simp
    rw [← Finset.sum_congr rfl term]
    split_ifs <;> simp

lemma sum_piP (p : MvPolynomial ι ℤ) :
    ∃ S₀ : Finset M, ∀ S, S₀ ⊆ S → ∑ d ∈ S, piP w d p = p := by
  classical
  refine ⟨p.support.image (Finsupp.weight w), fun S hS => ?_⟩
  ext b
  simp only [piP, LinearMap.coe_mk, AddHom.coe_mk, coeff_sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hS (Finset.mem_image_of_mem _ (mem_support_iff.2 (Ne.symm hne))))

/-- The degree `d` projection of `Q = P ⊗_{P₀} P̂₀`; the degree `d` part of `Q` is its range. -/
noncomputable def qProj (d : M) : Qring w x m →ₗ[P0 w ℤ] Qring w x m :=
  LinearMap.rTensor _ (piP w d)

lemma qProj_tmul (d : M) (p : MvPolynomial ι ℤ) (y : P0hat w x m) :
    qProj d (p ⊗ₜ[P0 w ℤ] y) = piP w d p ⊗ₜ y := rfl

lemma piP_piP (d : M) (p : MvPolynomial ι ℤ) : piP w d (piP w d p) = piP w d p :=
  (weightedHomogeneousComponent_isWeightedHomogeneous d p).weightedHomogeneousComponent_same

lemma qProj_idem (d : M) (q : Qring w x m) : qProj d (qProj d q) = qProj d q := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul p y => rw [qProj_tmul, qProj_tmul, piP_piP]
  | add u v hu hv => simp only [map_add, hu, hv]

lemma sum_qProj (q : Qring w x m) : ∃ S₀ : Finset M, ∀ S, S₀ ⊆ S → ∑ d ∈ S, qProj d q = q := by
  classical
  induction q using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun S _ => by simp⟩
  | tmul p y =>
    obtain ⟨S₀, h⟩ := sum_piP (w := w) p
    refine ⟨S₀, fun S hS => ?_⟩
    conv_rhs => rw [← h S hS]
    rw [TensorProduct.sum_tmul]
    rfl
  | add u v hu hv =>
    obtain ⟨S, hS⟩ := hu
    obtain ⟨T, hT⟩ := hv
    refine ⟨S ∪ T, fun U hU => ?_⟩
    simp only [map_add, Finset.sum_add_distrib]
    rw [hS U (Finset.union_subset_left hU), hT U (Finset.union_subset_right hU)]

variable (hx : ∀ i, x i ∈ 𝒞 (w i)) (hC : CompletePair 𝒞 m)

lemma Qmap_qProj (d : M) (q : Qring w x m) :
    Qmap hx hC (qProj d q) = ((decompose 𝒞 (Qmap hx hC q) d : 𝒞 d) : C) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul p y =>
    rw [qProj_tmul, Qmap_tmul, Qmap_tmul,
      decompose_mul_zero (phiHat_isLim hx hC y).1, proj_aeval hx]
    rfl
  | add u v hu hv =>
    rw [map_add, (Qmap hx hC).map_add, (Qmap hx hC).map_add, hu, hv, decompose_add,
      DirectSum.add_apply, AddMemClass.coe_add]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
/-- `C = Q/(f₁,…,f_s)` with `f_ℓ` homogeneous (§5 of the note). Noetherianity of `P̂₀` is a
hypothesis here only because `StacksFrontier.RingTheory.AdicCompletion.NoetherianRing` is not in the
sparse checkout. -/
theorem Qmap_ker_homogeneous [IsNoetherianRing (P0hat w x m)] :
    ∃ (s : ℕ) (f : Fin s → Qring w x m) (deg : Fin s → M), (∀ ℓ, qProj (deg ℓ) (f ℓ) = f ℓ) ∧
      Ideal.span (Set.range f) = RingHom.ker (Qmap hx hC) := by
  classical
  have := Fintype.ofFinite ι
  have hft : Algebra.FiniteType (P0 w ℤ) (MvPolynomial ι ℤ) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
  have hnoeth : IsNoetherianRing (Qring w x m) := by
    have h1 : Algebra.FiniteType (P0hat w x m) (P0hat w x m ⊗[P0 w ℤ] MvPolynomial ι ℤ) :=
      inferInstance
    have h2 : IsNoetherianRing (P0hat w x m ⊗[P0 w ℤ] MvPolynomial ι ℤ) :=
      Algebra.FiniteType.isNoetherianRing (P0hat w x m) _
    exact isNoetherianRing_of_ringEquiv _
      (Algebra.TensorProduct.comm (P0 w ℤ) (P0hat w x m) (MvPolynomial ι ℤ)).toRingEquiv
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian (RingHom.ker (Qmap hx hC)) :
    (RingHom.ker (Qmap hx hC)).FG)
  choose! S hS using fun q : Qring w x m => sum_qProj (w := w) (x := x) (m := m) q
  let G : Finset (M × Qring w x m) := t.biUnion fun g => (S g).image fun d => (d, qProj d g)
  let e := G.equivFin
  refine ⟨G.card, fun ℓ => (e.symm ℓ : M × Qring w x m).2, fun ℓ => (e.symm ℓ : M × Qring w x m).1,
    fun ℓ => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.1 (e.symm ℓ).2
    obtain ⟨d, _, hd⟩ := Finset.mem_image.1 hg
    beta_reduce
    rw [← hd]
    exact qProj_idem d g
  · rw [Ideal.span_le]
    rintro _ ⟨ℓ, rfl⟩
    obtain ⟨g, hgt, hg⟩ := Finset.mem_biUnion.1 (e.symm ℓ).2
    obtain ⟨d, _, hd⟩ := Finset.mem_image.1 hg
    beta_reduce
    rw [← hd]
    have hg0 : Qmap hx hC g = 0 := by
      have : g ∈ RingHom.ker (Qmap hx hC) := by rw [← ht]; exact Ideal.subset_span hgt
      exact this
    show Qmap hx hC (qProj d g) = 0
    rw [Qmap_qProj, hg0]
    simp
  · rw [← ht, Ideal.span_le]
    intro g hg
    rw [← hS g (S g) (Finset.Subset.refl _)]
    refine Ideal.sum_mem _ fun d hd => Ideal.subset_span ?_
    have hmem : (d, qProj d g) ∈ G :=
      Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_image_of_mem _ hd⟩
    exact ⟨e ⟨_, hmem⟩, by simp⟩

end Kernel
end AlgMag.ChartAlg

end PartP8

section PartP9
open IsLocalRing CategoryTheory

namespace AlgMag.ChartAlg

lemma map_eq_of_truncationsBijective {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
    (h : TruncationsBijective A B) :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
  refine map_maximalIdeal_eq_of_cotangent fun b hb => ?_
  obtain ⟨a, ha⟩ := h.surj 2 (Ideal.Quotient.mk _ b)
  have h0 : algebraMap A B a - b ∈ maximalIdeal B ^ 2 := Ideal.Quotient.eq.1 ha
  have hd : b - algebraMap A B a ∈ maximalIdeal B ^ 2 := by
    have := neg_mem h0
    rwa [neg_sub] at this
  have h2 : maximalIdeal B ^ 2 ≤ maximalIdeal B := Ideal.pow_le_self (by norm_num)
  have hla : algebraMap A B a ∈ maximalIdeal B := by
    have := sub_mem hb (h2 hd)
    rwa [sub_sub_cancel] at this
  have ham : a ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hla ⊢
    exact fun hu => hla (hu.map _)
  have : b = algebraMap A B a + (b - algebraMap A B a) := by ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ ham) hd

/-- **Étaleness at `w`** (§5 of the note, "Étale"). Here `S` is the ring of an affine chart of `W`
over the ring `R` of an affine étale chart of `X`, `q` the point `w` over `p` the point `x`,
`Ξ = Q̂_𝔫`, the truncations of `𝒪_{X,x}` are those of `E = Ξ/(f)` and those of `𝒪_{W,w}` are those of
`B̂ = Ξ/(f̃)`. There is `N₀` (the Artin–Rees constants of `f`, `r`) such that if `f̃ ≡ f`, `r̃ ≡ r`
modulo `𝔫^(N+1)`, `N ≥ N₀`, with `r̃` syzygies of `f̃` and the two presentations compatible modulo
`𝔫²` (the note's `ξ̃ ≡ ξ`, `N ≥ 1`), then `W → X` is étale at `w`. -/
theorem isEtaleAt_of_presentations {R S Ξ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    [IsNoetherianRing (Localization.AtPrime p)] [IsNoetherianRing (Localization.AtPrime q)]
    [IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))]
    [CommRing Ξ] [IsNoetherianRing Ξ] (𝔫 : Ideal Ξ) [𝔫.IsMaximal] {s t : ℕ} (f : Fin s → Ξ)
    (r : Fin t → Fin s → Ξ)
    (hr : Submodule.span Ξ (Set.range r) = LinearMap.ker (Fintype.linearCombination Ξ f)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (f' : Fin s → Ξ) (r' : Fin t → Fin s → Ξ),
      (∀ ℓ, f' ℓ - f ℓ ∈ 𝔫 ^ (N + 1)) → (∀ j ℓ, r' j ℓ - r j ℓ ∈ 𝔫 ^ (N + 1)) →
      (∀ j, ∑ ℓ, r' j ℓ * f' ℓ = 0) →
      ∀ (eA : ∀ j, (Localization.AtPrime p ⧸ maximalIdeal (Localization.AtPrime p) ^ j) ≃+*
          Ξ ⧸ (Ideal.span (Set.range f) ⊔ 𝔫 ^ j))
        (eB : ∀ j, (Localization.AtPrime q ⧸ maximalIdeal (Localization.AtPrime q) ^ j) ≃+*
          Ξ ⧸ (Ideal.span (Set.range f') ⊔ 𝔫 ^ j)),
        (∀ (a : Localization.AtPrime p) (ξ : Ξ),
          eA 2 (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ξ →
          eB 2 (Ideal.Quotient.mk _ (algebraMap _ _ a)) = Ideal.Quotient.mk _ ξ) →
        Algebra.IsEtaleAt R q := by
  obtain ⟨N₀, hN₀⟩ := lemma51_initial 𝔫 f r hr
  refine ⟨N₀, fun N hN f' r' hf hr' hs eA eB hcompat => ?_⟩
  have hin := hN₀ N hN f' r' hf hr' hs
  have hT := truncationsBijective_of_presentations 𝔫 _ _ hin eA eB hcompat
  exact isEtaleAt_of_truncationsBijective p q hT (map_eq_of_truncationsBijective hT)

end AlgMag.ChartAlg

end PartP9
