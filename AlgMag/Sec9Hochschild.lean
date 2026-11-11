/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Hochschild cohomology for diagonalizable monoids via formulas

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §9.

Everything here is over an affine base `B = Spec R`, with `V = B` quasi-compact: `F` is an
`R`-module, and `F ⊗ R[M]^{⊗ n}` is presented, as in the paper, as the formal direct sum
`⨁_{(m₁,…,mₙ)} F X^{m₁} ⊗ ⋯ ⊗ X^{mₙ}`, that is `(Fin n → M) →₀ F`. The differential is defined by
the formula of Proposition 9.12; its identification with Definition 9.4 (natural transformations
`H^n → F`, Proposition 9.12's first assertion), Propositions 9.1, 9.9, 9.10 for general `H`, and the
gluing over a non-affine `B` are not formalized here.

## Main results

* `Coaction.delta_single`: the formula of Proposition 9.12.
* `coactionEquivDecomposition`: Proposition 9.11.
* `Coaction.delta_delta`: Remark 9.6.
* `Coaction.H1_subsingleton`: Proposition 9.13.
* `Coaction.H_subsingleton`: `Hⁿ = 0` for all `n ≥ 1`, the statement conjectured in Remark 9.14.
* `Coaction.lastCoeff_delta`: the contracting identity behind both, extending the paper's
  `e = -f₀`.

`M` is an arbitrary commutative monoid: none of this needs finite generation or cancellativity.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AlgMag.Hochschild

variable (R M F : Type*) [CommRing R] [AddCommMonoid M] [AddCommGroup F] [Module R F]

/-- An `R[M]`-comodule structure on `F` (Proposition 9.10 for `H = 𝔸(M)`, affine base), with
`F ⊗ R[M] = ⨁ₘ F X^m` written `M →₀ F`, and comultiplication `X^m ↦ X^m ⊗ X^m`, counit
`X^m ↦ 1`. -/
structure Coaction where
  /-- the coaction `F → F ⊗ R[M]` -/
  ρ : F →ₗ[R] M →₀ F
  /-- `(ρ ⊗ Id) ∘ ρ = (Id ⊗ Δ) ∘ ρ` -/
  coassoc : ∀ x, ((ρ x).sum fun k y => (ρ y).mapDomain fun m => (m, k)) =
    (ρ x).mapDomain fun m => (m, m)
  /-- `(Id ⊗ ε) ∘ ρ = Id` -/
  counit : ∀ x, (ρ x).sum (fun _ y => y) = x

/-- The `n`-cochains `Cⁿ(𝔸(M)_B, F)(B) = ⨁_{m ∈ Mⁿ} F_m` of Proposition 9.12. -/
abbrev Cochain (n : ℕ) : Type _ := (Fin n → M) →₀ F

variable {R M F}

/-- The words `(m₁,…,mₙ) ↦ (m₁,…,mᵢ,mᵢ,…,mₙ₊₁)`. -/
abbrev dupWord {n : ℕ} (i : Fin n) (m : Fin n → M) : Fin (n + 1) → M := m ∘ Fin.predAbove i

/-- `(m₁,…,mₙ) ↦ (m₁,…,mₙ,0)`. -/
abbrev snoc0 {n : ℕ} (m : Fin n → M) : Fin (n + 1) → M := Fin.snoc (α := fun _ => M) m 0

/-- `(m₁,…,mₙ) ↦ (k,m₁,…,mₙ)`. -/
abbrev consW {n : ℕ} (k : M) (m : Fin n → M) : Fin (n + 1) → M := Fin.cons (α := fun _ => M) k m

/-- The component `ρ_m` of the coaction (Proposition 9.11). -/
noncomputable def Coaction.comp (A : Coaction R M F) (m : M) : F →ₗ[R] F :=
  Finsupp.lapply m ∘ₗ A.ρ

@[simp] lemma Coaction.comp_apply (A : Coaction R M F) (m : M) (x : F) :
    A.comp m x = A.ρ x m := rfl

/-- First term of `δ`: `f X^{m} ↦ ∑ₖ ρₖ(f) X^k X^{m}`. -/
noncomputable def Coaction.first (A : Coaction R M F) (n : ℕ) :
    Cochain M F n →ₗ[R] Cochain M F (n + 1) :=
  Finsupp.lsum R fun m => Finsupp.lmapDomain F R (fun k => consW k m) ∘ₗ A.ρ

/-- Middle terms of `δ`: `f X^{m₁} ⋯ X^{mₙ} ↦ f X^{m₁} ⋯ Δ(X^{mᵢ}) ⋯ X^{mₙ}`. -/
noncomputable def dup (R : Type*) [CommRing R] [Module R F] {n : ℕ} (i : Fin n) :
    Cochain M F n →ₗ[R] Cochain M F (n + 1) :=
  Finsupp.lmapDomain F R (dupWord i)

/-- Last term of `δ`: `f X^{m} ↦ f X^{m} X^0`. -/
noncomputable def last (R : Type*) [CommRing R] [Module R F] (n : ℕ) :
    Cochain M F n →ₗ[R] Cochain M F (n + 1) :=
  Finsupp.lmapDomain F R snoc0

omit [AddCommMonoid M] in
private lemma lastCoeff_inj_aux [Zero M] {n : ℕ} :
    Function.Injective (fun m : Fin n → M => (Fin.snoc (α := fun _ => M) m 0 : Fin (n + 1) → M)) :=
  fun a b h => by
    have := congrArg Fin.init h
    simpa [Fin.init_snoc] using this

variable (M F) in
/-- Coefficient extraction at `X^0` in the last variable: `(e x)(m) = x(m,0)`. -/
noncomputable def lastCoeff (R : Type*) [CommRing R] [Module R F] (n : ℕ) :
    Cochain M F (n + 1) →ₗ[R] Cochain M F n :=
  Finsupp.lcomapDomain snoc0 lastCoeff_inj_aux

open Classical in
lemma lastCoeff_single {n : ℕ} (w : Fin (n + 1) → M) (f : F) :
    lastCoeff M F R n (Finsupp.single w f) =
      if w (Fin.last n) = 0 then Finsupp.single (Fin.init w) f else 0 := by
  ext u
  have hu : (lastCoeff M F R n (Finsupp.single w f)) u = (Finsupp.single w f) (snoc0 u) := rfl
  rw [hu]
  split_ifs with h
  · have e : w = snoc0 (Fin.init w) := by
      conv_lhs => rw [← Fin.snoc_init_self (α := fun _ => M) w, h]
    by_cases hc : Fin.init w = u
    · subst hc
      rw [← e]; simp
    · rw [Finsupp.single_eq_of_ne, Finsupp.single_eq_of_ne]
      · exact fun hh => hc hh.symm
      · intro hh; apply hc; rw [← hh]; simp [Fin.init_snoc]
  · rw [Finsupp.single_eq_of_ne]; · simp
    intro hh; apply h; rw [← hh]; simp

private lemma init_consW {n : ℕ} (k : M) (w : Fin (n + 1) → M) :
    Fin.init (consW k w) = consW k (Fin.init w) := by
  funext t
  refine Fin.cases ?_ (fun t => ?_) t
  · simp [Fin.init, consW]
  · simp only [Fin.init, consW]
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
    rfl

private lemma consW_last {n : ℕ} (k : M) (w : Fin (n + 1) → M) :
    consW k w (Fin.last (n + 1)) = w (Fin.last n) := by
  rw [← Fin.succ_last]; exact Fin.cons_succ _ _ _

private lemma lastCoeff_mapDomain_cons {n : ℕ} (w : Fin (n + 1) → M) (g : M →₀ F) :
    lastCoeff M F R (n + 1) (g.mapDomain fun k => consW k w) =
      open Classical in if w (Fin.last n) = 0 then
        g.mapDomain (fun k => consW k (Fin.init w)) else 0 := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [Finsupp.mapDomain_add, map_add, ha, hb]
    split_ifs <;> simp [Finsupp.mapDomain_add]
  | single k y =>
    rw [Finsupp.mapDomain_single, lastCoeff_single, consW_last, init_consW]
    split_ifs <;> simp [Finsupp.mapDomain_single]

private lemma val_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (Fin.predAbove p i : ℕ) = if (p : ℕ) < i then (i : ℕ) - 1 else i := by
  unfold Fin.predAbove
  by_cases h : p.castSucc < i
  · have h' : (p : ℕ) < i := by simpa [Fin.lt_def] using h
    simp [h, h']
  · have h' : ¬ (p : ℕ) < i := by simpa [Fin.lt_def] using h
    simp [h, h']

private lemma predAbove_castSucc_castSucc {n : ℕ} (i : Fin n) (t : Fin (n + 1)) :
    Fin.predAbove i.castSucc t.castSucc = (Fin.predAbove i t).castSucc := by
  ext; simp only [val_predAbove, Fin.val_castSucc]

private lemma predAbove_last_cast {n : ℕ} (t : Fin (n + 1)) :
    Fin.predAbove (Fin.last n) t.castSucc = t := by
  ext; simp only [val_predAbove, Fin.val_castSucc, Fin.val_last]; have := t.2; split_ifs <;> omega

private lemma predAbove_any_last {n : ℕ} (i : Fin (n + 1)) :
    Fin.predAbove i (Fin.last (n + 1)) = Fin.last n := by
  ext; simp only [val_predAbove, Fin.val_last]; have := i.2; split_ifs <;> omega

/-- The identity `σ_b ∘ σ_{a+1}`-type relation between the word-duplication maps, `a ≤ b`. -/
private lemma predAbove_comp {n : ℕ} (a b : Fin (n + 1)) (h : a ≤ b) (t : Fin (n + 3)) :
    Fin.predAbove b (Fin.predAbove a.castSucc t) = Fin.predAbove a (Fin.predAbove b.succ t) := by
  have h' : (a : ℕ) ≤ b := h
  ext
  simp only [val_predAbove, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

lemma lastCoeff_first (A : Coaction R M F) {n : ℕ} (x : Cochain M F (n + 1)) :
    lastCoeff M F R (n + 1) (A.first (n + 1) x) = A.first n (lastCoeff M F R n x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | single w f =>
    have e1 : ∀ (k : ℕ) (u : Fin k → M), A.first k (Finsupp.single u f) =
        (A.ρ f).mapDomain (fun l => consW l u) := by
      intro k u; simp [Coaction.first, Finsupp.lmapDomain_apply]
    rw [lastCoeff_single, e1, lastCoeff_mapDomain_cons]
    split_ifs
    · rw [e1]
    · simp

lemma lastCoeff_dup_castSucc {n : ℕ} (i : Fin n) (x : Cochain M F (n + 1)) :
    lastCoeff M F R (n + 1) (dup R i.castSucc x) = dup R i (lastCoeff M F R n x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | single w f =>
    have e : ∀ (k : ℕ) (j : Fin k) (u : Fin k → M), dup R j (Finsupp.single u f) =
        Finsupp.single (dupWord j u) f := by
      intro k j u; simp [dup, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [e, lastCoeff_single, lastCoeff_single]
    have h1 : dupWord i.castSucc w (Fin.last (n + 1)) = w (Fin.last n) := by
      simp [dupWord, predAbove_any_last]
    have h2 : Fin.init (dupWord i.castSucc w) = dupWord i (Fin.init w) := by
      funext t
      simp [Fin.init, dupWord, predAbove_castSucc_castSucc]
    rw [h1, h2]
    split_ifs
    · rw [e]
    · simp

lemma lastCoeff_dup_last {n : ℕ} (x : Cochain M F (n + 1)) :
    lastCoeff M F R (n + 1) (dup R (Fin.last n) x) = last R n (lastCoeff M F R n x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | single w f =>
    have e : dup R (Fin.last n) (Finsupp.single w f) =
        Finsupp.single (dupWord (Fin.last n) w) f := by
      simp [dup, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [e, lastCoeff_single, lastCoeff_single]
    have h1 : dupWord (Fin.last n) w (Fin.last (n + 1)) = w (Fin.last n) := by
      simp [dupWord, predAbove_any_last]
    have h2 : Fin.init (dupWord (Fin.last n) w) = w := by
      funext t
      simp [Fin.init, dupWord, predAbove_last_cast]
    rw [h1, h2]
    split_ifs with h
    · have e' : w = snoc0 (Fin.init w) := by
        conv_lhs => rw [← Fin.snoc_init_self (α := fun _ => M) w, h]
      simp only [last, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rw [← e']
    · simp

lemma lastCoeff_last {n : ℕ} (x : Cochain M F n) :
    lastCoeff M F R n (last R n x) = x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb]
  | single w f =>
    simp only [last, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [lastCoeff_single]
    simp [snoc0, Fin.init_snoc]

namespace Coaction

variable (A : Coaction R M F)

/-- The differential `δ : Cⁿ → Cⁿ⁺¹`, by the formula of Proposition 9.12. -/
noncomputable def delta (n : ℕ) : Cochain M F n →ₗ[R] Cochain M F (n + 1) :=
  A.first n + (∑ i : Fin n, ((-1 : ℤ) ^ ((i : ℕ) + 1)) • dup R i) +
    ((-1 : ℤ) ^ (n + 1)) • last R n

/-- The formula of Proposition 9.12 on a monomial. -/
theorem delta_single {n : ℕ} (m : Fin n → M) (f : F) :
    A.delta n (Finsupp.single m f) =
      (A.ρ f).mapDomain (fun k => consW k m) +
      (∑ i : Fin n, ((-1 : ℤ) ^ ((i : ℕ) + 1)) • Finsupp.single (dupWord i m) f) +
      ((-1 : ℤ) ^ (n + 1)) • Finsupp.single (snoc0 m) f := by
  simp only [delta, first, dup, last, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Finsupp.lsum_single, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- The contracting identity: `e ∘ δ - δ ∘ e = (-1)ⁿ` on `Cⁿ⁺¹`, with `e` the extraction of the
coefficient of `X^0` in the last variable. It uses nothing about `ρ`. -/
theorem lastCoeff_delta (n : ℕ) (x : Cochain M F (n + 1)) :
    lastCoeff M F R (n + 1) (A.delta (n + 1) x) =
      A.delta n (lastCoeff M F R n x) + ((-1 : ℤ) ^ n) • x := by
  simp only [delta, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_add,
    map_zsmul, map_sum, Fin.sum_univ_castSucc, lastCoeff_first, lastCoeff_dup_castSucc,
    lastCoeff_dup_last, lastCoeff_last, Fin.val_castSucc, Fin.val_last]
  rw [show ((-1 : ℤ) ^ (n + 1 + 1)) = (-1) ^ n by ring]
  abel

/-- **Vanishing, explicit form** (generalizes Proposition 9.13, the case `n = 0`): a cocycle
`x ∈ Cⁿ⁺¹` is the coboundary of `(-1)ⁿ⁺¹ e(x)`. For `n = 0` this is the paper's `e = -f₀`. -/
theorem eq_delta_of_cocycle (n : ℕ) (x : Cochain M F (n + 1)) (hx : A.delta (n + 1) x = 0) :
    x = A.delta n (((-1 : ℤ) ^ (n + 1)) • lastCoeff M F R n x) := by
  have h := A.lastCoeff_delta n x
  rw [hx, map_zero] at h
  have hs : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have : ((-1 : ℤ) ^ n) • x = - A.delta n (lastCoeff M F R n x) :=
    (eq_neg_of_add_eq_zero_right h.symm)
  calc x = ((-1 : ℤ) ^ n * (-1) ^ n) • x := by rw [hs, one_smul]
    _ = _ := by rw [mul_smul, this, map_zsmul, pow_succ]; simp

/-! ### `δ² = 0` (Remark 9.6) -/

/-- `x ↦ ∑ₖ ρₖ(f) X^k X^{m} X^0`: embeds `Cⁿ` in words of length `n+2`, on which `δ` becomes the
alternating sum of the letter-duplication maps. -/
noncomputable def iota (n : ℕ) : Cochain M F n →ₗ[R] Cochain M F (n + 2) :=
  Finsupp.lsum R fun m => Finsupp.lmapDomain F R (fun k => consW k (snoc0 m)) ∘ₗ A.ρ

/-- Deleting the first and last letter. -/
noncomputable def retr (R : Type*) [CommRing R] [Module R F] (n : ℕ) :
    Cochain M F (n + 2) →ₗ[R] Cochain M F n :=
  Finsupp.lmapDomain F R (fun w i => w i.castSucc.succ)

lemma iota_single {n : ℕ} (m : Fin n → M) (f : F) :
    A.iota n (Finsupp.single m f) = (A.ρ f).mapDomain (fun k => consW k (snoc0 m)) := by
  simp [iota, Finsupp.lmapDomain_apply]

lemma retr_iota {n : ℕ} (x : Cochain M F n) : retr R n (A.iota n x) = x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single m f =>
    rw [iota_single, retr, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
    have : ((fun w (i : Fin n) => w i.castSucc.succ) ∘ fun k => consW k (snoc0 m)) =
        fun _ => m := by
      funext k i
      simp [consW, snoc0]
    rw [this, Finsupp.mapDomain]
    conv_rhs => rw [← A.counit f]
    rw [Finsupp.sum, Finsupp.sum, Finsupp.single_finsetSum]

/-- `ρ` satisfies the coefficient form of coassociativity. -/
lemma coassocLHS_apply (ρ : F →ₗ[R] M →₀ F) (x : F) (m k : M) :
    ((ρ x).sum fun k y => (ρ y).mapDomain fun m => (m, k)) (m, k) = ρ (ρ x k) m := by
  classical
  have inj : ∀ b : M, Function.Injective (fun m : M => (m, b)) :=
    fun b a c h => (Prod.ext_iff.1 h).1
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single k]
  · exact Finsupp.mapDomain_apply (inj k) _ _
  · intro b _ hb
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact hb (Prod.ext_iff.1 ha).2
  · intro _; simp

lemma coassocRHS_apply (g : M →₀ F) (m k : M) :
    (g.mapDomain fun m => (m, m)) (m, k) = open Classical in if m = k then g m else 0 := by
  classical
  have inj : Function.Injective (fun m : M => (m, m)) := fun a c h => (Prod.ext_iff.1 h).1
  split_ifs with h
  · subst h; exact Finsupp.mapDomain_apply inj _ _
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 ha
    exact h (h1.symm.trans h2)

/-- `ρ_m ∘ ρ_k = ρ_k` if `k = m`, `0` otherwise (Proposition 9.11). -/
theorem comp_comp (m k : M) (x : F) :
    A.comp m (A.comp k x) = open Classical in if m = k then A.comp k x else 0 := by
  have := congrArg (fun g => g (m, k)) (A.coassoc x)
  simp only [coassocLHS_apply, coassocRHS_apply] at this
  simp only [comp_apply, this]
  split_ifs with h
  · rw [h]
  · rfl

lemma rho_comp (k : M) (x : F) : A.ρ (A.comp k x) = Finsupp.single k (A.comp k x) := by
  classical
  ext m
  have := A.comp_comp m k x
  simp only [comp_apply] at this ⊢
  rw [this, Finsupp.single_apply]
  by_cases h : m = k
  · subst h; simp
  · simp [h, Ne.symm h]

end Coaction

private lemma cons_predAbove_succ {n : ℕ} (j : Fin n) (k : M) (u : Fin n → M) :
    dupWord (n := n + 1) j.succ (consW k u) = consW k (dupWord j u) := by
  funext t
  refine Fin.cases ?_ (fun s => ?_) t
  · simp [dupWord, consW]
  · simp only [dupWord, consW, Function.comp, Fin.succ_predAbove_succ, Fin.cons_succ]

private lemma word0 {n : ℕ} (k : M) (m : Fin n → M) :
    dupWord (n := n + 2) 0 (consW k (snoc0 m)) = consW k (snoc0 (consW k m)) := by
  funext t
  refine Fin.cases ?_ (fun s => ?_) t
  · simp [dupWord, consW]
  · have : snoc0 (consW k m) = consW k (snoc0 m) := by
      simp only [snoc0, consW]; rw [Fin.cons_snoc_eq_snoc_cons]
    rw [this]
    simp [dupWord, consW]

private lemma wordMid {n : ℕ} (t : Fin n) (m : Fin n → M) :
    dupWord (n := n + 1) t.castSucc (snoc0 m) = snoc0 (dupWord t m) := by
  funext s
  refine Fin.lastCases ?_ (fun s => ?_) s
  · simp [dupWord, snoc0, predAbove_any_last]
  · simp [dupWord, snoc0, predAbove_castSucc_castSucc]

private lemma wordLast {n : ℕ} (m : Fin n → M) :
    dupWord (Fin.last n) (snoc0 m) = snoc0 (snoc0 m) := by
  funext s
  refine Fin.lastCases ?_ (fun s => ?_) s
  · simp [dupWord, snoc0, predAbove_any_last]
  · simp [dupWord, snoc0, predAbove_last_cast]

/-- The alternating sum of letter duplications. -/
noncomputable def altDup (R : Type*) [CommRing R] [Module R F] (n : ℕ) :
    Cochain M F (n + 2) →ₗ[R] Cochain M F (n + 3) :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • dup R i

/-- Alternating double sums vanish given the (co)simplicial exchange relation. -/
private lemma alt_sq {G : Type*} [AddCommGroup G] (n : ℕ) (t : Fin (n + 2) → Fin (n + 3) → G)
    (h : ∀ (i : Fin (n + 2)) (j : Fin (n + 2)), j ≤ i → t i j.castSucc = t j i.succ) :
    ∑ i : Fin (n + 2), ∑ j : Fin (n + 3), (((-1 : ℤ) ^ (i : ℕ)) * (-1) ^ (j : ℕ)) • t i j = 0 := by
  simp only [← Finset.sum_product']
  let S : Finset (Fin (n + 2) × Fin (n + 3)) := {ij | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : Fin (n + 2) × Fin (n + 3), ij ∈ S → Fin (n + 2) × Fin (n + 3) := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    refine ⟨by simpa [φ] using congr_arg Prod.snd h, ?_⟩
    have := congr_arg (fun p => (p.1 : ℕ)) h
    ext
    simpa [φ] using this
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp at hij'
    · simp only [S, Finset.mem_filter_univ, Fin.val_castSucc, Fin.val_pred]
      omega
    · simp [φ]
  · rintro ⟨i, j⟩ hij
    have hij' : (j : ℕ) ≤ i := (Finset.mem_filter.mp hij).2
    have hlt : (j : ℕ) < n + 2 := by have := i.2; omega
    have hj : j = (⟨j, hlt⟩ : Fin (n + 2)).castSucc := rfl
    dsimp only [φ]
    have ht : t i j = t (Fin.castLT j hlt) i.succ := by
      conv_lhs => rw [hj]
      exact h i _ hij'
    rw [ht, ← neg_smul]
    congr 1
    simp only [Fin.val_castLT, Fin.val_succ, pow_succ]
    ring

lemma altDup_altDup (n : ℕ) (x : Cochain M F (n + 2)) :
    altDup R (n + 1) (altDup R n x) = 0 := by
  have e : altDup R (n + 1) (altDup R n x) =
      ∑ i : Fin (n + 2), ∑ j : Fin (n + 3), (((-1 : ℤ) ^ (i : ℕ)) * (-1) ^ (j : ℕ)) •
        dup R j (dup R i x) := by
    simp only [altDup, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul,
      smul_smul, Finset.smul_sum]
  rw [e]
  apply alt_sq
  intro i j hji
  simp only [dup, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext w t
  simp only [dupWord, Function.comp]
  rw [predAbove_comp j i hji t]

namespace Coaction

variable (A : Coaction R M F)

lemma iota_mapDomain_first {n : ℕ} (m : Fin n → M) (f : F) :
    A.iota (n + 1) ((A.ρ f).mapDomain fun k => consW k m) =
      (A.ρ f).mapDomain fun k => consW k (snoc0 (consW k m)) := by
  classical
  simp only [Finsupp.mapDomain]
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [iota_single]
  have : A.ρ (A.ρ f k) = Finsupp.single k (A.ρ f k) := A.rho_comp k f
  rw [this, Finsupp.mapDomain_single]

/-- On words, `δ` is the alternating sum of letter duplications. -/
lemma iota_delta {n : ℕ} (x : Cochain M F n) :
    A.iota (n + 1) (A.delta n x) = altDup R n (A.iota n x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single m f =>
    rw [delta_single, iota_single]
    simp only [map_add, map_sum, map_zsmul, iota_mapDomain_first, iota_single]
    simp only [altDup, LinearMap.sum_apply, LinearMap.smul_apply, dup, Finsupp.lmapDomain_apply,
      ← Finsupp.mapDomain_comp]
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    have h0 : (dupWord (n := n + 2) 0 ∘ fun k => consW k (snoc0 m)) =
        fun k => consW k (snoc0 (consW k m)) := funext fun k => word0 k m
    have hm : ∀ t : Fin n, (dupWord (n := n + 2) t.castSucc.succ ∘ fun k => consW k (snoc0 m)) =
        fun k => consW k (snoc0 (dupWord t m)) := fun t => funext fun k => by
      simp only [Function.comp]
      rw [cons_predAbove_succ, wordMid]
    have hl : (dupWord (n := n + 2) (Fin.last n).succ ∘ fun k => consW k (snoc0 m)) =
        fun k => consW k (snoc0 (snoc0 m)) := funext fun k => by
      simp only [Function.comp]
      rw [cons_predAbove_succ, wordLast]
    simp only [h0, hm, hl, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.val_castSucc,
      Fin.val_last, add_assoc]

/-- **Remark 9.6**: `δ ∘ δ = 0`. -/
theorem delta_delta (n : ℕ) (x : Cochain M F n) : A.delta (n + 1) (A.delta n x) = 0 := by
  rw [← retr_iota A (A.delta (n + 1) (A.delta n x)), iota_delta, iota_delta, altDup_altDup,
    map_zero]

/-- `Zⁿ` (Definition 9.7). -/
noncomputable def Z (n : ℕ) : Submodule R (Cochain M F n) := LinearMap.ker (A.delta n)

/-- `Bⁿ` (Definition 9.7): `B⁰ = 0`, `Bⁿ⁺¹ = im δ`. -/
noncomputable def B : ∀ n : ℕ, Submodule R (Cochain M F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (A.delta n)

theorem B_le_Z (n : ℕ) : A.B n ≤ A.Z n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨x, rfl⟩
    exact A.delta_delta n x

/-- `Hⁿ_monoid(𝔸(M)_B, F)` (Definition 9.7), with `B = Spec R`. -/
abbrev H (n : ℕ) : Type _ := (A.Z n) ⧸ (A.B n).comap (A.Z n).subtype

/-- **Proposition 9.13 and Remark 9.14, affine base**: `Hⁿ = 0` for all `n ≥ 1`. -/
theorem H_subsingleton (n : ℕ) : Subsingleton (A.H (n + 1)) := by
  apply Submodule.Quotient.subsingleton_iff.2
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  exact ⟨_, (A.eq_delta_of_cocycle n x hx).symm⟩

/-- **Proposition 9.13** (`n = 1`, affine base). -/
theorem H1_subsingleton : Subsingleton (A.H 1) := A.H_subsingleton 0

end Coaction

/-! ### Proposition 9.11 -/

variable (R M F) in
/-- The data of Proposition 9.11, on sections: `ρ_m` orthogonal idempotents, summing to the
identity, with finitely many nonzero **at each section**. (The printed wording is that finitely
many of the `ρ_m` are nonzero locally; see `regular_comp_ne_zero`.) -/
structure Decomposition where
  /-- the components -/
  comp : M → F →ₗ[R] F
  finite : ∀ x, (Function.support fun m => comp m x).Finite
  same : ∀ m x, comp m (comp m x) = comp m x
  ne : ∀ m k x, k ≠ m → comp m (comp k x) = 0
  sum : ∀ x, ∑ᶠ m, comp m x = x

/-- **Proposition 9.11, affine base**: comodule structures correspond to decompositions. -/
noncomputable def coactionEquivDecomposition : Coaction R M F ≃ Decomposition R M F where
  toFun A :=
    { comp := A.comp
      finite := fun x => (A.ρ x).hasFiniteSupport
      same := fun m x => by rw [A.comp_comp]; simp
      ne := fun m k x h => by rw [A.comp_comp]; simp [Ne.symm h]
      sum := fun x => by
        have hs : Function.support (fun m => A.comp m x) ⊆ ((A.ρ x).support : Set M) := by
          intro m hm; simpa using hm
        rw [finsum_eq_sum_of_support_subset _ hs]
        exact A.counit x }
  invFun D :=
    { ρ :=
        { toFun := fun x => Finsupp.ofSupportFinite (fun m => D.comp m x) (D.finite x)
          map_add' := fun x y => by ext m; exact (D.comp m).map_add x y
          map_smul' := fun r x => by ext m; exact (D.comp m).map_smul r x }
      coassoc := fun x => by
        classical
        ext ⟨m, k⟩ : 1
        rw [Coaction.coassocLHS_apply, Coaction.coassocRHS_apply]
        change D.comp m (D.comp k x) = if m = k then D.comp m x else 0
        split_ifs with h
        · subst h; exact D.same _ _
        · exact D.ne _ _ _ (Ne.symm h)
      counit := fun x => by
        have hs : Function.support (fun m => D.comp m x) ⊆ (D.finite x).toFinset := by simp
        conv_rhs => rw [← D.sum x, finsum_eq_sum_of_support_subset _ hs]
        rfl }
  left_inv A := by
    have key : ∀ A B : Coaction R M F, A.ρ = B.ρ → A = B := by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
      cases h
      rfl
    exact key _ _ (LinearMap.ext fun x => Finsupp.ext fun m => rfl)
  right_inv D := by
    cases D
    rfl

variable (R M) in
/-- The regular comodule `R[M]`, `X^m ↦ X^m ⊗ X^m`. -/
noncomputable def regular : Coaction R M (M →₀ R) where
  ρ := Finsupp.lsum R fun m => (Finsupp.lsingle m) ∘ₗ (Finsupp.lsingle m)
  coassoc := fun x => by
    classical
    ext ⟨m, k⟩ : 1
    rw [Coaction.coassocLHS_apply, Coaction.coassocRHS_apply]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb =>
      simp only [map_add, Finsupp.add_apply, ha, hb]
      split_ifs <;> simp
    | single l r =>
      by_cases h : l = k <;> by_cases h' : m = k <;> simp_all [Finsupp.single_apply]
  counit := fun x => by
    classical
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ha, hb]
    | single m r => simp

/-- On `F = R[M]`, every `ρ_m` is nonzero, so for infinite `M` the finiteness in Proposition 9.11
cannot hold for the endomorphisms `ρ_m` themselves: it holds at each section. -/
theorem regular_comp_ne_zero [Nontrivial R] (m : M) : (regular R M).comp m ≠ 0 := by
  intro h
  have := congrArg (fun g => g (Finsupp.single m 1) m) h
  simp [regular] at this

end AlgMag.Hochschild
