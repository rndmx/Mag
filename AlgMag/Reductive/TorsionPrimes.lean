/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Rooted.MinimalRootReductive
import AlgMag.Reductive.WeylPart
import AlgMag.Reductive.SLSpCriterion
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.GroupTheory.Index

/-!
# Weyl magnets and torsion primes (`sections/torsion.tex`)

## Lemma `lem:closed-stable`

`closed_iff_stable`: for a finite crystallographic root pairing `P` over `ℤ` (Mathlib's
`RootPairing`), a subset `R ⊆ Φ = range P.root` is closed iff `[R⟩ ∩ Φ = R`. The root-system
fact `(γ, β) > 0, γ ≠ β ⇒ γ - β ∈ Φ` is Mathlib's `RootPairing.root_sub_root_mem_of_pairingIn_pos`
(it holds without reducedness); the `W`-invariant scalar product is Mathlib's `RootPairing.RootForm`.

## Theorem `thm:torsion-primes`, combinatorial core

`M` an abelian group with a finite group `W` acting, `Φ ⊆ M`, reflections `refl α = s_α` with
`(1 - s_α)M ⊆ ℤα`. Notation: `Z w = (1 - w)M` (`Rooted.weylMagnet`), `Rw Φ w = Z_w ∩ Φ`,
`C_w = weylPart (Z w) = {v | Z_v ⊆ Z_w}`, `reflGroup refl R = W(R) = ⟨s_α | α ∈ R⟩`.
Redundancy is `Z w = weylMagnetLower Φ act w` (as in `joinIrreducibles_reductive`).

* `mem_reflGroup_redundant`: `w ∈ W(R_w) ⇒ Z_w = ℤR_w`, hence redundant (direction (i)).
* `orderOf_smul_mem_Z`: `tors(M/Z_w)` is killed by the order of `w` (`M` torsion-free).
* `posSystemExists`: `W(R_w)` is transitive on the positive systems of `R_w` (Bourbaki VI §1
  no. 5 Thm 2 (a)), via a regular element `λ` (`exists_regular`) and a maximization.
* `stepA`, `stepB`: Steps A and B of direction (ii).
* `exists_candidate_of_levi`: the power argument producing a `p`-candidate.
* `torsion_primes`: **Theorem `thm:torsion-primes`**, with the group-theoretic facts of
  Steinberg (1975) as explicit inputs (see its docstring).
-/

namespace AlgMag.Reductive.Torsion

open Set RootPairing

/-! ### Lemma `lem:closed-stable` -/

section ClosedStable

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Finite ι]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]

/-- `R` is **closed** in `Φ`: `α, β ∈ R`, `α + β ∈ Φ ⇒ α + β ∈ R`. -/
def IsClosedIn (Φ R : Set M) : Prop := ∀ α ∈ R, ∀ β ∈ R, α + β ∈ Φ → α + β ∈ R

omit [Finite ι] in
/-- For roots, positivity of the invariant form `(α_i, α_j)` (Mathlib's `RootForm`) gives
positivity of the Cartan integer `⟨α_i, α_j^∨⟩`. -/
lemma pairingIn_pos_of_rootForm_pos [Fintype ι] {i j : ι}
    (h : 0 < P.RootForm (P.root i) (P.root j)) : 0 < P.pairingIn ℤ i j := by
  have h2 := (P.posRootForm ℤ).two_mul_apply_root_root i j
  obtain ⟨s, hs, hs'⟩ := (P.posRootForm ℤ).exists_pos_eq j
  have hform : (P.posRootForm ℤ).form = P.RootForm := rfl
  rw [hform] at h2 hs'
  have hp : P.pairing i j = P.pairingIn ℤ i j := by
    rw [← P.algebraMap_pairingIn ℤ]; rfl
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hs'
  rw [← hs', hp] at h2
  by_contra hle
  push Not at hle
  nlinarith

omit [Finite ι] in
/-- The invariant form is positive on roots: `0 < (α, α)`. -/
lemma rootForm_root_self_pos [Fintype ι] (i : ι) : 0 < P.RootForm (P.root i) (P.root i) := by
  obtain ⟨s, hs, hs'⟩ := (P.posRootForm ℤ).exists_pos_eq i
  have hform : (P.posRootForm ℤ).form = P.RootForm := rfl
  rw [hform] at hs'
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hs'
  rw [← hs']; exact hs

omit [Finite ι] [P.IsCrystallographic] in
/-- `(α, α) ⟨x, α^∨⟩ = 2 (α, x)` (SGA3 XXI 1.2.1 (10), Mathlib's `rootForm_self_smul_coroot`). -/
lemma rootForm_self_mul_coroot [Fintype ι] (i : ι) (x : M) :
    P.RootForm (P.root i) (P.root i) * P.coroot' i x = 2 * P.RootForm (P.root i) x := by
  have h := congrArg (P.toLinearMap x) (P.rootForm_self_smul_coroot i)
  rw [map_smul, map_nsmul, toLinearMap_apply_apply_Polarization, smul_eq_mul, nsmul_eq_mul] at h
  simpa using h

/-- **Lemma `lem:closed-stable`.** A subset `R ⊆ Φ` is closed iff it is additively stable,
`[R⟩ ∩ Φ = R`. -/
theorem closed_iff_stable {R : Set M} (hR : R ⊆ range P.root) :
    IsClosedIn (range P.root) R ↔
      (AddSubmonoid.closure R : Set M) ∩ range P.root = R := by
  classical
  let _ := Fintype.ofFinite ι
  constructor
  · intro hcl
    refine Subset.antisymm ?_ fun x hx => ⟨AddSubmonoid.subset_closure hx, hR hx⟩
    rintro γ ⟨hγ, hγΦ⟩
    obtain ⟨l, hlR, rfl⟩ := AddSubmonoid.exists_list_of_mem_closure hγ
    -- induction on the number of summands
    suffices H : ∀ n, ∀ l : List M, l.length = n → (∀ x ∈ l, x ∈ R) → l.sum ∈ range P.root →
        l.sum ∈ R from H _ l rfl hlR hγΦ
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro l hl hlR hΦ
    obtain ⟨i, hi⟩ := hΦ
    -- `0 < (γ, γ) = Σ (γ, β_k)`
    have hpos : 0 < P.RootForm (P.root i) (P.root i) := by
      obtain ⟨s, hs, hs'⟩ := (P.posRootForm ℤ).exists_pos_eq i
      have hform : (P.posRootForm ℤ).form = P.RootForm := rfl
      rw [hform] at hs'
      simp only [Algebra.algebraMap_self, RingHom.id_apply] at hs'
      rw [← hs']; exact hs
    have hsum : P.RootForm (P.root i) l.sum = (l.map (P.RootForm (P.root i))).sum :=
      map_list_sum (P.RootForm (P.root i)) l
    obtain ⟨x, hxl, hx⟩ : ∃ x ∈ l, 0 < P.RootForm (P.root i) x := by
      by_contra hne
      push Not at hne
      have key : ∀ L : List ℤ, (∀ y ∈ L, y ≤ 0) → L.sum ≤ 0 := by
        intro L hL
        induction L with
        | nil => simp
        | cons a t ih =>
          rw [List.sum_cons]
          exact add_nonpos (hL a List.mem_cons_self) (ih fun y hy => hL y (List.mem_cons_of_mem a hy))
      have : (l.map (P.RootForm (P.root i))).sum ≤ 0 :=
        key _ fun y hy => by
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
          exact hne z hz
      rw [← hsum, ← hi] at this
      exact absurd hpos (not_lt.2 this)
    have hxR := hlR x hxl
    obtain ⟨j, hj⟩ := hR hxR
    by_cases hij : i = j
    · rw [← hi, hij, hj]; exact hxR
    · have hsub : P.root i - P.root j ∈ range P.root :=
        P.root_sub_root_mem_of_pairingIn_pos (pairingIn_pos_of_rootForm_pos P (hj ▸ hx)) hij
      have herase : x + (l.erase x).sum = l.sum := List.sum_erase hxl
      have hlen : (l.erase x).length < n := by
        rw [List.length_erase_of_mem hxl, ← hl]
        exact Nat.sub_lt (List.length_pos_of_mem hxl) one_pos
      have hdiff : (l.erase x).sum = P.root i - P.root j := by
        rw [hj, hi, ← herase]; abel
      have hmem : (l.erase x).sum ∈ R :=
        ih _ hlen _ rfl (fun y hy => hlR y (List.mem_of_mem_erase hy)) (hdiff ▸ hsub)
      have := hcl _ hmem x hxR (by rw [add_comm, herase, ← hi]; exact ⟨i, rfl⟩)
      rwa [add_comm, herase] at this
  · intro hst α hα β hβ hαβ
    rw [← hst]
    exact ⟨AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure hα)
      (AddSubmonoid.subset_closure hβ), hαβ⟩

/-- `lem:closed-stable` in the repository's form `Rooted.IsStableElt`. -/
theorem closed_iff_isStableElt {R : Set M} (hR : R ⊆ range P.root) :
    IsClosedIn (range P.root) R ↔ Rooted.IsStableElt (range P.root) R :=
  (closed_iff_stable P hR).trans ⟨fun h => ⟨hR, h⟩, fun h => h.2⟩

end ClosedStable

/-! ### Combinatorial core of Theorem `thm:torsion-primes` -/

section Core

variable {M : Type*} [AddCommGroup M] {W : Type*} [Group W] [DistribMulAction W M]

variable (W M) in
/-- The action of `W` on `M` as additive endomorphisms. -/
def actOf : W → M →+ M := fun w =>
  { toFun := fun m => w • m, map_zero' := smul_zero w, map_add' := smul_add w }

@[simp] lemma actOf_apply (w : W) (m : M) : actOf M W w m = w • m := rfl

variable (M) in
/-- The **Weyl magnet** `Z_w = (1 - w)M` (`Rooted.weylMagnet`). -/
abbrev Z (w : W) : AddSubmonoid M := Rooted.weylMagnet (actOf M W w)

lemma mem_Z {w : W} {z : M} : z ∈ Z M w ↔ ∃ x, x - w • x = z := by
  simp only [Z, Rooted.weylMagnet, AddMonoidHom.mem_mrange, AddMonoidHom.sub_apply,
    AddMonoidHom.id_apply, actOf_apply]

lemma sub_mem_Z (w : W) (x : M) : x - w • x ∈ Z M w := mem_Z.2 ⟨x, rfl⟩

lemma neg_mem_Z {w : W} {x : M} (hx : x ∈ Z M w) : -x ∈ Z M w := Rooted.neg_mem_weylMagnet hx

lemma Z_one : Z M (1 : W) = ⊥ := by
  ext z
  rw [mem_Z, AddSubmonoid.mem_bot]
  exact ⟨fun ⟨x, hx⟩ => by rw [← hx, one_smul, sub_self], fun h => ⟨0, by rw [h, smul_zero, sub_self]⟩⟩

/-- `(1 - v)M ⊆ Z_w ↔ Z_v ⊆ Z_w`. -/
lemma weylIn_iff {v w : W} : WeylIn (Z M w) v ↔ Z M v ≤ Z M w :=
  ⟨fun h z hz => by obtain ⟨x, rfl⟩ := mem_Z.1 hz; exact h x, fun h m => h (sub_mem_Z v m)⟩

variable (M) in
/-- `Z_w` as an additive subgroup. -/
def ZG (w : W) : AddSubgroup M := { Z M w with neg_mem' := fun hx => neg_mem_Z hx }

lemma mem_ZG {w : W} {x : M} : x ∈ ZG M w ↔ x ∈ Z M w := Iff.rfl

/-- `R_w = Φ ∩ Z_w`. -/
def Rw (Φ : Set M) (w : W) : Set M := (Z M w : Set M) ∩ Φ

/-- `W(R)`, the subgroup generated by the reflections `s_α`, `α ∈ R`. -/
def reflGroup (refl : M → W) (R : Set M) : Subgroup W := Subgroup.closure (refl '' R)

lemma reflGroup_mono {refl : M → W} {R R' : Set M} (h : R ⊆ R') :
    reflGroup refl R ≤ reflGroup refl R' :=
  Subgroup.closure_mono (image_mono h)

lemma reflGroup_empty (refl : M → W) : reflGroup refl (∅ : Set M) = ⊥ := by
  simp [reflGroup]

/-- `weylMagnetLower ≤ Z_w`. -/
lemma weylMagnetLower_le (Φ : Set M) (w : W) :
    Rooted.weylMagnetLower Φ (actOf M W) w ≤ Z M w :=
  sup_le (AddSubmonoid.closure_le.2 inter_subset_left) (iSup₂_le fun _ hv => le_of_lt hv)

/-- `Σ_{i<n} w^i (y - w y) = y - w^n y`. -/
lemma sum_pow_smul_sub (w : W) (y : M) (n : ℕ) :
    ∑ i ∈ Finset.range n, w ^ i • (y - w • y) = y - w ^ n • y := by
  have h := Finset.sum_range_sub' (fun i => w ^ i • y) n
  simp only [pow_zero, one_smul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_sub, smul_smul, ← pow_succ]

lemma sub_pow_smul_mem_Z (w : W) (x : M) (i : ℕ) : x - w ^ i • x ∈ Z M w := by
  induction i with
  | zero => rw [pow_zero, one_smul, sub_self]; exact zero_mem _
  | succ i ih =>
    have e : x - w ^ (i + 1) • x = (x - w ^ i • x) + (w ^ i • x - w • (w ^ i • x)) := by
      rw [smul_smul, ← pow_succ']; abel
    rw [e]; exact add_mem ih (sub_mem_Z w _)

/-- **The torsion of `M/Z_w` is killed by the order of `w`** (first paragraph of the proof of
`thm:torsion-primes`; `M` torsion-free): if `n x ∈ Z_w` with `n ≠ 0`, then `ord(w) x ∈ Z_w`. -/
theorem orderOf_smul_mem_Z [IsAddTorsionFree M] (w : W) {n : ℕ} (hn : n ≠ 0) {x : M}
    (hx : n • x ∈ Z M w) : orderOf w • x ∈ Z M w := by
  obtain ⟨y, hy⟩ := mem_Z.1 hx
  have hN : ∑ i ∈ Finset.range (orderOf w), w ^ i • x = 0 := by
    have h := sum_pow_smul_sub w y (orderOf w)
    rw [pow_orderOf_eq_one, one_smul, sub_self, hy] at h
    have e : ∀ i, w ^ i • (n • x) = n • (w ^ i • x) := fun i => smul_comm _ _ _
    simp only [e] at h
    rw [← Finset.smul_sum] at h
    exact (nsmul_eq_zero_iff_right hn).1 h
  have e : orderOf w • x = ∑ i ∈ Finset.range (orderOf w), (x - w ^ i • x) := by
    rw [Finset.sum_sub_distrib, hN, sub_zero, Finset.sum_const, Finset.card_range]
  rw [e]
  exact AddSubmonoid.sum_mem _ fun i _ => sub_pow_smul_mem_Z w x i

/-- If `w^N = 1` and `n x ∈ Z_w` (`n ≠ 0`), then `N x ∈ Z_w`. -/
lemma nsmul_mem_Z_of_pow_eq_one [IsAddTorsionFree M] {w : W} {N : ℕ} (hw : w ^ N = 1)
    {n : ℕ} (hn : n ≠ 0) {x : M} (hx : n • x ∈ Z M w) : N • x ∈ Z M w := by
  obtain ⟨c, hc⟩ := orderOf_dvd_of_pow_eq_one hw
  rw [hc, mul_comm, mul_smul]
  exact AddSubmonoid.nsmul_mem _ (orderOf_smul_mem_Z w hn hx) c

/-- Bézout in `Z_w`. -/
lemma mem_Z_of_coprime {w : W} {a b : ℕ} (hab : Nat.Coprime a b) {x : M}
    (ha : a • x ∈ Z M w) (hb : b • x ∈ Z M w) : x ∈ Z M w := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have e : x = u • ((a : ℤ) • x) + v • ((b : ℤ) • x) := by
    rw [← mul_smul, ← mul_smul, ← add_smul, huv, one_smul]
  rw [e, natCast_zsmul, natCast_zsmul]
  exact (ZG M w).add_mem ((ZG M w).zsmul_mem ha u) ((ZG M w).zsmul_mem hb v)

/-- A vector of `Z_w` fixed by `w` (`w^n = 1`, `n ≠ 0`) is `0`: `V^w ∩ (1 - w)V = 0`. -/
lemma eq_zero_of_mem_Z_of_fixed [IsAddTorsionFree M] {w : W} {n : ℕ} (hw : w ^ n = 1)
    (hn : n ≠ 0) {ρ : M} (hρ : ρ ∈ Z M w) (hfix : w • ρ = ρ) : ρ = 0 := by
  obtain ⟨y, rfl⟩ := mem_Z.1 hρ
  have h := sum_pow_smul_sub w y n
  rw [hw, one_smul, sub_self] at h
  have e : ∀ i, w ^ i • (y - w • y) = y - w • y := by
    intro i
    induction i with
    | zero => rw [pow_zero, one_smul]
    | succ i ih => rw [pow_succ', mul_smul, ih, hfix]
  simp only [e, Finset.sum_const, Finset.card_range] at h
  exact (nsmul_eq_zero_iff_right hn).1 h

section Refl

variable {Φ : Set M} {refl : M → W}
  (hrefl : ∀ α ∈ Φ, ∀ m : M, m - refl α • m ∈ AddSubgroup.zmultiples α)
include hrefl

/-- `(1 - w)M ⊆ ℤR` for `w ∈ W(R)`. -/
lemma sub_mem_closure_of_mem_reflGroup {R : Set M} (hRΦ : R ⊆ Φ) {w : W}
    (hw : w ∈ reflGroup refl R) (m : M) : m - w • m ∈ AddSubgroup.closure R :=
  sub_mem_of_mem_closure (fun s hs m => by
    obtain ⟨α, hα, rfl⟩ := hs
    exact AddSubgroup.zmultiples_le_of_mem (AddSubgroup.subset_closure hα) (hrefl α (hRΦ hα) m))
    hw m

/-- **Direction (i), key step.** If `w ∈ W(R_w)` then `Z_w = ℤR_w`, so `Z_w` is redundant. -/
theorem mem_reflGroup_redundant (hneg : ∀ α ∈ Φ, -α ∈ Φ) {w : W}
    (hw : w ∈ reflGroup refl (Rw Φ w)) :
    Z M w = Rooted.weylMagnetLower Φ (actOf M W) w := by
  refine le_antisymm (fun z hz => ?_) (weylMagnetLower_le Φ w)
  obtain ⟨x, rfl⟩ := mem_Z.1 hz
  have h1 := sub_mem_closure_of_mem_reflGroup hrefl inter_subset_right hw x
  have h2 := SLSp.mem_closure_of_symm (S := Rw Φ w)
    (fun y hy => ⟨neg_mem_Z hy.1, hneg y hy.2⟩) h1
  exact (le_sup_left : AddSubmonoid.closure (Rw Φ w) ≤ _) h2

/-- **Direction (i).** A non-redundant `Z_w` has `w ∉ W(R_w)`. -/
theorem not_mem_reflGroup_of_nonredundant (hneg : ∀ α ∈ Φ, -α ∈ Φ) {w : W}
    (hne : Z M w ≠ Rooted.weylMagnetLower Φ (actOf M W) w) : w ∉ reflGroup refl (Rw Φ w) :=
  fun hw => hne (mem_reflGroup_redundant hrefl hneg hw)

variable [Finite W]

/-- `W(R_w) ⊆ C_w`. -/
lemma reflGroup_le_weylPart (w : W) : reflGroup refl (Rw Φ w) ≤ weylPart (W := W) (Z M w) :=
  closure_le_weylPart (Z := AddSubgroup.closure (Rw Φ w))
    (fun z hz => (AddSubgroup.closure_le (ZG M w)).2 (fun _ hx => hx.1) hz)
    (fun s hs m => by
      obtain ⟨α, hα, rfl⟩ := hs
      exact AddSubgroup.zmultiples_le_of_mem (AddSubgroup.subset_closure hα)
        (hrefl α hα.2 m))

end Refl

variable [Finite W] {Φ : Set M} {refl : M → W}

section Normal

variable (hΦW : ∀ (v : W) α, α ∈ Φ → v • α ∈ Φ)
  (hconj : ∀ (v : W) α, α ∈ Φ → v * refl α * v⁻¹ = refl (v • α))
include hΦW hconj

/-- `W(R_w)` is normal in `C_w` (`v s_α v⁻¹ = s_{vα}`). -/
lemma reflGroup_conj_mem (w : W) :
    ∀ v ∈ weylPart (W := W) (Z M w), ∀ u ∈ reflGroup refl (Rw Φ w),
      v * u * v⁻¹ ∈ reflGroup refl (Rw Φ w) :=
  closure_normal_in_weylPart fun v hv s hs => by
    obtain ⟨α, hα, rfl⟩ := hs
    exact ⟨v • α, ⟨weylPart_smul_mem hv hα.1, hΦW v α hα.2⟩, (hconj v α hα.2).symm⟩

lemma normal_subgroupOf (w : W) :
    ((reflGroup refl (Rw Φ w)).subgroupOf (weylPart (W := W) (Z M w))).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using reflGroup_conj_mem hΦW hconj w g g.2 n hn⟩

/-- If every prime dividing `[C_w : W(R_w)]` is `p`, then `C_w/W(R_w)` is a `p`-group: every
`v ∈ C_w` has `v^{p^k} ∈ W(R_w)` for some `k`. -/
lemma pow_mem_of_unique_prime {p : ℕ} (w : W)
    (hq : ∀ q, q.Prime → q ∣ (reflGroup refl (Rw Φ w)).relIndex (weylPart (W := W) (Z M w)) → q = p) :
    ∀ v ∈ weylPart (W := W) (Z M w), ∃ k, v ^ (p ^ k) ∈ reflGroup refl (Rw Φ w) := by
  intro v hv
  set H := reflGroup refl (Rw Φ w)
  set C := weylPart (W := W) (Z M w)
  have := normal_subgroupOf hΦW hconj w
  have hpos : (H.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hk := Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun hd hdd => hq _ hd hdd)
  refine ⟨(H.subgroupOf C).index.primeFactorsList.length, ?_⟩
  have h1 : ((⟨v, hv⟩ : C) : C ⧸ H.subgroupOf C) ^ Nat.card (C ⧸ H.subgroupOf C) = 1 :=
    pow_card_eq_one'
  have hc : Nat.card (C ⧸ H.subgroupOf C) = (H.subgroupOf C).index := rfl
  rw [hc, hk, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

/-- **Direction (i), quotient step.** If `v ∈ C_w \ W(R_w)` has `p`-power order, then `p`
divides `[C_w : W(R_w)]`. -/
lemma prime_dvd_relIndex {p : ℕ} (hp : p.Prime) (w : W) {v : W} (hv : v ∈ weylPart (W := W) (Z M w))
    (hvH : v ∉ reflGroup refl (Rw Φ w)) {n : ℕ} (hvn : v ^ (p ^ n) = 1) :
    p ∣ (reflGroup refl (Rw Φ w)).relIndex (weylPart (W := W) (Z M w)) := by
  set H := reflGroup refl (Rw Φ w)
  set C := weylPart (W := W) (Z M w)
  have := normal_subgroupOf hΦW hconj w
  set g : C ⧸ H.subgroupOf C := ((⟨v, hv⟩ : C) : C ⧸ H.subgroupOf C)
  have hg1 : g ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact hvH
  have hgp : g ^ (p ^ n) = 1 := by
    have : (⟨v, hv⟩ : C) ^ (p ^ n) = 1 := Subtype.ext (by simp [hvn])
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  obtain ⟨j, -, hord⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hgp)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hord
    exact hg1 hord
  have hdvd : orderOf g ∣ Nat.card (C ⧸ H.subgroupOf C) := orderOf_dvd_natCard g
  rw [hord] at hdvd
  exact (dvd_pow_self p hj0).trans hdvd

end Normal

variable (Φ refl) in
/-- `Z_w` is a **`p`-candidate**: `w` has `p`-power order and `w ∉ W(R_w)`. -/
def IsCand (p : ℕ) (w : W) : Prop :=
  (∃ n, w ^ (p ^ n) = 1) ∧ w ∉ reflGroup refl (Rw Φ w)

/-- The positive roots `R_w^+ = {β ∈ R_w | f β > 0}` cut out by `f`. -/
def posRoots (Φ : Set M) (w : W) (f : M →+ ℤ) : Set M := {β | β ∈ Rw Φ w ∧ 0 < f β}

variable (Φ refl) in
/-- **Positive systems, transitivity.** A positive system `R_w^+ = {β ∈ R_w | f β > 0}` of
`R_w` (`f` nonzero on `R_w`) such that every coset `v W(R_w)`, `v ∈ C_w`, contains an element
mapping `R_w^+` into itself: `W(R_w)` acts transitively on the positive systems of `R_w`
(Bourbaki, Lie VI §1 no. 5 Thm 2; Humphreys, *Reflection groups and Coxeter groups*, 1.8),
applied to the positive system `v⁻¹ R_w^+` (`v` stabilizes `R_w`). Proved in
`posSystemExists`. -/
def PosSystemExists (w : W) : Prop :=
  ∃ f : M →+ ℤ, (∀ β ∈ Rw Φ w, f β ≠ 0) ∧
    ∀ v ∈ weylPart (W := W) (Z M w), ∃ u ∈ reflGroup refl (Rw Φ w),
      MapsTo (fun β => (v * u) • β) (posRoots Φ w f) (posRoots Φ w f)

/-- **A regular element.** If `B α α ≠ 0` for `α` in a finite set `S`, some `λ` has
`B α λ ≠ 0` for all `α ∈ S`. -/
lemma exists_regular (B : LinearMap.BilinForm ℤ M) (S : Finset M)
    (hS : ∀ α ∈ S, B α α ≠ 0) : ∃ l : M, ∀ α ∈ S, B α l ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert γ S hγ ih =>
    obtain ⟨l, hl⟩ := ih fun α hα => hS α (Finset.mem_insert_of_mem hα)
    by_cases h : B γ l = 0
    · -- `λ' = N λ + γ` with `N > Σ_{β ∈ S} |B β γ|`
      have hN1 : (1 : ℤ) ≤ 1 + ∑ β ∈ S, |B β γ| :=
        le_add_of_nonneg_right (Finset.sum_nonneg fun β _ => abs_nonneg _)
      refine ⟨(1 + ∑ β ∈ S, |B β γ|) • l + γ, fun α hα => ?_⟩
      rw [map_add, map_zsmul, smul_eq_mul]
      rcases Finset.mem_insert.1 hα with rfl | hα
      · rw [h, mul_zero, zero_add]; exact hS α (Finset.mem_insert_self _ _)
      · have hle : |B α γ| ≤ ∑ β ∈ S, |B β γ| :=
          Finset.single_le_sum (f := fun β => |B β γ|) (fun β _ => abs_nonneg _) hα
        have ha : 1 ≤ |B α l| := Int.one_le_abs (hl α hα)
        intro h0
        have e : B α γ = -((1 + ∑ β ∈ S, |B β γ|) * B α l) := by linarith
        have habs : |B α γ| = (1 + ∑ β ∈ S, |B β γ|) * |B α l| := by
          rw [e, abs_neg, abs_mul, abs_of_pos (by linarith)]
        nlinarith
    · exact ⟨l, fun α hα => by
        rcases Finset.mem_insert.1 hα with rfl | hα
        · exact h
        · exact hl α hα⟩

/-- **Positive systems: `W(R_w)` is transitive on them** (`PosSystemExists`), for `Φ` finite and
`W`-stable, with a bilinear form `B` positive on `Φ` such that `s_α x = x - c α` with
`(α, α) c = 2 (α, x)` (the invariant form of a root datum, `rootForm_self_mul_coroot`).

Proof: take `λ` regular (`B β λ ≠ 0` for `β ∈ Φ`, `exists_regular`) and `f = B(·, λ)`. Given
`v ∈ C_w`, choose `u ∈ W(R_w)` maximizing `B(v u λ, λ)`. For `γ ∈ R_w^+`,
`B(v u s_γ λ, λ) = B(v u λ, λ) - c B(v u γ, λ)` with `c > 0` (as `(γ,γ) c = 2 B(γ, λ) > 0`), so
maximality gives `B(v u γ, λ) ≥ 0`, and `> 0` by regularity: `v u` maps `R_w^+` into itself. -/
theorem posSystemExists (B : LinearMap.BilinForm ℤ M)
    (hΦW : ∀ (v : W) α, α ∈ Φ → v • α ∈ Φ) (hΦfin : Φ.Finite)
    (hBpos : ∀ α ∈ Φ, 0 < B α α)
    (hBrefl : ∀ α ∈ Φ, ∀ x : M, ∃ c : ℤ, x - refl α • x = c • α ∧ B α α * c = 2 * B α x)
    (w : W) : PosSystemExists Φ refl w := by
  classical
  obtain ⟨l, hl⟩ := exists_regular B hΦfin.toFinset
    (fun α hα => (hBpos α ((Set.Finite.mem_toFinset _).1 hα)).ne')
  have hl' : ∀ α ∈ Φ, B α l ≠ 0 := fun α hα => hl α ((Set.Finite.mem_toFinset _).2 hα)
  have hrefl : ∀ α ∈ Φ, ∀ m : M, m - refl α • m ∈ AddSubgroup.zmultiples α := fun α hα m => by
    obtain ⟨c, hc, -⟩ := hBrefl α hα m
    rw [hc]; exact ⟨c, rfl⟩
  refine ⟨(B.flip l).toAddMonoidHom, fun β hβ => hl' β hβ.2, fun v hv => ?_⟩
  obtain ⟨u, huH, hmax⟩ := Set.exists_max_image (reflGroup refl (Rw Φ w) : Set W)
    (fun u => B ((v * u) • l) l) (Set.toFinite _) ⟨1, (reflGroup refl (Rw Φ w)).one_mem⟩
  refine ⟨u, huH, fun β hβ => ?_⟩
  have hvu : v * u ∈ weylPart (W := W) (Z M w) :=
    mul_mem hv (reflGroup_le_weylPart hrefl w huH)
  refine ⟨⟨weylPart_smul_mem hvu hβ.1.1, hΦW _ _ hβ.1.2⟩, ?_⟩
  show 0 < B ((v * u) • β) l
  obtain ⟨c, hc, hcB⟩ := hBrefl β hβ.1.2 l
  have hβpos : 0 < B β l := hβ.2
  have hββ := hBpos β hβ.1.2
  have hc0 : 0 < c := by
    by_contra hle
    push Not at hle
    nlinarith
  have hs : refl β ∈ reflGroup refl (Rw Φ w) := Subgroup.subset_closure ⟨β, hβ.1, rfl⟩
  have hle := hmax (u * refl β) ((reflGroup refl (Rw Φ w)).mul_mem huH hs)
  have hsl : refl β • l = l - c • β := by rw [← hc]; abel
  have hzs : (v * u) • (c • β) = c • ((v * u) • β) := by
    have := map_zsmul (actOf M W (v * u)) c β
    simpa only [actOf_apply] using this
  have e : (v * (u * refl β)) • l = (v * u) • l - c • ((v * u) • β) := by
    rw [← mul_assoc, mul_smul, hsl, smul_sub, hzs]
  rw [e, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hle
  have hnn : 0 ≤ B ((v * u) • β) l := by nlinarith
  exact lt_of_le_of_ne hnn (hl' _ (hΦW _ _ hβ.1.2)).symm

/-- A minimal `p`-candidate exists as soon as a `p`-candidate exists (`W` finite). -/
lemma exists_min_cand {p : ℕ} (h : ∃ w, IsCand Φ refl p w) :
    ∃ w, IsCand Φ refl p w ∧ ∀ v, IsCand Φ refl p v → Z M v ≤ Z M w → Z M v = Z M w := by
  obtain ⟨w, hw, hmin⟩ := Set.Finite.exists_minimalFor (fun w => Z M w)
    {w | IsCand Φ refl p w} (Set.toFinite _) h
  exact ⟨w, hw, fun v hv hle => le_antisymm hle (hmin hv hle)⟩

section Steps

variable (hrefl : ∀ α ∈ Φ, ∀ m : M, m - refl α • m ∈ AddSubgroup.zmultiples α)
  (hneg : ∀ α ∈ Φ, -α ∈ Φ)
include hrefl hneg

/-- **Step A** of direction (ii). Let `Z_w` be a minimal `p`-candidate, and assume that
`C_v/W(R_v)` is a `p`-group for every `p`-candidate `Z_v`. Then `R_w = ∅`.

`hpos` (transitivity of `W(R_w)` on positive systems) is proved in `posSystemExists`. It gives
`g ∈ w W(R_w)` preserving `R_w^+`; `w' = g^m`, with `m` the prime-to-`p` part of the order of `g`,
has `p`-power order, lies outside `W(R_w)` (`g^{p^k} ∈ W(R_w)` and Bézout) and preserves `R_w^+`.
Minimality gives `Z_{w'} = Z_w`, and `ρ = Σ R_w^+ ∈ Z_{w'}` is fixed by `w'`, so `ρ = 0` and
`R_w = ∅`. (Uniqueness in simple transitivity is not needed.) -/
theorem stepA [IsAddTorsionFree M] {p : ℕ} (hp : p.Prime) (hΦfin : Φ.Finite)
    (hpg : ∀ v, IsCand Φ refl p v → ∀ u ∈ weylPart (W := W) (Z M v),
      ∃ k, u ^ (p ^ k) ∈ reflGroup refl (Rw Φ v))
    {w : W} (hw : IsCand Φ refl p w) (hpos : PosSystemExists Φ refl w)
    (hmin : ∀ v, IsCand Φ refl p v → Z M v ≤ Z M w → Z M v = Z M w) : Rw Φ w = ∅ := by
  classical
  obtain ⟨f, hf0, hST1⟩ := hpos
  have hwC : w ∈ weylPart (W := W) (Z M w) := weylIn_iff.2 le_rfl
  obtain ⟨u, huH, hmaps⟩ := hST1 w hwC
  have hgC : w * u ∈ weylPart (W := W) (Z M w) :=
    mul_mem hwC (reflGroup_le_weylPart hrefl w huH)
  have hgH : w * u ∉ reflGroup refl (Rw Φ w) := fun h => hw.2 (by
    have := (reflGroup refl (Rw Φ w)).mul_mem h (inv_mem huH)
    rwa [mul_inv_cancel_right] at this)
  have hpowmaps : ∀ k, MapsTo (fun β => ((w * u) ^ k) • β) (posRoots Φ w f) (posRoots Φ w f) := by
    intro k
    induction k with
    | zero => intro β hβ; simpa using hβ
    | succ k ih =>
      intro β hβ
      show (w * u) ^ (k + 1) • β ∈ _
      rw [pow_succ, mul_smul]
      exact ih (hmaps hβ)
  -- `w' = (w u)^m`, `m` the prime-to-`p` part of the order of `w u`
  obtain ⟨k, hk⟩ := hpg w hw (w * u) hgC
  obtain ⟨e, m, hpm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (w * u)).ne' p hp.one_lt.ne'
  have hw'ord : ((w * u) ^ m) ^ (p ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hw'H : (w * u) ^ m ∉ reflGroup refl (Rw Φ w) := by
    intro h1
    have hcop : Nat.Coprime m (p ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm))
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have hdec : w * u = ((w * u) ^ m) ^ a * ((w * u) ^ (p ^ k)) ^ b := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
        mul_comm (m : ℤ) a, mul_comm _ b, hab, zpow_one]
    exact hgH (by
      rw [hdec]
      exact (reflGroup refl (Rw Φ w)).mul_mem ((reflGroup refl (Rw Φ w)).zpow_mem h1 a)
        ((reflGroup refl (Rw Φ w)).zpow_mem hk b))
  have hw'C : (w * u) ^ m ∈ weylPart (W := W) (Z M w) := pow_mem hgC m
  have hmaps' := hpowmaps m
  have hZle : Z M ((w * u) ^ m) ≤ Z M w := weylIn_iff.1 hw'C
  have hcand' : IsCand Φ refl p ((w * u) ^ m) :=
    ⟨⟨e, hw'ord⟩, fun hmem => hw'H (reflGroup_mono (R := Rw Φ ((w * u) ^ m)) (R' := Rw Φ w)
      (fun β hβ => ⟨hZle hβ.1, hβ.2⟩) hmem)⟩
  have hZeq := hmin _ hcand' hZle
  -- `ρ = Σ_{β ∈ R_w^+} β`
  have hRpfin : (posRoots Φ w f).Finite := hΦfin.subset fun β hβ => hβ.1.2
  set S := hRpfin.toFinset
  have hperm : ∑ β ∈ S, ((w * u) ^ m) • β = ∑ β ∈ S, β := by
    have himg : S.image (fun β => ((w * u) ^ m) • β) = S := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_)
        (Finset.card_image_of_injective S (MulAction.injective ((w * u) ^ m))).ge
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hx
      rw [Set.Finite.mem_toFinset] at hβ ⊢
      exact hmaps' hβ
    have := Finset.sum_image (f := fun x => x) (s := S) (g := fun β => ((w * u) ^ m) • β)
      (fun x _ y _ h => MulAction.injective ((w * u) ^ m) h)
    rw [himg] at this
    exact this.symm
  have hρfix : ((w * u) ^ m) • ∑ β ∈ S, β = ∑ β ∈ S, β := by rw [Finset.smul_sum]; exact hperm
  have hρZ : ∑ β ∈ S, β ∈ Z M ((w * u) ^ m) := by
    rw [hZeq]
    exact AddSubmonoid.sum_mem _ fun β hβ => ((Set.Finite.mem_toFinset _).1 hβ).1.1
  have hρ0 := eq_zero_of_mem_Z_of_fixed hw'ord (pow_ne_zero e hp.ne_zero) hρZ hρfix
  have hS : S = ∅ := by
    by_contra hne
    have hfpos : 0 < f (∑ β ∈ S, β) := by
      rw [map_sum]
      exact Finset.sum_pos (fun β hβ => ((Set.Finite.mem_toFinset _).1 hβ).2)
        (Finset.nonempty_iff_ne_empty.2 hne)
    rw [hρ0, map_zero] at hfpos
    exact lt_irrefl 0 hfpos
  ext β
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hβ
  have hβS : β ∉ S := by rw [hS]; simp
  have hnβ : -β ∉ S := by rw [hS]; simp
  rw [Set.Finite.mem_toFinset] at hβS hnβ
  rcases lt_trichotomy (f β) 0 with h | h | h
  · exact hnβ ⟨⟨neg_mem_Z hβ.1, hneg β hβ.2⟩, by rw [map_neg]; omega⟩
  · exact hf0 β hβ h
  · exact hβS ⟨hβ, h⟩

omit hrefl hneg in
/-- **Step B** of direction (ii). If `Z_w` is a minimal `p`-candidate with `R_w = ∅`, then
`C_w` is a `p`-group and `Z_w` is non-redundant (`W` acts faithfully). -/
theorem stepB {p : ℕ} (hfaith : ∀ w : W, (∀ m : M, w • m = m) → w = 1)
    (hpg : ∀ v, IsCand Φ refl p v → ∀ u ∈ weylPart (W := W) (Z M v),
      ∃ k, u ^ (p ^ k) ∈ reflGroup refl (Rw Φ v))
    {w : W} (hw : IsCand Φ refl p w) (hR : Rw Φ w = ∅)
    (hmin : ∀ v, IsCand Φ refl p v → Z M v ≤ Z M w → Z M v = Z M w) :
    Z M w ≠ Rooted.weylMagnetLower Φ (actOf M W) w ∧
      ∀ v ∈ weylPart (W := W) (Z M w), ∃ k, v ^ (p ^ k) = 1 := by
  have hH : reflGroup refl (Rw Φ w) = ⊥ := by rw [hR]; exact reflGroup_empty refl
  have hpgw : ∀ v ∈ weylPart (W := W) (Z M w), ∃ k, v ^ (p ^ k) = 1 := fun v hv => by
    obtain ⟨k, hk⟩ := hpg w hw v hv
    rw [hH, Subgroup.mem_bot] at hk
    exact ⟨k, hk⟩
  refine ⟨fun heq => ?_, hpgw⟩
  have hsmall : ∀ v : W, Z M v < Z M w → Z M v = ⊥ := by
    intro v hlt
    have hvC : v ∈ weylPart (W := W) (Z M w) := weylIn_iff.2 hlt.le
    by_cases hv1 : v = 1
    · rw [hv1]; exact Z_one
    · exfalso
      have hRv : Rw Φ v = ∅ := by
        apply Set.eq_empty_of_subset_empty
        intro β hβ
        have : β ∈ Rw Φ w := ⟨hlt.le hβ.1, hβ.2⟩
        rwa [hR] at this
      have hc : IsCand Φ refl p v :=
        ⟨hpgw v hvC, by rw [hRv, reflGroup_empty, Subgroup.mem_bot]; exact hv1⟩
      exact hlt.ne (hmin v hc hlt.le)
  have hlow : Rooted.weylMagnetLower Φ (actOf M W) w = ⊥ := by
    refine le_antisymm (sup_le ?_ (iSup₂_le fun v hv => (hsmall v hv).le)) bot_le
    rw [AddSubmonoid.closure_le]
    intro x hx
    have : x ∈ Rw Φ w := hx
    rw [hR] at this
    exact this.elim
  rw [hlow] at heq
  apply hw.2
  rw [hfaith w fun m => ?_]
  · exact one_mem _
  · have := sub_mem_Z w m
    rw [heq, AddSubmonoid.mem_bot, sub_eq_zero] at this
    exact this.symm

end Steps

/-- **The power argument.** Let `L ⊆ M` (`L = P^⊥`), `v ∈ W_L = {u | (1 - u)M ⊆ L}` with
`v ∉ W(Φ ∩ L)`, and assume `W_L/W(Φ ∩ L)` is a `p`-group. Then some power of `v` is a
`p`-candidate. -/
theorem exists_candidate_of_levi {p : ℕ} (hp : p.Prime) (L : AddSubmonoid M) {v : W}
    (hvL : WeylIn L v) (hvH : v ∉ reflGroup refl ((L : Set M) ∩ Φ))
    (hpL : ∀ u, WeylIn L u → ∃ k, u ^ (p ^ k) ∈ reflGroup refl ((L : Set M) ∩ Φ)) :
    ∃ w, IsCand Φ refl p w := by
  set H := reflGroup refl ((L : Set M) ∩ Φ)
  obtain ⟨k, hk⟩ := hpL v hvL
  obtain ⟨e, m, hpm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos v).ne' p hp.one_lt.ne'
  refine ⟨v ^ m, ⟨e, ?_⟩, fun hmem => ?_⟩
  · rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  · have hvm : WeylIn L (v ^ m) := (weylPart (W := W) L).pow_mem (mem_weylPart.2 hvL) m
    have hsub : Rw Φ (v ^ m) ⊆ (L : Set M) ∩ Φ := fun β hβ => by
      obtain ⟨x, hx⟩ := mem_Z.1 hβ.1
      exact ⟨hx ▸ hvm x, hβ.2⟩
    have h1 : v ^ m ∈ H := reflGroup_mono hsub hmem
    have hcop : Nat.Coprime m (p ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm))
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have e : v = (v ^ m) ^ a * (v ^ (p ^ k)) ^ b := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
        mul_comm (m : ℤ) a, mul_comm _ b, hab, zpow_one]
    exact hvH (by rw [e]; exact H.mul_mem (H.zpow_mem h1 a) (H.zpow_mem hk b))

/-! ### Theorem `thm:torsion-primes` -/

/-- **Theorem `thm:torsion-primes`.** `p` is a torsion prime iff some non-redundant Weyl magnet
`Z_w` has `w` of `p`-power order; moreover for a torsion prime there is such a `Z_w` with
`Φ ∩ Z_w = ∅` and `W_{Z_w} = C_w` a `p`-group.

Setting: `M = X^*(T)` (torsion-free), `W` the Weyl group acting faithfully (`hfaith`), `Φ` the
roots (finite, `W`-stable, `Φ = -Φ`), `B` a bilinear form with `(α, α) > 0` on roots,
`refl α = s_α` with `s_α x = x - c α`, `(α, α) c = 2 (α, x)` (so `(1 - s_α)M ⊆ ℤα`; for a root
datum `B` is the invariant form `RootForm`, `c = ⟨x, α^∨⟩`), and `v s_α v⁻¹ = s_{vα}`.
`IsTorsionPrime` is Steinberg's notion (Steinberg 1975, Def. 2.1), not
defined here. **Inputs** (classical facts, cited):
* `hSt` — Steinberg 1975, Lemma 2.14(c) (`C_w/W(R_w) ≅ Z_G(T^w)/Z_G(T^w)°`, the roots vanishing
  on `T^w` being `R_w`) and Thm. 2.24 (a prime dividing `|Z_G(S)/Z_G(S)°|` is a torsion prime
  and divides `|π_0(S)|`, here `π_0(T^w)` dual to `tors(M/Z_w)`), with Cauchy's theorem for the
  finite abelian group `tors(M/Z_w)` (a prime divisor `q` of its order gives `x ∉ Z_w`,
  `q x ∈ Z_w`).
* `hLevi` — Steinberg 1975, Thm. 2.28 (a torsion prime `p` gives an elementary abelian
  `p`-subgroup of rank `≤ 3` not in a torus), reduced as in the paper to `P ⊆ T` with `Z_G(P)`
  disconnected, and Lemma 2.14 + Thm. 2.24: for `L = P^⊥`, `W_L/W(Φ ∩ L)` is a nontrivial
  `p`-group (`W_L = {u | (1 - u)M ⊆ L}`, the pointwise stabilizer of `P`).
The transitivity of `W(R_w)` on the positive systems of `R_w` is proved (`posSystemExists`).
The fact that `tors(M/Z_w)` is killed by the order of `w` is proved (`orderOf_smul_mem_Z`). -/
theorem torsion_primes [IsAddTorsionFree M] (IsTorsionPrime : ℕ → Prop) {p : ℕ} (hp : p.Prime)
    (hneg : ∀ α ∈ Φ, -α ∈ Φ) (hΦW : ∀ (v : W) α, α ∈ Φ → v • α ∈ Φ) (hΦfin : Φ.Finite)
    (B : LinearMap.BilinForm ℤ M) (hBpos : ∀ α ∈ Φ, 0 < B α α)
    (hBrefl : ∀ α ∈ Φ, ∀ x : M, ∃ c : ℤ, x - refl α • x = c • α ∧ B α α * c = 2 * B α x)
    (hconj : ∀ (v : W) α, α ∈ Φ → v * refl α * v⁻¹ = refl (v • α))
    (hfaith : ∀ w : W, (∀ m : M, w • m = m) → w = 1)
    (hSt : ∀ (w : W) (q : ℕ), q.Prime →
      q ∣ (reflGroup refl (Rw Φ w)).relIndex (weylPart (W := W) (Z M w)) →
        IsTorsionPrime q ∧ ∃ x : M, x ∉ Z M w ∧ q • x ∈ Z M w)
    (hLevi : IsTorsionPrime p → ∃ (L : AddSubmonoid M) (v : W), WeylIn L v ∧
      v ∉ reflGroup refl ((L : Set M) ∩ Φ) ∧
      ∀ u, WeylIn L u → ∃ k, u ^ (p ^ k) ∈ reflGroup refl ((L : Set M) ∩ Φ)) :
    (IsTorsionPrime p ↔
      ∃ w : W, (∃ n, w ^ (p ^ n) = 1) ∧ Z M w ≠ Rooted.weylMagnetLower Φ (actOf M W) w) ∧
    (IsTorsionPrime p → ∃ w : W, (∃ n, w ^ (p ^ n) = 1) ∧
      Z M w ≠ Rooted.weylMagnetLower Φ (actOf M W) w ∧ Rw Φ w = ∅ ∧
      IsPGroup p (weylPart (W := W) (Z M w))) := by
  have hrefl : ∀ α ∈ Φ, ∀ m : M, m - refl α • m ∈ AddSubgroup.zmultiples α := fun α hα m => by
    obtain ⟨c, hc, -⟩ := hBrefl α hα m
    rw [hc]; exact ⟨c, rfl⟩
  -- `C_v/W(R_v)` is a `p`-group for every `p`-candidate `Z_v`
  have hpg : ∀ v, IsCand Φ refl p v → ∀ u ∈ weylPart (W := W) (Z M v),
      ∃ k, u ^ (p ^ k) ∈ reflGroup refl (Rw Φ v) := by
    intro v ⟨⟨n, hn⟩, _⟩
    refine pow_mem_of_unique_prime hΦW hconj v fun q hq hdvd => ?_
    obtain ⟨-, x, hx, hqx⟩ := hSt v q hq hdvd
    by_contra hne
    have hpx := nsmul_mem_Z_of_pow_eq_one hn hq.ne_zero hqx
    exact hx (mem_Z_of_coprime (Nat.Coprime.pow_right n ((Nat.coprime_primes hq hp).2 hne))
      hqx hpx)
  have hmore : IsTorsionPrime p → ∃ w : W, (∃ n, w ^ (p ^ n) = 1) ∧
      Z M w ≠ Rooted.weylMagnetLower Φ (actOf M W) w ∧ Rw Φ w = ∅ ∧
      IsPGroup p (weylPart (W := W) (Z M w)) := by
    intro ht
    obtain ⟨L, v, hvL, hvH, hpL⟩ := hLevi ht
    obtain ⟨w, hw, hmin⟩ := exists_min_cand (exists_candidate_of_levi hp L hvL hvH hpL)
    have hR := stepA hrefl hneg hp hΦfin hpg hw (posSystemExists B hΦW hΦfin hBpos hBrefl w) hmin
    obtain ⟨hne, hC⟩ := stepB hfaith hpg hw hR hmin
    exact ⟨w, hw.1, hne, hR, fun g => (hC g.1 g.2).imp fun k hk => Subtype.ext (by simpa using hk)⟩
  refine ⟨⟨fun ht => ?_, ?_⟩, hmore⟩
  · obtain ⟨w, hw, hne, -⟩ := hmore ht
    exact ⟨w, hw, hne⟩
  · rintro ⟨w, ⟨n, hn⟩, hne⟩
    have hwH := not_mem_reflGroup_of_nonredundant hrefl hneg hne
    have hwC : w ∈ weylPart (W := W) (Z M w) := weylIn_iff.2 le_rfl
    exact (hSt w p hp (prime_dvd_relIndex hΦW hconj hp w hwC hwH hn)).1

end Core

end AlgMag.Reductive.Torsion

#print axioms AlgMag.Reductive.Torsion.closed_iff_stable
#print axioms AlgMag.Reductive.Torsion.closed_iff_isStableElt
#print axioms AlgMag.Reductive.Torsion.mem_reflGroup_redundant
#print axioms AlgMag.Reductive.Torsion.orderOf_smul_mem_Z
#print axioms AlgMag.Reductive.Torsion.exists_regular
#print axioms AlgMag.Reductive.Torsion.posSystemExists
#print axioms AlgMag.Reductive.Torsion.stepA
#print axioms AlgMag.Reductive.Torsion.stepB
#print axioms AlgMag.Reductive.Torsion.exists_candidate_of_levi
#print axioms AlgMag.Reductive.Torsion.torsion_primes
