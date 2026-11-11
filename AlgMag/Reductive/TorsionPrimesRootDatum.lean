/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TorsionPrimes
import AlgMag.Reductive.WeylPartReflections
import AlgMag.Reductive.ComponentsMeetNormalizerProof

/-!
# `sections/torsion.tex` for a split reductive group with a root datum

`D : SplitReductiveData.WithRootDatum π`: `M = Additive X`, `W = D.W`, `Φ = roots π`.
The structural hypotheses of `Torsion.torsion_primes` (`Φ = -Φ`, `W`-stability and finiteness of
`Φ`, the invariant form `RootForm` with `s_α x = x - ⟨x, α^∨⟩ α` and `(α, α)⟨x, α^∨⟩ = 2 (α, x)`,
`v s_α v⁻¹ = s_{vα}`, faithfulness) are discharged from the root datum, and with them the
transitivity of `W(R_w)` on positive systems (`posSystemExists`); the Steinberg inputs `hSt`,
`hLevi` remain hypotheses.

* `closed_iff_stable_rootDatum`: **Lemma `lem:closed-stable`** for `G`.
* `torsion_primes_rootDatum`: **Theorem `thm:torsion-primes`** for `G`.
* `torsion_primes_joinIrreducibles`: the same with "non-redundant" read as "lies in the minimal root"
  (`joinIrreducibles_eq_lattice`, Theorem `thm:red-rooted`).
-/

suppress_compilation

open Set RootPairing Magnetism TauCeti WithConv

namespace AlgMag.Reductive.Torsion

open AlgMag.Reductive

universe u

variable {X : Type u} [CommGroup X]
variable {k : Type u} {H : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [DecidableEq X]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable {π : H →ₐc[k] MonoidAlgebra k X} (D : SplitReductiveData.WithRootDatum π)
set_option linter.unusedSectionVars false

/-- **Lemma `lem:closed-stable`** for `G`: `R ⊆ Φ` is closed iff `[R⟩ ∩ Φ = R`. -/
theorem closed_iff_stable_rootDatum (D : SplitReductiveData.WithRootDatum π) {R : Set (Additive X)} (hR : R ⊆ roots π) :
    IsClosedIn (roots π) R ↔ (AddSubmonoid.closure R : Set (Additive X)) ∩ roots π = R := by
  haveI := D.finite_ι
  haveI := D.crystallographic
  rw [← D.range_root] at hR ⊢
  exact closed_iff_stable D.P hR

open Classical in
/-- The reflection `s_α ∈ W` attached to a root `α` (`1` off the roots). -/
noncomputable def reflM (m : Additive X) : D.W :=
  if h : ∃ i, D.P.root i = m then D.refl h.choose else 1

lemma reflM_root (i : D.ι) : reflM D (D.P.root i) = D.refl i := by
  have h : ∃ j, D.P.root j = D.P.root i := ⟨i, rfl⟩
  rw [reflM, dif_pos h, D.P.root.injective h.choose_spec]

lemma actOf_eq : actOf (Additive X) D.W = fun w : D.W => actW (w : X ≃* X) := by
  funext w; ext m; rfl

lemma roots_neg (D : SplitReductiveData.WithRootDatum π) : ∀ α ∈ roots π, -α ∈ roots π := by
  intro α hα
  rw [← D.range_root] at hα ⊢
  obtain ⟨i, rfl⟩ := hα
  exact D.P.neg_root_mem i

/-- `v α_i = α_j` and `v s_{α_i} v⁻¹ = s_{α_j}`. -/
lemma exists_smul_root (v : D.W) (i : D.ι) :
    ∃ j, D.P.root j = v • D.P.root i ∧ v * D.refl i * v⁻¹ = D.refl j := by
  obtain ⟨g, hg⟩ := D.exists_weylGroup_of_weyl v
  have hginv : ∀ m : Additive X, v⁻¹ • m = ((g : D.P.Aut)⁻¹) • m := by
    intro m
    apply MulAction.injective v
    change v • v⁻¹ • m = v • ((g : D.P.Aut)⁻¹ • m)
    rw [smul_inv_smul, ← hg, smul_inv_smul]
  refine ⟨(g : D.P.Aut).indexEquiv i, by rw [RootPairing.Equiv.root_indexEquiv_eq_smul, hg], ?_⟩
  refine (weyl_ext fun m => ?_).symm
  rw [D.refl_smul, mul_smul, mul_smul, hginv, D.refl_smul, ← hg, D.smul_reflection,
    smul_inv_smul]

/-- **Theorem `thm:torsion-primes`** for `G` (inputs `hSt`, `hLevi` as in
`Torsion.torsion_primes`, which see for the citations). -/
theorem torsion_primes_rootDatum [IsAddTorsionFree (Additive X)] (IsTorsionPrime : ℕ → Prop)
    {p : ℕ} (hp : p.Prime)
    (hSt : ∀ (w : D.W) (q : ℕ), q.Prime →
      q ∣ (reflGroup (reflM D) (Rw (roots π) w)).relIndex (weylPart (W := D.W) (Z (Additive X) w)) →
        IsTorsionPrime q ∧ ∃ x : Additive X, x ∉ Z (Additive X) w ∧ q • x ∈ Z (Additive X) w)
    (hLevi : IsTorsionPrime p → ∃ (L : AddSubmonoid (Additive X)) (v : D.W), WeylIn L v ∧
      v ∉ reflGroup (reflM D) ((L : Set (Additive X)) ∩ roots π) ∧
      ∀ u : D.W, WeylIn L u → ∃ k, u ^ (p ^ k) ∈ reflGroup (reflM D) ((L : Set (Additive X)) ∩ roots π)) :
    (IsTorsionPrime p ↔ ∃ w : D.W, (∃ n, w ^ (p ^ n) = 1) ∧
      Rooted.weylMagnet (actW (w : X ≃* X)) ≠
        Rooted.weylMagnetLower (roots π) (fun w : D.W => actW (w : X ≃* X)) w) ∧
    (IsTorsionPrime p → ∃ w : D.W, (∃ n, w ^ (p ^ n) = 1) ∧
      Rooted.weylMagnet (actW (w : X ≃* X)) ≠
        Rooted.weylMagnetLower (roots π) (fun w : D.W => actW (w : X ≃* X)) w ∧
      (Rooted.weylMagnet (actW (w : X ≃* X)) : Set (Additive X)) ∩ roots π = ∅ ∧
      IsPGroup p (weylPart (W := D.W) (Rooted.weylMagnet (actW (w : X ≃* X))))) := by
  haveI := D.finite_ι
  have hΦW : ∀ (v : D.W) α, α ∈ roots π → v • α ∈ roots π := by
    intro v α hα
    rw [← D.range_root] at hα ⊢
    obtain ⟨i, rfl⟩ := hα
    obtain ⟨j, hj, -⟩ := exists_smul_root D v i
    exact ⟨j, hj⟩
  have hΦfin : (roots π).Finite := D.range_root ▸ Set.finite_range _
  letI := Fintype.ofFinite D.ι
  -- the invariant form `RootForm` of the root datum: `(α, α) > 0`, `(α, α) ⟨x, α^∨⟩ = 2 (α, x)`
  have hBpos : ∀ α ∈ roots π, 0 < D.P.RootForm α α := by
    intro α hα
    rw [← D.range_root] at hα
    obtain ⟨i, rfl⟩ := hα
    exact rootForm_root_self_pos D.P i
  have hBrefl : ∀ α ∈ roots π, ∀ x : Additive X, ∃ c : ℤ,
      x - reflM D α • x = c • α ∧ D.P.RootForm α α * c = 2 * D.P.RootForm α x := by
    intro α hα x
    rw [← D.range_root] at hα
    obtain ⟨i, rfl⟩ := hα
    refine ⟨D.P.coroot' i x, ?_, rootForm_self_mul_coroot D.P i x⟩
    rw [reflM_root, D.refl_smul, reflection_apply, sub_sub_cancel]
  have hconj : ∀ (v : D.W) α, α ∈ roots π → v * reflM D α * v⁻¹ = reflM D (v • α) := by
    intro v α hα
    rw [← D.range_root] at hα
    obtain ⟨i, rfl⟩ := hα
    obtain ⟨j, hj, hc⟩ := exists_smul_root D v i
    rw [reflM_root, ← hj, reflM_root, hc]
  have hfaith : ∀ w : D.W, (∀ m : Additive X, w • m = m) → w = 1 :=
    fun w h => weyl_ext fun m => by rw [h m, one_smul]
  have H := torsion_primes IsTorsionPrime hp (roots_neg D) hΦW hΦfin D.P.RootForm hBpos hBrefl
    hconj hfaith hSt hLevi
  simp only [Z, Rw, actOf_eq] at H
  exact H

/-- Non-redundant Weyl magnets are the Weyl magnets in the minimal root. -/
lemma weylMagnet_mem_joinIrreducibles_iff [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [Monoid.FG X] [IsMulTorsionFree X] (w : D.W) :
    Rooted.weylMagnet (actW (w : X ≃* X)) ∈ Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) ↔
      Rooted.weylMagnet (actW (w : X ≃* X)) ≠
        Rooted.weylMagnetLower (roots π) (fun w : D.W => actW (w : X ≃* X)) w := by
  rw [joinIrreducibles_eq_lattice D]
  constructor
  · rintro (⟨a, ha, hZ⟩ | ⟨w', hZ, hne⟩)
    · exfalso
      have ha' : a ∈ Set.range D.P.root := D.range_root ▸ ha
      have h1 : a ∈ Rooted.weylMagnet (actW (w : X ≃* X)) := hZ ▸ Rooted.mono_le_iff.1 le_rfl
      have h2 : -a ∈ Rooted.mono a := hZ ▸ Rooted.neg_mem_weylMagnet h1
      have h0 := rootPairing_cone D.P ha' a (Rooted.mono_le_iff.1 le_rfl) h2
      exact D.P.zero_notMem_range_root (h0 ▸ ha')
    · simp only [Rooted.weylMagnetLower] at hne ⊢
      rw [hZ]
      exact hne
  · intro hne
    exact Or.inr ⟨w, rfl, hne⟩

/-- **Theorem `thm:torsion-primes`** in minimal-root form: `p` is a torsion prime iff some Weyl
root `Z_w` with `w` of `p`-power order lies in the minimal root of the conjugation action. -/
theorem torsion_primes_joinIrreducibles [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [Monoid.FG X] [IsMulTorsionFree X] (IsTorsionPrime : ℕ → Prop) {p : ℕ} (hp : p.Prime)
    (hSt : ∀ (w : D.W) (q : ℕ), q.Prime →
      q ∣ (reflGroup (reflM D) (Rw (roots π) w)).relIndex (weylPart (W := D.W) (Z (Additive X) w)) →
        IsTorsionPrime q ∧ ∃ x : Additive X, x ∉ Z (Additive X) w ∧ q • x ∈ Z (Additive X) w)
    (hLevi : IsTorsionPrime p → ∃ (L : AddSubmonoid (Additive X)) (v : D.W), WeylIn L v ∧
      v ∉ reflGroup (reflM D) ((L : Set (Additive X)) ∩ roots π) ∧
      ∀ u : D.W, WeylIn L u → ∃ k, u ^ (p ^ k) ∈ reflGroup (reflM D) ((L : Set (Additive X)) ∩ roots π)) :
    IsTorsionPrime p ↔ ∃ w : D.W, (∃ n, w ^ (p ^ n) = 1) ∧
      Rooted.weylMagnet (actW (w : X ≃* X)) ∈ Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) := by
  rw [(torsion_primes_rootDatum D IsTorsionPrime hp hSt hLevi).1]
  exact exists_congr fun w => and_congr_right fun _ => (weylMagnet_mem_joinIrreducibles_iff D w).symm

end AlgMag.Reductive.Torsion

#print axioms AlgMag.Reductive.Torsion.closed_iff_stable_rootDatum
#print axioms AlgMag.Reductive.Torsion.torsion_primes_rootDatum
#print axioms AlgMag.Reductive.Torsion.weylMagnet_mem_joinIrreducibles_iff
#print axioms AlgMag.Reductive.Torsion.torsion_primes_joinIrreducibles
