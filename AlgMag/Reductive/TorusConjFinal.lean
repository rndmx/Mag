/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TuStep
import AlgMag.Reductive.BigradedF3
import AlgMag.Reductive.LimitTorus

/-!
# T1-dyn: torus conjugacy in a dynamic parabolic

`exists_unipotent_conjugate_eq_of_isMaximalTorus'`: every maximal torus of `B = P_B(λ)` is
conjugate to the central maximal torus `T` of the Levi by a `k`-point of `U_B(λ)`.
Notes: `equivalence-reductive/T-steps.md`, section T1-dyn.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H] [DecidableEq H]
  [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- **Steps 2–3 of T1-dyn** (`S ∩ U = 1`, `p(S) ⊆ T` by centrality and maximality of `T` in the
Levi): every maximal torus lies in `T · U = T · U_{≥1}`. -/
theorem tuIdeal_one_le' {T : HopfIdeal k H} (h : DynHyp l T) [IsAlgClosed k]
    (S : HopfIdeal k H) (hS : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) S) :
    tuIdeal l T 1 ≤ S.toIdeal := by
  have hsP : ∀ s : WithConv (H →ₐ[k] k), s ∈ parabolic k l := fun g ↦ by
    refine (negativeCoefficientIdeal_le_ker_iff l g).mp ?_
    have : negativeCoefficientIdeal l = (parabolicDefiningHopfIdeal l).toIdeal :=
      (parabolicDefiningHopfIdeal_toIdeal l).symm
    rw [this, h.hP]
    intro x hx
    have : x = 0 := by simpa using hx
    simp [this]
  haveI := isReduced_of_isMaximalTorus S hS
  refine tuIdeal_one_le_of_points l T S fun s hs ↦ ?_
  exact ⟨limit k l ⟨s, hsP s⟩, (limit k l ⟨s, hsP s⟩)⁻¹ * s,
    limit_mem_torus' l h S hS s hs (hsP s), limit_inv_mul_mem_unipotent l ⟨s, hsP s⟩,
    (mul_inv_cancel_left _ _).symm⟩

/-- **T1-dyn.** Let `B = Spec H` be smooth over an algebraically closed field `k`, `λ` a
cocharacter with `P_B(λ) = B`, and `T` a maximal torus through which `λ` factors and which is
central in the Levi `Z_B(λ)`. Then every maximal torus `S` of `B` is conjugate to `T` by a
`k`-point of `U_B(λ)`. Assembled from `tuIdeal_one_le'`, `tuIdeal_step'` and `tuIdeal_eventually`. -/
theorem exists_unipotent_conjugate_eq_of_isMaximalTorus' [IsAlgClosed k]
    (hP : parabolicDefiningHopfIdeal l = ⊥)
    (T : HopfIdeal k H) (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) T)
    (hlT : T.toIdeal ≤ RingHom.ker (l : H →ₐ[k] LaurentPolynomial k))
    (hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv (H →ₐ[k] A)),
      (leviDefiningHopfIdeal l).toIdeal ≤ RingHom.ker (ofConv g) →
      T.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g)
    (S : HopfIdeal k H) (hS : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) S) :
    ∃ u : WithConv (H →ₐ[k] k),
      (BialgHom.unipotentDefiningHopfIdeal l).toIdeal ≤ RingHom.ker (ofConv u) ∧
        S.conjugate u = T := by
  have h : DynHyp l T := ⟨hP, hT, hlT, hcent⟩
  -- induction: for every `n ≥ 1` some `u ∈ U(k)` puts `S` inside `T · U_{≥n}`
  have key : ∀ n, ∃ u : WithConv (H →ₐ[k] k), u ∈ unipotent k l ∧
      tuIdeal l T (n + 1) ≤ (S.conjugate u).toIdeal := by
    intro n
    induction n with
    | zero => exact ⟨1, Subgroup.one_mem _, by simpa using tuIdeal_one_le' l h S hS⟩
    | succ n ih =>
      obtain ⟨u, hu, hle⟩ := ih
      obtain ⟨v, hv, hle'⟩ := tuIdeal_step' h (Nat.succ_pos n) (S.conjugate u) (isMaximalTorus_conjugate' hS u) hle
      refine ⟨v * u, Subgroup.mul_mem _ hv hu, ?_⟩
      rwa [HopfIdeal.conjugate_mul]
  obtain ⟨N, hN⟩ := tuIdeal_eventually l h
  obtain ⟨u, hu, hle⟩ := key N
  have hSu := isMaximalTorus_conjugate' hS u
  have hTS : T ≤ S.conjugate u := by
    intro x hx
    have hx' : x ∈ tuIdeal l T (N + 1) := by rw [hN (N + 1) (Nat.le_succ N)]; exact hx
    exact hle hx'
  refine ⟨u, ?_, le_antisymm (hSu.2 hT.1 hTS) hTS⟩
  rw [BialgHom.unipotentDefiningHopfIdeal_toIdeal]
  exact (BialgHom.unipotentCoefficientIdeal_le_ker_iff l u).mpr hu

end AlgMag.Reductive

#print axioms AlgMag.Reductive.exists_unipotent_conjugate_eq_of_isMaximalTorus'
