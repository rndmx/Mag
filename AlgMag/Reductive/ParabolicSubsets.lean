/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ComponentsMeetNormalizerProof
import AlgMag.Reductive.DescentToField

/-!
# Pure magnets containing the basis ↔ subsets of the basis (Theorem 15.16 (iv), magnet part)

`G` split reductive, basis `𝓑 = D.P.root '' D.b.support`. Then `ζ ↦ ℕ𝓑 + ℕ(-ζ)` is a bijection
from the subsets `ζ ⊆ 𝓑` onto the pure magnets containing `𝓑`, with inverse
`N ↦ ξ_N = {α ∈ 𝓑 | -α ∈ N}`.

* `Parabolic.xi_closure_eq`: `ξ_{ℕ𝓑 + ℕ(-ζ)} = ζ` (simple roots are linearly independent);
* `Parabolic.bijOn_std_of_hull`: the bijection, from `E(G^N) = ℕ𝓑 + ℕ(-ξ_N)` for `N ⊇ 𝓑`;
* `parabolic_std_bijOn_lattice` (`k` algebraically closed) and `parabolic_std_bijOn_field`.
-/

suppress_compilation

open Magnetism TauCeti WithConv

namespace AlgMag.Reductive

namespace Parabolic

open scoped Pointwise

/-- **`ξ_{ℕ𝓑 + ℕ(-ζ)} = ζ`** for `ζ ⊆ 𝓑`, `𝓑` the simple roots of a base: compare coefficients of
`α` in the (linearly independent) simple roots. -/
theorem xi_closure_eq {ι M N' : Type*} [AddCommGroup M] [AddCommGroup N']
    {P : RootPairing ι ℤ M N'} (b : P.Base) {ζ : Set M}
    (hζ : ζ ⊆ P.root '' (b.support : Set ι)) :
    xi (P.root '' (b.support : Set ι))
      (AddSubmonoid.closure (P.root '' (b.support : Set ι) ∪ -ζ)) = ζ := by
  classical
  have key : ∀ x ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι) ∪ -ζ), ∃ f : ι → ℤ,
      (∀ i ∈ b.support, 0 ≤ f i ∨ P.root i ∈ ζ) ∧ x = ∑ i ∈ b.support, f i • P.root i := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      rcases hx with ⟨j, hj, rfl⟩ | hx
      · refine ⟨fun i => if i = j then 1 else 0, fun i _ => Or.inl (by dsimp only; split_ifs <;> omega), ?_⟩
        simp [ite_smul, Finset.mem_coe.1 hj]
      · obtain ⟨j, hj, hjx⟩ := hζ (Set.mem_neg.1 hx)
        refine ⟨fun i => if i = j then -1 else 0, fun i _ => ?_, ?_⟩
        · by_cases h : i = j
          · subst h; right; rw [hjx]; exact Set.mem_neg.1 hx
          · left; simp [h]
        · simp [ite_smul, Finset.mem_coe.1 hj, hjx]
    | zero => exact ⟨0, fun _ _ => Or.inl le_rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, hf, rfl⟩ := hx
      obtain ⟨g, hg, rfl⟩ := hy
      refine ⟨f + g, fun i hi => ?_, by simp [add_smul, Finset.sum_add_distrib]⟩
      rcases hf i hi with h | h
      · rcases hg i hi with h' | h'
        · left; simp only [Pi.add_apply]; omega
        · exact Or.inr h'
      · exact Or.inr h
  ext α
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hneg⟩
    have hj' : j ∈ b.support := Finset.mem_coe.1 hj
    obtain ⟨f, hf, hfe⟩ := key _ hneg
    have h0 : ∑ i ∈ b.support, (f i + if i = j then 1 else 0) • P.root i = 0 := by
      simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', hj', ite_true, ← hfe, neg_add_cancel]
    have := linearIndepOn_iff'.1 b.linearIndepOn_root b.support _ subset_rfl h0 j hj'
    simp only [ite_true] at this
    rcases hf j hj' with h | h
    · omega
    · exact h
  · intro hα
    exact ⟨hζ hα, AddSubmonoid.subset_closure (Or.inr (by simpa using hα))⟩

/-- **Bijection `ζ ↦ ℕB + ℕ(-ζ)`** from the subsets of `B` onto the pure magnets containing `B`,
inverse `N ↦ ξ_N`, given the hull formula `E(N) = ℕB + ℕ(-ξ_N)` for `N ⊇ B` and `ξ_{ℕB+ℕ(-ζ)} = ζ`. -/
theorem bijOn_std_of_hull {M α : Type*} [AddCommGroup M] [CompleteLattice α]
    {Y : AddSubmonoid M → α} (hY : AttractorOrder Y) {B : Set M}
    (hull : ∀ N : AddSubmonoid M, B ⊆ N →
      sInf {L | Y L = Y N} = AddSubmonoid.closure (B ∪ -xi B N))
    (hxi : ∀ ζ ⊆ B, xi B (AddSubmonoid.closure (B ∪ -ζ)) = ζ) :
    Set.BijOn (fun ζ : Set M => AddSubmonoid.closure (B ∪ -ζ)) {ζ | ζ ⊆ B}
        {N | IsPure Y N ∧ B ⊆ N} ∧
      Set.InvOn (fun N : AddSubmonoid M => xi B N)
        (fun ζ : Set M => AddSubmonoid.closure (B ∪ -ζ)) {ζ | ζ ⊆ B}
        {N | IsPure Y N ∧ B ⊆ N} := by
  have hinv : Set.InvOn (fun N : AddSubmonoid M => xi B N)
      (fun ζ : Set M => AddSubmonoid.closure (B ∪ -ζ)) {ζ | ζ ⊆ B}
      {N | IsPure Y N ∧ B ⊆ N} := by
    refine ⟨fun ζ hζ => hxi ζ hζ, fun N hN => ?_⟩
    show AddSubmonoid.closure (B ∪ -xi B N) = N
    rw [← hull N hN.2]
    exact hN.1.pureOf_map hY
  refine ⟨hinv.bijOn (fun ζ hζ => ?_) (fun N _ α hα => hα.1), hinv⟩
  set N := AddSubmonoid.closure (B ∪ -ζ)
  have hBN : B ⊆ N := fun α hα => AddSubmonoid.subset_closure (Or.inl hα)
  refine ⟨?_, hBN⟩
  have hNe : pureOf Y (Y N) = N := by
    show sInf {L | Y L = Y N} = N
    rw [hull N hBN, hxi ζ hζ]
  show IsPure Y N
  rw [← hNe]
  exact isPure_pureOf hY ⟨N, rfl⟩

end Parabolic

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}

section Lattice

variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)] [Monoid.FG X] [IsMulTorsionFree X]

/-- **Theorem 15.16 (iv), magnet part** (`k` algebraically closed): `ζ ↦ ℕ𝓑 + ℕ(-ζ)` is a
bijection from the subsets of the basis `𝓑` onto the pure magnets containing `𝓑`, with inverse
`N ↦ ξ_N = {α ∈ 𝓑 | -α ∈ N}`. -/
theorem parabolic_std_bijOn_lattice (D : SplitReductiveData.WithRootDatum π) :
    Set.BijOn
        (fun ζ : Set (Additive X) => AddSubmonoid.closure (D.P.root '' D.b.support ∪ -ζ))
        {ζ | ζ ⊆ D.P.root '' D.b.support}
        {N | IsPure (affineY (torusGrading π)) N ∧ D.P.root '' D.b.support ⊆ N} ∧
      Set.InvOn (fun N : AddSubmonoid (Additive X) => Parabolic.xi (D.P.root '' D.b.support) N)
        (fun ζ : Set (Additive X) => AddSubmonoid.closure (D.P.root '' D.b.support ∪ -ζ))
        {ζ | ζ ⊆ D.P.root '' D.b.support}
        {N | IsPure (affineY (torusGrading π)) N ∧ D.P.root '' D.b.support ⊆ N} :=
  Parabolic.bijOn_std_of_hull (affineY_infPreserving (torusGrading π)).attractorOrder
    (fun _ hBN => red_parabolic_hull_lattice D hBN)
    (fun _ hζ => Parabolic.xi_closure_eq D.b hζ)

end Lattice

section Field

variable [Algebra.FiniteType k H] [Algebra.Smooth k H] [Monoid.FG X] [IsMulTorsionFree X]

/-- **Theorem 15.16 (iv), magnet part**, over any field. -/
theorem parabolic_std_bijOn_field (D : SplitReductiveData.WithRootDatum π) :
    Set.BijOn
        (fun ζ : Set (Additive X) => AddSubmonoid.closure (D.P.root '' D.b.support ∪ -ζ))
        {ζ | ζ ⊆ D.P.root '' D.b.support}
        {N | IsPure (affineY (torusGrading π)) N ∧ D.P.root '' D.b.support ⊆ N} ∧
      Set.InvOn (fun N : AddSubmonoid (Additive X) => Parabolic.xi (D.P.root '' D.b.support) N)
        (fun ζ : Set (Additive X) => AddSubmonoid.closure (D.P.root '' D.b.support ∪ -ζ))
        {ζ | ζ ⊆ D.P.root '' D.b.support}
        {N | IsPure (affineY (torusGrading π)) N ∧ D.P.root '' D.b.support ⊆ N} :=
  Parabolic.bijOn_std_of_hull (affineY_infPreserving (torusGrading π)).attractorOrder
    (fun _ hBN => red_parabolic_hull_field D hBN)
    (fun _ hζ => Parabolic.xi_closure_eq D.b hζ)

end Field

end AlgMag.Reductive

#print axioms AlgMag.Reductive.parabolic_std_bijOn_lattice
#print axioms AlgMag.Reductive.parabolic_std_bijOn_field
