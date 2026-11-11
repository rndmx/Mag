/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.SplitReductive
import AlgMag.Reductive.LieAttractor
import AlgMag.Reductive.IdentityComponentRoots
import AlgMag.Rooted.ReductivePure

/-!
# The attractor determines the roots and the Weyl part (Theorem `thm:red-attractors` (i))

* `mem_of_lieSubalgebra_eq` : if `Lie(G^N) = Lie(G^L)` and `α ∈ N` is a root, then `α ∈ L`
  (no root groups needed: an adjoint weight vector of weight `α` lies in `Lie(G^N)`).
* `weylMagnet_le_of_magnetIdeal_eq` : if `G^N = G^L` and `(1 - w)M ⊆ N`, `w ∈ W`, then
  `(1 - w)M ⊆ L` (through `n_w`).
* `attractor_reflects` : the hypothesis `hrefl` of `Rooted.reductiveInput_of_attractors`.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Reductive

open AlgMag.Weyl

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

attribute [local instance] Derivation.adjointComodule in
/-- **Roots part of `thm:red-attractors` (i).** -/
theorem mem_of_lieSubalgebra_eq {N L : Magnet (Additive X)}
    (hNL : (magnetHopfIdeal π N).lieSubalgebra (B := k) =
      (magnetHopfIdeal π L).lieSubalgebra (B := k))
    {α : Additive X} (hα : α ∈ roots π) (hN : α ∈ N) : α ∈ L := by
  by_contra hL
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  set d := Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) x with hd
  have hdN : d ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k) := by
    rw [mem_lieSubalgebra_magnetHopfIdeal_iff]
    intro χ hχ h hh
    exact cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace hx
      (fun e => hχ (by rw [show χ = α from Additive.toMul.injective e]; exact hN)) hh
  rw [hNL, mem_lieSubalgebra_magnetHopfIdeal_iff] at hdN
  apply hx0
  apply (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).injective
  rw [map_zero]
  ext h
  have hh : h ∈ ⨆ β, torusGrading π β := by
    rw [(isInternal_torusGrading π).submodule_iSup_eq_top]; trivial
  induction hh using Submodule.iSup_induction' with
  | mem β y hy =>
    by_cases hβ : β = α
    · subst hβ
      exact hdN _ hL y hy
    · exact cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace hx
        (fun e => hβ (Additive.toMul.injective e)) hy
  | zero => rw [map_zero]; rfl
  | add y z _ _ hy hz => rw [map_add, hy, hz]; simp

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- Equal attractor ideals give equal Lie algebras. -/
lemma lieSubalgebra_eq_of_magnetIdeal_eq {N L : Magnet (Additive X)}
    (h : magnetIdeal (torusGrading π) N = magnetIdeal (torusGrading π) L) :
    (magnetHopfIdeal π N).lieSubalgebra (B := k) = (magnetHopfIdeal π L).lieSubalgebra (B := k) := by
  have : magnetHopfIdeal π N = magnetHopfIdeal π L := by
    apply HopfIdeal.ext; intro x
    rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal, magnetHopfIdeal_toIdeal,
      magnetHopfIdeal_toIdeal, h]
  rw [this]

/-- `n_w ∈ G^N(k)` iff `(1 - w)M ⊆ N`. -/
theorem rep_mem_attractorSubgroup_iff (D : SplitReductiveData π) (w : D.W) (N : Magnet (Additive X)) :
    D.rep w ∈ attractorSubgroup π N k ↔ weylMagnet (w : X ≃* X) ≤ N :=
  mem_attractorSubgroup_iff_weylMagnet_le π D.surjective (D.rep_normalizing w) N

/-- **Weyl part of `thm:red-attractors` (i).** -/
theorem weylMagnet_le_of_magnetIdeal_eq (D : SplitReductiveData π) {N L : Magnet (Additive X)}
    (h : magnetIdeal (torusGrading π) N = magnetIdeal (torusGrading π) L) (w : D.W)
    (hN : weylMagnet (w : X ≃* X) ≤ N) : weylMagnet (w : X ≃* X) ≤ L := by
  rw [← rep_mem_attractorSubgroup_iff D, mem_attractorSubgroup, ← h, ← mem_attractorSubgroup,
    rep_mem_attractorSubgroup_iff D]
  exact hN

/-- The action of `σ ∈ Aut(X)` on `M = Additive X`. -/
def actW (σ : X ≃* X) : Additive X →+ Additive X := MonoidHom.toAdditive σ.toMonoidHom

omit [DecidableEq X] [Module.Finite k (Bialgebra.CotangentSpace k H)] in
lemma joinDense_weylMagnet_eq (σ : X ≃* X) :
    Rooted.weylMagnet (actW σ) = weylMagnet σ := by
  apply le_antisymm
  · rintro _ ⟨χ, rfl⟩
    exact AddSubmonoid.subset_closure ⟨χ, rfl⟩
  · rw [weylMagnet, AddSubmonoid.closure_le]
    rintro _ ⟨χ, rfl⟩
    exact ⟨χ, rfl⟩

/-- **Theorem `thm:red-attractors` (i), as the hypothesis `hrefl` of
`Rooted.reductiveInput_of_attractors`.** -/
theorem attractor_reflects (D : SplitReductiveData π) :
    ∀ N L : AddSubmonoid (Additive X), affineY (torusGrading π) N = affineY (torusGrading π) L →
      (∀ a ∈ roots π, a ∈ N → a ∈ L) ∧
        ∀ w : D.W, Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N →
          Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L := by
  intro N L h
  rw [affineY_eq_iff] at h
  refine ⟨fun a ha hN => mem_of_lieSubalgebra_eq (lieSubalgebra_eq_of_magnetIdeal_eq h) ha hN,
    fun w hw => ?_⟩
  rw [joinDense_weylMagnet_eq] at hw ⊢
  exact weylMagnet_le_of_magnetIdeal_eq D h w hw

omit [DecidableEq X] in
/-- The roots are finite. -/
lemma finite_roots : (roots π).Finite :=
  (Derivation.finite_nontrivialAdjointWeights π).preimage Additive.toMul.injective.injOn

/-- **Theorem `thm:red-rooted`** given `thm:red-attractors` (iii) (`hdet`); (i) is proved above. -/
theorem reductive_joinDense_of_hdet (D : SplitReductiveData π)
    (hdet : ∀ N L : AddSubmonoid (Additive X), L ≤ N → (∀ a ∈ roots π, a ∈ N → a ∈ L) →
      (∀ w : D.W, Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N →
        Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L) →
      affineY (torusGrading π) L = affineY (torusGrading π) N) :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
      (Rooted.reductiveRoot (roots π) fun w : D.W => actW (w : X ≃* X)) :=
  Rooted.reductive_joinDense_of_attractors hdet (attractor_reflects D)

/-- **Theorem `thm:red-classification`, finiteness of `Π(a)`**, given `hdet`. -/
theorem finite_pure_of_hdet (D : SplitReductiveData π)
    (hdet : ∀ N L : AddSubmonoid (Additive X), L ≤ N → (∀ a ∈ roots π, a ∈ N → a ∈ L) →
      (∀ w : D.W, Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N →
        Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L) →
      affineY (torusGrading π) L = affineY (torusGrading π) N) :
    {N | IsPure (affineY (torusGrading π)) N}.Finite :=
  haveI := D.finite
  Rooted.finite_pure hdet (attractor_reflects D) finite_roots

section AlgClosed

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- **`thm:red-attractors` (iii), inclusion `⊇`.** For `k` algebraically closed, a point of
`(G^N)° · n_w` with `w ∈ W_N` lies in `G^N`: `⋃_{w ∈ W_N} K_R n_w ⊆ G^N`. -/
theorem mul_rep_mem_attractorSubgroup (D : SplitReductiveData π) {N : Magnet (Additive X)}
    {g : WithConv (H →ₐ[k] k)} (hg : compIdeal π N ≤ RingHom.ker g.ofConv) (w : D.W)
    (hw : weylMagnet (w : X ≃* X) ≤ N) : g * D.rep w ∈ attractorSubgroup π N k := by
  refine Subgroup.mul_mem _ ?_ ((rep_mem_attractorSubgroup_iff D w N).2 hw)
  rw [mem_attractorSubgroup]
  refine le_trans (fun x hx => ?_) hg
  show compMk π N x = 0
  have hx' : x ∈ (magnetHopfIdeal π N).toIdeal := by rw [magnetHopfIdeal_toIdeal]; exact hx
  show Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx', map_zero]

end AlgClosed

end AlgMag.Reductive

