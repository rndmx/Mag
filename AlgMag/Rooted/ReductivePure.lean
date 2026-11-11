/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Rooted.ReductiveRooted
import AlgMag.Sec15PureMagnets

/-!
# Theorem `thm:red-pure` from Theorem `thm:red-attractors` (combinatorial step)

Let `Y N` be the attractor of `N`. Assume
* (`hdet`, Theorem `thm:red-attractors` (iii)) `G^N` depends only on `(R(N), W_N)`, in the form:
  `L ≤ N` with the same roots and the same Weyl part have the same attractor;
* (`hrefl`, Theorem `thm:red-attractors` (i)) `G^N = G^L` implies `R(N) ⊆ L` and `W_N ⊆ W_L`.
Then `E(G^N) = [R(N)⟩ + Λ_N` (`reductiveHull`), and the pure-magnet input `ReductiveInput` of
`reductive_joinDense` holds (`reductiveInput_of_attractors`).
-/

namespace AlgMag.Rooted

variable {M : Type*} [AddCommGroup M] {Φ : Set M} {W : Type*} {act : W → M →+ M}
variable {α : Type*} {Y : AddSubmonoid M → α}

lemma reductiveHull_le (N : AddSubmonoid M) : reductiveHull Φ act N ≤ N :=
  sup_le (AddSubmonoid.closure_le.2 Set.inter_subset_left) (iSup₂_le fun _ h => h)

lemma mem_reductiveHull_of_root {N : AddSubmonoid M} {a : M} (ha : a ∈ Φ) (hN : a ∈ N) :
    a ∈ reductiveHull Φ act N :=
  le_sup_left (a := AddSubmonoid.closure ((N : Set M) ∩ Φ)) (AddSubmonoid.subset_closure ⟨hN, ha⟩)

lemma weylMagnet_le_reductiveHull {N : AddSubmonoid M} {w : W} (hw : weylMagnet (act w) ≤ N) :
    weylMagnet (act w) ≤ reductiveHull Φ act N :=
  le_trans (le_iSup₂ (f := fun w (_ : w ∈ {w | weylMagnet (act w) ≤ N}) => weylMagnet (act w)) w hw)
    le_sup_right

variable
  (hdet : ∀ N L : AddSubmonoid M, L ≤ N → (∀ a ∈ Φ, a ∈ N → a ∈ L) →
    (∀ w, weylMagnet (act w) ≤ N → weylMagnet (act w) ≤ L) → Y L = Y N)
  (hrefl : ∀ N L : AddSubmonoid M, Y N = Y L →
    (∀ a ∈ Φ, a ∈ N → a ∈ L) ∧ ∀ w, weylMagnet (act w) ≤ N → weylMagnet (act w) ≤ L)
include hdet hrefl
set_option linter.unusedSectionVars false

/-- `G^{E} = G^N` for `E = [R(N)⟩ + Λ_N`. -/
lemma attractor_reductiveHull (N : AddSubmonoid M) : Y (reductiveHull Φ act N) = Y N :=
  hdet N _ (reductiveHull_le N) (fun _ ha hN => mem_reductiveHull_of_root ha hN)
    (fun _ hw => weylMagnet_le_reductiveHull hw)

/-- `[R(N)⟩ + Λ_N` is contained in every magnet with the attractor of `N`. -/
lemma reductiveHull_le_of_eq {N L : AddSubmonoid M} (h : Y N = Y L) :
    reductiveHull Φ act N ≤ L := by
  obtain ⟨h1, h2⟩ := hrefl N L h
  exact sup_le (AddSubmonoid.closure_le.2 fun a ha => h1 a ha.2 ha.1) (iSup₂_le fun w hw => h2 w hw)

/-- **Theorem `thm:red-pure`.** `E(G^N) = [R(N)⟩ + Λ_N`: it has the attractor of `N` and is the
least such magnet. -/
theorem reductiveHull_eq_pureOf (N : AddSubmonoid M) :
    reductiveHull Φ act N = sInf {L | Y L = Y N} :=
  le_antisymm (le_sInf fun L hL => reductiveHull_le_of_eq hdet hrefl hL.symm)
    (sInf_le (attractor_reductiveHull hdet hrefl N))

/-- **Theorem `thm:red-pure`, consequences**: the input of `reductive_joinDense`. -/
theorem reductiveInput_of_attractors : ReductiveInput (IsPure Y) Φ act where
  pure_iff N := by
    constructor
    · intro hN
      exact le_antisymm (hN _ (attractor_reductiveHull hdet hrefl N).symm) (reductiveHull_le N)
    · intro hN _ hL
      rw [hN]; exact reductiveHull_le_of_eq hdet hrefl hL
  hull_pure N _ hL :=
    reductiveHull_le_of_eq hdet hrefl ((attractor_reductiveHull hdet hrefl N).symm.trans hL)

/-- **Theorem `thm:red-rooted`** from Theorem `thm:red-attractors` (i), (iii). -/
theorem reductive_joinDense_of_attractors : IsJoinDense (IsPure Y) (reductiveRoot Φ act) :=
  reductive_joinDense (reductiveInput_of_attractors hdet hrefl)

/-- **Theorem `thm:red-classification` (i), injectivity and finiteness.** A pure magnet is
determined by `(R(N), W_N)`; hence `Π(a)` is finite when `Φ` and `W` are. -/
theorem pure_eq_of_pair {N L : AddSubmonoid M} (hN : IsPure Y N) (hL : IsPure Y L)
    (h1 : (N : Set M) ∩ Φ = (L : Set M) ∩ Φ)
    (h2 : {w | weylMagnet (act w) ≤ N} = {w | weylMagnet (act w) ≤ L}) : N = L := by
  have H := reductiveInput_of_attractors hdet hrefl
  rw [(H.pure_iff N).1 hN, (H.pure_iff L).1 hL]
  unfold reductiveHull
  rw [h1, h2]

theorem finite_pure [Finite W] (hΦ : Φ.Finite) : {N | IsPure Y N}.Finite := by
  refine Set.Finite.of_finite_image
    (f := fun N : AddSubmonoid M => ((N : Set M) ∩ Φ, {w | weylMagnet (act w) ≤ N})) ?_ ?_
  · refine (hΦ.finite_subsets.prod (Set.toFinite (Set.univ : Set (Set W)))).subset ?_
    rintro _ ⟨N, -, rfl⟩
    exact ⟨Set.inter_subset_right, trivial⟩
  · intro N hN L hL he
    simp only [Prod.mk.injEq] at he
    exact pure_eq_of_pair hdet hrefl hN hL he.1 he.2

end AlgMag.Rooted

