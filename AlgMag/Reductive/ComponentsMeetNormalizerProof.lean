/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.GluePrereqs
import AlgMag.Reductive.RegularConjugatesOpen
import AlgMag.Reductive.AttractorReflects
import AlgMag.Reductive.SplitReductiveRootDatum
import AlgMag.Rooted.MinimalRootReductive
import AlgMag.Reductive.SLSpCriterion
import AlgMag.Rooted.MonogenicPure
import AlgMag.Reductive.EtaleSliceAssembly
import AlgMag.Reductive.SliceTangentFinal
import AlgMag.Reductive.ParabolicBijection
import AlgMag.Rooted.ReductiveClassification

/-!
# `G^N(k) = K(k) · N_G(T)(k)` and `hdet` (Theorem `thm:red-attractors` (iii))

Instantiation of C3 (`exists_mul_normalizer_of_irreducible`) with C1
(`regular_conj_mem_normalizer`), C2 (a)–(c) (`zariski`, `irreducibleSpace_points`,
`continuous_conj_subtype`) and `GluePrereqs.lean`. Step C2 (d), the open set of regular
conjugates, is the hypothesis `RegularConjugatesOpen π` until it is proved.
-/

suppress_compilation

open Magnetism TauCeti WithConv

namespace AlgMag.Reductive

open scoped Zariski

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **Step C2 (d)**: `K(k)` contains a nonempty open set of conjugates of regular points. -/
def RegularConjugatesOpen : Prop :=
  ∀ N : Magnet (Additive X), ∃ U : Set (compSubgroup π N), IsOpen U ∧ U.Nonempty ∧
    ∀ x ∈ U, ∃ g ∈ compSubgroup π N, ∃ t ∈ regularPoints π N,
      (x : WithConv (H →ₐ[k] k)) = g * t * g⁻¹

variable {π}

/-- **`G^N(k) ⊆ K(k) · N_G(T)(k)`** (C1–C3). -/
theorem componentsMeetNormalizer (D : SplitReductiveData π)
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) (hC2 : RegularConjugatesOpen π) :
    ComponentsMeetNormalizer π (fun w : D.W => (w : X ≃* X)) := by
  intro N g hg
  haveI := irreducibleSpace_points π N (compSubgroup π N : Set _) (mem_compSubgroup π N)
  obtain ⟨U, hUo, hUn, hU⟩ := hC2 N
  obtain ⟨h, hh, n, hn, rfl⟩ := exists_mul_normalizer_of_irreducible
    (attractorSubgroup π N k) (compSubgroup π N) (normalizerW π D) (compSubgroup_le π N)
    (fun a ha x hx => conj_mem_compSubgroup π N ha hx)
    (fun a ha => continuous_conj_subtype (compSubgroup π N : Set _) a
      (fun x hx => conj_mem_compSubgroup π N ha hx))
    (regularPoints π N) U hUo hUn hU
    (fun y hy t ht t' ht' e => by
      obtain ⟨σ, hσ⟩ := regular_conj_mem_normalizer π D.surjective hT N y hy t ht t' ht' e
      exact mem_normalizerW_of_isNormalizingWith π D hσ) g hg
  obtain ⟨w, hw⟩ := hn
  exact ⟨h, n, w, (mem_compSubgroup π N h).1 hh, hw, rfl⟩

/-- **`hdet`** (Theorem `thm:red-attractors` (iii)) in the form of `reductive_joinDense_of_hdet`. -/
theorem hdet (D : SplitReductiveData π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (hC2 : RegularConjugatesOpen π) :
    ∀ N L : AddSubmonoid (Additive X), L ≤ N → (∀ a ∈ roots π, a ∈ N → a ∈ L) →
      (∀ w : D.W, Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N →
        Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L) →
      affineY (torusGrading π) L = affineY (torusGrading π) N := by
  intro N L hle hR hW
  refine (affineY_eq_iff _).2 (hdet_of_components D.surjective (componentsMeetNormalizer D hT hC2)
    N L hle hR fun w hw => ?_)
  rw [joinDense_weylMagnet_le_iff] at hw ⊢
  rw [← joinDense_weylMagnet_eq] at hw ⊢
  exact hW w hw

/-- `hdet` with step C2 (d) as the explicit hypothesis `RegularConjugatesOpen π`. -/
theorem hdet_of_openRegularConjugates (D : SplitReductiveData π)
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) (hC2 : RegularConjugatesOpen π) :
    ∀ N L : AddSubmonoid (Additive X), L ≤ N → (∀ a ∈ roots π, a ∈ N → a ∈ L) →
      (∀ w : D.W, Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N →
        Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L) →
      affineY (torusGrading π) L = affineY (torusGrading π) N :=
  hdet D hT hC2

/-- **Theorem `thm:red-rooted`.** -/
theorem reductive_joinDense (D : SplitReductiveData π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (hC2 : RegularConjugatesOpen π) :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
      (Rooted.reductiveRoot (roots π) fun w : D.W => actW (w : X ≃* X)) :=
  reductive_joinDense_of_hdet D (hdet D hT hC2)

/-- **Theorem `thm:red-classification`: `Π(a)` is finite.** -/
theorem finite_pure (D : SplitReductiveData π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (hC2 : RegularConjugatesOpen π) :
    {N | IsPure (affineY (torusGrading π)) N}.Finite :=
  finite_pure_of_hdet D (hdet D hT hC2)

/-! ### Corollaries: `ReductiveInput`, parabolic bijection, classification (ii), minimal root -/

/-- **`ReductiveInput`** for the pure magnets of `G` (from `hdet` and `attractor_reflects`). -/
theorem reductiveInput (D : SplitReductiveData π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (hC2 : RegularConjugatesOpen π) :
    Rooted.ReductiveInput (IsPure (affineY (torusGrading π))) (roots π)
      (fun w : D.W => actW (w : X ≃* X)) :=
  Rooted.reductiveInput_of_attractors (hdet D hT hC2) (attractor_reflects D)

/-- **Theorem `thm:red-parabolic` for `G`** (pure magnets containing a Weyl-conjugate of the
base ↔ parabolic subsets of roots). -/
theorem parabolic_bijOn (D : SplitReductiveData.WithRootDatum π)
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) (hC2 : RegularConjugatesOpen π) :
    Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} ∧
      Set.InvOn AddSubmonoid.closure
        (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} :=
  D.bijOn_parabolic_pure (reductiveInput D.toSplitReductiveData hT hC2)

/-- **Theorem `thm:red-classification` (ii) for `G`.** -/
theorem classification_ii (D : SplitReductiveData π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (hC2 : RegularConjugatesOpen π) {R : Set (Additive X)} (hRΦ : R ⊆ roots π)
    (hR : (AddSubmonoid.closure R : Set (Additive X)) ∩ roots π = R) :
    IsPure (affineY (torusGrading π))
        (sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)}) ∧
      ((sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)} : AddSubmonoid (Additive X)) :
          Set (Additive X)) ∩ roots π = R :=
  Rooted.reductive_classification_ii (hdet D hT hC2) (attractor_reflects D) hRΦ hR

/-- `joinIrreducibles` of the pure magnets of `G` is the unique minimal root. -/
theorem joinIrreducibles_isLeast (D : SplitReductiveData π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (hC2 : RegularConjugatesOpen π) :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
        (Rooted.joinIrreducibles (IsPure (affineY (torusGrading π)))) ∧
      ∀ Ψ, Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) Ψ →
        Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) ⊆ Ψ :=
  haveI := D.finite
  Rooted.joinIrreducibles_reductive_isLeast (hdet D hT hC2) (attractor_reflects D) finite_roots

/-- **Minimal-root formula for `G`**: the classical roots `ℕα` and the Weyl magnets `Z_w` not
generated by smaller pure magnets. -/
theorem joinIrreducibles_eq (D : SplitReductiveData π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (hC2 : RegularConjugatesOpen π) (h0 : (0 : Additive X) ∉ roots π)
    (hcone : ∀ a ∈ roots π, ∀ x, x ∈ Rooted.mono a → -x ∈ Rooted.mono a → x = 0)
    (hred : ∀ a ∈ roots π, ∀ b ∈ roots π, b ∈ Rooted.mono a → b = a) :
    Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) = Rooted.mono '' roots π ∪
      {Z | ∃ w : D.W, Z = Rooted.weylMagnet (actW (w : X ≃* X)) ∧
        Rooted.weylMagnet (actW (w : X ≃* X)) ≠
          Rooted.weylMagnetLower (roots π) (fun w : D.W => actW (w : X ≃* X)) w} :=
  Rooted.joinIrreducibles_reductive (hdet D hT hC2) (attractor_reflects D) h0 hcone hred

/-! ### The combinatorial hypotheses of the minimal-root formula, from the root datum -/

section RootDatumCombinatorics

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootPairing ι ℤ M N)

/-- Roots are non-torsion: `n • α = 0 ⇒ n = 0` (pair with the coroot: `2n = 0`). -/
lemma rootPairing_nsmul_root_eq_zero {i : ι} {n : ℕ} (h : n • P.root i = 0) : n = 0 := by
  have := congrArg (fun v => P.toLinearMap v (P.coroot i)) h
  simp only [map_nsmul, LinearMap.smul_apply, P.root_coroot_two, map_zero,
    LinearMap.zero_apply, nsmul_eq_mul] at this
  omega

/-- `ℕα ∩ -ℕα = 0` for a root `α`. -/
lemma rootPairing_cone {a : M} (ha : a ∈ Set.range P.root) (x : M)
    (hx : x ∈ Rooted.mono a) (hx' : -x ∈ Rooted.mono a) : x = 0 := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hx
  obtain ⟨n, hn⟩ := AddSubmonoid.mem_closure_singleton.1 hx'
  have h : (m + n) • P.root i = 0 := by rw [add_nsmul, hn, add_neg_cancel]
  have := rootPairing_nsmul_root_eq_zero P h
  have hm : m = 0 := by omega
  rw [hm, zero_nsmul]

/-- Reducedness: a root in `ℕα` is `α`. -/
lemma rootPairing_eq_of_mem_mono [P.IsReduced] {a b : M} (ha : a ∈ Set.range P.root)
    (hb : b ∈ Set.range P.root) (hba : b ∈ Rooted.mono a) : b = a := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨n, hn⟩ := AddSubmonoid.mem_closure_singleton.1 hba
  have hdep : ¬ LinearIndependent ℤ ![P.root j, P.root i] := by
    rw [LinearIndependent.pair_iff]
    intro h
    have := h 1 (-(n : ℤ)) (by rw [one_smul, neg_smul, natCast_zsmul, hn, add_neg_cancel])
    exact one_ne_zero this.1
  rcases RootPairing.IsReduced.eq_or_eq_neg j i hdep with h | h
  · exact h
  · exfalso
    have h2 : (n + 1) • P.root i = 0 := by rw [add_nsmul, one_nsmul, hn, h, neg_add_cancel]
    have := rootPairing_nsmul_root_eq_zero P h2
    omega

end RootDatumCombinatorics

/-- **Minimal-root formula for `G`** with the combinatorial hypotheses discharged by the root
datum. -/
theorem joinIrreducibles_eq_of_rootDatum (D : SplitReductiveData.WithRootDatum π)
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) (hC2 : RegularConjugatesOpen π) :
    Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) = Rooted.mono '' roots π ∪
      {Z | ∃ w : D.W, Z = Rooted.weylMagnet (actW (w : X ≃* X)) ∧
        Rooted.weylMagnet (actW (w : X ≃* X)) ≠
          Rooted.weylMagnetLower (roots π) (fun w : D.W => actW (w : X ≃* X)) w} := by
  have hr := D.range_root
  refine joinIrreducibles_eq D.toSplitReductiveData hT hC2 ?_ ?_ ?_
  · rw [← hr]; exact D.P.zero_notMem_range_root
  · intro a ha; rw [← hr] at ha; exact rootPairing_cone D.P ha
  · intro a ha b hb; rw [← hr] at ha hb; exact rootPairing_eq_of_mem_mono D.P ha hb

/-! ### Paper statements (`\ifreductivefull` block of `sections/reductive.tex`) -/

/-- **Theorem `thm:red-attractors` (ii)**: `G^N(k) = ⋃_{w ∈ W_N} K(k) n_w` (`k` alg. closed). -/
theorem red_attractors_ii (D : SplitReductiveData π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (hC2 : RegularConjugatesOpen π) (N : Magnet (Additive X)) (g : WithConv (H →ₐ[k] k)) :
    g ∈ attractorSubgroup π N k ↔ ∃ (h n : WithConv (H →ₐ[k] k)) (w : D.W),
      compIdeal π N ≤ RingHom.ker h.ofConv ∧ Weyl.IsNormalizingWith π k n (w : X ≃* X) ∧
      Weyl.weylMagnet (w : X ≃* X) ≤ N ∧ g = h * n :=
  mem_attractor_iff D.surjective (componentsMeetNormalizer D hT hC2) N g

/-- **Theorem `thm:red-pure`**: `E(G^N) = [R(N)⟩ + Λ_N`. -/
theorem red_pure (D : SplitReductiveData π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (hC2 : RegularConjugatesOpen π) (N : AddSubmonoid (Additive X)) :
    Rooted.reductiveHull (roots π) (fun w : D.W => actW (w : X ≃* X)) N =
      sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} :=
  Rooted.reductiveHull_eq_pureOf (hdet D hT hC2) (attractor_reflects D) N

/-- **Theorem `thm:red-classification` (i), injectivity**: a pure magnet is determined by
`(R(N), W_N)`. -/
theorem red_classification_i_inj (D : SplitReductiveData π)
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) (hC2 : RegularConjugatesOpen π)
    {N L : AddSubmonoid (Additive X)} (hN : IsPure (affineY (torusGrading π)) N)
    (hL : IsPure (affineY (torusGrading π)) L)
    (h1 : (N : Set (Additive X)) ∩ roots π = (L : Set (Additive X)) ∩ roots π)
    (h2 : {w : D.W | Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N} =
      {w : D.W | Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L}) : N = L :=
  Rooted.pure_eq_of_pair (hdet D hT hC2) (attractor_reflects D) hN hL h1 h2

/-- **Theorem `thm:red-SL-Sp`, (i) ⇔ (ii) ⇔ (iii)** for `G`. -/
theorem red_SL_Sp (D : SplitReductiveData.WithRootDatum π)
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) (hC2 : RegularConjugatesOpen π) :
    List.TFAE [Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N} {E | Rooted.IsStableElt (roots π) E},
      Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) (Rooted.mono '' roots π),
      SLSp.JoinIrredWeylGenerated (roots π) (fun w : D.W => actW (w : X ≃* X))] :=
  SLSp.tfae_criterion (reductiveInput D.toSplitReductiveData hT hC2) (by
    intro α hα
    rw [← D.range_root] at hα ⊢
    obtain ⟨i, rfl⟩ := hα
    exact D.P.neg_root_mem i)

/-- **Monogenic pure magnets of `G`** (`X` torsion-free): the nonzero monogenic pure magnets
are exactly the rays `ℕα`, `α ∈ Φ`. -/
theorem red_pure_mono_iff (D : SplitReductiveData.WithRootDatum π) [IsMulTorsionFree X]
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) (hC2 : RegularConjugatesOpen π)
    (N : AddSubmonoid (Additive X)) :
    (IsPure (affineY (torusGrading π)) N ∧
        ∃ x, x ≠ 0 ∧ N = AddSubmonoid.closure {x}) ↔
      ∃ a ∈ roots π, N = AddSubmonoid.closure {a} :=
  Rooted.pure_mono_iff (hdet D.toSplitReductiveData hT hC2)
    (attractor_reflects D.toSplitReductiveData)
    (by rw [← D.range_root]; exact D.P.zero_notMem_range_root) N

/-! ### Final form: `X` a lattice, no hypothesis

`hT` is `compIdeal_bot_iff_of_torsionFree`, and `RegularConjugatesOpen π` is
`regularConjugatesOpen_lattice_final π D` (`SliceTangentFinal.lean`). -/

section Lattice

variable [Monoid.FG X] [IsMulTorsionFree X]

lemma hT_lattice (D : SplitReductiveData π) : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0 :=
  compIdeal_bot_iff_of_torsionFree π D

/-- **Step C2(d)**, proved (`SliceTangentFinal.lean`). -/
lemma hC2_lattice (D : SplitReductiveData π) : RegularConjugatesOpen π :=
  regularConjugatesOpen_lattice_final π D

/-- `G^N(k) ⊆ K(k) · N_G(T)(k)`. -/
theorem componentsMeetNormalizer_lattice (D : SplitReductiveData π) :
    ComponentsMeetNormalizer π (fun w : D.W => (w : X ≃* X)) :=
  componentsMeetNormalizer D (hT_lattice D) (hC2_lattice D)

/-- **Theorem `thm:red-attractors`** (`hdet`). -/
theorem hdet_lattice (D : SplitReductiveData π) :
    ∀ N L : AddSubmonoid (Additive X), L ≤ N → (∀ a ∈ roots π, a ∈ N → a ∈ L) →
      (∀ w : D.W, Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N →
        Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L) →
      affineY (torusGrading π) L = affineY (torusGrading π) N :=
  hdet D (hT_lattice D) (hC2_lattice D)

/-- **Theorem `thm:red-attractors` (ii)**. -/
theorem red_attractors_ii_lattice (D : SplitReductiveData π)
    (N : Magnet (Additive X)) (g : WithConv (H →ₐ[k] k)) :
    g ∈ attractorSubgroup π N k ↔ ∃ (h n : WithConv (H →ₐ[k] k)) (w : D.W),
      compIdeal π N ≤ RingHom.ker h.ofConv ∧ Weyl.IsNormalizingWith π k n (w : X ≃* X) ∧
      Weyl.weylMagnet (w : X ≃* X) ≤ N ∧ g = h * n :=
  red_attractors_ii D (hT_lattice D) (hC2_lattice D) N g

/-- **Theorem `thm:red-pure`**. -/
theorem red_pure_lattice (D : SplitReductiveData π)
    (N : AddSubmonoid (Additive X)) :
    Rooted.reductiveHull (roots π) (fun w : D.W => actW (w : X ≃* X)) N =
      sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} :=
  red_pure D (hT_lattice D) (hC2_lattice D) N

/-- `ReductiveInput` for the pure magnets of `G`. -/
theorem reductiveInput_lattice (D : SplitReductiveData π) :
    Rooted.ReductiveInput (IsPure (affineY (torusGrading π))) (roots π)
      (fun w : D.W => actW (w : X ≃* X)) :=
  reductiveInput D (hT_lattice D) (hC2_lattice D)

/-- **Theorem `thm:red-classification` (i)**, injectivity. -/
theorem red_classification_i_inj_lattice (D : SplitReductiveData π)
    {N L : AddSubmonoid (Additive X)} (hN : IsPure (affineY (torusGrading π)) N)
    (hL : IsPure (affineY (torusGrading π)) L)
    (h1 : (N : Set (Additive X)) ∩ roots π = (L : Set (Additive X)) ∩ roots π)
    (h2 : {w : D.W | Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N} =
      {w : D.W | Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L}) : N = L :=
  red_classification_i_inj D (hT_lattice D) (hC2_lattice D) hN hL h1 h2

/-- **Theorem `thm:red-classification` (i)**, finiteness of `Π(a)`. -/
theorem finite_pure_lattice (D : SplitReductiveData π) :
    {N | IsPure (affineY (torusGrading π)) N}.Finite :=
  finite_pure D (hT_lattice D) (hC2_lattice D)

/-- **Theorem `thm:red-classification` (ii)**. -/
theorem classification_ii_lattice (D : SplitReductiveData π)
    {R : Set (Additive X)} (hRΦ : R ⊆ roots π)
    (hR : (AddSubmonoid.closure R : Set (Additive X)) ∩ roots π = R) :
    IsPure (affineY (torusGrading π))
        (sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)}) ∧
      ((sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)} : AddSubmonoid (Additive X)) :
          Set (Additive X)) ∩ roots π = R :=
  classification_ii D (hT_lattice D) (hC2_lattice D) hRΦ hR

/-- **Theorem `thm:red-parabolic`**. -/
theorem parabolic_bijOn_lattice (D : SplitReductiveData.WithRootDatum π) :
    Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} ∧
      Set.InvOn AddSubmonoid.closure
        (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧ R ∪ -R = roots π} :=
  parabolic_bijOn D
    (hT_lattice D.toSplitReductiveData) (hC2_lattice D.toSplitReductiveData)

/-- **Theorem `thm:red-rooted`**. -/
theorem reductive_joinDense_lattice (D : SplitReductiveData π) :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
      (Rooted.reductiveRoot (roots π) fun w : D.W => actW (w : X ≃* X)) :=
  reductive_joinDense D (hT_lattice D) (hC2_lattice D)

/-- **Theorem `thm:red-rooted`, minimal root** (unique minimal root). -/
theorem joinIrreducibles_isLeast_lattice (D : SplitReductiveData π) :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
        (Rooted.joinIrreducibles (IsPure (affineY (torusGrading π)))) ∧
      ∀ Ψ, Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) Ψ →
        Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) ⊆ Ψ :=
  joinIrreducibles_isLeast D (hT_lattice D) (hC2_lattice D)

/-- **Theorem `thm:red-rooted`, minimal-root formula**. -/
theorem joinIrreducibles_eq_lattice (D : SplitReductiveData.WithRootDatum π) :
    Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) = Rooted.mono '' roots π ∪
      {Z | ∃ w : D.W, Z = Rooted.weylMagnet (actW (w : X ≃* X)) ∧
        Rooted.weylMagnet (actW (w : X ≃* X)) ≠
          Rooted.weylMagnetLower (roots π) (fun w : D.W => actW (w : X ≃* X)) w} :=
  joinIrreducibles_eq_of_rootDatum D
    (hT_lattice D.toSplitReductiveData) (hC2_lattice D.toSplitReductiveData)

/-- **Theorem `thm:red-SL-Sp`**. -/
theorem red_SL_Sp_lattice (D : SplitReductiveData.WithRootDatum π) :
    List.TFAE [Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N} {E | Rooted.IsStableElt (roots π) E},
      Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) (Rooted.mono '' roots π),
      SLSp.JoinIrredWeylGenerated (roots π) (fun w : D.W => actW (w : X ≃* X))] :=
  red_SL_Sp D
    (hT_lattice D.toSplitReductiveData) (hC2_lattice D.toSplitReductiveData)

/-- **Monogenic pure magnets**: exactly the rays `ℕα`, `α ∈ Φ`. -/
theorem red_pure_mono_iff_lattice (D : SplitReductiveData.WithRootDatum π) (N : AddSubmonoid (Additive X)) :
    (IsPure (affineY (torusGrading π)) N ∧
        ∃ x, x ≠ 0 ∧ N = AddSubmonoid.closure {x}) ↔
      ∃ a ∈ roots π, N = AddSubmonoid.closure {a} :=
  red_pure_mono_iff D
    (hT_lattice D.toSplitReductiveData) (hC2_lattice D.toSplitReductiveData) N

end Lattice

/-! ### Full coverage of `thm:red-classification` (i) and `thm:red-parabolic` -/

section Coverage

open scoped TensorProduct
open TauCeti.Cocharacter

lemma weylMagnet_one_le_bot : Weyl.weylMagnet (1 : X ≃* X) ≤ ⊥ :=
  AddSubmonoid.closure_le.2 (by rintro _ ⟨χ, rfl⟩; simp)

/-- A `k`-point normalizing `T` with automorphism `w ∈ W` lies in `n_w T(k)`. -/
theorem exists_torus_of_isNormalizingWith (D : SplitReductiveData π)
    {n : WithConv (H →ₐ[k] k)} {w : D.W} (hn : Weyl.IsNormalizingWith π k n (w : X ≃* X)) :
    ∃ t : WithConv (H →ₐ[k] k), RingHom.ker π.toAlgHom ≤ RingHom.ker t.ofConv ∧
      n = D.rep w * t := by
  have ht := Weyl.IsNormalizingWith.mul π hn (Weyl.IsNormalizingWith.inv π (D.rep_normalizing w))
  rw [mul_inv_cancel] at ht
  have hbot : (D.rep w)⁻¹ * n ∈ attractorSubgroup π ⊥ k :=
    (Weyl.mem_attractorSubgroup_iff_weylMagnet_le π D.surjective ht ⊥).2 weylMagnet_one_le_bot
  exact ⟨(D.rep w)⁻¹ * n, ker_le_of_mem_bot π D hbot, (mul_inv_cancel_left _ _).symm⟩

variable [Monoid.FG X] [IsMulTorsionFree X]

/-- **Theorem `thm:red-classification` (i), bijection.** `N ↦ (R(N), W_N)` is a bijection from
`Π(a)` onto the compatible pairs, with inverse `(R, W') ↦ L(R, W')`. -/
theorem red_classification_i_lattice (D : SplitReductiveData π) :
    Set.BijOn (Rooted.pairOf (roots π) (fun w : D.W => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π) (fun w : D.W => actW (w : X ≃* X)) p} ∧
      Set.InvOn (fun p : Set (Additive X) × Set D.W =>
          Rooted.pairMagnet (fun w : D.W => actW (w : X ≃* X)) p.1 p.2)
        (Rooted.pairOf (roots π) (fun w : D.W => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π) (fun w : D.W => actW (w : X ≃* X)) p} :=
  Rooted.bijOn_pairOf (reductiveInput_lattice D)

/-- **Theorem `thm:red-classification` (i), attractor of `L(R, W')`**: for a compatible pair,
`G^{L(R, W')}(k) = ⋃_{w ∈ W'} K_R(k) n_w`. -/
theorem red_classification_attractor_lattice (D : SplitReductiveData π) {R : Set (Additive X)} {W' : Set D.W}
    (hp : Rooted.IsCompatiblePair (roots π) (fun w : D.W => actW (w : X ≃* X)) (R, W'))
    (g : WithConv (H →ₐ[k] k)) :
    g ∈ attractorSubgroup π (Rooted.pairMagnet (fun w : D.W => actW (w : X ≃* X)) R W') k ↔
      ∃ h : WithConv (H →ₐ[k] k), rootComp π R ≤ RingHom.ker h.ofConv ∧
        ∃ w ∈ W', g = h * D.rep w := by
  set L := Rooted.pairMagnet (fun w : D.W => actW (w : X ≃* X)) R W'
  obtain ⟨h1, h2⟩ := Rooted.isCompatiblePair_iff.1 hp
  have hK : compIdeal π L = rootComp π R := by
    rw [compIdeal_eq_rootComp]
    exact congrArg (rootComp π) h1
  have hW : ∀ w : D.W, Weyl.weylMagnet (w : X ≃* X) ≤ L ↔ w ∈ W' := by
    intro w
    rw [← joinDense_weylMagnet_eq]
    exact Set.ext_iff.1 h2 w
  constructor
  · intro hg
    obtain ⟨h, n, w, hh, hn, hwL, rfl⟩ := (red_attractors_ii_lattice D L g).1 hg
    obtain ⟨t, ht, rfl⟩ := exists_torus_of_isNormalizingWith D hn
    have hrep : D.rep w ∈ attractorSubgroup π L k := (rep_mem_attractorSubgroup_iff D w L).2 hwL
    have htK : t ∈ compSubgroup π L :=
      (mem_compSubgroup π L t).2 ((compIdeal_le_ker_torus π D L).trans ht)
    have hm := (compSubgroup π L).mul_mem ((mem_compSubgroup π L h).2 hh)
      (conj_mem_compSubgroup π L hrep htK)
    refine ⟨h * (D.rep w * t * (D.rep w)⁻¹), hK ▸ (mem_compSubgroup π L _).1 hm, w,
      (hW w).1 hwL, ?_⟩
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨h, hh, w, hw, rfl⟩
    exact mul_rep_mem_attractorSubgroup D (hK ▸ hh) w ((hW w).2 hw)

/-- **Theorem `thm:red-parabolic`, `E(G^N) = ℕB + ℕ(-ξ)`** for a magnet `N ⊇ B`. -/
theorem red_parabolic_hull_lattice (D : SplitReductiveData.WithRootDatum π) {N : AddSubmonoid (Additive X)}
    (hBN : D.P.root '' D.b.support ⊆ N) :
    sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} =
      AddSubmonoid.closure (D.P.root '' D.b.support ∪
        -Parabolic.xi (D.P.root '' D.b.support) N) := by
  have S := RootSystem.RootDatum.simpleSystem D.P D.b
  rw [← red_pure_lattice D.toSplitReductiveData N,
    ← reductiveHull_congr D.weyl_eq N, ← D.range_root]
  exact Parabolic.reductiveHull_eq_of_basis S.toInversionData S.pos_or_neg S.neg_mem
    S.basis_sub hBN

/-- **Theorem `thm:red-parabolic`, `G^N = P_ξ`** for a magnet `N ⊇ B`, `ξ = {α ∈ B | -α ∈ N}`,
with `P_ξ = P(λ)` for any cocharacter `λ` vanishing on `ξ` and positive on `B \ ξ`
(`G` geometrically connected). -/
theorem red_parabolic_lattice (D : SplitReductiveData.WithRootDatum π)
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (ψ : X →* Multiplicative ℤ) {N : AddSubmonoid (Additive X)}
    (hBN : D.P.root '' D.b.support ⊆ N)
    (hξ : ∀ α ∈ Parabolic.xi (D.P.root '' D.b.support) N, pairingHom ψ α = 0)
    (hpos : ∀ α ∈ D.P.root '' D.b.support,
      α ∉ Parabolic.xi (D.P.root '' D.b.support) N → 0 < pairingHom ψ α) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  have S := RootSystem.RootDatum.simpleSystem D.P D.b
  have hY := Rooted.attractor_reductiveHull (hdet_lattice D.toSplitReductiveData)
    (attractor_reflects D.toSplitReductiveData) N
  rw [red_pure_lattice D.toSplitReductiveData N, red_parabolic_hull_lattice D hBN]
    at hY
  rw [← (affineY_eq_iff _).1 hY]
  refine Parabolic.magnetIdeal_basis_neg_eq_parabolic π ψ ?_ hξ hpos
  rw [← D.range_root]
  exact S.pos_or_neg

end Coverage

end AlgMag.Reductive
