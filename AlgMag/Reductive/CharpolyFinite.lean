/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.NoTorusUnipotent
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Theorem A, Step 2: the characteristic polynomial takes finitely many values

This file proves the named input `hstep2` of `AlgMag.Reductive.NoTorusUnipotent.theoremA`
(equivalence.tex, Thm 2.1, Step 2), except in the case `k = F̄_p`. That case is the named
leftover `Step2OverFpBar`.

Route (shorter than the paper's): the paper uses complex absolute values in characteristic `0`
and transcendence in characteristic `p`. We use one integrality argument for both.
* `exists_isOpen_forall_mem_iff_of_isConstructible`: on a space with a generic point `η`, a
  constructible set agrees with `η` on an open neighbourhood of `η` (induction on constructible
  sets).
* `eq_or_cofinite_values` (Chevalley, Mathlib `PrimeSpectrum.isConstructible_range_comap`): on
  an irreducible finite-type algebra over `k = k̄`, a regular function `c` is either constant on
  `k`-points or takes every value outside the roots of some nonzero polynomial.
* `isIntegral_charpoly_coeff`: if every semisimple part has finite order, the eigenvalues are
  roots of unity, so the characteristic-polynomial coefficients are integral over `ℤ`.
* `charpolyValuesFinite_of_exists_not_isIntegral`: if some element of `k` is not integral over
  `ℤ`, the non-integral elements form an infinite set (its powers). A cofinite set of values
  would meet it. So every coefficient is constant, and in particular takes finitely many values.
  This covers characteristic `0` (`1/2` is not integral, `not_forall_isIntegral_of_charZero`) and
  characteristic `p` with `k ≠ F̄_p`.
* `hstep2`: the input of `theoremA`, from the leftover `Step2OverFpBar`.

Leftover (named, NOT proved): `Step2OverFpBar k H`, i.e. `hstep2` when every element of `k` is
integral over `ℤ` (that is, `k = F̄_p`). The paper handles this case by specialization from
`(k(t))‾`. It is true for every `H`, and vacuously for `GL₂` (`GL₂` has a nontrivial torus).
-/

open Polynomial WithConv TauCeti TauCeti.HopfAlgebra Topology
open scoped TensorProduct

namespace AlgMag.Reductive.CharpolyFinite

open AlgMag.Reductive.NoTorusUnipotent

universe u

/-! ### Constructible sets near a generic point -/

/-- If every point is a specialization of `η`, a constructible set `s` contains either all or
none of the points of some open neighbourhood of `η`. -/
theorem exists_isOpen_forall_mem_iff_of_isConstructible {X : Type*} [TopologicalSpace X]
    (η : X) (hη : ∀ x, η ⤳ x) {s : Set X} (hs : IsConstructible s) :
    ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ ∀ x ∈ U, (x ∈ s ↔ η ∈ s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact V hV _ =>
    by_cases h : η ∈ V
    · exact ⟨V, hV, h, fun x hx ↦ ⟨fun _ ↦ h, fun _ ↦ hx⟩⟩
    · exact ⟨Set.univ, isOpen_univ, trivial,
        fun x _ ↦ ⟨fun hx ↦ (hη x).mem_open hV hx, fun h' ↦ (h h').elim⟩⟩
  | union s _ t _ hs ht =>
    obtain ⟨U, hU, hηU, hUs⟩ := hs
    obtain ⟨W, hW, hηW, hWt⟩ := ht
    refine ⟨U ∩ W, hU.inter hW, ⟨hηU, hηW⟩, fun x hx ↦ ?_⟩
    simp only [Set.mem_union, hUs x hx.1, hWt x hx.2]
  | compl s _ hs =>
    obtain ⟨U, hU, hηU, hUs⟩ := hs
    exact ⟨U, hU, hηU, fun x hx ↦ by simp only [Set.mem_compl_iff, hUs x hx]⟩

/-! ### A regular function on an irreducible variety: constant or cofinitely many values -/

/-- **Chevalley dichotomy.** On an irreducible finite-type algebra over `k = k̄`, a regular
function `c` is either constant on `k`-points, or there is a nonzero polynomial `p` such that
`c` takes every value `t` with `p t ≠ 0`. -/
theorem eq_or_cofinite_values {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [IrreducibleSpace (PrimeSpectrum A)] (c : A) :
    (∃ a : k, ∀ f : A →ₐ[k] k, f c = a) ∨
      ∃ p : k[X], p ≠ 0 ∧ ∀ t : k, ¬ p.IsRoot t → ∃ f : A →ₐ[k] k, f c = t := by
  classical
  have hprime : (nilradical A).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 inferInstance
  let φ : k[X] →+* A := (Polynomial.aeval c : k[X] →ₐ[k] A).toRingHom
  have hφ : ∀ p : k[X], φ p = Polynomial.aeval c p := fun _ ↦ rfl
  by_cases hker : ∃ p : k[X], p ≠ 0 ∧ φ p ∈ nilradical A
  · -- `c` satisfies a polynomial relation at every point: finitely many values, hence one
    left
    obtain ⟨p, hp, hφp⟩ := hker
    refine exists_eq_of_finite_values c ((Polynomial.finite_setOfPred_isRoot hp).subset ?_)
    rintro _ ⟨f, rfl⟩
    have h0 : f (φ p) = 0 := ((mem_nilradical.1 hφp).map f).eq_zero
    rw [hφ, ← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval] at h0
    exact h0
  · right
    push Not at hker
    have hfp : φ.FinitePresentation := by
      refine RingHom.FinitePresentation.of_finiteType.1 ?_
      refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k k[X]) ?_
      have : φ.comp (algebraMap k k[X]) = algebraMap k A :=
        (Polynomial.aeval c : k[X] →ₐ[k] A).comp_algebraMap
      rw [this, RingHom.finiteType_algebraMap]
      infer_instance
    have hs := PrimeSpectrum.isConstructible_range_comap hfp
    let η : PrimeSpectrum k[X] := ⟨⊥, Ideal.isPrime_bot⟩
    have hηs : η ∈ Set.range (PrimeSpectrum.comap φ) := by
      refine ⟨⟨nilradical A, hprime⟩, PrimeSpectrum.ext ?_⟩
      ext p
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, η, Ideal.mem_bot]
      refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]; exact zero_mem _⟩
      by_contra hp
      exact hker p hp h
    obtain ⟨U, hU, hηU, hUs⟩ := exists_isOpen_forall_mem_iff_of_isConstructible η
      (fun x ↦ (PrimeSpectrum.le_iff_specializes η x).1 bot_le) hs
    obtain ⟨_, ⟨p, rfl⟩, hηp, hpU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηU hU
    refine ⟨p, fun h ↦ hηp (by simp [η, h]), fun t ht ↦ ?_⟩
    let x : PrimeSpectrum k[X] :=
      ⟨Ideal.span {Polynomial.X - Polynomial.C t}, (Ideal.span_singleton_prime (X_sub_C_ne_zero t)).2 (prime_X_sub_C t)⟩
    have hx : x ∈ U := hpU (by
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
      intro hmem
      exact ht (dvd_iff_isRoot.1 (Ideal.mem_span_singleton.1 hmem)))
    obtain ⟨P, hP⟩ := (hUs x hx).2 hηs
    have hcP : c - algebraMap k A t ∈ P.asIdeal := by
      have : Polynomial.X - Polynomial.C t ∈ (PrimeSpectrum.comap φ P).asIdeal := by
        rw [hP]; exact Ideal.subset_span rfl
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hφ] at this
      simpa using this
    obtain ⟨f, hPf, -⟩ := TauCeti.exists_algHom_apply_ne_zero_of_notMem_radical (k := k) (K := k)
      P.asIdeal (x := 1) (by rw [P.2.radical]; exact (Ideal.ne_top_iff_one _).1 P.2.ne_top)
    refine ⟨f, ?_⟩
    have := hPf hcP
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_eq_zero] at this
    exact this

/-! ### Integrality of the characteristic-polynomial coefficients -/

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The action of `g ^ N` is the `N`-th power of the action of `g`. -/
theorem endOfPoint_pow (M : FGComoduleCat.{u, u, u} k H) (g : WithConv (H →ₐ[k] k)) (N : ℕ) :
    Comodule.endOfPoint M (g ^ N).ofConv = Comodule.endOfPoint M g.ofConv ^ N := by
  induction N with
  | zero => rw [pow_zero, pow_zero, endOfPoint_one]
  | succ N ih =>
    rw [pow_succ, pow_succ, ← ih, ← Comodule.pointsAction_toLinearMap,
      ← Comodule.pointsAction_toLinearMap, ← Comodule.pointsAction_toLinearMap, map_mul]
    rfl

/-- If every semisimple part has finite order, then every characteristic-polynomial coefficient is
integral over `ℤ`: the eigenvalues are roots of unity. -/
theorem isIntegral_charpoly_coeff [IsAlgClosed k] (hss : SemisimplePartsFiniteOrder k H)
    (M : FGComoduleCat.{u, u, u} k H) (g : WithConv (H →ₐ[k] k)) (i : ℕ) :
    IsIntegral ℤ ((Comodule.endOfPoint M g.ofConv).charpoly.coeff i) := by
  obtain ⟨N, hN, hu⟩ := hss g
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one] at hu
  obtain ⟨m, hm⟩ := hu M
  rw [endOfPoint_pow] at hm
  set f := Comodule.endOfPoint M g.ofConv
  refine Polynomial.isIntegral_coeff_of_factors _ ?_ (IsAlgClosed.splits _) ?_ i
  · rw [(LinearMap.charpoly_monic f).leadingCoeff]
    exact isIntegral_one
  · intro μ hμ
    obtain ⟨v, hv⟩ :=
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2 hμ).exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector
      (p := ((Polynomial.X : k[X]) ^ N - 1) ^ m) hv
    have h2 : Polynomial.aeval f (((Polynomial.X : k[X]) ^ N - 1) ^ m) = 0 := by
      simpa [map_pow, map_sub, aeval_X, map_one] using hm
    rw [h2, LinearMap.zero_apply] at h1
    have h3 : (((Polynomial.X : k[X]) ^ N - 1) ^ m).eval μ = 0 :=
      (smul_eq_zero.1 h1.symm).resolve_right hv.2
    simp only [eval_pow, eval_sub, eval_X, eval_one] at h3
    have h4 : μ ^ N = 1 := sub_eq_zero.1 (pow_eq_zero_iff'.mp h3).1
    exact IsIntegral.of_pow hN (h4 ▸ isIntegral_one)

/-! ### Step 2 when `k` has an element not integral over `ℤ` -/

omit [CommRing H] [HopfAlgebra k H] in
/-- If some element of `k` is not integral over `ℤ`, the non-integral elements form an infinite
set: the powers `x ^ (n + 1)` are pairwise distinct and non-integral. -/
theorem infinite_setOf_not_isIntegral (hk : ∃ x : k, ¬ IsIntegral ℤ x) :
    {t : k | ¬ IsIntegral ℤ t}.Infinite := by
  obtain ⟨x, hx⟩ := hk
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ isIntegral_zero)
  let w : kˣ := Units.mk0 x hx0
  have hw : ¬ IsOfFinOrder w := by
    rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨n, hn, hwn⟩
    have : x ^ n = 1 := by simpa [w] using congrArg Units.val hwn
    exact hx (IsIntegral.of_pow hn (this ▸ isIntegral_one))
  have hinj := injective_pow_iff_not_isOfFinOrder.2 hw
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ x ^ (n + 1)) ?_ ?_
  · intro a b hab
    have : w ^ (a + 1) = w ^ (b + 1) := Units.ext (by simpa [w] using hab)
    exact Nat.succ_injective (hinj this)
  · intro n hn
    exact hx (IsIntegral.of_pow n.succ_pos hn)

/-- **Step 2 when `k ≠ F̄_p`** (proved). Suppose `k = k̄` has an element not integral over `ℤ`
(characteristic `0`, or characteristic `p` with `k ≠ F̄_p`), `G` is irreducible and every
semisimple part has finite order. Then the characteristic-polynomial coefficients take finitely
many values (in fact one). -/
theorem charpolyValuesFinite_of_exists_not_isIntegral [IsAlgClosed k] [Algebra.FiniteType k H]
    [IrreducibleSpace (PrimeSpectrum H)] (hk : ∃ x : k, ¬ IsIntegral ℤ x)
    (hss : SemisimplePartsFiniteOrder k H) : CharpolyValuesFinite k H := by
  intro M i
  obtain ⟨c, hc⟩ := charpolyRegular k H M i
  have hrange : (Set.range fun g : WithConv (H →ₐ[k] k) ↦
      (Comodule.endOfPoint M g.ofConv).charpoly.coeff i) =
      Set.range fun f : H →ₐ[k] k ↦ f c := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.ofConv, hc g⟩
    · rintro ⟨f, rfl⟩
      exact ⟨toConv f, (hc (toConv f)).symm⟩
  rw [hrange]
  rcases eq_or_cofinite_values (k := k) c with ⟨a, ha⟩ | ⟨p, hp, hsurj⟩
  · exact (Set.finite_singleton a).subset (by rintro _ ⟨f, rfl⟩; exact ha f)
  · exfalso
    have hint : ∀ t : k, ¬ p.IsRoot t → IsIntegral ℤ t := fun t ht ↦ by
      obtain ⟨f, rfl⟩ := hsurj t ht
      rw [show f c = (toConv f).ofConv c from rfl, hc (toConv f)]
      exact isIntegral_charpoly_coeff hss M _ i
    exact infinite_setOf_not_isIntegral hk
      ((Polynomial.finite_setOfPred_isRoot hp).subset fun t ht ↦ by_contra fun h ↦ ht (hint t h))

omit [CommRing H] [HopfAlgebra k H] in
/-- In characteristic `0`, `1/2` is not integral over `ℤ`, so the leftover case does not occur. -/
theorem not_forall_isIntegral_of_charZero [CharZero k] : ¬ ∀ x : k, IsIntegral ℤ x := by
  intro h
  let f : ℚ →ₐ[ℤ] k := (Algebra.ofId ℚ k).restrictScalars ℤ
  have h2 : IsIntegral ℤ (f (1 / 2)) := h _
  rw [isIntegral_algHom_iff f (fun a b hab ↦ (algebraMap ℚ k).injective hab)] at h2
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [algebraMap_int_eq, eq_intCast] at hn
  have h3 : ((2 * n : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    push_cast
    rw [hn]
    norm_num
  have h4 : (2 * n : ℤ) = 1 := by exact_mod_cast h3
  omega

/-! ### The leftover and `hstep2` -/

variable (k H) in
/-- **Leftover (named input, NOT proved): Step 2 over `F̄_p`.** This is `hstep2` when every
element of `k` is integral over `ℤ`, i.e. `k = k̄` is algebraic over `F_p`; it cannot happen in
characteristic `0` (`not_forall_isIntegral_of_charZero`). The paper (Thm 2.1, Step 2, last case)
specializes from `K = (k(t))‾`. True for every `H`, and vacuously for `GL₂` (which has a
nontrivial torus, so `NoNontrivialTorus` fails). -/
def Step2OverFpBar [Algebra.FiniteType k H] : Prop :=
  (∀ x : k, IsIntegral ℤ x) → NoNontrivialTorus k H → SemisimplePartsFiniteOrder k H →
    CharpolyValuesFinite k H

/-- In characteristic `0` the leftover holds (its first hypothesis fails). -/
theorem step2OverFpBar_of_charZero [CharZero k] [Algebra.FiniteType k H] :
    Step2OverFpBar k H :=
  fun h ↦ (not_forall_isIntegral_of_charZero h).elim

/-- **`hstep2`** (the input of `theoremA`), from the leftover `Step2OverFpBar`. -/
theorem hstep2 [IsAlgClosed k] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
    (hFp : Step2OverFpBar k H) :
    NoNontrivialTorus k H → SemisimplePartsFiniteOrder k H → CharpolyValuesFinite k H := by
  intro htor hss
  by_cases hk : ∀ x : k, IsIntegral ℤ x
  · exact hFp hk htor hss
  · push Not at hk
    have : IrreducibleSpace (PrimeSpectrum H) :=
      OpenCellNotes.irreducibleSpace_of_connectedSpace k
    exact charpolyValuesFinite_of_exists_not_isIntegral hk hss

/-- **Theorem A** with `hstep2` replaced by the leftover `Step2OverFpBar`. -/
theorem theoremA_of_step2OverFpBar [IsAlgClosed k] [Algebra.FiniteType k H]
    [ConnectedSpace (PrimeSpectrum H)] (hcl : ∀ g : WithConv (H →ₐ[k] k), ClosureInput g)
    (hFp : Step2OverFpBar k H) (htor : NoNontrivialTorus k H) (g : WithConv (H →ₐ[k] k)) :
    IsUnipotentPoint g :=
  theoremA hcl (hstep2 hFp) htor g

/-- **Theorem A in characteristic `0`**: only the closure input `hcl` remains. -/
theorem theoremA_of_charZero [CharZero k] [IsAlgClosed k] [Algebra.FiniteType k H]
    [ConnectedSpace (PrimeSpectrum H)] (hcl : ∀ g : WithConv (H →ₐ[k] k), ClosureInput g)
    (htor : NoNontrivialTorus k H) (g : WithConv (H →ₐ[k] k)) : IsUnipotentPoint g :=
  theoremA_of_step2OverFpBar hcl step2OverFpBar_of_charZero htor g

end AlgMag.Reductive.CharpolyFinite

#print axioms AlgMag.Reductive.CharpolyFinite.hstep2
#print axioms AlgMag.Reductive.CharpolyFinite.theoremA_of_charZero
