/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import AlgMag.Foundations
import AlgMag.Affine.Representability

/-!
# Pure magnets

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), §15.

The order-theoretic part of §15 uses only Proposition 3.29 and Fact 3.34. We therefore work with
a map `Y` from magnets to a complete lattice satisfying `AlgMag.AttractorOrder`; this hypothesis is
a theorem in the affine case (`AlgMag.affineY_infPreserving`, `AlgMag.InfPreserving.attractorOrder`).
Full preservation of intersections, `AlgMag.InfPreserving`, is false outside the affine case
(Remark 3.25): for `D(ℤ)` acting on `P¹`, `X^ℕ ×_X X^{-ℕ} = {0} ⊔ G_m ⊔ {∞}` but `X^0 = {0, ∞}`.
-/

open DirectSum

set_option linter.unusedSectionVars false

namespace AlgMag

variable {M : Type*} [AddCommMonoid M]

section Abstract

variable {α : Type*}

/-- A **pure magnet** (Definition 15.2, in the form of Proposition 15.1 (ii)): every magnet with
the same attractor contains `N`. -/
def IsPure (Y : AddSubmonoid M → α) (N : AddSubmonoid M) : Prop :=
  ∀ L : AddSubmonoid M, Y N = Y L → N ≤ L

/-- The set of pure magnets `Π(a)` (Definition 15.2 (ii)). -/
def pureMagnets (Y : AddSubmonoid M → α) : Set (AddSubmonoid M) := {N | IsPure Y N}

variable [CompleteLattice α]

/-- What §15 uses of `N ↦ X^N`: Proposition 3.29 (monotone) and Fact 3.34 (a nonempty family of
magnets with the same attractor has that attractor for its intersection). -/
structure AttractorOrder (Y : AddSubmonoid M → α) : Prop where
  monotone : Monotone Y
  sInf_of_const : ∀ (s : Set (AddSubmonoid M)) (y : α), s.Nonempty → (∀ N ∈ s, Y N = y) →
    Y (sInf s) = y

/-- `N ↦ X^N` preserves arbitrary intersections. This holds for affine `X`, not in general
(Remark 3.25). -/
def InfPreserving (Y : AddSubmonoid M → α) : Prop :=
  ∀ s : Set (AddSubmonoid M), Y (sInf s) = ⨅ N ∈ s, Y N

variable {Y : AddSubmonoid M → α}

/-- Proposition 3.29, deduced from intersection preservation. -/
lemma InfPreserving.monotone (hY : InfPreserving Y) : Monotone Y := by
  intro N L h
  have : sInf ({N, L} : Set (AddSubmonoid M)) = N := by simpa using h
  rw [← this, hY]
  exact iInf₂_le L (by simp)

lemma InfPreserving.map_inf (hY : InfPreserving Y) (N L : AddSubmonoid M) :
    Y (N ⊓ L) = Y N ⊓ Y L := by
  rw [← sInf_pair, hY, iInf_pair]

lemma InfPreserving.attractorOrder (hY : InfPreserving Y) : AttractorOrder Y where
  monotone := hY.monotone
  sInf_of_const s y := by
    rintro ⟨N₀, h₀⟩ h
    rw [hY]
    exact le_antisymm ((iInf₂_le N₀ h₀).trans_eq (h N₀ h₀)) (le_iInf₂ fun N hN => (h N hN).ge)

/-- **Proposition 15.1.** `N` is pure iff every strictly smaller magnet has a strictly smaller
attractor. -/
theorem isPure_iff_lt (hY : AttractorOrder Y) (N : AddSubmonoid M) :
    IsPure Y N ↔ ∀ L, L < N → Y L < Y N := by
  constructor
  · intro h L hL
    refine lt_of_le_of_ne (hY.monotone hL.le) fun e => ?_
    exact absurd (h L e.symm) (not_le_of_gt hL)
  · intro h L e
    by_contra hNL
    have hlt : N ⊓ L < N := lt_of_le_of_ne inf_le_left fun e' => hNL (inf_eq_left.mp e')
    have := h _ hlt
    have hinf : Y (N ⊓ L) = Y N := by
      rw [← sInf_pair]
      refine hY.sInf_of_const _ _ ⟨N, by simp⟩ ?_
      simpa using e.symm
    rw [hinf] at this
    exact lt_irrefl _ this

/-- The magnet `E(y) = ⋂ {N | X^N = y}` of Theorem 15.3. -/
def pureOf (Y : AddSubmonoid M → α) (y : α) : AddSubmonoid M := sInf {N | Y N = y}

lemma map_pureOf (hY : AttractorOrder Y) {y : α} (hy : y ∈ Set.range Y) : Y (pureOf Y y) = y := by
  obtain ⟨N₀, rfl⟩ := hy
  exact hY.sInf_of_const _ _ ⟨N₀, rfl⟩ fun _ hN => hN

lemma isPure_pureOf (hY : AttractorOrder Y) {y : α} (hy : y ∈ Set.range Y) :
    IsPure Y (pureOf Y y) := fun L hL =>
  sInf_le (show Y L = y by rw [← hL, map_pureOf hY hy])

lemma IsPure.pureOf_map {N : AddSubmonoid M} (hN : IsPure Y N) (hY : AttractorOrder Y) :
    pureOf Y (Y N) = N :=
  le_antisymm (sInf_le rfl) (hN _ (map_pureOf hY ⟨N, rfl⟩).symm)

/-- **Theorem 15.3.** The canonical bijection between pure magnets and attractors, sending `N` to
`X^N`, with inverse `y ↦ ⋂ {N | X^N = y}`. -/
def pureEquivRange (hY : AttractorOrder Y) : pureMagnets Y ≃ Set.range Y where
  toFun N := ⟨Y N, N, rfl⟩
  invFun y := ⟨pureOf Y y, isPure_pureOf hY y.2⟩
  left_inv N := Subtype.ext (IsPure.pureOf_map N.2 hY)
  right_inv y := Subtype.ext (map_pureOf hY y.2)

/-- A complement to §15 (not in the paper), for intersection-preserving `Y`, so for affine `X`:
pure magnets are stable under arbitrary joins of magnets, and `0` is pure. Thus `Π(a)` is a complete
lattice under inclusion. -/
theorem isPure_sSup (hY : InfPreserving Y) {s : Set (AddSubmonoid M)} (hs : ∀ N ∈ s, IsPure Y N) :
    IsPure Y (sSup s) := by
  intro K hK
  refine sSup_le fun N hN => ?_
  have hle : Y N ≤ Y K := hK ▸ hY.monotone (le_sSup hN)
  have : N ≤ N ⊓ K := hs N hN _ (by rw [hY.map_inf, inf_eq_left.mpr hle])
  exact this.trans inf_le_right

lemma isPure_bot : IsPure Y (⊥ : AddSubmonoid M) := fun _ _ => bot_le

/-- The finiteness mechanism in the proof of Theorem 15.4: if attractors are determined by
intersecting with a finite set `E` of degrees, there are finitely many pure magnets. Moreover
each pure magnet is generated by its elements in `E`. -/
lemma IsPure.eq_closure_inter {E : Set M} (h : ∀ N, Y N = Y (AddSubmonoid.closure ((N : Set M) ∩ E)))
    {N : AddSubmonoid M} (hN : IsPure Y N) : N = AddSubmonoid.closure ((N : Set M) ∩ E) :=
  le_antisymm (hN _ (h N))
    ((AddSubmonoid.closure_le).mpr Set.inter_subset_left)

lemma finite_pureMagnets_of_inter {E : Set M} (hE : E.Finite)
    (h : ∀ N, Y N = Y (AddSubmonoid.closure ((N : Set M) ∩ E))) : (pureMagnets Y).Finite := by
  refine (hE.finite_subsets.image AddSubmonoid.closure).subset fun N hN => ?_
  exact ⟨(N : Set M) ∩ E, Set.inter_subset_right, (IsPure.eq_closure_inter h hN).symm⟩

/-- The formal part of **Proposition 15.5** (and of Theorem 15.4 (ii)): if equality of attractors
on `U` implies equality on `X`, then `Π(a_X) ⊆ Π(a_U)`. Restricted scope: the implication is the
geometric content of Proposition 15.5, which uses strongly-FPR atlases and is taken here as the
hypothesis `h`. -/
theorem pureMagnets_subset_of_reflects {β : Type*} {Y' : AddSubmonoid M → β}
    (h : ∀ N L, Y' N = Y' L → Y N = Y L) : pureMagnets Y ⊆ pureMagnets Y' :=
  fun _ hN L e => hN L (h _ _ e)

end Abstract

section Functor

open CategoryTheory Opposite

universe u v

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {F : Cᵒᵖ ⥤ Type u}

/-- The image of `X^N` in `X`, as a family of subsets of points: the convention of Theorem 15.3
identifies `X^N` and `X^L` when these agree. `IsPure (attractorImage act)` is Definition 15.2 for
a functor with an action, and the results above apply as soon as `AttractorOrder` holds
(Proposition 3.29 and Fact 3.34). -/
def attractorImage (act : AAction 𝒪 M F) (N : AddSubmonoid M) : ∀ T : C, Set (F.obj (op T)) :=
  fun T => Set.range (AttractorPt.toPoint (act := act) (N := N) (T := T))

end Functor

section Affine

variable [DecidableEq M]
variable {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]
variable (𝒜 : M → Submodule R₀ A)

open Magnetism

lemma magnetIdeal_anti_pure {N L : AddSubmonoid M} (h : N ≤ L) : magnetIdeal 𝒜 L ≤ magnetIdeal 𝒜 N := by
  refine Ideal.span_le.mpr ?_
  simp only [Set.iUnion_subset_iff]
  exact fun m hm a ha => mem_magnetIdeal_of_notMem (fun hN => hm (h hN)) ha

/-- The affine attractor map: `N ↦ X^N = Spec (A / J_N)`, valued in closed subschemes of `X`, i.e.
in ideals of `A` with the reversed order. -/
def affineY : AddSubmonoid M → (Ideal A)ᵒᵈ := fun N => OrderDual.toDual (magnetIdeal 𝒜 N)

/-- Propositions 3.29, 3.32, 3.34 in the affine case: `J_{⋂ N_i} = ∑ J_{N_i}`. -/
theorem affineY_infPreserving : InfPreserving (affineY 𝒜) := by
  intro s
  refine le_antisymm (le_iInf₂ fun N hN => ?_) ?_
  · exact magnetIdeal_anti_pure 𝒜 (sInf_le hN)
  · show magnetIdeal 𝒜 (sInf s) ≤ OrderDual.ofDual (⨅ N ∈ s, affineY 𝒜 N)
    refine Ideal.span_le.mpr ?_
    simp only [Set.iUnion_subset_iff]
    intro m hm a ha
    obtain ⟨N, hN, hmN⟩ : ∃ N ∈ s, m ∉ N := by
      by_contra! h
      exact hm (AddSubmonoid.mem_sInf.mpr h)
    have h1 : a ∈ magnetIdeal 𝒜 N := mem_magnetIdeal_of_notMem hmN ha
    have h2 : (⨅ N ∈ s, affineY 𝒜 N) ≤ affineY 𝒜 N := iInf₂_le N hN
    exact h2 h1

/-- Equality of affine attractors is equality of ideals. -/
lemma affineY_eq_iff {N L : AddSubmonoid M} :
    affineY 𝒜 N = affineY 𝒜 L ↔ magnetIdeal 𝒜 N = magnetIdeal 𝒜 L := Iff.rfl

/-- The degrees in which `A` does not vanish modulo `J`, i.e. on the closed subscheme `V(J)`. -/
def nonvanishingDegrees (J : Ideal A) : Set M := {m | ∃ a ∈ 𝒜 m, a ∉ J}

/-- Explicit form of `E(X^N)` in the affine case (not stated in the paper, which only has the
intersection): `E(X^N)` is generated by the degrees that do not vanish on `X^N`. -/
theorem magnetIdeal_closure_nonvanishing (N : AddSubmonoid M) :
    magnetIdeal 𝒜 (AddSubmonoid.closure (nonvanishingDegrees 𝒜 (magnetIdeal 𝒜 N))) =
      magnetIdeal 𝒜 N := by
  refine le_antisymm ?_ (magnetIdeal_anti_pure 𝒜 ?_)
  · refine Ideal.span_le.mpr ?_
    simp only [Set.iUnion_subset_iff]
    intro m hm a ha
    by_contra hJ
    exact hm (AddSubmonoid.subset_closure ⟨a, ha, hJ⟩)
  · refine AddSubmonoid.closure_le.mpr ?_
    rintro m ⟨a, ha, hJ⟩
    by_contra hm
    exact hJ (mem_magnetIdeal_of_notMem hm ha)

/-- In the affine case, `N` is pure iff it is generated by the degrees not vanishing on `X^N`. -/
theorem isPure_affine_iff (N : AddSubmonoid M) :
    IsPure (affineY 𝒜) N ↔
      N = AddSubmonoid.closure (nonvanishingDegrees 𝒜 (magnetIdeal 𝒜 N)) := by
  constructor
  · intro h
    refine le_antisymm (h _ (magnetIdeal_closure_nonvanishing 𝒜 N).symm) ?_
    refine AddSubmonoid.closure_le.mpr ?_
    rintro m ⟨a, ha, hJ⟩
    by_contra hm
    exact hJ (mem_magnetIdeal_of_notMem hm ha)
  · intro h L hL
    rw [h]
    refine AddSubmonoid.closure_le.mpr ?_
    rintro m ⟨a, ha, hJ⟩
    by_contra hm
    exact hJ ((affineY_eq_iff 𝒜).mp hL ▸ mem_magnetIdeal_of_notMem hm ha)

variable [GradedAlgebra 𝒜]

/-- The key step of **Theorem 15.4 (i)**: if `A` is generated by homogeneous elements of degree
in `E`, then `X^N = X^{⟨N ∩ E⟩}`. -/
theorem magnetIdeal_closure_inter {E : Set M}
    (hgen : Algebra.adjoin R₀ (⋃ m ∈ E, (𝒜 m : Set A)) = ⊤) (N : AddSubmonoid M) :
    magnetIdeal 𝒜 N = magnetIdeal 𝒜 (AddSubmonoid.closure ((N : Set M) ∩ E)) := by
  set N' := AddSubmonoid.closure ((N : Set M) ∩ E) with hN'
  have hle : N' ≤ N := AddSubmonoid.closure_le.mpr Set.inter_subset_left
  set J := magnetIdeal 𝒜 N with hJ
  let G : Set A := {x | ∃ k, x ∈ 𝒜 k ∧ (k ∈ N' ∨ x ∈ J)}
  let W : Submodule R₀ A := Submodule.span R₀ G
  have hWmul : ∀ a ∈ W, ∀ b ∈ W, a * b ∈ W := by
    intro a ha b hb
    have hWW : W * W ≤ W := by
      show Submodule.span R₀ G * Submodule.span R₀ G ≤ Submodule.span R₀ G
      rw [Submodule.span_mul_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, ⟨k, hx, hk⟩, y, ⟨l, hy, hl⟩, rfl⟩
      refine Submodule.subset_span ⟨k + l, SetLike.mul_mem_graded hx hy, ?_⟩
      rcases hk with hk | hk
      · rcases hl with hl | hl
        · exact Or.inl (N'.add_mem hk hl)
        · exact Or.inr (J.mul_mem_left _ hl)
      · exact Or.inr (J.mul_mem_right _ hk)
    exact hWW (Submodule.mul_mem_mul ha hb)
  have hW : ∀ a : A, a ∈ W := by
    intro a
    have ha : a ∈ Algebra.adjoin R₀ (⋃ m ∈ E, (𝒜 m : Set A)) := hgen ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
      obtain ⟨m, hm, hx⟩ := hx
      refine Submodule.subset_span ⟨m, hx, ?_⟩
      by_cases hmN : m ∈ N
      · exact Or.inl (AddSubmonoid.subset_closure ⟨hmN, hm⟩)
      · exact Or.inr (mem_magnetIdeal_of_notMem hmN hx)
    | algebraMap r =>
      exact Submodule.subset_span ⟨0, SetLike.algebraMap_mem_graded 𝒜 r, Or.inl N'.zero_mem⟩
    | add x y _ _ hx hy => exact W.add_mem hx hy
    | mul x y _ _ hx hy => exact hWmul x hx y hy
  have hproj : ∀ m, m ∉ N' → ∀ a ∈ W, GradedAlgebra.proj 𝒜 m a ∈ J := by
    intro m hm a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hxk, hk⟩ := hx
      by_cases hkm : k = m
      · subst hkm
        rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hxk]
        exact hk.resolve_left hm
      · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hxk hkm]
        exact J.zero_mem
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
    | smul r x _ hx =>
      rw [map_smul, ← algebraMap_smul A r, smul_eq_mul]
      exact J.mul_mem_left _ hx
  refine le_antisymm (magnetIdeal_anti_pure 𝒜 hle) (Ideal.span_le.mpr ?_)
  simp only [Set.iUnion_subset_iff]
  intro m hm a ha
  have := hproj m hm a (hW a)
  rwa [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha] at this

/-- A finite-type graded algebra is generated by homogeneous elements of finitely many degrees. -/
theorem exists_finite_degrees [Algebra.FiniteType R₀ A] :
    ∃ E : Set M, E.Finite ∧ Algebra.adjoin R₀ (⋃ m ∈ E, (𝒜 m : Set A)) = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R₀ A).FG)
  refine ⟨↑(S.biUnion fun s => (DirectSum.decompose 𝒜 s).support), Finset.finite_toSet _, ?_⟩
  refine top_le_iff.mp (hS ▸ Algebra.adjoin_le ?_)
  intro s hs
  rw [SetLike.mem_coe, ← DirectSum.sum_support_decompose 𝒜 s]
  refine Subalgebra.sum_mem _ fun m hm => Algebra.subset_adjoin ?_
  simp only [Set.mem_iUnion]
  exact ⟨m, Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨s, hs, hm⟩), SetLike.coe_mem _⟩

/-- **Theorem 15.4 (i)** over an affine base: `Π(a)` is finite when `X = Spec A` is of finite type
over `S = Spec R₀`. Finite presentation is not needed, and neither is any localization on `S`:
over an affine base the homogeneous components of finitely many generators suffice. -/
theorem finite_pureMagnets_affine [Algebra.FiniteType R₀ A] :
    (pureMagnets (affineY 𝒜)).Finite := by
  obtain ⟨E, hE, hgen⟩ := exists_finite_degrees 𝒜
  exact finite_pureMagnets_of_inter hE fun N => magnetIdeal_closure_inter 𝒜 hgen N

/-- **Remark 15.6**, affine case and for all magnets: the set of attractors is finite. In
particular so is the set of `X^{D(M/Z)} = X^Z` for subgroups `Z ⊆ M`. -/
theorem finite_range_affineY [Algebra.FiniteType R₀ A] : (Set.range (affineY 𝒜)).Finite := by
  refine ((finite_pureMagnets_affine 𝒜).image (affineY 𝒜)).subset ?_
  rintro y hy
  exact ⟨_, isPure_pureOf (affineY_infPreserving 𝒜).attractorOrder hy, map_pureOf (affineY_infPreserving 𝒜).attractorOrder hy⟩

end Affine

section Rank

/-- **Definition 15.9.** The rank `rk(N)`: the least cardinal of a subset generating `N`. -/
noncomputable def monoidRank (N : AddSubmonoid M) : Cardinal :=
  ⨅ E : {E : Set M // AddSubmonoid.closure E = N}, Cardinal.mk E.1

lemma monoidRank_le {N : AddSubmonoid M} {E : Set M} (hE : AddSubmonoid.closure E = N) :
    monoidRank N ≤ Cardinal.mk E :=
  ciInf_le' (fun E : {E : Set M // AddSubmonoid.closure E = N} => Cardinal.mk E.1) ⟨E, hE⟩

lemma le_monoidRank {N : AddSubmonoid M} {c : Cardinal}
    (h : ∀ E : Set M, AddSubmonoid.closure E = N → c ≤ Cardinal.mk E) : c ≤ monoidRank N :=
  haveI : Nonempty {E : Set M // AddSubmonoid.closure E = N} := ⟨⟨N, AddSubmonoid.closure_eq N⟩⟩
  le_ciInf fun E => h E.1 E.2

/-- The empty set generates the zero monoid (§15). -/
lemma monoidRank_bot : monoidRank (⊥ : AddSubmonoid M) = 0 := by
  have := monoidRank_le (E := (∅ : Set M)) AddSubmonoid.closure_empty
  simpa using this

/-- A nonzero monogenic magnet has rank one. This covers `rk(ℕ) = 1` and `rk(2ℕ) = 1` of the list
following Fact 15.11. -/
lemma monoidRank_closure_singleton {x : M} (hx : x ≠ 0) :
    monoidRank (AddSubmonoid.closure {x}) = 1 := by
  refine le_antisymm ?_ (le_monoidRank fun E hE => ?_)
  · simpa using monoidRank_le (E := {x}) rfl
  · rw [Cardinal.one_le_iff_ne_zero, Cardinal.mk_ne_zero_iff]
    by_contra hne
    have hE0 : E = ∅ := Set.not_nonempty_iff_eq_empty'.mp hne
    rw [hE0, AddSubmonoid.closure_empty] at hE
    have : x ∈ (⊥ : AddSubmonoid M) := hE ▸ AddSubmonoid.subset_closure rfl
    exact hx (AddSubmonoid.mem_bot.mp this)

/-- **Fact 15.11.** `rk(ℤⁿ) = n + 1` for `n ≥ 1`. The hypothesis is necessary: `ℤ⁰ = 0` has rank
`0` by `monoidRank_bot`, so the printed formula fails for `n = 0`. -/
theorem monoidRank_int_pi {n : ℕ} (hn : 0 < n) :
    monoidRank (⊤ : AddSubmonoid (Fin n → ℤ)) = n + 1 := by
  classical
  let e : Fin n → (Fin n → ℤ) := fun i => Pi.single i 1
  refine le_antisymm ?_ (le_monoidRank fun E hE => ?_)
  · -- generators `eᵢ` and `-∑ eᵢ`
    let t : Fin n → ℤ := -∑ i, e i
    let F : Finset (Fin n → ℤ) := insert t (Finset.univ.image e)
    have hF : AddSubmonoid.closure (F : Set (Fin n → ℤ)) = ⊤ := by
      set C := AddSubmonoid.closure (F : Set (Fin n → ℤ))
      have he : ∀ i, e i ∈ C := fun i =>
        AddSubmonoid.subset_closure (by simp [F])
      have ht : t ∈ C := AddSubmonoid.subset_closure (by simp [F])
      have hne : ∀ i, -e i ∈ C := fun i => by
        have h := Finset.add_sum_erase Finset.univ e (Finset.mem_univ i)
        have : -e i = t + ∑ j ∈ Finset.univ.erase i, e j := by
          simp only [t]; rw [← h]; abel
        rw [this]
        exact C.add_mem ht (C.sum_mem fun j _ => he j)
      refine top_le_iff.mp fun v _ => ?_
      have hv : v = ∑ i, v i • e i := by
        ext j
        simp [e, Finset.sum_apply, Pi.single_apply]
      rw [hv]
      refine C.sum_mem fun i _ => ?_
      obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (v i)
      · rw [hk, natCast_zsmul]; exact C.nsmul_mem (he i) k
      · rw [hk, neg_smul, ← smul_neg, natCast_zsmul]; exact C.nsmul_mem (hne i) k
    refine (monoidRank_le hF).trans ?_
    have hc : Cardinal.mk (F : Set (Fin n → ℤ)) = (F.card : Cardinal) := by
      simpa using Cardinal.mk_coe_finset (s := F)
    rw [hc]
    have : F.card ≤ n + 1 := (Finset.card_insert_le _ _).trans (by
      simpa using Finset.card_image_le (s := Finset.univ) (f := e))
    exact_mod_cast this
  · by_contra hlt
    have hlt : Cardinal.mk E < (n : Cardinal) + 1 := not_le.mp hlt
    have hle : Cardinal.mk E ≤ Cardinal.mk (Fin n) := by
      have : Cardinal.mk E ≤ n := by
        have h' : (n : Cardinal) + 1 = ((n + 1 : ℕ) : Cardinal) := by push_cast; rfl
        rw [h'] at hlt
        obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp (hlt.trans Cardinal.natCast_lt_aleph0)
        rw [hk] at hlt ⊢
        have : k < n + 1 := by exact_mod_cast hlt
        exact_mod_cast Nat.lt_succ_iff.mp this
      simpa using this
    obtain ⟨emb⟩ := Cardinal.le_def _ _ |>.mp hle
    have hEne : Nonempty E := by
      by_contra hne
      have hE0 : E = ∅ := Set.not_nonempty_iff_eq_empty'.mp hne
      rw [hE0, AddSubmonoid.closure_empty] at hE
      have h1 : e ⟨0, hn⟩ ∈ (⊥ : AddSubmonoid (Fin n → ℤ)) := hE ▸ AddSubmonoid.mem_top _
      have := congrFun (AddSubmonoid.mem_bot.mp h1) ⟨0, hn⟩
      simp [e] at this
    let f : Fin n → E := Function.invFun emb
    have hf : Function.Surjective f := Function.invFun_surjective emb.injective
    let g : Fin n → (Fin n → ℤ) := fun i => (f i : Fin n → ℤ)
    have hcomb : ∀ w : Fin n → ℤ, ∃ p : Fin n → ℕ, w = ∑ i, p i • g i := by
      intro w
      have hw : w ∈ AddSubmonoid.closure E := hE ▸ AddSubmonoid.mem_top _
      induction hw using AddSubmonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, hi⟩ := hf ⟨x, hx⟩
        refine ⟨Pi.single i 1, ?_⟩
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
        simp [g, hi]
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨p, rfl⟩ := hx
        obtain ⟨q, rfl⟩ := hy
        exact ⟨p + q, by simp [add_smul, Finset.sum_add_distrib]⟩
    let Λ := Fintype.linearCombination ℤ g
    have hsurj : Function.Surjective Λ := fun w => by
      obtain ⟨p, rfl⟩ := hcomb w
      exact ⟨fun i => (p i : ℤ), by simp [Λ, Fintype.linearCombination_apply]⟩
    have hinj : Function.Injective Λ := IsNoetherian.injective_of_surjective_endomorphism Λ hsurj
    obtain ⟨p, hp⟩ := hcomb (-∑ i, g i)
    have hzero : Λ (fun i => (p i : ℤ) + 1) = Λ 0 := by
      have hp' : ∑ i, p i • g i + ∑ i, g i = 0 := by rw [← hp]; simp
      simpa [Λ, Fintype.linearCombination_apply, add_smul, Finset.sum_add_distrib] using hp'
    have := congrFun (hinj hzero) ⟨0, hn⟩
    simp only [Pi.zero_apply] at this
    omega

end Rank

section MonoidAlgebra

open Magnetism

variable [DecidableEq M] (R : Type*) [CommRing R] (L N : AddSubmonoid M)

/-- The elements of `L` all of whose divisors in `L` lie in `N`. It is the largest subset of `N`
closed under divisibility in `L`; it need not be a submonoid. The set of nonvanishing degrees
of the self-action of `𝔸(L)` is this set. -/
def divisorCore : Set M := {m | ∃ h : m ∈ L, ∀ l l' : L, (⟨m, h⟩ : L) = l + l' → (l : M) ∈ N}

variable {L N}

lemma divisorCore_subset : divisorCore L N ⊆ N := by
  rintro m ⟨h, hm⟩
  exact hm ⟨m, h⟩ 0 (by simp)

/-- `divisorCore L N` is closed under divisibility in `L`. -/
lemma divisorCore_of_add {m m' : L} (h : ((m + m' : L) : M) ∈ divisorCore L N) :
    (m : M) ∈ divisorCore L N := by
  obtain ⟨hL, hd⟩ := h
  refine ⟨m.2, fun l l' e => hd l (l' + m') ?_⟩
  have e' : m = l + l' := e
  rw [Subtype.coe_eta, e', add_assoc]

/-- Coefficients at positions in `divisorCore L N` vanish on `J_N` for the self-action of
`𝔸(L)`. -/
lemma coeff_eq_zero_of_mem_magnetIdeal {a : AddMonoidAlgebra R L}
    (ha : a ∈ magnetIdeal (magnetGrading L R) N) {k : L}
    (hk : (k : M) ∈ divisorCore L N) : a.coeff k = 0 := by
  let bad : Set L := {k | (k : M) ∉ divisorCore L N}
  let T : AddSubmonoid (AddMonoidAlgebra R L) :=
    AddSubmonoid.closure {x | ∃ b ∈ bad, ∃ r, x = AddMonoidAlgebra.single b r}
  have hmulT : ∀ c, ∀ x ∈ T, c * x ∈ T := by
    intro c x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, r, rfl⟩ := hx
      induction c using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add u v hu hv => rw [add_mul]; exact T.add_mem hu hv
      | single l s =>
        rw [AddMonoidAlgebra.single_mul_single]
        refine AddSubmonoid.subset_closure ⟨l + b, fun h => hb ?_, _, rfl⟩
        rw [add_comm] at h
        exact divisorCore_of_add h
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact T.add_mem hu hv
  have hJT : a ∈ T := by
    induction ha using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
      obtain ⟨m, hm, hx⟩ := hx
      by_cases hmL : m ∈ L
      · obtain ⟨c, rfl⟩ := exists_single_of_mem_magnetGrading hmL hx
        exact AddSubmonoid.subset_closure ⟨_, fun h => hm (divisorCore_subset h), c, rfl⟩
      · rw [magnetGrading_eq_bot hmL, Submodule.mem_bot] at hx
        rw [hx]; exact T.zero_mem
    | zero => exact T.zero_mem
    | add x y _ _ hx hy => exact T.add_mem hx hy
    | smul c x _ hx => exact hmulT c x hx
  clear ha
  induction hJT using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, r, rfl⟩ := hx
    have hne : b ≠ k := fun e => hb (e ▸ hk)
    simp [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hne.symm]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]

variable (N) in
/-- For the self-action of `𝔸(L)` with `R` nontrivial, the nonvanishing degrees of `X^N` are
exactly `divisorCore L N`. -/
theorem nonvanishingDegrees_eq_divisorCore [Nontrivial R] :
    nonvanishingDegrees (magnetGrading L R) (magnetIdeal (magnetGrading L R) N) =
      divisorCore L N := by
  ext m
  constructor
  · rintro ⟨a, ha, haJ⟩
    have hmL : m ∈ L := by
      by_contra hmL
      rw [magnetGrading_eq_bot hmL, Submodule.mem_bot] at ha
      exact haJ (ha ▸ Ideal.zero_mem _)
    refine ⟨hmL, fun l l' e => ?_⟩
    by_contra hl
    obtain ⟨c, rfl⟩ := exists_single_of_mem_magnetGrading hmL ha
    refine haJ ?_
    have : AddMonoidAlgebra.single (⟨m, hmL⟩ : L) c =
        AddMonoidAlgebra.single l (1 : R) * AddMonoidAlgebra.single l' c := by
      rw [AddMonoidAlgebra.single_mul_single, one_mul, e]
    rw [this]
    exact Ideal.mul_mem_right _ _ (mem_magnetIdeal_of_notMem hl (single_mem_magnetGrading l 1))
  · rintro hm
    obtain ⟨hmL, -⟩ := id hm
    refine ⟨AddMonoidAlgebra.single (⟨m, hmL⟩ : L) 1, single_mem_magnetGrading _ _, fun hJ => ?_⟩
    have := coeff_eq_zero_of_mem_magnetIdeal R hJ (k := ⟨m, hmL⟩) hm
    simp [AddMonoidAlgebra.coeff_single] at this

variable (N) in
/-- For the self-action of `𝔸(L)` over a nonempty base, `N` is pure iff it is generated by
`divisorCore L N`. This form is not in the paper; compare Example (ix) after Fact 15.11. -/
theorem isPure_self_iff [Nontrivial R] :
    IsPure (affineY (magnetGrading L R)) N ↔ N = AddSubmonoid.closure (divisorCore L N) := by
  rw [isPure_affine_iff, nonvanishingDegrees_eq_divisorCore]

/-- The monomials of degree in `E` generate `R[⟨E⟩]`. -/
lemma adjoin_magnetGrading_closure (E : Set M) :
    Algebra.adjoin R (⋃ m ∈ E, (↑(magnetGrading (AddSubmonoid.closure E) R m) : Set (AddMonoidAlgebra R (AddSubmonoid.closure E)))) = ⊤ := by
  set S := Algebra.adjoin R (⋃ m ∈ E, (↑(magnetGrading (AddSubmonoid.closure E) R m) : Set (AddMonoidAlgebra R (AddSubmonoid.closure E))))
  have hmono : ∀ (m : M) (h : m ∈ AddSubmonoid.closure E),
      AddMonoidAlgebra.single (⟨m, h⟩ : AddSubmonoid.closure E) (1 : R) ∈ S := by
    intro m h
    induction h using AddSubmonoid.closure_induction with
    | mem x hx =>
      refine Algebra.subset_adjoin ?_
      simp only [Set.mem_iUnion]
      exact ⟨x, hx, single_mem_magnetGrading _ _⟩
    | zero => exact S.one_mem
    | add x y hx hy ihx ihy =>
      have := S.mul_mem ihx ihy
      rw [AddMonoidAlgebra.single_mul_single, one_mul] at this
      exact this
  refine top_le_iff.mp fun a _ => ?_
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => exact S.zero_mem
  | add u v hu hv => exact S.add_mem (hu trivial) (hv trivial)
  | single l r =>
    have : AddMonoidAlgebra.single l r = r • AddMonoidAlgebra.single l (1 : R) := by
      simp [AddMonoidAlgebra.smul_single]
    rw [this]
    exact S.smul_mem (hmono l.1 l.2) r

/-- **Example (ix) after Fact 15.11** ([23, Proposition 3.1]). Let `M` be cancellative, `E ⊆ M`,
and let `𝔸(M)_S` act on `𝔸(⟨E⟩)_S` through the inclusion, with `S = Spec R ≠ ∅`. If (a) no proper
subset of `E` generates `⟨E⟩` and (b) `⟨E⟩` has no nonzero invertible element, then the pure
magnets are exactly the magnets generated by subsets of `E`. -/
theorem pureMagnets_self_eq [IsCancelAdd M] [Nontrivial R] (E : Set M)
    (ha : ∀ E' : Set M, E' ⊂ E → AddSubmonoid.closure E' ≠ AddSubmonoid.closure E)
    (hb : ∀ x ∈ AddSubmonoid.closure E, ∀ y ∈ AddSubmonoid.closure E, x + y = 0 → x = 0) :
    pureMagnets (affineY (magnetGrading (AddSubmonoid.closure E) R)) =
      AddSubmonoid.closure '' Set.powerset E := by
  have ha' : ∀ e ∈ E, e ∉ AddSubmonoid.closure (E \ {e}) := by
    intro e he hmem
    refine ha (E \ {e}) ⟨Set.sdiff_subset, fun h => (h he).2 rfl⟩ (le_antisymm
      (AddSubmonoid.closure_mono Set.sdiff_subset) (AddSubmonoid.closure_le.mpr fun x hx => ?_))
    by_cases hxe : x = e
    · exact hxe ▸ hmem
    · exact AddSubmonoid.subset_closure ⟨hx, hxe⟩
  ext N
  constructor
  · intro hN
    have hinter := fun K : AddSubmonoid M =>
      magnetIdeal_closure_inter (magnetGrading (AddSubmonoid.closure E) R)
        (adjoin_magnetGrading_closure R E) K
    exact ⟨(N : Set M) ∩ E, Set.inter_subset_right, (IsPure.eq_closure_inter hinter hN).symm⟩
  · rintro ⟨E', hE', rfl⟩ K hK
    refine AddSubmonoid.closure_le.mpr fun e heE' => ?_
    by_contra heK
    have heE : e ∈ E := hE' heE'
    have heL : e ∈ AddSubmonoid.closure E := AddSubmonoid.subset_closure heE
    have hdec : ∀ x ∈ AddSubmonoid.closure E, ∃ a : ℕ, ∃ z ∈ AddSubmonoid.closure (E \ {e}),
        x = a • e + z := by
      intro x hx
      induction hx using AddSubmonoid.closure_induction with
      | mem x hx =>
        by_cases hxe : x = e
        · exact ⟨1, 0, zero_mem _, by simp [hxe]⟩
        · exact ⟨0, x, AddSubmonoid.subset_closure ⟨hx, hxe⟩, by simp⟩
      | zero => exact ⟨0, 0, zero_mem _, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, z, hz, rfl⟩ := hx
        obtain ⟨b, w, hw, rfl⟩ := hy
        exact ⟨a + b, z + w, add_mem hz hw, by rw [add_smul]; abel⟩
    have hsub : AddSubmonoid.closure (E \ {e}) ≤ AddSubmonoid.closure E :=
      AddSubmonoid.closure_mono Set.sdiff_subset
    have hcore : e ∈ divisorCore (AddSubmonoid.closure E) (AddSubmonoid.closure E') := by
      refine ⟨heL, fun l l' hll' => ?_⟩
      have heq : e = (l : M) + l' := congrArg Subtype.val hll'
      obtain ⟨a, z, hz, hl⟩ := hdec l l.2
      obtain ⟨b, w, hw, hl'⟩ := hdec l' l'.2
      have heq' : e = (a + b) • e + (z + w) := by
        calc e = (l : M) + l' := heq
          _ = (a • e + z) + (b • e + w) := by rw [← hl, ← hl']
          _ = _ := by rw [add_smul]; abel
      rcases hab : a + b with _ | c
      · rw [hab, zero_smul, zero_add] at heq'
        have hm : z + w ∈ AddSubmonoid.closure (E \ {e}) := add_mem hz hw
        rw [← heq'] at hm
        exact absurd hm (ha' e heE)
      · have h0 : c • e + (z + w) = 0 := by
          apply add_left_cancel (a := e)
          rw [add_zero]
          conv_rhs => rw [heq', hab, succ_nsmul]
          abel
        have hzL := hsub hz
        have hwL := hsub hw
        have hz0 : z = 0 := hb z hzL (w + c • e) (add_mem hwL (nsmul_mem heL c))
          (by rw [← h0]; abel)
        rcases c with _ | c
        · have ha1 : a = 0 ∨ a = 1 := by omega
          rw [hl, hz0, add_zero]
          rcases ha1 with rfl | rfl
          · simpa using zero_mem _
          · simpa using AddSubmonoid.subset_closure heE'
        · have he0 : e = 0 := hb e heL (c • e + (z + w))
            (add_mem (nsmul_mem heL c) (add_mem hzL hwL))
            (by rw [← h0, succ_nsmul]; abel)
          exact absurd (he0 ▸ zero_mem _) (ha' e heE)
    have hJ := coeff_eq_zero_of_mem_magnetIdeal R (N := AddSubmonoid.closure E')
      (a := AddMonoidAlgebra.single (⟨e, heL⟩ : AddSubmonoid.closure E) 1)
      (((affineY_eq_iff _).mp hK).symm ▸
        mem_magnetIdeal_of_notMem heK (single_mem_magnetGrading (⟨e, heL⟩ : AddSubmonoid.closure E) 1))
      (k := ⟨e, heL⟩) hcore
    simp [AddMonoidAlgebra.coeff_single] at hJ

/-- If `A` has a homogeneous unit in every degree and `M ≠ 0`, `A ≠ 0`, then `Π(a) = {0, M}`. -/
theorem pureMagnets_eq_of_units {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]
    [Nontrivial A] [Nontrivial M] (𝒜 : M → Submodule R₀ A)
    (hu : ∀ m, ∃ u ∈ 𝒜 m, IsUnit u) :
    pureMagnets (affineY 𝒜) = {⊥, ⊤} := by
  have htop : ∀ K : AddSubmonoid M, K ≠ ⊤ → magnetIdeal 𝒜 K = ⊤ := by
    intro K hK
    obtain ⟨m, hm⟩ : ∃ m, m ∉ K := by
      by_contra! h
      exact hK (top_le_iff.mp fun x _ => h x)
    obtain ⟨u, hu, hunit⟩ := hu m
    exact Ideal.eq_top_of_isUnit_mem _ (mem_magnetIdeal_of_notMem hm hu) hunit
  have hTop : magnetIdeal 𝒜 (⊤ : AddSubmonoid M) = ⊥ := by
    rw [magnetIdeal, Ideal.span_eq_bot]
    simp
  have hbt : (⊥ : AddSubmonoid M) ≠ ⊤ := bot_ne_top
  ext N
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hN
    by_cases hNt : N = ⊤
    · exact Or.inr hNt
    · refine Or.inl (le_bot_iff.mp (hN ⊥ ?_))
      exact (htop N hNt).trans (htop ⊥ hbt).symm
  · rintro (rfl | rfl)
    · exact isPure_bot
    · intro K hK
      by_contra hne
      have hK' : K ≠ ⊤ := fun e => hne (by simp [e])
      have : magnetIdeal 𝒜 (⊤ : AddSubmonoid M) = magnetIdeal 𝒜 K := hK
      rw [hTop, htop K hK'] at this
      exact bot_ne_top this

/-- **Example 15.10 (ii)**, in the generality of a nonzero group: for `D(G)_S` acting on itself by
multiplication, with `S = Spec R ≠ ∅`, one has `Π(a) = {0, G}`. -/
theorem pureMagnets_group_self {G : Type*} [AddCommGroup G] [DecidableEq G] [Nontrivial G]
    [Nontrivial R] :
    pureMagnets (affineY (magnetGrading (⊤ : AddSubmonoid G) R)) = {⊥, ⊤} := by
  refine pureMagnets_eq_of_units _ fun m => ?_
  refine ⟨AddMonoidAlgebra.single (⟨m, trivial⟩ : (⊤ : AddSubmonoid G)) 1,
    single_mem_magnetGrading _ _, IsUnit.of_mul_eq_one
      (AddMonoidAlgebra.single (⟨-m, trivial⟩ : (⊤ : AddSubmonoid G)) 1) ?_⟩
  rw [AddMonoidAlgebra.single_mul_single, one_mul, AddMonoidAlgebra.one_def]
  congr 1
  exact Subtype.ext (by simp)

/-- **Example 15.10 (i)**: for the trivial action (`A` concentrated in degree `0`), `Π(a) = {0}`. -/
theorem pureMagnets_trivial {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]
    (𝒜 : M → Submodule R₀ A) (h𝒜 : ∀ m, m ≠ 0 → 𝒜 m = ⊥) :
    pureMagnets (affineY 𝒜) = {⊥} := by
  have hJ : ∀ K : AddSubmonoid M, magnetIdeal 𝒜 K = ⊥ := by
    intro K
    rw [magnetIdeal, Ideal.span_eq_bot]
    intro a ha
    simp only [Set.mem_iUnion, SetLike.mem_coe] at ha
    obtain ⟨m, hm, ha⟩ := ha
    have hm0 : m ≠ 0 := fun e => hm (e ▸ K.zero_mem)
    rwa [h𝒜 m hm0, Submodule.mem_bot] at ha
  ext N
  simp only [Set.mem_singleton_iff]
  exact ⟨fun hN => le_bot_iff.mp (hN ⊥ ((hJ N).trans (hJ ⊥).symm)), fun e => e ▸ isPure_bot⟩

/-- Audit of **Example (vi) after Fact 15.11.** If a `ℤ/6`-graded algebra `A ≠ 0` has homogeneous
units in degrees `2` and `3`, as the coordinate ring of `D(ℤ/6)³` does for the printed action,
then `Π(a) = {0, ℤ/6}`: two elements, not the four printed. -/
theorem pureMagnets_zmod_six {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A] [Nontrivial A]
    (𝒜 : ZMod 6 → Submodule R₀ A) [GradedAlgebra 𝒜] {y z : A} (hy : y ∈ 𝒜 2) (hz : z ∈ 𝒜 3)
    (huy : IsUnit y) (huz : IsUnit z) :
    pureMagnets (affineY 𝒜) = {⊥, ⊤} := by
  have : Fact (1 < 6) := ⟨by norm_num⟩
  refine pureMagnets_eq_of_units 𝒜 fun m => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, m = a • (2 : ZMod 6) + b • (3 : ZMod 6) :=
    ⟨2 * m.val, 3 * m.val, by revert m; decide⟩
  exact ⟨y ^ a * z ^ b, SetLike.mul_mem_graded (SetLike.pow_mem_graded a hy)
    (SetLike.pow_mem_graded b hz), (huy.pow a).mul (huz.pow b)⟩

/-- **Example (vii) after Fact 15.11.** `D(ℤ)` acting on `𝔸(ℕ∖{1})`, where `ℕ∖{1} = ⟨2,3⟩`:
the pure magnets are `0, 2ℕ, 3ℕ, ⟨2,3⟩`. -/
theorem pureMagnets_two_three [Nontrivial R] :
    pureMagnets (affineY (magnetGrading (AddSubmonoid.closure ({2, 3} : Set ℤ)) R)) =
      {⊥, AddSubmonoid.closure {2}, AddSubmonoid.closure {3},
        AddSubmonoid.closure ({2, 3} : Set ℤ)} := by
  have hdvd : ∀ (d x : ℤ), x ∈ AddSubmonoid.closure ({d} : Set ℤ) → d ∣ x := by
    intro d x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]
    | zero => exact dvd_zero d
    | add x y _ _ hx hy => exact dvd_add hx hy
  have hnn : ∀ x ∈ AddSubmonoid.closure ({2, 3} : Set ℤ), 0 ≤ x := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl <;> norm_num
    | zero => exact le_rfl
    | add x y _ _ hx hy => exact add_nonneg hx hy
  have h2 : (2 : ℤ) ∈ AddSubmonoid.closure ({2, 3} : Set ℤ) :=
    AddSubmonoid.subset_closure (by simp)
  have h3 : (3 : ℤ) ∈ AddSubmonoid.closure ({2, 3} : Set ℤ) :=
    AddSubmonoid.subset_closure (by simp)
  rw [pureMagnets_self_eq R _ ?_ ?_]
  · ext N
    constructor
    · rintro ⟨E', hE', rfl⟩
      rw [Set.mem_powerset_iff, Set.subset_pair_iff_eq] at hE'
      rcases hE' with rfl | rfl | rfl | rfl <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl | rfl | rfl)
      · exact ⟨∅, by simp, AddSubmonoid.closure_empty⟩
      · exact ⟨{2}, by simp, rfl⟩
      · exact ⟨{3}, by simp, rfl⟩
      · exact ⟨_, Set.mem_powerset (Set.Subset.refl _), rfl⟩
  · intro E' hE' heq
    obtain ⟨e, he, heE'⟩ := Set.exists_of_ssubset hE'
    rcases he with rfl | he
    · have hle : AddSubmonoid.closure E' ≤ AddSubmonoid.closure {3} :=
        AddSubmonoid.closure_mono fun x hx => by
          rcases hE'.1 hx with rfl | h
          · exact absurd hx heE'
          · exact h
      have := hdvd 3 2 (hle (heq ▸ h2))
      omega
    · rw [Set.mem_singleton_iff.mp he] at heE'
      have hle : AddSubmonoid.closure E' ≤ AddSubmonoid.closure {2} :=
        AddSubmonoid.closure_mono fun x hx => by
          rcases hE'.1 hx with h | h
          · exact h
          · rw [Set.mem_singleton_iff.mp h] at hx
            exact absurd hx heE'
      have := hdvd 2 3 (hle (heq ▸ h3))
      omega
  · intro x hx y hy h
    have := hnn x hx
    have := hnn y hy
    omega

end MonoidAlgebra

section Convention

open Magnetism

universe u

variable [DecidableEq M] {R₀ : Type*} {A : Type u} [CommRing R₀] [CommRing A] [Algebra R₀ A]
variable (𝒜 : M → Submodule R₀ A) [GradedAlgebra 𝒜]

/-- The image of `X^N(C)` in `X(C) = Hom_{R₀}(A, C)` consists of the maps killing `J_N`. -/
theorem range_psiAux (N : AddSubmonoid M) (C : Type*) [CommRing C] [Algebra R₀ C] :
    Set.range (psiAux : Attractor 𝒜 N C → (A →ₐ[R₀] C)) = {f | ∀ a ∈ magnetIdeal 𝒜 N, f a = 0} := by
  ext f
  constructor
  · rintro ⟨φ, rfl⟩ a ha
    exact psiAux_eq_zero_of_mem_magnetIdeal φ ha
  · intro hf
    let F : (A ⧸ magnetIdeal 𝒜 N) →ₐ[R₀] C := Ideal.Quotient.liftₐ _ f hf
    refine ⟨theta 𝒜 N C F, AlgHom.ext fun a => ?_⟩
    have h := congrArg (fun G : (A ⧸ magnetIdeal 𝒜 N) →ₐ[R₀] C =>
      G (Ideal.Quotient.mkₐ R₀ (magnetIdeal 𝒜 N) a)) (psi_theta F)
    exact h

/-- The convention of Theorem 15.3 in the affine case: `X^N(C)` and `X^L(C)` agree inside `X(C)`
for all `C` iff `J_N = J_L`, i.e. iff `affineY 𝒜 N = affineY 𝒜 L`. -/
theorem magnetIdeal_eq_iff_range_eq (N L : AddSubmonoid M) :
    magnetIdeal 𝒜 N = magnetIdeal 𝒜 L ↔
      ∀ (C : Type u) [CommRing C] [Algebra R₀ C],
        Set.range (psiAux : Attractor 𝒜 N C → (A →ₐ[R₀] C)) =
          Set.range (psiAux : Attractor 𝒜 L C → (A →ₐ[R₀] C)) := by
  constructor
  · intro h C _ _
    rw [range_psiAux, range_psiAux, h]
  · have key : ∀ N L : AddSubmonoid M, (∀ (C : Type u) [CommRing C] [Algebra R₀ C],
        Set.range (psiAux : Attractor 𝒜 N C → (A →ₐ[R₀] C)) =
          Set.range (psiAux : Attractor 𝒜 L C → (A →ₐ[R₀] C))) →
        magnetIdeal 𝒜 L ≤ magnetIdeal 𝒜 N := by
      intro N L h a ha
      have hmem : Ideal.Quotient.mkₐ R₀ (magnetIdeal 𝒜 N) ∈
          Set.range (psiAux : Attractor 𝒜 L (A ⧸ magnetIdeal 𝒜 N) →
            (A →ₐ[R₀] (A ⧸ magnetIdeal 𝒜 N))) := by
        rw [← h, range_psiAux]
        intro b hb
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
      rw [range_psiAux] at hmem
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hmem a ha)
    intro h
    exact le_antisymm (key L N fun C _ _ => (h C).symm) (key N L h)

end Convention

end AlgMag
