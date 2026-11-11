/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.DoubleScalarCombi
import AlgMag.DoubleScalarChartAttr
import AlgMag.Sec15General
import AlgMag.Sec3Final

/-!
# Algebraic magnetism invariants of a double scalar action on the projective plane

A. Mayeux, arXiv:2509.04274v3.

`S = Spec R` with `R` a nonzero commutative ring (the printed Proposition 4.1 needs `S ≠ ∅`), and `ℙ²` is the functor
of rank one summands on affine `S`-schemes. Coordinates `x = 0, y = 1, z = 2`.

## Main results

* `AlgMag.DoubleScalar.act_formula`: the action of §3.
* `AlgMag.DoubleScalar.prop41`, `AlgMag.DoubleScalar.ncard_pure`: **Proposition 4.1**, and the `29` pure magnets.
* `AlgMag.DoubleScalar.lem42` (`DoubleScalarChartAttr`): **Lemma 4.2**.
* `AlgMag.DoubleScalar.pure_eq_fig2`, `AlgMag.DoubleScalar.fig2_attractor`, `AlgMag.DoubleScalar.fig2_comp`,
  `AlgMag.DoubleScalar.fig2_disjoint`, `AlgMag.DoubleScalar.fig2_glue`, `AlgMag.DoubleScalar.zunion_p1`: **§5, Figures 1 and 2**.
* `AlgMag.DoubleScalar.printed_misprint`: the misprint on p. 7.
* `AlgMag.DoubleScalar.magnetClass`, `AlgMag.DoubleScalar.prop62`, `AlgMag.DoubleScalar.IsLambdafiable`,
  `AlgMag.DoubleScalar.prop64`, `AlgMag.DoubleScalar.prop64_p2`: **Definitions 6.1, 6.3, Propositions 6.2, 6.4**.
* `AlgMag.DoubleScalar.prop65`, `AlgMag.DoubleScalar.prop65_count`: **Proposition 6.5**.
* `AlgMag.DoubleScalar.rem66`: **Remark 6.6**.

## Proofs and remarks

Remark 5.1 (i) is not a precise statement; for `ℙ(ι)` with any diagonal action its content is
`AlgMag.DoubleScalar.mem_image_iff_zunion` and `AlgMag.DoubleScalar.pureMagnets_bijOn`. Remark 5.1 (ii) mentions `SL₃`,
outside this formalization; `AlgMag.DoubleScalar.phi_eq_diff` shows that `Φ` is the set of the `w i - w j`.

**The proof of Proposition 4.1.** The printed proof of surjectivity says "*Since `X^N = X^L`, we have
`(𝔸²)^N = (𝔸²)^L` for all `s`*". No reason is given, and restricting to a stable open does not give this: for
`U = 𝔾_m ⊂ X = 𝔸¹`, `X^ℕ = X^ℤ` and `U^ℕ ≠ U^ℤ` (`a1_image_eq`, `gm_image_ne`). The conclusion is true for the charts
of the paper, by the tangent vector at the fixed point of the chart (`mem_of_tangent`, `image_eq_iff_chart_attr`). A
proof on points over a field can not work: `[1 : u]` is both in `X^ℕ` and `X^ℤ` for `ℙ¹`. The proposition is true, and
so are the count `29` and Proposition 6.5, which relies on it.

**§7** announces the results of [4] on finiteness for stacks, which are not formalized here. The cited implication
"a strongly-FPR atlas gives finitely many pure magnets" of *Algebraic Magnetism* is `AlgMag.thm154_ii`,
`AlgMag.thm154_ii_lfp`, and the conjecture is `AlgMag.Conj69ii`.
-/

open CategoryTheory Opposite Matrix AlgebraicGeometry

set_option linter.unusedSectionVars false

namespace AlgMag.DoubleScalar

/-! ### Definitions 6.1, 6.3, Propositions 6.2, 6.4, in general -/

section Lambda

variable {M : Type*} [AddCommGroup M] {α : Type*}

/-- **Definition 6.1.** `m^N(a) = {N' ∈ m(a) | X^N = X^{N'}}`. -/
def magnetClass (Y : AddSubmonoid M → α) (N : AddSubmonoid M) : Set (AddSubmonoid M) := {N' | Y N = Y N'}

/-- **§6.1.** The purification `E(N)` of the magnet `N`. -/
def purification (Y : AddSubmonoid M → α) (N : AddSubmonoid M) : AddSubmonoid M :=
  pureOf Y (Y N)

/-- **§6.1: the decomposition `m(a) = ⨆_{N ∈ Π(a)} m^N(a)`.** Each magnet is in the class of exactly one pure
magnet. As in Theorem 15.3 of *Algebraic Magnetism*, this needs the conclusion of Fact 3.34 (`AttractorOrder`); this
hypothesis is not visible in §6.1, where `X` is any separated algebraic space. -/
theorem existsUnique_pure [CompleteLattice α] {Y : AddSubmonoid M → α} (hY : AttractorOrder Y)
    (N : AddSubmonoid M) : ∃! P, IsPure Y P ∧ N ∈ magnetClass Y P := by
  refine ⟨pureOf Y (Y N), ⟨isPure_pureOf hY ⟨N, rfl⟩, map_pureOf hY ⟨N, rfl⟩⟩, ?_⟩
  rintro P ⟨hP, hc⟩
  have hc' : Y P = Y N := hc
  rw [← hc']
  exact (IsPure.pureOf_map hP hY).symm

/-- **Proposition 6.2.** Let `f : M → ℤ`. These are equivalent: (i) `X^{f⁻¹(ℕ)} = X^N`, (ii) `E(f⁻¹(ℕ)) = E(N)`,
(iii) `f⁻¹(ℕ) ∈ m^N(a)`, (iv) there are `N', N'' ∈ m^N(a)` with `N' ⊂ f⁻¹(ℕ) ⊂ N''`. -/
theorem prop62 [CompleteLattice α] {Y : AddSubmonoid M → α} (hY : AttractorOrder Y) (f : M →+ ℤ)
    (N : AddSubmonoid M) :
    List.TFAE [Y (posN.comap f) = Y N,
      purification Y (posN.comap f) = purification Y N,
      posN.comap f ∈ magnetClass Y N,
      ∃ N' ∈ magnetClass Y N, ∃ N'' ∈ magnetClass Y N, N' ≤ posN.comap f ∧ posN.comap f ≤ N''] := by
  tfae_have 1 → 2 := fun h => by
    unfold purification
    rw [h]
  tfae_have 2 → 3 := fun h => by
    have h1 := map_pureOf hY (y := Y (posN.comap f)) ⟨_, rfl⟩
    have h2 := map_pureOf hY (y := Y N) ⟨_, rfl⟩
    unfold purification at h
    rw [h, h2] at h1
    exact h1
  tfae_have 3 → 4 := fun h => ⟨_, h, _, h, le_rfl, le_rfl⟩
  tfae_have 4 → 1 := by
    rintro ⟨N', h1, N'', h2, h3, h4⟩
    have h1' : Y N = Y N' := h1
    have h2' : Y N = Y N'' := h2
    refine le_antisymm ?_ ?_
    · rw [h2']
      exact hY.monotone h4
    · rw [h1']
      exact hY.monotone h3
  tfae_finish

/-- **Definition 6.3.** `N` is `a`-lambdafiable if there is `f : M → ℤ` with the equivalent properties of
Proposition 6.2. -/
def IsLambdafiable (Y : AddSubmonoid M → α) (N : AddSubmonoid M) : Prop :=
  ∃ f : M →+ ℤ, Y (posN.comap f) = Y N

end Lambda

/-- **Proposition 6.4.** For a scheme `X` over any `S`, `M` countable (`M` finitely generated in the paper) and `N`
lambdafiable, there is `λ : 𝔾_m → D(M)`, dual to `f : M → ℤ`, such that `X^+ = X^N`: on the left the `𝔾_m`-action
through `λ`, on the right the `D(M)`-action. The printed proof cites Proposition 3.31 (ii) of *Algebraic
Magnetism* (numbered 3.30 in arXiv:2203.08231), which is `AlgMag.prop331_ii`. That Lean statement is for schemes;
the paper allows `X` a separated algebraic space. See `prop64_p2` for `ℙ²`. -/
theorem prop64 {B : BigFppfSite.{0}} {S : AlgebraicGeometry.Scheme.{0}} {hS : B.Contains S}
    {M : Type} [AddCommGroup M] [Countable M] {U : BigFppfOver B S hS}
    {aX : AAction (fppfO B S hS) M (yoneda.obj U)} {N : AddSubmonoid M}
    (h : IsLambdafiable (attractorImage aX) N) :
    ∃ f : M →+ ℤ, attractorImage (actAlong f aX) posN = attractorImage aX N := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, Eq.trans ?_ hf⟩
  funext T
  ext x
  constructor
  · rintro ⟨ψ, rfl⟩
    obtain ⟨χ, rfl⟩ := (prop331_ii (f := f) (Y := posN) (aX := aX) T).2 ψ
    exact ⟨χ, (toPoint_ptAlong χ).symm⟩
  · rintro ⟨χ, rfl⟩
    exact ⟨ptAlong aX χ, toPoint_ptAlong χ⟩

/-! ### General lemmas on `ℙ(ι)` -/

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R]
variable {M : Type} [AddCommGroup M] (w : ι → M)

/-- `AttractorOrder` for `ℙ(ι)`, so that §15 applies. The stronger statement that a point lying in `X^{N_i}` for all
`i` lies in `X^{⋂ N_i}` is false by Remark 3.25 of *Algebraic Magnetism*. -/
theorem attractorOrder_pn [Nontrivial R] : AttractorOrder (attractorImage (pnAction R w)) where
  monotone := attractorImage_monotone _
  sInf_of_const s y := by
    rintro ⟨N₀, h₀⟩ h
    rw [← h N₀ h₀]
    refine image_eq_of_inter w (Set.Subset.antisymm ?_ ?_)
    · exact fun x hx => ⟨sInf_le h₀ hx.1, hx.2⟩
    · rintro x ⟨hx, hO⟩
      refine ⟨?_, hO⟩
      refine AddSubmonoid.mem_sInf.mpr fun L hL => ?_
      have e := (image_eq_iff w).mp ((h N₀ h₀).trans (h L hL).symm)
      have : x ∈ (N₀ : Set M) ∩ Om w := ⟨hx, hO⟩
      rw [e] at this
      exact this.1

/-- **Sanity check of the definition of `ℙ(ι)`.** Over a local ring, the rank one summands of `D^ι` are the lines
spanned by a vector with a coordinate equal to one. -/
theorem isLineN_iff_of_isLocalRing {D : Type} [CommRing D] [IsLocalRing D] {K : Submodule D (ι → D)} :
    IsLineN K ↔ ∃ (s : ι) (v : ι → D), v s = 1 ∧ K = Submodule.span D {v} := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨s, -, hs⟩ : ∃ s ∈ (Finset.univ : Finset ι), IsUnit (P s s) := by
      by_contra hn
      push Not at hn
      have h1 : (∑ i, P i i) ∈ IsLocalRing.maximalIdeal D :=
        Ideal.sum_mem _ fun i _ => (IsLocalRing.mem_maximalIdeal _).mpr (hn i (Finset.mem_univ i))
      have h2 : ∑ i, P i i = 1 := hP.trace_eq
      rw [h2] at h1
      exact (IsLocalRing.mem_maximalIdeal _).mp h1 isUnit_one
    obtain ⟨g, hg⟩ := hs.exists_right_inv
    have hv : (fun i => g * P i s) s = 1 := by
      change g * P s s = 1
      rw [mul_comm]; exact hg
    refine ⟨s, fun i => g * P i s, hv, ?_⟩
    refine rng_eq_span_of_fixed hP (s := s) hv ?_
    funext i
    have := congrFun (col_fixed hP.idem s) i
    change ∑ k, P i k * (g * P k s) = g * P i s
    change ∑ k, P i k * P k s = P i s at this
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rintro ⟨s, v, hv, rfl⟩
    exact ⟨chartProj s v, isRankOneProj_chartProj s hv, (rng_chartProj s hv).symm⟩

/-- A projector is locally in the charts of its columns, for any family of charts covering its diagonal. -/
theorem zunion_of_proj' {D : Type} [CommRing D] {α : Type} [Fintype α] {s : α → ι} {S : α → Finset ι}
    {Q : Matrix ι ι D} (hQ : IsRankOneProj Q)
    (hcov : Ideal.span (Set.range fun a => Q (s a) (s a)) = ⊤)
    (hsupp : ∀ a i, i ≠ s a → i ∉ S a → Q i (s a) = 0) : ZUnion s S (rng Q) := by
  classical
  refine ⟨fun a => Q (s a) (s a), hcov, fun a => ?_⟩
  let A := Localization.Away (Q (s a) (s a))
  let φ := algebraMap D A
  obtain ⟨g, hg⟩ : ∃ g : A, φ (Q (s a) (s a)) * g = 1 :=
    (IsLocalization.Away.algebraMap_isUnit (Q (s a) (s a)) : IsUnit (φ _)).exists_right_inv
  let v : ι → A := fun i => g * φ (Q i (s a))
  have hQ' := hQ.map φ
  have hvs : v (s a) = 1 := by
    change g * φ (Q (s a) (s a)) = 1
    rw [mul_comm]; exact hg
  refine ⟨v, ⟨hvs, fun j hj hjS => ?_⟩, ?_⟩
  · change g * φ (Q j (s a)) = 0
    rw [hsupp a j hj hjS, map_zero, mul_zero]
  · rw [bcv_rng]
    refine rng_eq_span_of_fixed hQ' (s := s a) hvs ?_
    have hc := col_fixed hQ'.idem (s a)
    funext i
    have := congrFun hc i
    change ∑ k, φ (Q i k) * (g * φ (Q k (s a))) = g * φ (Q i (s a))
    change ∑ k, φ (Q i k) * φ (Q k (s a)) = φ (Q i (s a)) at this
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The diagonal of a rank one projector with orthogonal diagonal entries is a rank one projector. -/
lemma isRankOneProj_diag {D : Type} [CommRing D] {P : Matrix ι ι D} (hP : IsRankOneProj P)
    (h : ∀ i j, i ≠ j → P i i * P j j = 0) :
    IsRankOneProj (Matrix.of fun i j => (if i = j then (1 : D) else 0) * P i j) := by
  have htr : ∑ i, P i i = 1 := hP.trace_eq
  refine ⟨?_, ?_, ?_⟩
  · ext i k
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single i]
    · by_cases hik : i = k
      · subst hik
        simp only [ite_true, one_mul]
        calc P i i * P i i = ∑ j, P i i * P j j := by
              rw [Finset.sum_eq_single i]
              · intro j _ hj
                exact h i j (Ne.symm hj)
              · simp
          _ = P i i := by rw [← Finset.mul_sum, htr, mul_one]
      · simp [hik]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · simpa [Matrix.trace] using htr
  · intro i j k l
    simp only [Matrix.of_apply]
    by_cases h1 : i = j
    · subst h1
      by_cases h2 : k = l
      · subst h2
        by_cases h3 : i = k
        · subst h3; simp
        · simp [h3, Ne.symm h3, h i k h3]
      · by_cases h3 : i = l
        · subst h3
          by_cases h4 : k = i
          · exact absurd h4 h2
          · simp [h4]
        · simp [h2, h3]
    · by_cases h3 : i = l
      · subst h3
        by_cases h4 : k = j
        · subst h4
          simp [h1, Ne.symm h1, h i k h1]
        · simp [h1, h4]
      · simp [h1, h3]

/-- **Proposition 6.4 for `ℙ(ι)`, over any base.** For `f : M → ℤ`, the `𝔾_m`-action through `λ` dual to `f` has
weights `f ∘ w`, and `X^+ = X^{f⁻¹(ℕ)}`. -/
theorem prop64_p2 (f : M →+ ℤ) :
    attractorImage (pnAction R (fun i => f (w i))) posN = attractorImage (pnAction R w) (posN.comap f) := by
  funext T
  ext K
  rw [mem_image_iff (D := unop T), mem_image_iff (D := unop T)]
  have e : ∀ i j, f (w i) - f (w j) ∉ posN ↔ w i - w j ∉ posN.comap f := by
    intro i j
    rw [AddSubmonoid.mem_comap, map_sub]
  simp only [e]

/-- The action of `𝔾_m` in `prop64_p2` is the action through `λ`: `t • K = λ(t) • K`. -/
theorem smul_along (f : M →+ ℤ) {U : (Aff R)ᵒᵖ} (h : APt (affO R) ℤ U) (K : (pn ι R).obj U) :
    (pnAction R (fun i => f (w i))).smul h K =
      (pnAction R w).smul (h.comp (AddMonoidHom.toMultiplicative f)) K := rfl

end General

/-! ### The double scalar action on `ℙ²` -/

section P2

variable {R : Type} [CommRing R]

/-- **§3.** The double scalar action `(λ, β) · [x : y : z] = [λx : βy : z]` of `D(ℤ²)` on `ℙ²`. -/
noncomputable abbrev dsAct (R : Type) [CommRing R] : AAction (affO R) (ℤ × ℤ) (pn (Fin 3) R) :=
  pnAction R wP

/-- **§3.** The formula of the action: with `λ = h(1,0)`, `β = h(0,1)`, the action sends the line through
`(x, y, z)` to the line through `(λx, βy, z)`. -/
theorem act_formula {D : CommAlgCat.{0} R} (h : Multiplicative (ℤ × ℤ) →* D) (v : Fin 3 → D) :
    (dgl fun i => h (Multiplicative.ofAdd (wP i))) v =
      ![h (Multiplicative.ofAdd (1, 0)) * v 0, h (Multiplicative.ofAdd (0, 1)) * v 1, v 2] := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · change h (Multiplicative.ofAdd (0, 0)) * v 2 = v 2
    have : Multiplicative.ofAdd ((0, 0) : ℤ × ℤ) = 1 := rfl
    rw [this, map_one, one_mul]

lemma om_eq : Om wP = (Phi : Set (ℤ × ℤ)) := by
  ext m
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact phi_eq_diff.1 i j hij
  · intro hm
    obtain ⟨i, j, hij, e⟩ := phi_eq_diff.2 m hm
    exact ⟨i, j, hij, e⟩

/-- **Proposition 4.1.** The set of pure magnets of `a` identifies with the additively stable subsets of `Φ`; the
bijection sends a pure magnet `N` to `N ∩ Φ`, and `E` to `[E⟩` in the other direction (`isPure_closure`). -/
theorem prop41 [Nontrivial R] :
    Set.BijOn (fun N : AddSubmonoid (ℤ × ℤ) => (N : Set (ℤ × ℤ)) ∩ (Phi : Set (ℤ × ℤ)))
      (pureMagnets (attractorImage (dsAct R))) {E | E ⊆ (Phi : Set (ℤ × ℤ)) ∧ AddStable E} := by
  have h := pureMagnets_bijOn (R := R) wP
  have e : {E | AddStableIn wP E} = {E : Set (ℤ × ℤ) | E ⊆ (Phi : Set (ℤ × ℤ)) ∧ AddStable E} := by
    ext E
    change (E ⊆ Om wP ∧ _ ∩ Om wP = E) ↔ _
    rw [om_eq]
    rfl
  rw [e] at h
  simp only [om_eq] at h
  exact h

/-- The stable subsets of `Φ` are those of `Closed` type. -/
lemma stable_set_eq : {E : Set (ℤ × ℤ) | E ⊆ (Phi : Set (ℤ × ℤ)) ∧ AddStable E} =
    (fun F : Finset (ℤ × ℤ) => (F : Set (ℤ × ℤ))) '' (Phi.powerset.filter Closed : Finset _) := by
  classical
  ext E
  constructor
  · rintro ⟨h1, h2⟩
    have e : ((Phi.filter (· ∈ E) : Finset _) : Set (ℤ × ℤ)) = E := by
      ext x
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨h1 h, h⟩⟩
    refine ⟨Phi.filter (· ∈ E), ?_, e⟩
    have hs : Phi.filter (· ∈ E) ⊆ Phi := Finset.filter_subset _ _
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs, ?_⟩)
    refine (addStable_iff_closed hs).mp ?_
    rw [e]
    exact h2
  · rintro ⟨F, hF, rfl⟩
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hF)
    have hs := Finset.mem_powerset.mp h1
    exact ⟨hs, addStable_of_closed hs h2⟩

/-- **§4.** There are `29` pure magnets. -/
theorem ncard_pure [Nontrivial R] : (pureMagnets (attractorImage (dsAct R))).ncard = 29 := by
  have h := prop41 (R := R)
  rw [stable_set_eq] at h
  have e1 := h.injOn.ncard_image
  rw [h.image_eq, Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset,
    card_stable] at e1
  exact e1.symm

/-- The magnet of a row of Figures 1, 2. -/
def Row.magnet (r : Row) : AddSubmonoid (ℤ × ℤ) := AddSubmonoid.closure {x | x ∈ r.gens}

lemma Row.mem_magnet_iff {r : Row} (h : r.Good) {m : ℤ × ℤ} (hm : m ∈ Phi) : m ∈ r.magnet ↔ m ∈ r.E := by
  have e := Row.closure_inter h
  constructor
  · intro hx
    have : m ∈ ((r.magnet : AddSubmonoid (ℤ × ℤ)) : Set (ℤ × ℤ)) ∩ (Phi : Set (ℤ × ℤ)) := ⟨hx, hm⟩
    rw [Row.magnet, e] at this
    exact this
  · intro hx
    have : m ∈ (r.E : Set (ℤ × ℤ)) := hx
    rw [← e] at this
    exact this.1

/-- **Figure 1.** The pure magnets are exactly the magnets of the rows of the figure, with `0` and `ℤ²`. -/
theorem pure_eq_fig2 [Nontrivial R] :
    pureMagnets (attractorImage (dsAct R)) = {N | ∃ r ∈ fig2, N = r.magnet} := by
  have hpure : ∀ r ∈ fig2, IsPure (attractorImage (dsAct R)) r.magnet := by
    intro r hr
    have h := fig2_good r hr
    refine (isPure_iff wP).mpr ?_
    apply le_antisymm
    · refine AddSubmonoid.closure_le.mpr fun x hx => AddSubmonoid.subset_closure ?_
      refine ⟨AddSubmonoid.subset_closure hx, ?_⟩
      rw [om_eq]
      exact h.1 (List.mem_toFinset.mpr hx)
    · exact AddSubmonoid.closure_le.mpr Set.inter_subset_left
  ext N
  constructor
  · intro hN
    have hst := (prop41 (R := R)).mapsTo hN
    rw [stable_set_eq] at hst
    obtain ⟨F, hF, e⟩ := hst
    have hF' : F ∈ (fig2.map Row.E).toFinset := by
      rw [fig2_complete.2]
      exact Finset.mem_coe.mp hF
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hF')
    refine ⟨r, hr, (prop41 (R := R)).injOn hN (hpure r hr) ?_⟩
    exact e.symm.trans (Row.closure_inter (fig2_good r hr)).symm
  · rintro ⟨r, hr, rfl⟩
    exact hpure r hr

/-- **Figure 1.** The inclusions of pure magnets are the inclusions of the stable sets. -/
theorem fig1_le {r r' : Row} (hr : r ∈ fig2) (hr' : r' ∈ fig2) : r.magnet ≤ r'.magnet ↔ r.E ⊆ r'.E := by
  have h := fig2_good r hr
  have h' := fig2_good r' hr'
  have hsub : r.E ⊆ Phi := step_subset_phi (step_subset_phi h.1)
  constructor
  · intro hle x hx
    exact (Row.mem_magnet_iff h' (hsub hx)).mp (hle ((Row.mem_magnet_iff h (hsub hx)).mpr hx))
  · intro hle
    refine AddSubmonoid.closure_le.mpr fun x hx => ?_
    have hxP : x ∈ Phi := h.1 (List.mem_toFinset.mpr hx)
    exact (Row.mem_magnet_iff h' hxP).mpr
      (hle (subset_step _ (subset_step _ (List.mem_toFinset.mpr hx))))

/-- **§5.** Every attractor contains the fixed locus, the attractor of `0`, and is contained in `ℙ²`, the attractor
of `ℤ²`. -/
theorem attractor_bounds (N : AddSubmonoid (ℤ × ℤ)) :
    attractorImage (dsAct R) ⊥ ≤ attractorImage (dsAct R) N ∧
      attractorImage (dsAct R) N ≤ attractorImage (dsAct R) ⊤ ∧
      ∀ (T : Aff R) (K : (pn (Fin 3) R).obj (op T)), K ∈ attractorImage (dsAct R) ⊤ T := by
  refine ⟨attractorImage_monotone _ bot_le, attractorImage_monotone _ le_top, fun T K => ?_⟩
  exact ⟨(attractorTopEquiv (dsAct R) T).symm K, (attractorTopEquiv (dsAct R) T).apply_symm_apply K⟩

/-- **§5, Figure 2.** For each row, the attractor `X^N` is the Zariski union of the charts `𝔸^{S s}` of the row, read
off from Lemma 4.2. With `fig2_disjoint`, `fig2_glue`, `zunion_p1` this is the printed entry: the charts in different
components are disjoint (`⊔`), and those in one component are glued in `ℙ²` (`∪_{ℙ²}`, `ℙ¹`). -/
theorem fig2_attractor {r : Row} (hr : r ∈ fig2) {D : CommAlgCat.{0} R}
    (K : (pn (Fin 3) R).obj (op (op D))) :
    K ∈ attractorImage (dsAct R) r.magnet (op D) ↔ ZUnion (id : Fin 3 → Fin 3) r.S K.1 := by
  have h := fig2_good r hr
  rw [mem_image_iff_zunion]
  have e : chartS wP r.magnet = r.S := by
    funext s
    ext j
    rw [mem_chartS, h.2.2.1 s j]
    refine and_congr_right fun hj => ?_
    exact Row.mem_magnet_iff h (phi_eq_diff.1 j s hj)
  rw [e]

/-- **§5.** The components of a row: two fixed points are in one component of `X^N` iff they have the same label. -/
theorem fig2_comp {r : Row} (hr : r ∈ fig2) (i j : Fin 3) :
    CompRel wP r.magnet i j ↔ r.cl i = r.cl j := by
  have h := fig2_good r hr
  rw [h.2.2.2 i j]
  by_cases hij : i = j
  · subst hij
    simp [CompRel]
  · simp only [hij, false_or, CompRel]
    exact and_congr (Row.mem_magnet_iff h (phi_eq_diff.1 i j hij))
      (Row.mem_magnet_iff h (phi_eq_diff.1 j i (Ne.symm hij)))

/-- **§5, Figure 2, `⊔`.** Two different charts of a row which are in different components do not meet. -/
theorem fig2_disjoint {r : Row} (hr : r ∈ fig2) {D : Type} [CommRing D] [Nontrivial D] {s t : Fin 3}
    (hst : s ≠ t) {K : Submodule D (Fin 3 → D)} (hK : IsLineN K) (h1 : InChart s (r.S s) K)
    (h2 : InChart t (r.S t) K) : r.cl s = r.cl t := by
  have h := fig2_good r hr
  obtain ⟨a, b⟩ := chart_disjoint hst hK h1 h2
  exact (h.2.2.2 s t).mpr (Or.inr ⟨((h.2.2.1 t s).mp b).2, ((h.2.2.1 s t).mp a).2⟩)

/-- **§5, Figure 2, `∪_{ℙ²}`.** Two different charts of a row which are in the same component are glued along the
locus where the coordinate is invertible: `𝔸¹ ∖ {z} = 𝔸¹ ∖ {y}` for `[±(0,1)⟩`. -/
theorem fig2_glue {r : Row} (hr : r ∈ fig2) {D : Type} [CommRing D] {s t : Fin 3} (hst : s ≠ t)
    (hc : r.cl s = r.cl t) {v : Fin 3 → D} (hv : IsChartVec s (r.S s) v) {g : D} (hg : v t * g = 1) :
    IsChartVec t (r.S t) (fun i => g * v i) ∧
      Submodule.span D {fun i => g * v i} = Submodule.span D {v} := by
  have h := fig2_good r hr
  obtain ⟨h1, h2⟩ := ((h.2.2.2 s t).mp hc).resolve_left hst
  have hs' : s ∈ r.S t := (h.2.2.1 t s).mpr ⟨hst, h1⟩
  have hS : ∀ j ∈ r.S s, j ≠ t → j ∈ r.S t := by
    intro j hj hjt
    obtain ⟨hjs, hjE⟩ := (h.2.2.1 s j).mp hj
    refine (h.2.2.1 t j).mpr ⟨hjt, ?_⟩
    have hc := h.2.1 _ hjE _ h1 (by
      rw [show wP j - wP s + (wP s - wP t) = wP j - wP t by abel]
      exact phi_eq_diff.1 j t hjt)
    rwa [show wP j - wP s + (wP s - wP t) = wP j - wP t by abel] at hc
  obtain ⟨a, -, c⟩ := chart_glue hst hS hs' hv hg
  exact ⟨a, c⟩

/-- **§5, the notation `ℙ¹`.** Let `r` be the third coordinate. The union of the chart `𝔸¹` of `s` and the chart `𝔸¹`
of `t`, glued as in `chart_glue`, is the set of lines of the plane `v_r = 0`. -/
theorem zunion_p1 {D : Type} [CommRing D] {r s t : Fin 3} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    {K : Submodule D (Fin 3 → D)} (hK : IsLineN K) :
    ZUnion (![s, t] : Fin 2 → Fin 3) ![{t}, {s}] K ↔ ∀ v ∈ K, v r = 0 := by
  classical
  obtain ⟨P, hP, rfl⟩ := hK
  have hall : ∀ i : Fin 3, i = r ∨ i = s ∨ i = t := by decide +revert
  constructor
  · intro h
    obtain ⟨Q, hQ, e, hsupp⟩ := exists_proj_of_zunion hP h
    intro v hv
    rw [← e] at hv
    have hfix := (mem_rng_iff hQ.idem).mp hv
    rw [← hfix]
    change ∑ k, Q r k * v k = 0
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hz : Q r k = 0
    · rw [hz, zero_mul]
    · exfalso
      obtain ⟨a, ha, h1⟩ := hsupp r k hz
      fin_cases a
      · change s = k at ha
        subst ha
        rcases h1 with h1 | h1
        · exact hrs h1
        · exact hrt (Finset.mem_singleton.mp h1)
      · change t = k at ha
        subst ha
        rcases h1 with h1 | h1
        · exact hrt h1
        · exact hrs (Finset.mem_singleton.mp h1)
  · intro h
    have hrow : ∀ j, P r j = 0 := fun j => h _ (col_mem_rng P j)
    have htr : P s s + P t t = 1 := by
      have := hP.trace_eq
      simp only [Matrix.trace, Matrix.diag_apply] at this
      have hdec : ∑ i : Fin 3, P i i = P r r + P s s + P t t := by
        have e : (Finset.univ : Finset (Fin 3)) = {r, s, t} :=
          Finset.ext fun i => by simpa using hall i
        rw [e, Finset.sum_insert (by simp [hrs, hrt]), Finset.sum_insert (by simp [hst]),
          Finset.sum_singleton]
        ring
      rw [hdec, hrow r, zero_add] at this
      exact this
    refine zunion_of_proj' hP ?_ ?_
    · rw [Ideal.eq_top_iff_one, ← htr]
      refine Ideal.add_mem _ (Ideal.subset_span ⟨0, rfl⟩) (Ideal.subset_span ⟨1, rfl⟩)
    · intro a i h1 h2
      fin_cases a
      · have h1' : i ≠ s := h1
        have h2' : i ≠ t := by simpa using h2
        obtain rfl := (hall i).resolve_right (by tauto)
        exact hrow _
      · have h1' : i ≠ t := h1
        have h2' : i ≠ s := by simpa using h2
        obtain rfl := (hall i).resolve_right (by tauto)
        exact hrow _

/-- **Misprint on p. 7.** The printed sentence "*The attractor attached to `[±(1,0)⟩` is given on the charts
respectively by `{x}`, `𝔸¹_{(0,1)}` and `𝔸¹_{(0,-1)}`*" should read `[±(0,1)⟩`, as the next sentence shows. For
`[±(1,0)⟩`, the chart `x` gives `𝔸¹_{(-1,0)}`, not `{x}`; for `[±(0,1)⟩` the statement holds. -/
theorem printed_misprint :
    chartS wP (AddSubmonoid.closure {x | x ∈ [((1, 0) : ℤ × ℤ), (-1, 0)]}) 0 = {2} ∧
    chartS wP (AddSubmonoid.closure {x | x ∈ [((0, 1) : ℤ × ℤ), (0, -1)]}) 0 = ∅ ∧
    chartS wP (AddSubmonoid.closure {x | x ∈ [((0, 1) : ℤ × ℤ), (0, -1)]}) 1 = {2} ∧
    chartS wP (AddSubmonoid.closure {x | x ∈ [((0, 1) : ℤ × ℤ), (0, -1)]}) 2 = {1} := by
  have key : ∀ r ∈ fig2, ∀ s, chartS wP r.magnet s = r.S s := by
    intro r hr s
    have h := fig2_good r hr
    ext j
    rw [mem_chartS, h.2.2.1 s j]
    exact and_congr_right fun hj => Row.mem_magnet_iff h (phi_eq_diff.1 j s hj)
  have r1 : (⟨[(1, 0), (-1, 0)], {2}, ∅, {0}, 0, 1, 0⟩ : Row) ∈ fig2 := by decide
  have r2 : (⟨[(0, 1), (0, -1)], ∅, {2}, {1}, 0, 1, 1⟩ : Row) ∈ fig2 := by decide
  exact ⟨key _ r1 0, key _ r2 0, key _ r2 1, key _ r2 2⟩

/-! ### Proposition 6.5 -/

/-- A morphism `ℤ² → ℤ` is a linear form. -/
lemma addHom_prod (f : ℤ × ℤ →+ ℤ) (v : ℤ × ℤ) : f v = f (1, 0) * v.1 + f (0, 1) * v.2 := by
  have e : v = v.1 • ((1, 0) : ℤ × ℤ) + v.2 • ((0, 1) : ℤ × ℤ) := by
    ext <;> simp
  conv_lhs => rw [e]
  rw [map_add, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul]
  ring

/-- The linear form `(u, v) ↦ pu + qv`. -/
def linForm (p q : ℤ) : ℤ × ℤ →+ ℤ where
  toFun v := p * v.1 + q * v.2
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add]
    ring

/-- A wider range of slopes. -/
def slopes2 : List ℤ := [-2, -1, 0, 1, 2]

set_option maxRecDepth 200000 in
/-- **Proof of Proposition 6.5, cardinality 3.** `E = {a, b, c}`, `c = a + b`, and `f : a, b ↦ 1` is such that
`f⁻¹(ℕ) ∩ Φ = E`. -/
theorem prop65_card3 : ∀ E ∈ Phi.powerset.filter Closed, E.card = 3 →
    ∃ a ∈ E, ∃ b ∈ E, E = {a, b, a + b} ∧ ∃ p ∈ slopes2, ∃ q ∈ slopes2,
      p * a.1 + q * a.2 = 1 ∧ p * b.1 + q * b.2 = 1 ∧
      Phi.filter (fun v => 0 ≤ p * v.1 + q * v.2) = E := by
  decide

set_option maxRecDepth 200000 in
/-- **Proof of Proposition 6.5, cardinality 4.** `E = {a, b, c, d}`, `c = a + b`, `d = -a`, and `f : a, d ↦ 0`,
`c, b ↦ 1` is such that `f⁻¹(ℕ) ∩ Φ = E`. -/
theorem prop65_card4 : ∀ E ∈ Phi.powerset.filter Closed, E.card = 4 →
    ∃ a ∈ E, ∃ b ∈ E, E = {a, b, a + b, -a} ∧ ∃ p ∈ slopes2, ∃ q ∈ slopes2,
      p * a.1 + q * a.2 = 0 ∧ p * b.1 + q * b.2 = 1 ∧
      Phi.filter (fun v => 0 ≤ p * v.1 + q * v.2) = E := by
  decide

/-- **Proof of Proposition 6.5, cardinality 0, 1, 2.** For any `f : ℤ² → ℤ`, at least three elements of `Φ` have
`f ≥ 0`: else four elements have `f < 0`, and two of them are opposite. -/
theorem three_le_card_filter (p q : ℤ) : 3 ≤ (Phi.filter (fun v => 0 ≤ p * v.1 + q * v.2)).card := by
  have key : ∀ a ∈ Phi, ∀ b ∈ Phi, ∀ c ∈ Phi, ({a, b, c} : Finset (ℤ × ℤ)).card = 3 →
      0 ≤ p * a.1 + q * a.2 → 0 ≤ p * b.1 + q * b.2 → 0 ≤ p * c.1 + q * c.2 →
      3 ≤ (Phi.filter (fun v => 0 ≤ p * v.1 + q * v.2)).card := by
    intro a ha b hb c hc hcard h1 h2 h3
    rw [← hcard]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨ha, h1⟩
    · exact Finset.mem_filter.mpr ⟨hb, h2⟩
    · exact Finset.mem_filter.mpr ⟨hc, h3⟩
  rcases le_total 0 p with h1 | h1 <;> rcases le_total 0 q with h2 | h2 <;>
    rcases le_total 0 (p - q) with h3 | h3
  · exact key (1, 0) (by decide) (0, 1) (by decide) (1, -1) (by decide) (by decide) (by simpa) (by simpa)
      (by simp; omega)
  · exact key (1, 0) (by decide) (0, 1) (by decide) (-1, 1) (by decide) (by decide) (by simpa) (by simpa)
      (by simp; omega)
  · exact key (1, 0) (by decide) (0, -1) (by decide) (1, -1) (by decide) (by decide) (by simpa) (by simp; omega)
      (by simp; omega)
  · exact key (1, 0) (by decide) (0, -1) (by decide) (-1, 1) (by decide) (by decide) (by simpa) (by simp; omega)
      (by simp; omega)
  · exact key (-1, 0) (by decide) (0, 1) (by decide) (1, -1) (by decide) (by decide) (by simp; omega) (by simpa)
      (by simp; omega)
  · exact key (-1, 0) (by decide) (0, 1) (by decide) (-1, 1) (by decide) (by decide) (by simp; omega) (by simpa)
      (by simp; omega)
  · exact key (-1, 0) (by decide) (0, -1) (by decide) (1, -1) (by decide) (by decide) (by simp; omega)
      (by simp; omega) (by simp; omega)
  · exact key (-1, 0) (by decide) (0, -1) (by decide) (-1, 1) (by decide) (by decide) (by simp; omega)
      (by simp; omega) (by simp; omega)

/-- `f⁻¹(ℕ) ∩ Φ`, computed. -/
lemma comap_inter (p q : ℤ) :
    ((posN.comap (linForm p q) : AddSubmonoid (ℤ × ℤ)) : Set (ℤ × ℤ)) ∩ (Phi : Set (ℤ × ℤ)) =
      ((Phi.filter (fun v => 0 ≤ p * v.1 + q * v.2) : Finset _) : Set (ℤ × ℤ)) := by
  ext v
  simp only [Set.mem_inter_iff, SetLike.mem_coe, AddSubmonoid.mem_comap, mem_posN, Finset.coe_filter,
    Set.mem_ofPred_eq, Finset.mem_coe]
  exact and_comm

/-- **Proposition 6.5.** Let `E ⊂ Φ` be additively stable. Then `[E⟩` is lambdafiable iff `#E ≥ 3`. -/
theorem prop65 [Nontrivial R] {E : Finset (ℤ × ℤ)} (hE : E ⊆ Phi) (hst : Closed E) :
    IsLambdafiable (attractorImage (dsAct R)) (AddSubmonoid.closure (E : Set (ℤ × ℤ))) ↔ 3 ≤ E.card := by
  have hS := addStable_of_closed hE hst
  have hmem : E ∈ Phi.powerset.filter Closed := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hE, hst⟩
  have of_form : ∀ p q : ℤ, Phi.filter (fun v => 0 ≤ p * v.1 + q * v.2) = E →
      IsLambdafiable (attractorImage (dsAct R)) (AddSubmonoid.closure (E : Set (ℤ × ℤ))) := by
    intro p q h
    refine ⟨linForm p q, (image_eq_iff wP).mpr ?_⟩
    rw [om_eq, comap_inter, h]
    exact hS.symm
  constructor
  · rintro ⟨f, hf⟩
    rw [image_eq_iff wP, om_eq, hS] at hf
    have hg : f = linForm (f (1, 0)) (f (0, 1)) := AddMonoidHom.ext fun v => addHom_prod f v
    rw [hg, comap_inter] at hf
    have := three_le_card_filter (f (1, 0)) (f (0, 1))
    rwa [Finset.coe_injective hf] at this
  · intro h3
    have hle : E.card ≤ 6 := Finset.card_le_card hE
    have h5 : E.card ≠ 5 := by
      intro h
      have : ∀ F ∈ Phi.powerset.filter Closed, F.card ≠ 5 := by decide
      exact this E hmem h
    have hcases : E.card = 3 ∨ E.card = 4 ∨ E.card = 6 := by omega
    rcases hcases with h | h | h
    · obtain ⟨_, _, _, _, _, p, _, q, _, _, _, e⟩ := prop65_card3 E hmem h
      exact of_form p q e
    · obtain ⟨_, _, _, _, _, p, _, q, _, _, _, e⟩ := prop65_card4 E hmem h
      exact of_form p q e
    · have hEq : E = Phi := Finset.eq_of_subset_of_card_le hE (by rw [h]; decide)
      exact of_form 0 0 (by rw [hEq]; decide)

set_option maxRecDepth 100000 in
/-- **Proposition 6.5, the count.** There are `13` additively stable subsets with `#E ≥ 3`, and `16` others. -/
theorem prop65_count :
    ((Phi.powerset.filter Closed).filter fun E => 3 ≤ E.card).card = 13 ∧
    ((Phi.powerset.filter Closed).filter fun E => ¬ 3 ≤ E.card).card = 16 := by
  decide

/-- **Proposition 6.5, the count, on pure magnets.** `13` lambdafiable pure magnets, `16` others. -/
theorem prop65_count_pure [Nontrivial R] :
    {N ∈ pureMagnets (attractorImage (dsAct R)) | IsLambdafiable (attractorImage (dsAct R)) N}.ncard = 13 ∧
    {N ∈ pureMagnets (attractorImage (dsAct R)) | ¬ IsLambdafiable (attractorImage (dsAct R)) N}.ncard = 16 := by
  classical
  have hb := prop41 (R := R)
  have htoS : ∀ N ∈ pureMagnets (attractorImage (dsAct R)), ∃ F ∈ Phi.powerset.filter Closed,
      (N : Set (ℤ × ℤ)) ∩ Phi = F ∧ N = AddSubmonoid.closure (F : Set (ℤ × ℤ)) := by
    intro N hN
    have hst := hb.mapsTo hN
    rw [stable_set_eq] at hst
    obtain ⟨F, hF, e⟩ := hst
    refine ⟨F, Finset.mem_coe.mp hF, e.symm, ?_⟩
    have h := (isPure_iff wP).mp hN
    rw [om_eq] at h
    rw [show (F : Set (ℤ × ℤ)) = (N : Set (ℤ × ℤ)) ∩ Phi from e]
    exact h
  have count : ∀ (Q : ℕ → Prop) [DecidablePred Q],
      {N ∈ pureMagnets (attractorImage (dsAct R)) |
        ∃ F ∈ Phi.powerset.filter Closed, (N : Set (ℤ × ℤ)) ∩ Phi = F ∧ Q F.card}.ncard =
      ((Phi.powerset.filter Closed).filter fun E => Q E.card).card := by
    intro Q _
    have himg : (fun N : AddSubmonoid (ℤ × ℤ) => (N : Set (ℤ × ℤ)) ∩ (Phi : Set (ℤ × ℤ))) ''
        {N ∈ pureMagnets (attractorImage (dsAct R)) |
          ∃ F ∈ Phi.powerset.filter Closed, (N : Set (ℤ × ℤ)) ∩ Phi = F ∧ Q F.card} =
        (fun F : Finset (ℤ × ℤ) => (F : Set (ℤ × ℤ))) ''
          (((Phi.powerset.filter Closed).filter fun E => Q E.card : Finset _) : Set (Finset (ℤ × ℤ))) := by
      ext E
      constructor
      · rintro ⟨N, ⟨-, F, hF, e, hQ⟩, rfl⟩
        exact ⟨F, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hF, hQ⟩), e.symm⟩
      · rintro ⟨F, hF, rfl⟩
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hF)
        have hin : (F : Set (ℤ × ℤ)) ∈ {E : Set (ℤ × ℤ) | E ⊆ (Phi : Set (ℤ × ℤ)) ∧ AddStable E} := by
          rw [stable_set_eq]
          exact ⟨F, Finset.mem_coe.mpr h1, rfl⟩
        obtain ⟨N, hN, e⟩ := hb.surjOn hin
        exact ⟨N, ⟨hN, F, h1, e, h2⟩, e⟩
    have hinj : Set.InjOn (fun N : AddSubmonoid (ℤ × ℤ) => (N : Set (ℤ × ℤ)) ∩ (Phi : Set (ℤ × ℤ)))
        {N ∈ pureMagnets (attractorImage (dsAct R)) |
          ∃ F ∈ Phi.powerset.filter Closed, (N : Set (ℤ × ℤ)) ∩ Phi = F ∧ Q F.card} :=
      hb.injOn.mono fun N hN => hN.1
    rw [← hinj.ncard_image, himg, Set.ncard_image_of_injective _ Finset.coe_injective,
      Set.ncard_coe_finset]
  have e1 : {N ∈ pureMagnets (attractorImage (dsAct R)) | IsLambdafiable (attractorImage (dsAct R)) N} =
      {N ∈ pureMagnets (attractorImage (dsAct R)) |
        ∃ F ∈ Phi.powerset.filter Closed, (N : Set (ℤ × ℤ)) ∩ Phi = F ∧ 3 ≤ F.card} := by
    ext N
    constructor
    · rintro ⟨hN, hl⟩
      obtain ⟨F, hF, e, hc⟩ := htoS N hN
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hF
      rw [hc] at hl
      exact ⟨hN, F, hF, e, (prop65 (Finset.mem_powerset.mp h1) h2).mp hl⟩
    · rintro ⟨hN, F, hF, e, hc⟩
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hF
      obtain ⟨F', hF', e', hc'⟩ := htoS N hN
      have : F = F' := Finset.coe_injective (e.symm.trans e')
      subst this
      refine ⟨hN, ?_⟩
      rw [hc']
      exact (prop65 (Finset.mem_powerset.mp h1) h2).mpr hc
  have e2 : {N ∈ pureMagnets (attractorImage (dsAct R)) | ¬ IsLambdafiable (attractorImage (dsAct R)) N} =
      {N ∈ pureMagnets (attractorImage (dsAct R)) |
        ∃ F ∈ Phi.powerset.filter Closed, (N : Set (ℤ × ℤ)) ∩ Phi = F ∧ ¬ 3 ≤ F.card} := by
    ext N
    constructor
    · rintro ⟨hN, hl⟩
      obtain ⟨F, hF, e, hc⟩ := htoS N hN
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hF
      rw [hc] at hl
      exact ⟨hN, F, hF, e, fun h => hl ((prop65 (Finset.mem_powerset.mp h1) h2).mpr h)⟩
    · rintro ⟨hN, F, hF, e, hc⟩
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hF
      obtain ⟨F', hF', e', hc'⟩ := htoS N hN
      have : F = F' := Finset.coe_injective (e.symm.trans e')
      subst this
      refine ⟨hN, ?_⟩
      rw [hc']
      exact fun h => hc ((prop65 (Finset.mem_powerset.mp h1) h2).mp h)
  rw [e1, e2, count (fun n => 3 ≤ n), count (fun n => ¬ 3 ≤ n)]
  exact prop65_count

/-! ### Remark 6.6 -/

/-- **Remark 6.6.** The attractor `X^{N,F}_Z = X^N ×_{X^F} Z` with prescribed limit `Z ⊂ X^F` along the face `F`, as
a family of points of `X^N`. As `X^N → X` is a monomorphism and `Z → X^F` is one, it is a subfunctor of `X^N`. -/
def prescribedLimit {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{0}} {M : Type*} [AddCommMonoid M]
    {F' : Cᵒᵖ ⥤ Type} {act : AAction 𝒪 M F'} {F N : AddSubmonoid M} (hF : IsFace F N)
    (Z : ∀ T : C, Set (AttractorPt act F T)) (T : C) : Set (AttractorPt act N T) :=
  {φ | AttractorPt.ofFace hF φ ∈ Z T}

/-- The magnet `[(1,0), (1,-1)⟩` of Remark 6.6. -/
def remN : AddSubmonoid (ℤ × ℤ) := AddSubmonoid.closure {x | x ∈ [((1, 0) : ℤ × ℤ), (1, -1)]}

/-- `0` is a face of `[(1,0), (1,-1)⟩`. -/
theorem rem_face : IsFace (⊥ : AddSubmonoid (ℤ × ℤ)) remN := by
  refine ⟨bot_le, ?_⟩
  have key : ∀ v ∈ remN, 0 ≤ v.1 ∧ 0 ≤ v.1 + v.2 ∧ (v.1 = 0 → v = 0) := by
    intro v hv
    induction hv using AddSubmonoid.closure_induction with
    | mem x hx =>
      simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp
    | zero => simp
    | add x y _ _ hx hy =>
      obtain ⟨a1, b1, c1⟩ := hx
      obtain ⟨a2, b2, c2⟩ := hy
      simp only [Prod.fst_add, Prod.snd_add]
      refine ⟨by omega, by omega, fun h => ?_⟩
      have h1 : x.1 = 0 := by omega
      have h2 : y.1 = 0 := by omega
      rw [c1 h1, c2 h2, add_zero]
  intro x y hx hy hxy
  have hs : x + y = 0 := hxy
  obtain ⟨a1, -, c1⟩ := key x hx
  obtain ⟨a2, -, c2⟩ := key y hy
  have h1 : (x + y).1 = 0 := by rw [hs]; rfl
  rw [Prod.fst_add] at h1
  exact ⟨c1 (by omega), c2 (by omega)⟩

set_option maxRecDepth 100000 in
/-- The relevant membership in `[(1,0), (1,-1)⟩`. -/
lemma rem_mem : ∀ i j : Fin 3, i ≠ j →
    (wP i - wP j ∈ remN ↔ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2)) := by
  have hr : (⟨[(1, 0), (1, -1)], ∅, {0}, {0}, 0, 1, 2⟩ : Row) ∈ fig2 := by decide
  have h := fig2_good _ hr
  have key : ∀ i j : Fin 3, i ≠ j →
      (wP i - wP j ∈ clo [(1, 0), (1, -1)] ↔ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2)) := by decide
  intro i j hij
  have e := Row.mem_magnet_iff h (phi_eq_diff.1 i j hij)
  have e' : (wP i - wP j ∈ remN) ↔ wP i - wP j ∈ clo [(1, 0), (1, -1)] := e
  rw [e']
  exact key i j hij

lemma xv_bot {R : Type} [CommRing R] {D : CommAlgCat.{0} R} (i j : Fin 3) :
    xv (R := R) (T' := op D) (⊥ : AddSubmonoid (ℤ × ℤ)) (wP i - wP j) 1 = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, sub_self]
    exact xv_zero _ _
  · rw [ite_eq_right hij]
    have : wP i - wP j ∉ (⊥ : AddSubmonoid (ℤ × ℤ)) := by
      have : ∀ i j : Fin 3, i ≠ j → wP i - wP j ≠ 0 := by decide
      simpa using this i j hij
    unfold xv
    rw [dite_eq_right this]

/-- The fixed locus `{y, z} ⊂ X^0` of Remark 6.6. -/
def remZ (R : Type) [CommRing R] (T : Aff R) : Set (AttractorPt (dsAct R) (⊥ : AddSubmonoid (ℤ × ℤ)) T) :=
  {ψ | ZUnion (![1, 2] : Fin 2 → Fin 3) ![∅, ∅] ψ.toPoint.1}

/-- **Remark 6.6.** For `N = [(1,0), (1,-1)⟩`, `F = 0` and `Z = {y, z} ⊂ X^0`, the attractor with prescribed limit is
`𝔸¹_{(1,-1)} ⊔ 𝔸¹_{(1,0)}`: the chart `𝔸¹` of `y` with the coordinate `x` of weight `(1,-1)`, and the chart `𝔸¹` of
`z` with the coordinate `x` of weight `(1,0)`. -/
theorem rem66 {D : CommAlgCat.{0} R} (K : (pn (Fin 3) R).obj (op (op D))) :
    (∃ φ ∈ prescribedLimit rem_face (remZ R) (op D), φ.toPoint = K) ↔
      ZUnion (![1, 2] : Fin 2 → Fin 3) ![{0}, {0}] K.1 := by
  classical
  have hdiag : ∀ {P : Matrix (Fin 3) (Fin 3) D} (hP : IsRankOneProj P)
      (hs : ∀ i j, wP i - wP j ∉ remN → P i j = 0),
      (AttractorPt.toPoint (AttractorPt.ofFace rem_face (liftPt wP remN hP hs))).1 =
        rng (Matrix.of fun i j => (if i = j then 1 else 0) * P i j) := by
    intro P hP hs
    rw [toPoint_ofFace wP rem_face hP hs]
    refine congrArg rng (Matrix.ext fun i j => ?_)
    simp only [Matrix.of_apply, xv_bot]
  have hdprop : ∀ {P : Matrix (Fin 3) (Fin 3) D} (hP : IsRankOneProj P)
      (hs : ∀ i j, wP i - wP j ∉ remN → P i j = 0),
      IsLineN (AttractorPt.toPoint (AttractorPt.ofFace rem_face (liftPt wP remN hP hs))).1 := fun hP hs =>
    (AttractorPt.toPoint (AttractorPt.ofFace rem_face (liftPt wP remN hP hs))).2
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨P, hP, hK, hs⟩ := (mem_image_iff wP φ.toPoint).mp ⟨φ, rfl⟩
    have hφ' : φ = liftPt wP remN hP hs :=
      toPoint_injective wP (Subtype.ext (hK.trans (liftPt_toPoint wP remN hP hs).symm))
    subst hφ'
    have hl : ZUnion (![1, 2] : Fin 2 → Fin 3) ![∅, ∅]
        (AttractorPt.toPoint (AttractorPt.ofFace rem_face (liftPt wP remN hP hs))).1 := hφ
    obtain ⟨L, hL, hLe⟩ := hdprop hP hs
    rw [hLe] at hl
    obtain ⟨Q, hQ, e, hsupp⟩ := exists_proj_of_zunion hL hl
    have hxx : P 0 0 = 0 := by
      have h1 : (fun i => (Matrix.of fun i j => (if i = j then (1 : D) else 0) * P i j) i 0) ∈ rng Q := by
        rw [e, ← hLe, hdiag]
        exact col_mem_rng _ 0
      have h2 := congrFun ((mem_rng_iff hQ.idem).mp h1) 0
      have hrow : ∀ k, Q 0 k = 0 := by
        intro k
        by_contra hz
        obtain ⟨a, ha, h3⟩ := hsupp 0 k hz
        fin_cases a
        · change (1 : Fin 3) = k at ha
          subst ha
          rcases h3 with h3 | h3
          · exact absurd h3 (by decide)
          · simp at h3
        · change (2 : Fin 3) = k at ha
          subst ha
          rcases h3 with h3 | h3
          · exact absurd h3 (by decide)
          · simp at h3
      have h4 : ∑ k, Q 0 k * (Matrix.of fun i j => (if i = j then (1 : D) else 0) * P i j) k 0 =
          (if (0 : Fin 3) = 0 then (1 : D) else 0) * P 0 0 := h2
      rw [Finset.sum_eq_zero fun k _ => by rw [hrow k, zero_mul]] at h4
      simpa using h4.symm
    have hcol0 : ∀ i, P i 0 = 0 := by
      intro i
      by_cases hi : i = 0
      · rw [hi, hxx]
      · refine hs i 0 ?_
        intro hm
        have := (rem_mem i 0 hi).mp hm
        simp at this
    have htr : P 1 1 + P 2 2 = 1 := by
      have := hP.trace_eq
      rw [Matrix.trace, Fin.sum_univ_three] at this
      simpa [hxx] using this
    rw [hK]
    refine zunion_of_proj' hP ?_ ?_
    · rw [Ideal.eq_top_iff_one, ← htr]
      exact Ideal.add_mem _ (Ideal.subset_span ⟨0, rfl⟩) (Ideal.subset_span ⟨1, rfl⟩)
    · intro a i h1 h2
      refine hs _ _ fun hm => ?_
      fin_cases a
      · have := (rem_mem i 1 h1).mp hm
        have hi : i = 0 := by
          rcases this with h | h
          · exact h.1
          · exact absurd h.2 (by decide)
        exact h2 (by simp [hi])
      · have := (rem_mem i 2 h1).mp hm
        have hi : i = 0 := by
          rcases this with h | h
          · exact absurd h.2 (by decide)
          · exact h.1
        exact h2 (by simp [hi])
  · intro h
    obtain ⟨L, hL, hLe⟩ := K.2
    rw [hLe] at h
    obtain ⟨Q, hQ, e, hsupp⟩ := exists_proj_of_zunion hL h
    have hcol : ∀ i j, Q i j ≠ 0 → (j = 1 ∧ (i = 1 ∨ i = 0)) ∨ (j = 2 ∧ (i = 2 ∨ i = 0)) := by
      intro i j hij
      obtain ⟨a, ha, h3⟩ := hsupp i j hij
      fin_cases a
      · change (1 : Fin 3) = j at ha
        subst ha
        refine Or.inl ⟨rfl, ?_⟩
        rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (by simpa using h3)
      · change (2 : Fin 3) = j at ha
        subst ha
        refine Or.inr ⟨rfl, ?_⟩
        rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (by simpa using h3)
    have hs : ∀ i j, wP i - wP j ∉ remN → Q i j = 0 := by
      intro i j hm
      by_contra hz
      have hij : i ≠ j := by
        rintro rfl
        simp at hm
      apply hm
      refine (rem_mem i j hij).mpr ?_
      rcases hcol i j hz with ⟨rfl, h1 | h1⟩ | ⟨rfl, h1 | h1⟩
      · exact absurd h1 hij
      · exact Or.inl ⟨h1, rfl⟩
      · exact absurd h1 hij
      · exact Or.inr ⟨h1, rfl⟩
    refine ⟨liftPt wP remN hQ hs, ?_, Subtype.ext ((liftPt_toPoint wP remN hQ hs).trans (e.trans hLe.symm))⟩
    change ZUnion _ _ (AttractorPt.toPoint (AttractorPt.ofFace rem_face (liftPt wP remN hQ hs))).1
    rw [hdiag hQ hs]
    have hxx : Q 0 0 = 0 := by
      by_contra hz
      rcases hcol 0 0 hz with h | h <;> exact absurd h.1 (by decide)
    have htr : Q 1 1 + Q 2 2 = 1 := by
      have := hQ.trace_eq
      rw [Matrix.trace, Fin.sum_univ_three] at this
      simpa [hxx] using this
    have hdp : IsRankOneProj (Matrix.of fun i j => (if i = j then (1 : D) else 0) * Q i j) := by
      refine isRankOneProj_diag hQ fun i j hij => ?_
      refine diag_mul_diag_eq_zero wP hQ hs fun hc => hij ?_
      have h1 := (rem_mem i j hij).mp hc.1
      have h2 := (rem_mem j i (Ne.symm hij)).mp hc.2
      have hi : i = 0 := by rcases h1 with h | h <;> exact h.1
      have hj : j = 0 := by rcases h2 with h | h <;> exact h.1
      rw [hi, hj]
    refine zunion_of_proj' hdp ?_ ?_
    · rw [Ideal.eq_top_iff_one]
      have m1 : Q 1 1 ∈ Ideal.span (Set.range fun a : Fin 2 =>
          (Matrix.of fun i j => (if i = j then (1 : D) else 0) * Q i j)
            ((![1, 2] : Fin 2 → Fin 3) a) ((![1, 2] : Fin 2 → Fin 3) a)) :=
        Ideal.subset_span ⟨0, by simp⟩
      have m2 : Q 2 2 ∈ Ideal.span (Set.range fun a : Fin 2 =>
          (Matrix.of fun i j => (if i = j then (1 : D) else 0) * Q i j)
            ((![1, 2] : Fin 2 → Fin 3) a) ((![1, 2] : Fin 2 → Fin 3) a)) :=
        Ideal.subset_span ⟨1, by simp⟩
      have := Ideal.add_mem _ m1 m2
      rwa [htr] at this
    · intro a i h1 _
      fin_cases a
      · have h1' : i ≠ 1 := h1
        simp [h1']
      · have h1' : i ≠ 2 := h1
        simp [h1']

end P2

/-! ### Axioms -/

#print axioms prop41
#print axioms isLineN_iff_of_isLocalRing
#print axioms fig1_le
#print axioms attractor_bounds
#print axioms attractorOrder_pn
#print axioms ncard_pure
#print axioms pure_eq_fig2
#print axioms fig2_attractor
#print axioms fig2_comp
#print axioms fig2_disjoint
#print axioms fig2_glue
#print axioms zunion_p1
#print axioms printed_misprint
#print axioms prop62
#print axioms prop64
#print axioms prop64_p2
#print axioms prop65
#print axioms prop65_count_pure
#print axioms rem66
#print axioms image_eq_iff_chart_attr
#print axioms gm_image_ne
#print axioms a1_image_eq
#print axioms exists_component
#print axioms component_rel_face

end AlgMag.DoubleScalar
