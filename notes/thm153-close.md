# Closing Theorem 15.3 in the printed generality: result and exact wall (2026-11-08)

Pure mathematics. Nothing compiled, no existing file edited. Magnet language only.

Source: [AM] = Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126-201, read through `am.txt` (pp. 140-153 for §3, 155-158 for §5-6, 184-185 for §15). "Verified" = redone by hand in this session. "Quoted" = taken from the print, from the Stacks Project by tag, from a note of this repo, or from a Lean declaration name, without redoing it.

Author's instruction for this task: aim at the printed generality (M any abelian monoid, X a separated algebraic space over S with an action of A(M)_S, nothing more); an extra hypothesis is acceptable only together with a counterexample. No counterexample was found. The verdict is therefore a precisely located wall, together with everything that can be proved in the printed generality.

---

## 0. The printed statement and its gap (verified)

§15 standing hypotheses (p. 184): "Let M be an abelian monoid. Let X be a separated algebraic space over S endowed with an action a of A(M)_S." m(M) = all submonoids of M.

Thm 15.3 (p. 185): bijection Π(a) → {X^N ⊂ X | N ∈ m(M)}, N ↦ X^N, inverse Y ↦ E(Y) := ⋂{N ∈ m(M) | X^N = Y}; X^N and X^L are identified iff X^N(T) = X^L(T) ⊂ X(T) for all T/S (Cor 3.30: X^N → X is a monomorphism when X is separated).

Printed proof: "By Proposition 3.34, we have Y = X^{E(Y)}" (twice). Fact 3.34 (p. 150) needs X separated and (i) X affine over S, or (ii) M a finitely generated abelian group, or (iii) M cancellative, M^gp finitely generated, X^{⋂_J N_l} a separated algebraic space for finite J. None is available under the §15 hypotheses, and the family {N | X^N = Y} is infinite in general. Moreover the printed proof of Fact 3.34 (ii)/(iii) for infinite families is itself invalid (colimit step, Tag 002H; corrections-verified.md votes 6, 7; witness `chain_no_point`). So the printed Thm 15.3 has no proof in the paper outside case (i).

---

## 1. What Theorem 15.3 is, exactly (verified, printed generality)

Throughout: M any abelian monoid, X a separated algebraic space over S, action of the monoid scheme A(M)_S. Y_N := the image of X^N(T) in X(T), functorially in T (the print's convention).

**Monotonicity.** N ⊂ L ⇒ Y_N ⊂ Y_L. Compose φ : A(N)_T → X_T with A(L)_T → A(N)_T (dual to Z[N] ⊂ Z[L]); equivariant, same value at the unit. No hypothesis.

**Lemma A (Thm 15.3 ⟺ Fact 3.34 for arbitrary families).** The following are equivalent for a fixed action:
(1) Thm 15.3 as printed;
(2) (∗) for every nonempty family (N_i)_{i∈I} of magnets with Y_{N_i} = Y for all i, Y_{⋂ N_i} = Y.

(2 ⇒ 1): Y_{E(Y)} = Y by (∗) applied to {N | Y_N = Y}; E(Y) is pure (Prop 15.1 (ii): Y_L = Y_{E(Y)} = Y ⇒ E(Y) ⊂ L by definition of E); for N pure, E(Y_N) ⊂ N by definition and N ⊂ E(Y_N) by purity; so N ↦ Y_N and Y ↦ E(Y) are inverse bijections. (1 ⇒ 2): if Y_{N_i} = Y for all i, (1) gives E(Y) pure with Y_{E(Y)} = Y; purity gives E(Y) ⊂ N_i for all i, so E(Y) ⊂ ⋂ N_i ⊂ N_{i_0}, and monotonicity gives Y = Y_{E(Y)} ⊂ Y_{⋂ N_i} ⊂ Y_{N_{i_0}} = Y. ∎

This is Lemma A of unrestrict-g5-thm153-154.md §1.3, re-verified here; it uses only monotonicity and Def 15.2.

**Lemma B (reduction to finite intersections and chains; Zorn).** Let 𝒩 := {N ∈ m(M) | Y_N = Y}, nonempty. Suppose
(F) N, L ∈ 𝒩 ⇒ N ∩ L ∈ 𝒩;
(C) every nonempty chain 𝒞 ⊂ 𝒩 (totally ordered by inclusion) has ⋂𝒞 ∈ 𝒩.
Then ⋂𝒩 ∈ 𝒩, i.e. (∗) holds for every family with common attractor Y.

Proof. By (C), every chain of the poset (𝒩, ⊇) has an upper bound in 𝒩, so Zorn gives a minimal element N_0 of (𝒩, ⊆). For N ∈ 𝒩, N ∩ N_0 ∈ 𝒩 by (F) and N ∩ N_0 ⊂ N_0, so N ∩ N_0 = N_0, i.e. N_0 ⊂ N. Hence N_0 = ⋂𝒩 ∈ 𝒩. For a subfamily (N_i) ⊂ 𝒩 with Q = ⋂ N_i: N_0 ⊂ Q ⊂ N_{i_0}, so Y = Y_{N_0} ⊂ Y_Q ⊂ Y_{N_{i_0}} = Y by monotonicity. ∎

Conversely (∗) trivially implies (F) and (C). So, in the printed generality:

> **Thm 15.3 ⟺ (F) + (C).**

(F) is Prop 3.32 for two magnets with a common attractor (if X^N = X^L = Y as subfunctors, then X^{N∩L} = (X^N)^L = (X^L)^L = X^L = Y, using Prop 3.32 twice; the induced actions of 3.11 agree because the identification is as A(M)-stable subfunctors of X). (C) is the chain case of Fact 3.34.

**Refinement of (C).** Every chain has a well-ordered cofinal subchain with the same intersection (standard). If M is countable (e.g. finitely generated), a strictly decreasing well-ordered chain of subsets of M is countable (pick one removed element per step; the map is injective into M), so it has a least element or an ω-cofinal subsequence. Hence for countable M:

> **Thm 15.3 ⟺ (F) + (C_ω)**, where (C_ω): for every decreasing sequence N_1 ⊃ N_2 ⊃ ... with Y_{N_k} = Y for all k, Y_{⋂ N_k} = Y.

Answer to lead (3) of the task: the infinite family is reducible to chains, not to finite subfamilies. A "degree" argument (finite E ⊂ M with X^N = X^{⟨N∩E⟩}) bounds the set of attractors, not the set 𝒩 (X = S with trivial action has 𝒩 = m(M)); the reduction from an infinite family to a finite one is false as a general principle and is exactly what (C) is about.

---

## 2. Two general tools in the printed generality (verified)

**Lemma C (orbit-map criterion).** Let x ∈ X(T), T affine, and o_x : A(M)_T → X_T, g ↦ g·x. For a magnet N let π_N : A(M)_T → A(N)_T be the morphism dual to R[N] ⊂ R[M] (equivariant: π_N(gh) = g·π_N(h), Fact 2.12). Then

  x ∈ X^N(T) ⟺ o_x factors through π_N.

⇒: if φ : A(N)_T → X_T is equivariant with φ(1) = x then φ(π_N(g)) = φ(g·1) = g·x. ⇐: let o_x = φ ∘ π_N with φ a T-morphism. The two maps A(M)_T ×_T A(N)_T → X_T, (g, a) ↦ φ(g·a) and g·φ(a), agree after composition with id × π_N : A(M)_T × A(M)_T → A(M)_T × A(N)_T (both become (g, h) ↦ (gh)·x). The ring map R[M] ⊗_R R[N] → R[M] ⊗_R R[M] is injective (Z[N] → Z[M] is a split injection of free Z-modules, with free cokernel), so id × π_N is schematically dominant; X_T is separated, so the equalizer of the two maps is a closed subscheme of A(M)_T × A(N)_T through which a schematically dominant morphism factors, hence everything. So φ is equivariant, and φ(1) = o_x(1) = x. ∎

Consequence: (∗) says that for every orbit map o : A(M)_T → X_T the set {N | o factors through Spec R[N]} is closed under arbitrary intersections of the subrings R[N] ⊂ R[M] (note R[⋂ N_i] = ⋂ R[N_i] inside R[M], monomial subrings). For affine X this is immediate (the image of O(X_T) → R[M] is spanned by monomials, Thm 3.20/Prop 3.24); for non-affine X it is not a formal property of factorizations (X = P^1_S with the standard D(Z)-action, o the inclusion of D(Z)_S, N = N and L = −N: o factors through both A(N) = A^1 and A(−N), not through A(0) = S), and the content of Prop 3.32/Fact 3.34 is precisely that the magnet structure rescues it.

**Lemma D (reduction to the closure of one orbit).** Let x ∈ X(T), T affine, and let Z ⊂ X_T be the scheme-theoretic image of o_x (exists since o_x is quasi-compact and X_T is quasi-separated: Stacks, Morphisms of Spaces, scheme theoretic image, Tags 082W-082Z; formation commutes with flat base change for quasi-compact morphisms). Then Z is an A(M)_T-stable closed subspace, and for every magnet N: x ∈ X^N(T) ⟺ x ∈ Z^N(T); likewise over every T'/T.

Proof. The composite A(M)_T × A(M)_T → A(M)_T × Z → X_T (multiply, then o_x) lands in Z; A(M)_T × A(M)_T → A(M)_T × Z is schematically dominant (flat base change of the scheme-theoretically dominant o_x along the flat A(M)_T × X_T → X_T); the preimage of Z under the action map A(M)_T × Z → X_T is a closed subspace through which it factors, hence all of A(M)_T × Z. So Z is stable. If φ : A(N)_T → X_T is equivariant with φ(1) = x then φ ∘ π_N = o_x lands in Z and π_N is schematically dominant, so φ lands in Z. ∎

Hence, for (∗), one may assume X_T = Z, the closure of a single orbit. This pins the shape of any counterexample (§4).

**Lemma E (cancellative M reduces to the group M^gp).** If M is cancellative, Prop 3.31 (iii) (verified: the proof uses only that Z[N] ⊗ Z[M] → Z[N] ⊗ Z[M^gp] is a split injection and that X is separated) gives X^N_M = X^N_{M^gp} for every N ⊂ M, where D(M^gp)_S acts through D(M^gp)_S → A(M)_S. So (F), (C), (∗) and Thm 15.3 for the A(M)-action follow from the same statements for the D(M^gp)-action restricted to the magnets contained in M. For M not cancellative, Z[M] → Z[M^gp] is not injective and no reduction is available from the paper; Lemmas A-D still hold verbatim (they never use cancellativity).

---

## 3. Status of (F) and (C) in the printed generality

| case | (F) finite intersections | (C) chains / arbitrary families | source |
|---|---|---|---|
| X affine over S, any M, any S | yes | yes | Prop 3.24 (Thm 3.20), verified; Lean `attractorOrder_affine` + `pureEquivRange` (unrestrict note §1.5) |
| M f.g. abelian group, X any separated space | yes | **open** for X a non-scheme space; by hand for X a scheme (fact334-attempt.md, fourth pass; unreviewed) | Lean `SDR4Final` (Lemma D there) for (F); fact334 notes for (C) |
| M cancellative, M^gp f.g. | as above via Lemma E | as above | Prop 3.31 (iii), verified |
| M a group, not f.g.; X not affine | **open** (Prop 3.32 (ii) is printed for f.g. M; SGA3 VIII 5.1 quotient step not re-verified for non-f.g. groups) | **open** | — |
| M not cancellative; X not affine | **open** (no tool in the paper) | **open** | — |
| X l.f.p. over qc S with an S-affine strongly-FPR atlas, M any abelian group | yes | yes | thm154-ii-nonfg.md Steps 4, 5(d) (checked) reduce all attractors to a f.g. M'; then Lean `fact334_strong` for M' (quoted) |
| X l.f.p., qc, S separated, M f.g. group | yes | yes | Lean `fact334_free` (on the Thm 6.8 stubs; quoted) |

Answer to lead (1): yes, for any abelian group M, X l.f.p. over quasi-compact S with an S-affine strongly-FPR atlas, Thm 15.3 holds: by Steps 4 and 5(d) of thm154-ii-nonfg.md every attractor of a is an attractor of the descended D(M')-action a', with M' f.g., and X^N_M = X^{N∩M'}_{M'}; a family N_i ⊂ M with common attractor gives the family N_i ∩ M' ⊂ M' with the same common attractor for a', `fact334_strong` gives Y = X^{⋂(N_i ∩ M')}_{M'} = X^{Q∩M'}_{M'} = X^Q_M. This is a conditional theorem (atlas, l.f.p., S qc), not the verdict.

Answer to lead (4): the affine case is Prop 3.24; P^1_S with D(Z) acting through one weight has three attractors (X, the two Bialynicki-Birula-type attractors containing the fixed locus) and all common-attractor families are preserved by intersection (the attractor depends only on which of e, −e lie in N); disjoint unions of lines with arbitrary weights, chains of P^1 likewise; nothing non-affine and small produces a counterexample, in agreement with §4.

Verified chain example in the printed generality (units case): M = Z, N_k = k!·N (or k!·Z), Q = 0, x ∈ X^{N_k}(T) for all k. By Lemma C, o_x : D(Z)_T → X_T factors through the k!-power map for all k, so o_x is invariant under μ_{k!,T} for all k. The equalizer of o_x ∘ m and o_x ∘ pr_2 on μ_{k!} × D(Z)_T, for all k, is a closed subscheme of G_{m,T} containing all μ_{k!}; a Laurent polynomial divisible by u^n − 1 for infinitely many n is zero, so ⋃ μ_{k!} is schematically dense and o_x is constant: x ∈ X^0(T). The same density argument handles any chain of subgroups (fact334-attempt R1, `mapDomain_eq_zero_of_directed`). The difficulty is entirely in the non-unit directions.

---

## 4. The exact remaining wall

By §1-3, in the printed generality the theorem reduces to (F) + (C), and after Lemma E to the following, with M an abelian group (f.g. after the atlas reduction when an atlas exists, otherwise not):

**(W1) Chains, X a separated algebraic space that is not a scheme, not l.f.p., M = Z^r.** T = Spec R, X separated over T with a D(M)_T-action, N_1 ⊃ N_2 ⊃ ..., Q = ⋂ N_k, x ∈ X^{N_k}(T) for all k; show x ∈ X^Q(T). By Lemma D one may take X = closure of the orbit of x. What is known about this configuration (fact334-attempt.md, quoted): the vertex is hit for large k when N_1 is sharp (fourth pass R0-R1), the image of A(N_1)_T → A(Q)_T can miss whole orbits of A(Q)_T (cone example N_k = {a ≥ 0, b ≥ −a/k}, Q = N^2, missed orbit {y = 0, x ≠ 0}), so fpqc descent along A(N_1) → A(Q) is unavailable; for X a scheme the fourth-pass proof expands the functions of an affine neighbourhood of the fixed vertex into series supported in Q and recovers them in S^{-1}R[Q] by the diagonal trick; for a non-scheme space only an étale neighbourhood exists, the expansion lands in a henselization, and the diagonal trick does not pass through algebraic (non-rational) relations (fifth pass). No counterexample: it would have to be a separated, non-l.f.p., non-scheme algebraic space, the closure of one torus orbit, with a fixed point having no equivariant étale affine neighbourhood seeing the chain; existence of such neighbourhoods for non-l.f.p. spaces is linked to approximation of [X/D(M)] (Rydh, Question 2.13, quoted from the note).

Why approximation does not close (W1) directly (verified): write X = lim X_λ with X_λ separated of finite presentation and affine transitions (Tag 07SU, X qcqs); the extension ψ : A(Q)_T → X exists iff compatible ψ_λ exist (uniqueness by schematic dominance of π_k and separatedness of X_λ); but the X_λ carry no action, and without the action the extension fails at finite level (the witness of `chain_no_point`: U = A^2_S minus one section receives compatible maps from all A(N_k)_S and nothing from A^2_S). So one needs the action on the approximations, i.e. approximation of the pair (X, action), which is the open question above.

**(W2) M a group that is not finitely generated, X not affine, no atlas.** Even (F) is not established: Prop 3.32 (ii) is printed for f.g. M and the Lean proves it for f.g. M; the limit-preserving trick (Prop 3.37 / Tag 04AK) needs X l.f.p. and reduces a single magnet to a f.g. one, not an intersection. With X l.f.p. over qc S and an S-affine strongly-FPR atlas the case is closed (§3).

**(W3) M not cancellative, X not affine.** No tool in the paper beyond Lemmas A-D. In the finite examples I computed (M = {0,e} and M = {0,e}×{0,f} with idempotents; A(M)_S a finite disjoint union of copies of S acting through commuting idempotent endomorphisms), every attractor is an equalizer-type condition and (F), (C) hold; no general argument.

The wall is (W1); (W2) and (W3) are the printed generality's remaining breadth, with no evidence either way.

---

## 5. Verdict

- **Not proved in the printed generality; not refuted.** Thm 15.3 as printed is equivalent (Lemma A, verified) to Fact 3.34 for arbitrary common-attractor families, hence (Lemma B, verified) to its finite case plus its chain case; for countable M to the finite case plus ω-chains.
- **Proved in the printed generality (any M, any S, X separated):** Lemmas A, B, C, D; the affine case (Prop 3.24); the reduction of cancellative M to M^gp (Prop 3.31 (iii), re-verified).
- **Proved conditionally:** every abelian group M, X l.f.p. over quasi-compact S with an S-affine strongly-FPR atlas (thm154-ii-nonfg Steps 4, 5(d) + Lean `fact334_strong`, both quoted).
- **Exact wall:** (W1) above: chains, M = Z^r, X a separated algebraic space that is neither a scheme nor l.f.p., which by Lemma D may be taken to be the closure of one orbit. For schemes the fourth-pass hand proof (unreviewed) closes it. No counterexample; none can exist among schemes (if that proof stands), affine spaces, or l.f.p. spaces with an atlas.
- **Paper-level item:** the printed proof of Thm 15.3 cites Fact 3.34 outside its hypotheses. Honest wording with no new hypothesis is not available; the smallest correct statement is "Theorem 15.3 holds whenever Fact 3.34 holds for all families of magnets with a common attractor, in particular if X is affine over S (any M), or if X is locally of finite presentation over a quasi-compact S with an S-affine strongly-FPR atlas (any abelian group M)". Per the author's instruction, this is recorded as the wall, not proposed as the new statement.

Stacks tags cited, not re-read in this session: 082W-082Z (scheme theoretic image for spaces), 07SU (approximation), 04AK (limit preserving), 002H (colimit universal property). Lean declarations quoted by name only: `attractorOrder_affine`, `pureEquivRange`, `SDR4Final` (Lemma D), `fact334_strong`, `fact334_free`, `chain_no_point`, `mapDomain_eq_zero_of_directed`.
