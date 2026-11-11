**Verdict: the last clause of Thm 6.8 / Thm A.2 is false as printed when S is not quasi-compact, even for S separated. It is correct (and "obvious") exactly when S is quasi-compact, or more generally when S admits a locally finite affine open cover with affine open immersions. The counterexample below is under hypothesis (ii); under hypothesis (i) (X separated over S) with S separated non-qc I could neither prove nor refute it — the safe statement is to add "S quasi-compact".**

## 1. What the words mean in the printed text (Def 6.1, p. 156–157)

- Def 6.1(iv): an equivariant atlas is étale surjective `U -> X` with `U = ⊔_{α∈A} U_α`, each `U_α` an **S-affine scheme**, i.e. `U_α -> S` is an affine morphism (relative, over S; nothing absolute). It is called **S-affine** if `A` may be chosen finite; Rem 6.2: equivalently `U` is a single scheme affine over S.
- Thm 6.8: "may be chosen quasi-compact (in particular S-affine here) if X -> S is quasi-compact". Three possible readings, and under the theorem's hypotheses (X quasi-separated, X -> S qc) **they all coincide**:
  - (a) `U -> X` quasi-compact: then `U -> S` is qc (composition with `X -> S` qc), so over each affine `V ⊂ S`, `U_V = ⊔ (U_α)_V` is qc, hence only finitely many pieces are nonempty, hence `U_V` affine. So `U -> S` is affine, i.e. `U` is S-affine with `A = {U}`.
  - (b) `U` S-affine (`A` finite): then `U -> S` affine hence qc, hence `U -> X` qc because X is quasi-separated (Stacks 03GI-type argument).
  - (c) `U` quasi-compact in the absolute sense: implies (a); conversely false when S is not qc (U -> X surjective and image of X in S non-qc forces U non-qc). So (c) is trivially unattainable as soon as the image of X is not qc; the printed "(in particular S-affine)" shows (a)/(b) is the intended meaning.
  
  So the question is well posed as: **does there exist a Z-FPR atlas `U -> X` with `U -> S` affine?** The earlier objection "finitely many affine charts cannot cover" is irrelevant (U need not be absolutely affine), and the hope "one S-affine chart over each affine of S that glues" is exactly what fails: the proof of A.2 says "the assumptions and conclusion being local over S, we may assume S affine" — existence of a Z-FPR atlas *is* local on S (take `⊔_i U_i` over an affine cover `{S_i}`), but existence of an **S-affine** atlas is not: `⊔_i U_i -> S` is affine only if every affine `V ⊂ S` meets finitely many `S_i`, i.e. the cover is locally finite. For S affine (the case the proof actually treats) the claim is indeed obvious: the images of the affine neighbourhoods `U(x)` are open and cover the qc space X, so finitely many suffice.

## 2. Counterexample (S separated, regular, irreducible, locally of finite type over a field; hypothesis (ii))

**Base.** Let k be a field, `Y_0 = A^2_k`, `p_1 ∈ Y_0` a closed point, `Y_1 = Bl_{p_1} Y_0` with exceptional curve `E_1`, `p_2 ∈ E_1` closed, `Y_2 = Bl_{p_2} Y_1`, etc. Put `S_n := Y_n \ {p_{n+1}}`; then `S_n ≅ Y_{n+1} \ E_{n+1} ⊂ S_{n+1}` is open, and `S := ∪_n S_n`. S is separated, regular, irreducible (increasing union of irreducible opens), locally of finite type over k, and **not quasi-compact** (`S_{n+1} \ S_n = E_{n+1} \ {p_{n+2}} ≠ ∅`). Being irreducible and non-qc, S has no locally finite open cover at all (the generic point lies in every member).

Choose closed points `q_n ∈ E_n \ {p_{n+1}} = S_n \ S_{n-1}`. The set `Q = {q_n}` is closed and discrete (`Q ∩ S_N = {q_1,…,q_N}`).

**Space.** Let `X` be S "with `q_n` replaced by n copies": glue the schemes `S^{(j)} := S \ {q_n : n < j}` (j ≥ 1) along the common open `S \ Q`. Then `X -> S` is étale, surjective, and **quasi-compact**: a qc open `V ⊂ S` lies in some `S_N`, so its preimage is a union of N+1 qc opens (copies j > N+1 add nothing new). X is a locally noetherian scheme, hence quasi-separated, and locally of finite presentation over S. It is not separated over S (fibre over `q_n` has n points glued along the complement), so we use hypothesis (ii): `M = Z`, `Z = 0`, `G = G_{m,S}` acting trivially (or `M = 0`). Then `X^{D(M/Z)} = X`, and any étale surjective `U -> X` with trivial action and U a disjoint union of S-affine schemes is a Z-FPR atlas (`U^G = U = U ×_X X^G`). Thm 6.8's existence part holds (e.g. `U = ⊔` affine opens of X).

**No S-affine atlas exists.** Suppose `U -> X` is an atlas with `U -> S` affine (equivalently, by §1, `U -> X` qc, or `U` S-affine). Then `U -> S` is affine étale, hence separated, quasi-compact, finitely presented.
1. Let η be the generic point of S, `K = k(S)`. `U_η` is a qc étale K-scheme, hence finite étale: `U_η = ⊔_i Spec L_i`, `d := Σ_i [L_i : K] < ∞`. Since `U -> S` is open, every irreducible (= connected, U being normal) component `C_i` of U has its generic point in `U_η`; so U has ≤ d components, `C_i` open in U, integral, normal, affine étale over S with function field `L_i`.
2. Fix n and put `R = O_{S,q_n}`, a regular (so normal, noetherian) local domain with fraction field K. `C_{i,R} := C_i ×_S Spec R` is normal, separated and quasi-finite over R, so by Zariski's Main Theorem it is an open subscheme of `Spec R_i'`, `R_i'` = integral closure of R in `L_i` (finite over R since R is noetherian normal and `L_i/K` finite separable). The number of primes of `R_i'` over the maximal ideal of R is ≤ `[L_i : K]` (R normal; e.g. `R_i' ⊗_R R^h ⊂ L_i ⊗_K K^h = ∏_j L_{ij}` with `Σ_j [L_{ij} : K^h] = [L_i : K]`, and each local factor of the finite `R^h`-algebra `R_i' ⊗ R^h` contains at least one of the minimal primes `L_{ij}`).
3. Hence `#|U_{q_n}| ≤ Σ_i [L_i : K] = d` for **every** n. But `U -> X` is surjective and `X_{q_n}` has n distinct points, so `#|U_{q_n}| ≥ n`. Contradiction for `n > d`.

So for this `(S, X, G)` every Z-FPR atlas has `U -> X` non-quasi-compact, `U` not S-affine, and U not quasi-compact. The clause fails under all three readings.

**Is S separated needed?** No — separation of S was *allowed* here, and the counterexample has S separated (even regular, irreducible). The same mechanism, with the line with countably many origins as S and `X` = that line with the n-th origin n-tupled, gives a shorter but non-separated example. What the counterexample does not cover is hypothesis (i): if `X -> S` is separated and quasi-compact, I have no counterexample and no proof for non-qc S (the growth trick is blocked: an étale separated qc `X -> S` already has fibres of bounded size by step 2; non-étale X such as `A^1_S` minus a locally finite set of points resist the same counting). Do not claim either way.

## 3. Exact correct statement

Replace the last clause of Thm 6.8 / Thm A.2 by:

"Then there exists a Z-FPR atlas `U -> X`. If moreover `X -> S` is quasi-compact **and S is quasi-compact**, U may be chosen quasi-compact; in particular U may be chosen S-affine (an affine scheme)."

Proof as in A.2: reduce to S affine of finite type over Z; the images of the affine G-equivariant étale neighbourhoods `U(x)` are open and cover the qc X, so finitely many suffice, and a finite disjoint union of affine schemes is affine. (This is the step the appendix calls obvious, and it is, once S is qc.)

Slightly more general version (same proof plus gluing `U := ⊔_i U_i`): if S has affine diagonal (e.g. S separated) and admits a locally finite cover by affine opens `S_i` (e.g. S a disjoint union of qc schemes), and `X -> S` is qc, then a Z-FPR atlas with `U -> S` affine (equivalently `U -> X` qc) exists; Z-FPR is checked piecewise since `X_i^H = X^H ×_X X_i` for an open G-stable `X_i`. Affine diagonal is needed so that `U_i -> S_i -> S` stays affine; local finiteness so that `⊔ U_i -> S` is qc. Note "locally noetherian" does not suffice (the line with infinitely many origins is locally noetherian with no locally finite affine cover), and "S qc" is the clean hypothesis.

## 4. Downstream in the paper (for the correction list)

- Prop 8.5 (p. 161, "X -> S quasi-compact and separated", S arbitrary) invokes "an S-affine N-FPR atlas as in Theorem 6.8" and then uses a *finite* set of generators of the graded `O_S`-algebra of U. Both steps need S quasi-compact (the finite generating set does not exist over non-qc S even when U is S-affine). Prop 8.5 should assume S quasi-compact as well (its hypothesis (i) is X separated, so it is not hit by the counterexample, but its proof is).
- Thm 8.3(v) and Lemma 6.7(ii) are unaffected (they take the S-affine atlas as a hypothesis or do not use the clause).
- Conjecture 6.9(ii) "If X/S is quasi-compact, there exists an S-affine strongly-FPR atlas" with "S an arbitrary scheme" is refuted by the example above as stated (trivial action, X not separated — but 6.9 assumes X separated over S, so the conjecture itself survives; only the Thm 6.8 clause falls).

Files consulted (read only): C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\am.txt (Def 6.1 at lines 1673–1697, Thm 6.8 at 1753–1762, Thm A.2 at 3915–3924, its proof at 4081–4122, Prop 8.5 at 1927–1939). No files edited.

# Opus review

**Result: the Thm 6.8 counterexample survives, but the proposed correction, the headline and two supporting claims are wrong.** No files edited. I reread Def 6.1, Rem 6.2, Thm 6.8, Conj 6.9, Prop 8.5, Thm A.2 and its proof in am.txt. No blanket hypothesis on S turned up: a search for conventions found only "fix a base scheme S" (line 769) and "S a scheme" (line 1657).

**What survives**

- **Readings of the clause, §1.** Def 6.1(iv) means `U_α -> S` affine, and readings (a) and (b) are equivalent.
  - (a) `U -> X` qc implies `U -> S` qc. So finitely many `U_α` lie over each affine V, and `U -> S` is affine.
  - (b) `U -> S` qc and X quasi-separated over S imply `U -> X` qc.
  - Reading `U -> S` qc is the same case.
  - Small slip: "(c) implies (a)" needs S quasi-separated, because absolute qc of U gives `U -> X` qc only then. This is harmless, since (c) is excluded anyway.
- **Base S, §2.**
  - `S_n` is open in `S_{n+1}`, because `p_{n+2} ∈ E_{n+1}` and `S_n = Y_{n+1} \ E_{n+1}`.
  - S is separated, regular, irreducible and not qc.
  - Q is closed and discrete.
- **Space X, §2.**
  - The fibre over `q_n` has exactly n points.
  - `X -> S` is étale, surjective and qc, because a qc open V lies in some `S_N` and only copies j ≤ N+1 matter.
  - X is locally noetherian, hence quasi-separated.
- **Counting, §2.**
  - U is normal, with finitely many components, each meeting the generic fibre.
  - Zariski's Main Theorem embeds `C_{i,R}` as an open in `Spec R_i'`.
  - The bound #primes over m ≤ `[L_i:K]` holds: primes are double cosets `D\G/H`, so there are at most `|G/H|`.
  - So `#U_{q_n} ≤ d < n` for large n, a contradiction.
- **Scope of the argument.** It never uses the action on U, which may be non-trivial. Non-existence is therefore unconditional under hypothesis (ii) with S separated.

**Refutation of the rest**

Example E:
- Let S be the plane with doubled origin, with charts `S_1, S_2 ≅ A^2`, over a field.
- Let `X = S_1`, with `X -> S` the open immersion, and take the trivial action (`M = 0`).
- Then X is separated, quasi-separated, finitely presented and qc over S, and S is quasi-compact and noetherian. Both (i) and (ii) hold.

Suppose `U_α -> S` is affine and étale over X, with some point over the origin of `S_1`.
- `U_α = U_α ×_S S_1` is affine, because `U_α` maps into `S_1`.
- `U_α ×_S S_2 = U_α \ f^{-1}(0)` is affine, because `S_2` is affine.
- `U_α` is regular of dimension 2 at those points and `f^{-1}(0)` is nonempty of codimension 2. By Hartogs the complement cannot be affine. Contradiction.

So E has **no equivariant atlas in the sense of Def 6.1(iv) at all**. This has four consequences:

1. **§3 is false.** The proposed fix "X -> S qc and S qc implies an S-affine atlas" fails on E.
   - The answer's gloss "S-affine (an affine scheme)" conflates two things: the finite `⊔U_i` is absolutely affine, but it is not affine over S when `S_i -> S` is not affine.
   - The headline "correct exactly when S is quasi-compact" is false for the same reason.
2. **§1 is false.** It says "existence of a Z-FPR atlas *is* local on S (take `⊔_i U_i`)". The composite `U_i -> S_i -> S` need not be affine. On E, even the first clause of Thm 6.8 and Thm A.2 fails as literally stated. The reduction "S affine" in the proof of A.2 is therefore invalid for the existence part too, not only for the last clause. The answer applies its affine-diagonal condition only in the "more general version", so it misses this.
3. **§4 is wrong on Conj 6.9.** Its sentence is self-contradictory: it says "refuted … the conjecture itself survives". E has X separated over an arbitrary S, so E **literally refutes both 6.9(i) and 6.9(ii)** unless S is restricted. Only the case with S of affine diagonal remains open from this analysis.
4. **The word "exactly" in the headline is unproved.** Nothing shows that the clause fails for *every* S outside the listed class. The answer builds one S and gives no argument for the converse. Claim only sufficiency and one counterexample.

**Repairs**

- **Existence.** Add to Thm 6.8 and A.2: S has affine diagonal (S separated suffices), or else S has an affine open cover with every `S_i -> S` an affine morphism. Then `⊔U_i` has S-affine pieces.
- **Last clause.** Add: S is quasi-compact, with the same condition as above. The finite `⊔U_i` is then affine over S. Alternatively, keep the "locally finite cover" version together with the same condition. That version does hold.
- **Prop 8.5.** The hypotheses must include S quasi-compact and the same condition, or S affine. The answer's "assume S quasi-compact" is not enough for the proof, because the S-affine atlas may not exist. The Prop 8.5 conclusion itself is not refuted, since on E it holds trivially. Only its proof is hit.
- **Still undecided.** Hypothesis (i) with S separated and non-qc is unresolved. I tried `X = S \ Q` on the blow-up tower and could not settle it, because it needs two Cartier divisors meeting exactly in Q. The answer's "do not claim either way" stands. Its line "the same mechanism … non-separated example" is fine.

VERDICT: BROKEN