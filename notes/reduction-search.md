**Result in one line.** No proposition of Section 3 reduces 3.31(ii)/3.32(ii) to the free case in the printed generality (X an arbitrary algebraic space): the two failing examples are irreducible cores, and every monoid-level reduction available in the paper preserves the freeness obstruction. What the paper does support is (I) a "squeeze" via 3.29 + 3.35 + Fact 3.6 that settles exactly the nested cases (both failing examples are nested) for X separated, and (II) a reduction to the affine case (i) via an FPR atlas (Prop. 5.1 / Thm 8.3 / Prop. 3.7, the "or 8.3" of Remark 3.13), valid for X separated with a suitable FPR atlas. Full proofs below. Sources: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\am.txt` (pp. 140–161, 178–192), `C:\Users\Arnaud\Desktop\algmag-stacks\notes\prop331-332-spaces-proof.md`.

## 0. Exact scope of the printed arguments

Both printed proofs use: F is invariant under a diagonalizable group D(K) acting on an affine T-scheme W = Spec A, hence F factors through Spec A_0. This is valid iff W → Spec A_0 is a D(K)-torsor, iff A is strongly graded (A_k·A_{−k} = A_0 for all k). For monoid algebras this is exactly geometric freeness:

- 3.31(ii): A = O_T[M×Y], deg(m,y) = f(m) − y ∈ K = f(M)+Y^gp. Stabilizer of a point in the stratum of a face Φ of Y is D(K/(f(M)+Φ^gp)); strongly graded ⟺ free ⟺ Y^gp ⊂ f(M)+Y^× (take Φ = Y^×). Then A_0 = O_T[f^{-1}(Y)], as printed.
- 3.32(ii): A = O_T[N×L], deg(n,l) = l − n. Free ⟺ strongly graded ⟺ N^gp+L^gp = N^×+L^×. Then A_0 = O_T[N∩L].

So the printed proofs are complete precisely in these cases. Free sub-cases used later: 3.31(ii) with f surjective (K = f(M)); 3.31(ii) with f injective and Y ⊂ f(M); 3.32(ii) with N, L groups; 3.32(ii) with N a group containing L^gp. Examples: M=0, Z=Z, Y=N gives f(M)+Y^× = 0 ≠ Z; M=Z, N=L=N gives Z ≠ 0. Confirmed.

## I. The squeeze (X separated): settles both failing examples, and exactly the nested cases

**Lemma T (trivial action).** Γ a f.g. abelian group acting trivially on a separated X, P ⊂ Γ any submonoid. Then X(T) → X^{P}(T), x ↦ (A(P)_T → T → X_T) is bijective.
Proof. 0 ⊂ P ⊂ Γ gives X^0 → X^P → X^Γ (Fact 3.10), both monomorphisms by Prop. 3.29 (X separated). X^0 = X^{D(Γ)} = X (Remark 3.5, trivial action); X^Γ = X (Fact 3.6, A(Γ) = D(Γ)); the composite sends x to D(Γ)_T → T → X_T, which Fact 3.6 (evaluation at the unit) identifies with x. A composite of two monomorphisms that is a bijection forces both to be bijections. ∎ Uses only 3.5, 3.6, 3.29, no 3.31/3.32: no circularity.

**Example 1 (M=0, Z=Z, Y=N).** θ: X^{0⊂0} = X → X^{N⊂Z}, x ↦ constant map; bijective by Lemma T. ∎

**Example 2 (M=Z, N=L=N).** α: X^N → (X^N)^N, f ↦ f∘mult, is injective (mult has the section a ↦ (a,1)). ε: (X^N)^N → (X^N)^Z = X^N, F ↦ F(−,1), is injective: for b ∈ D(Z)(T') one has F(a,b) = b·F(a,1), so F is determined on A(N)_T ×_T D(Z)_T, which is schematically dense in A(N)_T ×_T A(N)_T (Z[N] ⊂ Z[Z] has free cokernel), and X is separated (argument of 3.29; or quote 3.29 for X^N under the 3.32(iii) hypothesis "X^N separated"). ε∘α = id. Hence both are bijections: (X^N)^N = X^N. ∎

**Scope of the squeeze.** For general data it gives X^{N⊂M} ↪ X^{Y⊂Z} ↪ X^{Y+f(M)⊂Z} = X^{q(Y)⊂Z/f(M)} = X (free 3.31(ii) for q: Z → Z/f(M), then Lemma T because D(Z/f(M)) acts trivially on X); the composite is the forgetful map of Cor. 3.30, a bijection iff N = M, i.e. iff f(M) ⊂ Y. Likewise X^{N∩L} ↪ (X^N)^L ↪ X^N closes iff N ⊂ L (or L ⊂ N, the identification being symmetric). So, for X separated, 3.31(ii) holds when f(M) ⊂ Y and 3.32(ii) when N, L are nested; both examples are of this kind (0 ⊂ N; N ⊂ N). It does **not** cover e.g. M=Z, N=N, L=−N (not free, not nested): there (X^N)^{−N} = X^0 needs the separate limit argument F(a,b) = φ(a/b) → fixed point, i.e. genuine descent on the non-free locus.

## II. Reduction to the affine case (i) via an FPR atlas (Remark 3.13's "use 8.3")

Circularity check: Prop. 5.1 invokes 3.31 only for M → M/N^× (surjective, hence free), Thm 8.3 uses 5.1, 8.1, 3.20, 3.22; 8.1 uses 3.35, 3.22; 3.7, 3.17, 3.35 are independent. Nothing below uses a non-free instance of 3.31/3.32.

**Theorem A (3.31(ii)).** M, Z f.g. abelian groups, f, Y, N as in 3.31. Assume X separated over S and that there is a D(M)-equivariant S-affine étale surjective atlas u: U → X (Def. 6.1(iv)) which is Y^×-FPR for the induced D(Z)-action, i.e. U^{D(Z/Y^×)} = U ×_X X^{D(Z/Y^×)}. Then θ: X^{N⊂M} → X^{Y⊂Z}, φ ↦ φ∘A(f), is an isomorphism.
Proof. (1) θ is injective: if θ(φ_1) = θ(φ_2), equivariance gives φ_1∘π = φ_2∘π for π: D(M)_T ×_T A(Y)_T → A(N)_T, (g,y) ↦ g·A(f)(y). π is dual to Z[N] → Z[M×Y], X^n ↦ X^{(n,f(n))}, split injective, so π_T is schematically dominant for every T; the equalizer of (φ_1, φ_2) is closed in A(N)_T (X separated), hence φ_1 = φ_2 (argument of 3.29).
(2) p: U^{Y⊂Z} → X^{Y⊂Z} is an epimorphism of fppf sheaves: by Prop. 5.1(ii) for (X, D(Z), Y, face Y^×), U^Y = X^Y ×_{X^{Y^×}} U^{Y^×}, and U^{Y^×} = U^{D(Z/Y^×)} = U ×_X X^{D(Z/Y^×)} = U ×_X X^{Y^×} (Y^×-FPR, 3.35). So U^Y = X^Y ×_X U → X^Y is étale surjective.
(3) Kernel pair: U^Y ×_{X^Y} U^Y = (U ×_X U)^Y = R^Y by 3.7(ii), where R := U ×_X U is S-affine (closed in U ×_S U since X is separated).
(4) By 3.31(i) for U and for R, θ_U: U^N → U^Y and θ_R: R^N → R^Y are the identity of the same closed subscheme (Thm 3.20), compatible with the projections and with θ_X via 3.17. Hence X^Y = coeq(R^N ⇉ U^N) in sheaves, and the map U^N → X^N (3.17) coequalizes R^N, giving γ: X^Y → X^N with γ∘p = (U^N → X^N). Then θ∘γ∘p = (U^Y → X^Y)∘θ_U = p, so θ∘γ = id (p epi). With (1), θ is bijective. ∎
(If Y is finitely generated, 5.1(i) replaces 5.1(ii) and "separated" can be weakened to "affine diagonal" plus injectivity of θ.)

**Theorem B (3.32(ii)).** M f.g. abelian group, N, L ⊂ M. Assume X separated and that there is a D(M)-equivariant S-affine atlas U → X that is N^×-FPR and (N∩L)^×-FPR. Then α: X^{N∩L} → (X^N)^L, f ↦ f∘mult, is an isomorphism.
Proof. (1) α is injective (section a ↦ (a,1)).
(2) X^N is a separated algebraic space and U^N → X^N is an étale surjective equivariant S-affine atlas: Thm 8.3 (N^×-FPR, X separated), with U^N = X^N ×_{X^{N^×}} U^{N^×} (5.1) and U^N affine (3.20).
(3) U^N → X^N is L^×-FPR. Apply 3.7(ii) to the cartesian square of (2): (U^N)^{L^×} = (X^N)^{L^×} ×_{(X^{N^×})^{L^×}} (U^{N^×})^{L^×}. By 3.35 twice, (U^{N^×})^{L^×} = fixed points of D(M/L^×) inside U^{D(M/N^×)} = U^{D(M/(N^×∩L^×))} = U^{(N∩L)^×} (the subgroups D(M/N^×), D(M/L^×) generate D(M/(N^×∩L^×))), and likewise for X. (N∩L)^×-FPR gives U^{(N∩L)^×} = U ×_X X^{(N∩L)^×}, so (U^N)^{L^×} = (X^N)^{L^×} ×_X U = (X^N)^{L^×} ×_{X^N} (X^N ×_X U), and X^N ×_X U = X^N ×_{X^{N^×}} U^{N^×} = U^N by N^×-FPR and (2).
(4) By 5.1(ii) for (X^N, L, L^×) (X^N separated by 8.3(iii)), (U^N)^L = (X^N)^L ×_{(X^N)^{L^×}} (U^N)^{L^×} = (X^N)^L ×_{X^N} U^N, so q: (U^N)^L → (X^N)^L is étale surjective, with kernel pair ((U×_X U)^N)^L = (R^N)^L (3.7(ii) twice).
(5) By 3.32(i) for the S-affine U and R: (U^N)^L = U^{N∩L} and (R^N)^L = R^{N∩L}, identifications equal to α_U, α_R (both are the closed subscheme of 3.20 cut out by J_N + J_L = J_{N∩L}). So (X^N)^L = coeq(R^{N∩L} ⇉ U^{N∩L}); the map U^{N∩L} → X^{N∩L} induces γ: (X^N)^L → X^{N∩L}, and α∘γ∘q = (U^{N∩L} → (X^N)^L via (U^N)^L)∘α_U = q, so α∘γ = id; with (1), α is bijective. ∎

Existence of the atlases: Thm 6.8 gives a Z-FPR S-affine atlas for one subgroup Z (X quasi-separated, lfp, quasi-compact; separated or M/Z torsion-free); if M/Z is torsion-free every equivariant étale map is Z-FPR (Prop. 6.3 applied to D(M/Z)), so one atlas serves for all the subgroups needed; Fact 7.3 gives strongly-FPR atlases for Zariski locally linearizable actions. On the examples: Ex. 1 has Y^× = 0 and D(Z) acting trivially, so any affine étale atlas qualifies: Theorem A proves it for every separated X. Ex. 2 has N^× = (N∩L)^× = 0 and M = Z torsion-free: any equivariant atlas (6.8) works; Theorem B proves it for X separated, qs, lfp.

## III. Why no monoid-level reduction to the free case exists

Using only free instances plus 3.35 and Fact 3.6 (no separatedness), 3.31(ii) reduces as follows: (a) factor f = i∘s with s: M ↠ f(M) =: Z' (free); (b) X^{Y⊂Z} = (X^{Y^gp})^{Y} = (X^{D(Z/Y^gp)})^{Y⊂Y^gp} by free 3.32(ii) (N = Y^gp a group ⊃ L^gp), 3.35 and free injective 3.31(ii); (c) kill units by free surjective 3.31(ii) for Z → Z/Y^×. The residue is: Z' ⊂ Z, Y sharp with Y^gp = Z, X a D(Z')-space, claim X^{Y⊂Z} = X^{Y∩Z'⊂Z'}; this residue is free iff Z' = Z, i.e. iff the original instance was free. The freeness condition is intrinsic and these operations preserve it. The residual statement is Lemma D of the notes with Γ = Z/Z' (invariant maps A(Y) → X factor through the degree-0 part A(Y∩Z')), whose simplest instance is Example 1 ("invariant maps A^1 → X are constant for the trivial G_m-action"). For non-separated X the only available proof is the descent route in the notes; nothing in Section 3 produces an equality of attractors for different magnets without affineness or separatedness.

## IV. Candidate-by-candidate verdict (both examples, X an algebraic space)

- 3.16 (faces, closed immersion): needs X^N representable and X^N → X^F separated, i.e. already Thm 8.3; yields an immersion X^0 → X^N, not an equality. Fails alone.
- 3.24, 3.31(i), 3.32(i): affine X only. Fail on non-affine X; they are the endpoint of route II.
- 3.29, 3.30: X separated; give monomorphisms only. Exactly route I; close only in the nested cases.
- 3.31(iii): monoid-vs-group, X separated, Z = M^gp; it is itself a free injective instance (Y = N ⊂ f(M) = M). For Ex. 1, M^gp = 0 ≠ Z. Fails.
- 3.32(iii): uses (ii). Circular.
- 3.34: uses 3.32 and needs separated. Circular.
- 3.35, 3.5, 3.6 (attractor of a group, fixed points): sound, group magnets only; they power Lemma T and route II but do not touch a non-group Y.
- 3.36: needs representability by schemes, concerns cartesian squares along faces; says nothing on X^N vs X in Ex. 1.
- 3.37 (colimits): X separated lfp; reduces only to f.g. magnets, which the examples already are.
- Fact 3.15 (retraction p_{N,F}): makes X^0 = X a retract of X^N in Ex. 1; the missing injectivity of X^N → X is again 3.29 (route I).
- Passing to submonoids/groups, quotient by units: the peeling of §III; cannot change the freeness invariant.
- Localization to strata (torsor on the free open): correct stratum-wise, but the torsor quotient of a stratum is not an open of A(Y∩Z') in general (Y = N², Z' = Z(1,−1), Φ = N(1,0): quotient A(N(−1,1)) = A^1 versus A(Y∩Z') = pt); closing needs a limit argument along a one-parameter subgroup plus separatedness, which is Lemma T applied to orbit closures, not a proposition of the paper.
- 5.1 / 8.3 (atlas): works, = route II, with the extra hypotheses listed.

## V. Where the paper uses the non-free cases

5.1(i), 12.1, 12.4: 3.31 for M → M/N^× (free). 16.4(i),(ii): free injective instances (Y ⊂ f(M)) and free 3.32(ii) (N×Z, Z×N). 16.10: G affine, so 3.31(i). 3.32(iii), 3.34, 15.1, 15.5: X separated (and 15.5 also offers 3.24). So every application is either free, affine, or under separatedness; the only non-affine non-free applications (3.32(iii), 3.34, Section 15) all have X separated, where route I covers the nested cases and route II the rest under an FPR atlas. No corrigendum text drafted; no files edited.

# Opus review

The core survives, but the result as written fails on Theorems A and B and on one claimed consequence. I checked it against the journal text in `am.txt`, using the text extraction only, not the page images.

**Holds**
- **Freeness criteria (§0):** a relation 1 = Σ of monomial products forces y ∈ Y^×, resp. n ∈ N^×, l ∈ L^×. So the printed argument works exactly when Y^gp ⊂ f(M)+Y^×, resp. N^gp+L^gp = N^×+L^×. Both failing examples are confirmed.
- **Lemma T, Example 1, Example 2:** correct. They use only 3.5, 3.6 and 3.29, so there is no circularity.
- **Squeeze for f(M) ⊂ Y:** X → X^Y → X^{q(Y)} ≅ X is the identity, because A(q(Y)) → A(Y) → D(M) is trivial. The second arrow is a free surjective instance of 3.31(ii), which is sound.
- **Squeeze for nested N, L:** the injectivity of F ↦ F(−,1) is correct, using that A(N)×D(M) → A(N)×A(L) is dominant.
- **Logic of Theorems A and B:** steps (1) and (3)–(4) of A, and the FPR transfer and coequalizer of B, are correct given their inputs. That includes N^×∩L^× = (N∩L)^× and D(M/N^×), D(M/L^×) generating D(M/(N^×∩L^×)).
- **Uses of 3.31/3.32 in the paper (§V):** spot-checked at the uses in §12, §15 and 16.10. Section 15 has X separated (line 3239), 15.5 also offers 3.24 for its 3.32 step, 12.4 is affine, and 16.10 uses a group scheme.

**Fails as written**
1. **Theorems A and B omit a hypothesis.** Both rely on 5.1(ii) for non-finitely-generated Y, N, L.
   - The printed proof of 5.1(ii) is a colimit through 3.37 (lines 1646–1653). Prop. 3.37 assumes X separated and locally of finite presentation (line 1511).
   - So "X separated" alone is not established. Step (2) of A and steps (2) and (4) of B need "X lfp, or Y, resp. N and L, finitely generated".
   - Theorem B also uses 8.3 for N, whose case (a) cites the same 5.1(ii). X^N is lfp by 8.3(iv), so the repair carries through.
   - The circularity check missed this. 3.37 itself is not circular, since it uses neither 3.31 nor 3.32.
2. **The claim on Example 1 is false as derived.** The result says "Theorem A proves it for every separated X". Theorem A requires an S-affine atlas, which means finitely many charts (Def. 6.1(iv), Remark 6.2), and none exists for X = ⊔_∞ S.
   - Example 1 itself is safe, via Lemma T.
   - The same slip affects Example 2: "Theorem B proves it for X separated, qs, lfp" drops quasi-compactness, which 6.8 needs for an S-affine atlas.
   - Repair: restate A and B for a disjoint union of S-affine charts, applying 5.1 chart by chart. R is then a disjoint union of S-affine schemes U_a ×_X U_b.
3. **The existence paragraph is incomplete.**
   - Theorem A's condition is stated for D(Z), but 6.8 is stated for D(M). It needs the unstated translation: Y^×-FPR for D(Z) equals f⁻¹(Y^×)-FPR for D(M), because D(Z/Y^×) → D(M/f⁻¹(Y^×)) is fppf surjective on the acting group.
   - Theorem B needs one atlas that is FPR for two subgroups at once, and 6.8 gives only one subgroup per atlas. When the quotients have torsion and the action is not locally linearizable, that existence is not available from the paper (compare Conjecture 6.9). Route II for 3.32(ii) is therefore conditional there, not just "suitable".
4. **§III is misstated.**
   - As written, the residue cannot have both Z' = f(M) and Y^gp = Z. The action must first be pushed to Z' = (f(M)∩Y^gp) mod Y^×, using that D(Z/f(M)) and D(Z/Y^gp) act trivially. With that fix, the invariance claim is correct: the residue is free iff Y^gp ⊂ f(M)+Y^×.
   - §III shows only that these particular operations preserve the obstruction. The headline "no proposition reduces" is an exhaustion over §IV, not a proved impossibility. It is supported, and I found no missed candidate, but it does not rule out the author's unseen reduction.
5. **§IV mislabels 3.31(iii).** It is not a "free injective instance". There M is not a group, so (ii) does not apply, and its proof is a schematic-density argument using separatedness. The conclusion "fails" is unaffected.

**What stands after the repairs**
- For X separated, the squeeze settles exactly the nested cases, including both examples.
- Route II gives the rest under an FPR atlas, plus lfp or finitely generated magnets.
- For X non-separated, no route from the paper is known, only the descent proof in `C:\Users\Arnaud\Desktop\algmag-stacks\notes\prop331-332-spaces-proof.md`.

No files were edited.

VERDICT: BROKEN