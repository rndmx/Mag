# Fact 3.34 for infinite families, X separated, no atlas: attempt (2026-11-06)

Status: see "Fourth pass" at the end: printed (ii) PROVED ON PAPER for X a separated scheme, all families; X a non-scheme algebraic space open. Sections 1-6 are the first pass.

Setup. `M` f.g. abelian group, `(N_i)` magnets with `X^{N_i}` all equal. Finite intersections are fine (`fact334_finite_scheme` for schemes), so assume a decreasing directed family, `N_∞ = ⋂ N_i`. Printed proof uses `A(⋂ N_l)_S = colim_J A(⋂_J N_l)_S`, which fails in schemes (`chain_no_point`).

1. Which X can be a counterexample. Affine X: Prop 3.24. X with a strongly-FPR atlas: Lean, `fact334_strong`. X separated, l.f.p.: atlas from Thm 6.8 (on stubs), under the size cutoff. So a counterexample must be separated, NOT locally of finite presentation, and non-affine.

2. Proof in a special case (by hand). Take T affine, `f : A(N_1)_T → X` equivariant. It factors through `A(N_k)_T` for all k. Suppose (a) `A(N_1)_T → A(N_∞)_T` is faithfully flat and quasi-compact, and (b) the ideals `I_k` of `W_k = A(N_1) ×_{A(N_k)} A(N_1)` in `W = A(N_1) ×_{A(N_∞)} A(N_1)` have zero intersection. On `W`, the two maps to X agree on each closed `W_k`. X separated: their equalizer is closed in W and contains all W_k, so its ideal is in `⋂ I_k = 0`, so they agree on W. Fpqc descent (X is an fpqc sheaf) gives `A(N_∞)_T → X`. Equivariance descends too. Example where (a) holds: `N_k = cone((1,0),(k,1)) ∩ Z²`, `N_∞ = N(1,0)`, since `Z[N_k]` is free over `Z[t]`. Whether (b) holds in general was not settled.

3. Where (a) fails. `A(N_k) → A(N_∞)` need not be surjective. Example: `N_k = {a ≥ 0, b ≥ -a/k} ∩ Z²`, `N_∞ = N²`. Then the image in `A²` is `{y ≠ 0} ∪ {0}`: the orbit `{y = 0, x ≠ 0}` is missed for every k, because `(1,0)` is interior to the cone of N_k. So face lying-over fails for all k.

4. Natural counterexample attempt. Take X the image of the `A(N_k)` in `A(N_∞)`, as an open subscheme U. Then the inclusion would give a point of all `X^{N_k}` with no extension to `A(N_∞)`, since X^{N_∞} → would force the identity of `A(N_∞)` into U. This needs the missing locus closed and stable, hence containing the vertex. It does not work:
   - In the example of 3 the vertex is in the image, and any stable open containing it is everything.
   - In general the vertex is always hit for large k. If `n ∈ N_∞` is a nonunit with `-n` a unit of every `N_k`: the unit groups `N_k^×` have eventually constant rank, hence finite index in a fixed lattice, so a positive multiple of `-n` is in N_k, hence `-n ∈ N_k` for all k (`neg_mem_of_nsmul`), hence `-n ∈ N_∞`, contradiction. `neg_mem_iInf_of_multiples` is this step; the finite index step is by hand, not in Lean.
   So open subschemes of `A(N_∞)` give no counterexample.

5. Consequence of 4. If x = f(vertex) has a stable affine neighbourhood V in X, then the preimage of V in `A(N_1)_T` is a stable open containing the vertex locus, so it is all of it, f lands in V, and Prop 3.24 concludes. So the gap is exactly: non-affine X, not l.f.p., with no stable affine neighbourhood of a fixed point. (This assumes N_1 sharp and T local, by hand; the general reduction is by Prop 3.31.)

6. Exact wall. For a counterexample, one would need a separated non-l.f.p. scheme with a torus action and a fixed point with no stable affine neighbourhood, seeing the cones N_k but not their limit. For a proof, one would need to replace fpqc descent in 2 by something valid when `A(N_1) → A(N_∞)` is not surjective, as in 3: X would have to extend f over the missed orbits, and I found no argument from separatedness alone.

# Second pass (2026-11-06): proofs on paper. Sections 3-6 above are superseded where they conflict.

Lean checks only `pinching_iInf_eq_zero` and `krull_step` (AlgMag/Fact334InfAlgebra.lean). Everything else here is by hand and has had no independent review.

Setting: X separated scheme over S, M f.g. abelian group, T = Spec R, p in X^{N_k}(T) for all k, f_k : A(N_k)_T -> X the extensions.

A. Pinching: N_k = cone((1,0),(k,1)), N_inf = N(1,0). PROVED for every R. Coordinates (x,w) on A(N_1), w = xy. W = Spec R[x,w,w'], and W_k has ideal (x^(k-1)(w-w')). The equalizer of the two maps W -> X is closed and contains all W_k, whose ideals meet in 0. So the maps agree, and fpqc descent along A(N_1) -> A(N_inf) concludes.

B. Cone: N_k = {a>=0, b>=-a/k}, N_inf = N^2. PROVED for every R. More generally for N_1 sharp f.g. and N_inf f.g., with e in N_inf such that e + N_1 is in N_inf. Shrink T so that the vertex section lands in an affine open U of X_T (X separated over an affine piece of S).
 1. J_k = ideal of N_k\0, S_k = 1 + J_k. Every point of Spec S_k^{-1}R[N_k] specializes into V(J_k), so it lies in f_k^{-1}(U). This gives phi_k : O(U) -> S_k^{-1}R[N_k], compatible in k.
 2. Expand in series: phi_1(u) in R[[N_1]] has support in N_k for every k, hence in N_inf.
 3. Denominators. Write phi_1(u) = a/h, h in S_1. Let R_0 in R be the f.g. subring of the coefficients of a and h. The series c = a/h has coefficients in R_0. Put A = R_0[N_inf], noetherian, I = J_inf, b = chi^e h, e' = chi^e a, both in A. Then b c = e' with c in A^ = R_0[[N_inf]], so e' is in bA + I^n for all n, and `krull_step` gives g in 1+I with g e' = b a'. Since b is a nonzerodivisor in R_0[[N_1]], c = a'/g. So phi_1(u) lies in Lambda = S^{-1}R[N_inf], S = 1 + J_inf. This gives h : Spec Lambda -> U.
 4. On Spec S^{-1}R[M], h agrees with the orbit map of p: both agree after inverting S_1, elements of S_1 are nonzerodivisors of R[M], and the equalizer is closed.
 5. a : G x Spec Lambda -> A(N_inf)_T, (g,z) -> gz, is flat and quasi-compact. It is surjective: at a point z and a generic g, an element 1 + sum r_m chi^m of S takes the value 1 + sum r_m chi^m(z) g^(-m), nonzero since the g^(-m) are independent. So it is an fpqc cover.
 6. (g,z) -> g h(z) descends. On the fibre product the two maps agree over the torus A(M), by 4 and equivariance, the torus preimage is schematically dense by flatness, and the equalizer is closed. The descended map q extends p. Equivariance and being over T: same density argument.

C. Not settled. (i) N_inf of smaller rank and not of type A, e.g. N_k = cone((k,k+1),(k+1,k)), N_inf = N(1,1): step (b) of the first pass, or a mix of A and B. (ii) N_1 not sharp, with varying unit groups. If all N_k are groups, the fixed-point density argument works: Z[M/H_inf] injects in the product of Z[M/H_k], and the equalizer is closed. Mixed case not done. (iii) N_1 or N_inf not f.g.: krull_step needs A noetherian. N_1 = N^2, N_k = {a>=1,b>=0} + {(0,b),b>=k}, N_inf = {0} + {a>=1,b>=0}: here the series condition alone is NOT sufficient (x/(1+y) has support in N_inf and is not in Lambda); one must also use that f is constant on the fibre over the vertex. Open.

D. Approximation route, abandoned. A limit X = lim X_i with G-actions, X_i of finite type, would reduce everything to the l.f.p. case, with a directed pointwise form of `fact334_strong`. It needs [X/G] -> BG of approximation type. Rydh (J. Algebra 422 (2015); read in the arXiv version, not the journal) Questions 2.13 leaves open "Is every representable morphism of approximation type?". An affine groupoid presentation R in G x U x U exists for X qc separated, but finite-level R_i are not groupoids over one U_i. Not used.

No counterexample found. None of A, B restricts X: both hold for arbitrary separated X, so the "no stable affine neighbourhood" wall of section 6 is not an obstruction.

# Third pass (2026-11-06): SHARP CASE PROVED IN GENERAL by the diagonal trick. Sections A-C above are subsumed when some N_i is sharp. By hand, no independent review; the algebra core is in Lean (AlgMag/Fact334InfDiagonal.lean).

Theorem. X separated SCHEME over S, M f.g. abelian group, (N_i) arbitrary submonoids with X^{N_i} all equal, and some N_1 whose unit group lies in every N_i (for instance N_1 sharp). Then X^{N_1} = X^Q, Q = intersection. No finiteness on X, N_i, Q, R; rank of Q may drop.

Warning that motivates it. The plain intersection statement "c in S_k^{-1}R[N_k] for all k implies c in S^{-1}R[Q]" is FALSE. Q = {0} u {a>=1,b>=0}, N_k = Q u {(a,b): b>=L_k, a>=-b/k} (L_k -> oo), c = x/(1+y): for odd m>=max(k,L_k), c = x(1+y+..)/(1+y^m) type fraction with 1+y^m in S_k, and c is not in S^{-1}R[Q]. So the argument must use that the vertex is fixed by the torus. All previous attempts did not.

Case N_1 sharp. Reduce to N_i contained in N_1 by replacing N_i with N_1 n N_i (finite case, fact334_finite_scheme). T = Spec R small enough that v = f_1(vertex) lands in an affine open U of X_T. G = D(M). R' = R[M].
 1. S_i = 1 + J_i, J_i the ideal of N_i\0. Maximal ideals of S_i^{-1}R[N_i] contain J_i, so f_i maps Spec S_i^{-1}R[N_i] to U: phi_i : O(U) -> S_i^{-1}R[N_i], compatible. Put H = Hahn series over R on M for a total order on M/torsion positive on N_1\0 (the saturation of the image of N_1 is sharp); elements of S_i are units of H. So phi = phi_1 : O(U) -> H has values with support in every N_i, hence in Q. Constant term = v^*.
 2. v is G-fixed. So Omega = a^{-1}(U) n (G x U), open in G x U, contains V(I_v), I_v = ker(O(U) tensor R' -> R'). Hence w in 1 + I_v with D(w) in Omega. For u in O(U): a^*u = rho/w^n, with rho in O(U) tensor R'.
 3. E = S'^{-1}R'[N_1], S' = 1 + J_1 R'. The map (g,z) -> (g, f_1 z) : Spec E -> G x U lands in Omega and in D(w), and by equivariance a^*u pulls back to tau(phi u), where tau: chi^n -> g^n chi^n. Hence in Hahn series over R':
    tau(c) Psi = rho', c = phi(u), Psi = 1 - sum_m g^m d_m, rho' = sum_l g^l e_l, finite sums, d_m in phi(ker v), e_l in phi(O(U)).
 4. DIAGONAL. Delta : H(R') -> H(R), coefficient at s = coefficient of g^s in the coefficient at s. Delta(tau(c) B) = c Delta(B) (`diag_tau_mul`). So c g0 = a', g0 = 1 - sum_m [d_m]_m chi^m in 1 + J_Q R[Q] since supp d_m in Q\0, and a' = sum_l [e_l]_l chi^l in R[Q]. Hence c in Lambda = S^{-1}R[Q], S = 1 + J_Q. No noetherian hypothesis, no Krull: krull_step is no longer needed.
 5. h : Spec Lambda -> U, with h o pi = f_1 on Spec S_1^{-1}R[N_1], pi : A(N_1) -> A(Q).
 6. alpha : G x Spec Lambda -> A(Q)_T, (g,z) -> gz, is flat (shear, then localization), affine, surjective (at z over a field k, s = 1 + sum r_m chi^m goes to 1 + sum r_m z(m) g^m, nonzero in k[M] after a character of the torsion, since m is not torsion; so S maps to nonzero elements of a domain and the generic g works). fpqc cover.
 7. Descent of F(g,z) = g h(z). Fibre product = G x P_0, P_0 = Spec Pi, Pi = tau(S)^{-1}(R' tensor Lambda) (the locus t, z' with t z' in Spec Lambda). Need t h(z') = h(t z') on P_0. Pi -> H(R') is injective (all inverted elements are units of H(R') and R'[Q] embeds), so Pi -> E is injective. On Spec E, both maps are t f_1(z) = f_1(t z). Equalizer closed in P_0 since X separated, and contains the image of Spec E, whose ideal is 0. Done. This replaces the torus density of pass 2 and handles rank drop, so pinching needs no separate proof.
 8. q : A(Q)_T -> X. Equivariant by the cover G x G x Spec Lambda. q o pi = f_1 on the cover G x Spec S_1^{-1}R[N_1] of A(N_1)_T. Glue over T by the monomorphism of Prop 3.29.

Case units H = units of N_1 contained in all N_i. Replace N_i by N_1 n N_i, all with unit group H. Work over T1 = A(H)_T, group D(M/H), which acts over T1. R[N_i] is an M/H-graded R[H]-algebra, N_i/H sharp, Q/H = intersection of the N_i/H. Steps 1-8 run with graded pieces and T1 shrunk affine (allowed: shrinking T1 is why the unit case is not obstructed). The result q is D(M/H)-equivariant over T1 and q o pi = f_1. Full G-equivariance: the equalizer of the two maps G x A(Q) -> X is closed and contains the image of G x A(N_1), and R'[Q] -> R'[N_1] is injective.

Remaining: unit groups with no minimum, e.g. N_k = kZ x N in Z x Z (this example is easy: f_1 is invariant under mu_k for all k, and union of mu_k is schematically dense in G_m), mixed cases not done. Also X a separated algebraic space (no affine open nbhd; only etale) not done.

# Fourth pass (2026-11-06): unit groups without minimum, idea (details being written below). Reduce to H = intersection of units = 0 over T1 open in A(H)_T: choose N_1 of minimal unit rank among finite intersections; then N_i n H_1 = H_i; vertex map v_1 on A(H_1)_T is invariant under all D(H_1/H_i), hence under D(H_1/H), hence descends to v on A(H)_T. Then f_i(V(J_i)) lands in an affine nbhd of v(T1) and passes 1-8 run over T1.

Fourth pass, full proof. By hand, checked once line by line by its author, no independent review. Lean: AlgMag/Fact334InfDiagonal.lean, AlgMag/Fact334InfUnits.lean (algebra steps only). Supersedes "Remaining" of the third pass for schemes.

Theorem. X separated SCHEME over S, M f.g. abelian group, (N_i) arbitrary with all X^{N_i} equal. Then X^{N_i} = X^Q, Q = intersection. This is printed (ii) for schemes, with no added hypothesis.

R0. Directed, minimal rank. Close the family under finite intersections (fact334_finite_scheme; Q unchanged). Pick N_1 whose unit group H_1 has minimal rank, keep the N_i inside N_1. H_i = units of N_i. H_i <= H_1 has the same rank, so each x in H_1 has a multiple in H_i (`exists_nsmul_mem_of_finrank_eq`), so N_i n H_1 = H_i (`neg_mem_of_mem_units`), hence N_i\H_i is in N_1\H_1. H = intersection of the H_i = units of Q.
R1. Vertex. T = Spec R. pi: A(N_1)_T -> A(N_i)_T sends A(H_1)_T into A(H_i)_T by R0. So v_1 = f_1 on A(H_1)_T equals v_i o pi_i with pi_i a D(H_1/H_i)-torsor. So v_1 is invariant under each D(H_1/H_i). The equalizer of (g,z) -> v_1(gz), v_1(z) on D(H_1/H) x A(H_1)_T is closed and contains these subgroups, and their ideals meet in 0 (`mapDomain_eq_zero_of_directed`, coefficients R[H_1]). So v_1 descends along the D(H_1/H)-torsor: v : A(H)_T -> X, and v_i = v o pr_i for all i. Over T1 below, v is fixed by G' = D(M/H): g acts on A(H_1)_T preserving fibres of pr_1, and pr_1 is an fpqc epi.
R2. Base change. Cover A(H)_T by affine opens T1 = Spec R1 with v(T1) in an affine open U of X over an affine of S containing the image of T. W = U x T1, A = O(W). M' = M/H. B_i = R1 tensor_{R[H]} R[N_i], D = R1 tensor_{R[H]} R[Q], B = R1 tensor_{R[H]} R[M]: M'-graded, each piece free of rank 1 over R1 (a twisted group algebra in general, since H need not split). N_i' = N_i/H, Q' = Q/H is the intersection and is sharp, so Q'\0 has no torsion. Q' n H_1' = 0 (`iInf_inter_eq_zero`). f_i : Spec B_i -> X_{T1} are G'-equivariant over T1.
Hahn ring. Order. On M'/tors take a total group order positive on images of N_1'\H_1': the image in ((M'/tors)/sat H_1') of N_1' is sharp with saturation sharp, so Levi extends it; lexicographic with any order on sat H_1'. Calligraphic H = functions c on M' with c_m in B_m and PWO support in M'/tors (M' -> M'/tors has finite fibres, so convolution is defined). H' the same with B tensor R', R' = R1[M'].
1. J_i = pieces outside H_i', S_i = 1+J_i, E_i = S_i^{-1}B_i, C_i = B_i/J_i. S_i in S_1 by R0, S_i units of H. E_1 embeds in H. Maximal ideals of E_i contain J_i, and f_i on V(J_i) is v o pr_i, in W. So phi_i : A -> E_i, compatible. c = phi_1(u) has support in every N_i', hence in Q'; c_0 = v^*u.
2-4. As third pass, over R1, with tau(b_m) = g^m b_m and Delta on pieces. w in 1+I_v, D(w) in Omega, using that v is G'-fixed. phi(ker v) lies in J_1 E_1, so w maps to a unit of E' = S'^{-1}(B_1 tensor R'). tau(c) Psi = rho in H'. Delta gives c g0 = a', g0 in 1+J_Q D, a' in D. D embeds in H, S = 1+J_Q is in the units, so Lambda = S^{-1}D embeds in H and phi(A) is in Lambda. h : Spec Lambda -> W, h o pi = f_1 on Spec E_1.
5. alpha : G' x Spec Lambda -> Spec D flat, affine. Surjective: z in Spec D with field k, s = 1+sum s_m, m nonzero in Q', so m nontorsion; s(g^-1 z) = 1 + sum g^-m z(s_m) maps under k[M'] -> k[M'/tors] to an element with constant term 1, nonzero in this domain. Take g the generic point. Same for G' x Spec E_1 -> Spec B_1 since nonunits of N_1' are nontorsion.
6. Descent. As third pass step 7: Pi embeds in H', and Pi -> E' is injective, the equalizer is closed. q : Spec D -> X_{T1}, q o alpha = g h.
7. G'-equivariance by id x alpha. q o pi = f_1 on the cover G' x Spec E_1. 
8. Gluing over the T1: R[Q] -> R[N_1] is injective and stays so after the flat base change to T1 n T1', so the q's agree on overlaps by separatedness and glue to q : A(Q)_T -> X with q o pi = f_1. Full D(M)-equivariance and the T-structure: same injectivity on D(M) x A(Q). Mono by Prop 3.29. QED.

Algebraic spaces: OPEN. The whole reduction R0-R2 works (descent and separatedness only; shrink T1 etale). Hensel replacement: for U -> X etale affine lifting v, the pair (B_i, J_i) henselized gives phi : A -> series with support in Q'. Spec Lambda^h -> Spec Lambda is surjective (going down from V(J)), so G' x Spec Lambda^h is still an fpqc cover of Spec D. So it would suffice to show c in Lambda^h. Blocker: step 2 becomes tau(c) in the henselization of (phi(A) tensor R', phi(ker v)), algebraic and no longer rational, and Delta is only tau-linear, so it does not pass through polynomial relations (diagonals of algebraic series need not be algebraic). Thick neighbourhoods A/ker(v)^n are M'-graded, which gives formal grading only. No counterexample known. Neither proved nor refuted.

# Fifth pass (2026-11-06): algebraic spaces. By hand, no independent review. Lean: AlgMag/Fact334InfConductor.lean (two elementary monomial lemmas only).

Correction to section B (second pass). The hypothesis "e + N_1 in N_inf" FAILS for the cone example N_1 = {a>=0, b>=-a}, N_inf = N^2 (`cone_no_conductor`). So section B as written did not cover its own example. For schemes this is harmless: the third and fourth passes prove the cone case without that hypothesis.

Pinching, X a separated ALGEBRAIC SPACE: PROVED for every R. Section A uses only that the equalizer is closed (X separated) and that X is an fpqc sheaf; R[x,w] is free over R[x]. No chart of X enters.

All N_i groups, X a separated algebraic space: the fixed-point density argument also uses only the closed equalizer and descent along a torsor.

Cone case, X a separated algebraic space: OPEN. What was tried:
1. phi : A -> E_1^h exists (U -> X etale affine, section over V(J_1), henselian lifting), and c = phi(u) is in R[[N_1]] with support in Q.
2. R a field, ZQ = ZN_1, Q f.g.: c is algebraic over Frac k[Q], since the fraction fields agree. Then Artin approximation over k[Q]^h (k[Q] is excellent) and uniqueness of close roots of a separable polynomial should put c in k[Q]^h. Sketch only, not written in detail.
3. R general: BLOCKED. The auxiliary coordinates of an etale presentation of c have support in N_1, not in Q, and by `cone_no_conductor` no monomial moves them into Q. So approximation over R_0[Q]^h has no unknowns in the completion, and with nilpotents in R_0 there is no minimal polynomial. A pointwise result on fields does not give X^{N_1} = X^Q, which needs all T.
4. Descent, ZQ = M, N_1 f.g.: `exists_common_shift` gives e in Q with R[N_1][1/chi^e] = R[Q][1/chi^e]. So f_1 gives q_0 on the stable open D(chi^e) of A(Q)_T. If h : Spec Lambda^h -> X existed and agreed with q_0 after inverting chi^e, the extra sheets of Lambda^h tensor_Lambda Lambda^h would be handled by density of D(chi^e). This does not need the injection into Hahn series that fails on those sheets. It is conditional on 3.
5. Rank drop, X a space: descent itself is a second obstacle: no open q_0 exists, and Lambda^h tensor Lambda^h -> series kills the non-diagonal sheets, so the third-pass step 7 does not transfer.

Printed (iii), X a scheme: M^gp is a f.g. abelian group and D(M) = D(M^gp), so the fourth-pass theorem applied to X over M^gp gives it (route of `fact334_iii_of`). It only uses X a scheme, so X^{cap_J N_l} need not be one. Not written in Lean.

Status: printed (ii)/(iii) for X a separated non-scheme algebraic space stay undecided, no counterexample, no obstruction theorem. A counterexample needs a fixed point with no equivariant etale affine neighbourhood; for X not l.f.p. existence of such neighbourhoods is linked to Rydh's Question 2.13 (section D).
