# Adversarial check of thm153-close.md and fact334-attempt.md (2026-11-08)

Source used: [AM] published, am.txt (Prop 3.31 p.147-149, Prop 3.32 p.149-150, Fact 3.34 p.150, Prop 15.1, Def 15.2, Thm 15.3 p.184-185). Hand check only, nothing compiled, no existing file edited. Standing: M cancellative.

## Citations checked against the print
- Prop 3.31 (iii): hypotheses "M cancellative, Z = M^gp, N = Y, X separated". For N in M, Y := N in M^gp has f^{-1}(Y) = N (f injective by cancellativity), so the use in Lemma E is legitimate. Correct as cited.
- Prop 3.32: (i) affine, (ii) M f.g. abelian group, (iii) M cancellative, M^gp f.g., X and X^N separated. The note correctly says (F) is NOT available from the paper in the §15 generality.
- Fact 3.34 (i)-(iii) and its colimit proof: quoted correctly.
- Thm 15.3 proof cites "Proposition 3.34" (it is printed as Fact 3.34): gap as described in §0 confirmed.
- Prop 15.1: the proof of (i) => (ii) uses Prop 3.32, i.e. it is outside the §15 hypotheses too; (ii) => (i) uses only Prop 3.29.

## thm153-close.md

Lemma A: ACCEPTED, with one correction of wording. The argument uses purity in the form 15.1 (ii) (X^N = X^L => N in L). Def 15.2 defines purity as "the equivalent properties of 15.1", but that equivalence needs Prop 3.32 in direction (i) => (ii), unavailable in the printed generality. So Lemma A holds with "pure" := 15.1 (ii); the note should say so (with "pure" := 15.1 (i) the step "Y_L = Y => E(Y) in L" is not justified as written; it is still true here by definition of E, but the purity of E(Y) in sense (i) is not proved).

Monotonicity: ACCEPTED.

Lemma B (Zorn): ACCEPTED. Chains in (N, inclusion) have lower bounds by (C); minimal N_0; (F) gives N_0 in every N. Countable refinement: ACCEPTED (strictly decreasing well-ordered chain of subsets of a countable set is countable; a countable limit ordinal has cofinality omega). The sentence "(F) is Prop 3.32" is only true under the hypotheses of 3.32; the table says this, §1 does not.

Lemma C (orbit-map criterion): ACCEPTED. Z[N] -> Z[M] split injective with free cokernel, so id x pi_N is schematically dominant; equalizer closed by separatedness. Tested on P^1, G_m weight 1, x = the tautological point of G_m: o_x factors through A(N) and A(-N) but not A(0), as claimed.

Lemma D (closure of one orbit): ACCEPTED. o_x is quasi-compact (affine source, separated target); scheme-theoretic image commutes with flat base change for qc morphisms of spaces; stability and x in X^N <=> x in Z^N check. Also Z^N = X^N x_X Z for every point of Z (same argument), so the common-attractor hypothesis passes to Z; the note should state this, it is needed for "one may assume X_T = Z".

Lemma E (M -> M^gp): ACCEPTED (see citation check).

Units chain example (k!N, Q = 0): ACCEPTED. A Laurent polynomial in u over any ring divisible by u^n - 1 with n larger than its u-spread is 0.

§3 small example: ERROR (minor, no effect on the logic). P^1 with G_m acting with one weight has FOUR attractors, not three: X (N containing e and -e), X^N (e only), X^{-N} (-e only), and the fixed locus X^0 (neither, e.g. N = 2Z or <2,3>). The criterion "depends only on which of e, -e lie in N" is right and is stable under intersections, so (*) holds there.

Table rows "atlas" and "fact334_free/strong": PARTIAL, quoted from Lean/other notes, not checkable here.

Conditional cases / wall (W1)-(W3): no false claim found; they are status statements, not proofs.

## fact334-attempt.md, fourth pass (schemes)

Checked line by line: R0 (N_i n H_1 = H_i from equal rank: x in N_i n H_1, nx in H_i => -x = (n-1)x + (-nx) in N_i), R1 (D(H_1/H_i)-torsors; ideals of D(H_1/H_i) in R[H_1][H_1/H] meet in 0 by directedness and finite supports; descent along the free map R[H] -> R[H_1]; G' = D(M/H) acts trivially on A(H)), R2 (graded pieces free of rank 1 over R1), the order (image of N_1' modulo sat H_1' is sharp because N_1 n sat H_1 = H_1; saturation of a sharp cone in a torsion-free group is sharp; Levi), step 1 (J_i in the Jacobson radical; open containing all closed points of an affine scheme is everything; supports of E_i in N_i'), w in 1+I_v (I_v = ker(v^*) tensor R' since R' is free), phi(ker v) in J_1 E_1, the identity Delta(tau(c) B) = c Delta(B) (recomputed), supp d_m in Q' n (N_1' \ H_1') = Q' \ 0, surjectivity of alpha (torsion of a sharp Q' is 0; constant term 1 survives in k[M'/tors]), injectivity of Pi -> H' and Pi -> E' (inverted elements are units of H'), descent cocycle, q o pi = f_1 on Spec B_1 via the cover G' x Spec E_1, gluing by flat base change of R[Q] -> R[N_1].

No wrong step found. Not a full verification: the finite case (fact334_finite_scheme = Prop 3.32 (ii), whose SGA3 VIII 5.1 step I did not redo), Hahn-series convolution over the twisted pieces with M' -> M'/tors finite fibres, and Lean lemmas are taken as quoted. Verdict: PLAUSIBLE, UNREFUTED, NOT ACCEPTED as proved until an independent second reading of steps 2-6.

Earlier passes: section B (second pass) is false as written for its own example (cone_no_conductor, already noted by the author in the fifth pass). Algebraic-space case: open, correctly reported.
