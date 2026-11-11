# Chart lemma for quasi-separated X: paper proof of the missing steps (2026-11-06)

Own argument, no independent check. Closes on paper the three steps left open by the ChartQSStab round. No input needs X separated. X noetherian, locally of finite type, over Z after the usual reduction.

## Step 1. Gluing along a principal ideal (replaces eq_on_kernelPair)
C noetherian, g in C, C1 the g-adic completion, f : D(g) -> X, h : Spec C1 -> X agreeing on D(g)C1. Claim: h has equal pullbacks p, q to R = C1 tensor_C C1, so (0APL) f, h glue to Spec C -> X.
- p = q on D(g)R by hypothesis; R/g^k = C/g^k.
- V -> X affine etale, B affine etale over C1 with a lift Spec B -> V (cover of Spec C1). In B/g tensor_{C/g} B/g the diagonal is clopen, cut out by an idempotent. Take a lift u of it in B tensor_C B, P = D(u). P is etale over R, so Gamma(P) is flat over C; the images of such P contain V(g)R. On P/g^k the two projections coincide, so s, t : P -> V agree on all V(g^k).
- `eq_of_lift_etale` (Lean, proved): v s = v t on P. Proof: F = V x_X V, the diagonal is open since F -> V is etale. Over D(g), V(I) is the preimage of the diagonal, I the ideal of the equalizer of s, t, so V(I) is clopen in D(g): e in Gamma(P)_g with eI = 0, 1 - e in I. I lies in all g^k Gamma(P), so 1 - e = g w. Then (1 - g w) I is g-power torsion and lies in all g^k, so it is 0 by Lemma 4.5. Hence s = t on D(1 - g w), and D(1 - g w), D(g) cover P.
- So p = q on the images of the P and on D(g)R, which cover Spec R.

## Step 2. Several generators
a = (a1..ar), C noetherian, maps on D(a) and on Spec of the a-adic completion C^, compatible. Let C1 be the a1-adic completion: noetherian, and its (a2..ar)-adic completion is C^. Induction on r gives Spec C1 -> X from the map on D(a2..ar) of C1 and C^. Compatibility with D(a1) is checked on the fpqc cover D(a1) of C1 by D(a1, a2..ar) and D(a1) of C^. Step 1 for (C, a1) finishes.

## Step 3. Uniqueness (replaces eq_of_agree_of_iInf; its old form is false for qs X)
C noetherian with a in the Jacobson radical; x, y in X(C) agreeing on all V(a^k). Same P as Step 1 over C (B etale over C). I lies in all a^k Gamma(P), Gamma(P) noetherian, so by Krull I vanishes near V(a); so x = y on an open containing V(a), which is everything.

## Step 4. Noetherian algebraization (replaces 0GHK, removes Bhatt 1.1)
Claim: C noetherian a-adically complete, compatible phi_k : Spec C/a^k -> X. Then a unique phi : Spec C -> X. Noetherian induction on the closed subset of |X|, all thickenings at once.
- U a nonempty affine open of X (X qs), Z its complement, J its ideal. b in C the ideal algebraizing the phi_k^* J (Lemma 3.4, non-graded). Deligne (Lemma 4.3, non-graded) gives tau : D(b) -> U.
- C/b^l is a-complete and maps to the thickening Z^(l), smaller: psi_l : Spec C/b^l -> X, compatible by uniqueness.
- Claim S(X, Z): D noetherian b-complete, psi_l : Spec D/b^l -> X through Z^(l), tau : D(b) -> U compatible. Then Spec D -> X. By Step 2 it gives phi from C^b, tau.
- Proof of S, noetherian induction on Z. Stacks 07ST filtration (08GM squares): W -> X affine etale, isomorphism over a nonempty closed Z' in Z, so over all thickenings of Z'. c in D the ideal of Z'. Maps D/c^m -> thickening of Z' lie in W, W affine, so Spec D^c -> W -> X by a limit of rings. For h in c, S(X \ Z', Z \ Z') on the b-completion of D_h, then Step 2 with tau over (D_h, b), gives D_h -> X; these glue to D(c) -> X by Step 3. Step 2 over (D, c) gives Spec D -> X. Compatibility on D^c[1/h]: on its b-completion both algebraize the same system, Step 3; on D(b), Lemma 4.3 formula.

## Step 5. Lemma 4.2 for qs X
Reduce to a dense G-stable separated open, then apply ChartStratum.affineStratum. X irreducible f.t. over Z: Delta in X x X, F = closure(closure(Delta) \ Delta) has dimension < dim X, so X \ closure(pr1 F) is dense, stable and separated. Sketch only, for spaces.

## Other items
- Equivariance (Lemma 4.5 with R = O(G) tensor C): R noetherian, use the Step 3 chart argument with the torsion of Step 1, unchanged.
- Lemma 1.1: its proof is local and uses no separatedness; only the Lean route (exists_pull, O x_X U affine) does. To be redone with O x_X U quasi-affine.
- Stabilizer: ChartQSStab.lean. The stabilizer of a non-closed point need not be closed (X = (G_m x A^1)/H, H = {1} at s = 0, {+-1} for s != 0, is nowhere separated near s = 0): do not assume generic closedness before Step 5.
- For Thm 6.8(ii) only an equivariant etale affine chart through x is needed: G_u = G_x can be dropped, Thm A.1 gives Z-FPR.

## Lean state (second pass, 2026-11-06)
Compiled, no sorry, standard axioms: ChartQSCore, ChartQSAgree, ChartQSLift, ChartQSChart, ChartQSEq, ChartQSFlatQuot, ChartQSEqGens, ChartQSUnique, ChartQSMain.
- Step 1 is done in a simpler form than above: no kernel pair, no idempotent lift. `exists_chart_agree` takes any p, q in X(W) agreeing on all V(J^k), and gives an etale chart with s = t on all V(J^k).
- Step 2, for equalities only: no completion needed. Induction on generators through C/(g^k) (`eq_of_agree_list`, `flat_quot`). `ChartQS.eq_of_agree_basicOpen_of_agree_thickening` is the old statement for any algebraic space.
- Step 3: `eq_of_agree_pow`, for a in the Jacobson radical.
- ChartQSMain: eq_on_kernelPair, existsUnique_pushout, equivariant_of_agree, exists_glue, restrict_eq_of_strata, thm41_exists_of_strata, all with hX in place of hsep. thm41_exists_of_strata still takes hB (NoetherianAlgebraization).

## Correction: graded uniqueness
`ChartMain.thm41_unique` (any two points, graded complete pair m) is FALSE for non-separated X, and Step 3 does not cover it, since a graded complete pair m need not lie in the Jacobson radical. Example: T = A^1, m = (t), X = A^1 with doubled point at s = 1, phi, psi the two sections: they agree on all V(t^k), and differ. The qs replacement must assume phi, psi equivariant: the agreement locus is then an open stable set containing V(m), and a stable closed set missing V(m) is empty by the complete pair. To be written; ChartEffectiveFinal.chi_compat_aux uses it.

## Next
1. Equivariant thm41_unique. 2. Step 4 (NoetherianAlgebraization for qs X); Stacks 0AQH in the tree is local complete only, 0GHK separated only. 3. Step 5 (Lemma 4.2). 4. Re-derive the hsep chain: 38 Chart files mention hsep/IsSeparatedOver, some only by passing it on.

## Third pass (2026-11-06): equivariant uniqueness and the induction
Compiled, no sorry, standard axioms: ChartQSEquivUnique, ChartQSEffective.
- `thm41_unique_equivariant`: two equivariant points agreeing on all V(m^n) are equal, X any algebraic space. The sentence above "a stable closed set missing V(m) is empty" is too quick when D(M) is not reduced: the ideal of a stable closed set need not be homogeneous (mu_p on A^1, the point t = 1). The proof used: K the ideal of the complement of the agreement locus, 1 = r + f with r in m, f in K. The coaction of f is nilpotent modulo K (it lies in every prime over K, since the projection of D(c f) lies in the agreement locus). So a power f^N = 1 - r' has c(f^N) with coefficients in K; the degree 0 coefficient is 1 - s, s in m_0, a unit by completeness.
- `ChartQS.OpenStratumMap`: as `ChartMain.OpenStratumMap`, the maps chi_k assumed equivariant. `ChartQS.effective_of_stratum`, `ChartQS.effective_of_noetherian` use it, and need only NoetherianAlgebraization of the strata, plus h42 and h43.

## Next obstruction found: Lemma 4.3 in Lean (not mathematical)
`ChartDeligneCore.ChartOf` asks Z x_X V to be AFFINE with its universal property (`exists_chartOf` uses exists_eqLocus). For X only qs, Z x_X V is quasi-affine, so ChartOf does not exist in general. ChartDeligneCore uses it at lines 401, 408, 511, 632 and the whole Gam/descend route (900 lines) depends on it: to redo with a finite affine cover of Z x_X V, or Gam defined on all affine W over V. `chi_univ` (ChartDeligneCompat:107) must take chi equivariant as a hypothesis, which `ChartQS.OpenStratumMap` now provides, and not use eq_of_agree_of_iInf.

## Next
1. Deligne (ChartDeligneCore, Compat, Theta, Inst) with quasi-affine Z x_X V, giving ChartQS.StrataOver. 2. Step 4 (NoetherianAlgebraization). 3. Step 5 (Lemma 4.2). 4. Lemma 1.1, tower (`exists_affine_thickening`, `isAffine_relation`, ChartTowerChart:276, 367), both with the same quasi-affine issue.
