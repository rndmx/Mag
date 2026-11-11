# Adversarial check of atlas-definition.md (2026-11-07)

Source: published AM (Semigroup Forum 113). No lake/lean run.

## Verdicts

1. Option (b) as recommendation (pieces = stable affine schemes, "finite atlas" = U affine). ACCEPTED.
   Natural (standard presentation notion; Remark A.7 already says "disjoint sum of affine schemes").

2. Existence of atlases for all S (Thm 6.8 / A.2 under (b)). ACCEPTED.
   Appendix A reduces to S affine and outputs Spec(A) pieces; these are affine schemes whatever S is.
   Doubled-origin plane: U = V_1 = A^2 itself is a (b)-atlas. Non-quasi-separated S: the argument is
   local on affine opens of S, no qs used. X qc => finitely many pieces => U one affine scheme. OK.

3. Transfer lemma (U/S)^N = (U/Z)^N for U affine. Statement ACCEPTED; proof sketch REJECTED as written.
   First bad step: "choose W containing phi(1_t); phi^{-1}(W) meets the zero section". Nothing forces
   this (W must be chosen around phi(0_t), not phi(1_t)). Second gap: "shrinking T', phi(A(N)_{T'}) in W"
   needs an argument (A(N)_T -> T is not proper).
   Clean replacement: phi factors through U, and U -> S is invariant; U -> Spec O(U)_0 is a good quotient
   by a diagonalizable group, hence categorical among ALL schemes, so U -> S factors through
   Spec O(U)_0. The composite A(N)_T -> U -> Spec O(U)_0 is given by O(U)_0 -> (O(T)[N])_0 = O(T),
   so it factors through T. No hypothesis on S or N. Use this proof in the corrigendum.

4. Consequences for Thm 3.20, Cor 3.22, Lemma 3.26, Prop 5.1, Thm 8.3, Prop 12.2(ii), Prop 15.5. ACCEPTED
   (given item 3 with the replacement proof). U^N -> U^{N^x} affine as a map of affine schemes: fine.

5. (a)-atlas refines to (b)-atlas; (a) = (b) over separated S. ACCEPTED (Stacks 01SG; open immersions
   strongly FPR, FPR composes).

6. Prop 8.5, p.166, Thm 15.4 need S quasi-compact, not separated. ACCEPTED, with a remark:
   counterexample (disjoint union of Spec k, weights (1,n)) is valid since X -> S qc forces X non-qc.
   Not too rigid: "X quasi-compact" is an equivalent-strength, more natural alternative (image of X is
   in a qc open S' of S; replace S by S'). Suggest offering that wording. Prop 8.5 gluing of N_c over
   the cover uses monotonicity X^N subset X^{N_c'} subset X^{N_c} = X^N: fine.

7. "No statement needs S separated for an independent reason." ACCEPTED as far as the table goes;
   not re-verified line by line for Sections 9-14 (synthesis itself flags p.166 as "to be checked").

8. Conj 6.9 / Rem 15.8 wording. ACCEPTED.

9. Corrigendum wording (Def 6.1(iv), Thm 6.8, Fact 7.3, Prop 8.5, Thm 15.4). ACCEPTED, except: cite the
   transfer lemma with the good-quotient proof of item 3, and consider "X quasi-compact" in 8.5/15.4.

10. Lean plan (IsAffine fields, drop [S.IsSeparated] from thm68_*, rename IsFiniteAtlas, formalize
    transfer lemma). PLAUSIBLE, UNVERIFIED (no build run; consumers of IsAffineHom must be re-proved).
