# Check of thm154-ii-nonfg.md (2026-11-07)

Source: published AM (am.txt of the Semigroup Forum proof), Lean sources read, nothing compiled.

## 0. Print hypotheses on M: ACCEPTED
- §15 standing (p. 184): "Let M be an abelian monoid. Let X be a separated algebraic space over S endowed with an action a of A(M)_S." No finiteness.
- Thm 15.4: "Assume moreover that X is finitely presented over S ... (ii) M is a group and there exists an S-affine strongly-FPR atlas for X". No finiteness.
- So "M not f.g." is not an extension beyond the print: it IS the printed statement. Lean `[AddMonoid.FG M]` (Sec15Final.lean:48, section `Strong`; and :262 section `Printed`) is a Lean restriction. The printed proof of (ii) is incomplete for M not f.g. (it borrows f.g. tools).
- Def 6.1 (ii),(iii),(iv) and Rem 6.2 read: Z-FPR = U^{D(M/Z)} -> U x_X X^{D(M/Z)} iso; strongly-FPR = all subgroups Z. Matches the note's use.

## Lean names (read, not compiled)
- `thm154_ii_lfp` Sec15Final.lean:531: `[CompactSpace S] [IsAffineHom U.hom.hom]`, `IsStronglyFPRAtlas aU aX f`, `IsAlgebraicSpace`, `IsSeparatedOver X`, `Space.IsLocallyOfFinitePresentation`, concludes `(pureMagnets (attractorImage aX)).Finite ∧ (Set.range (attractorImage aX)).Finite`. Section variables `[AddCommGroup M] [AddMonoid.FG M]`. Correct as quoted.
- `exists_finite_degrees_site` Sec15General.lean:656 exists (`[CompactSpace S] [LocallyOfFiniteType U.hom.hom]`).
- `prop51_i_printed` PrintedProp51.lean:175 in section `Main` with `[AddGroup.FG M]` (line 99). Correct.

## Steps
1. Finite degrees, M' = <E>: ACCEPTED (S qc, U affine l.f.p. over S; only use of qc).
2. U^N = U^{N∩M'} by Thm 3.20: ACCEPTED.
3. Prop 5.1 (i) at the face Q = N^x, N f.g., M arbitrary: ACCEPTED. Checked: N/Q embeds in M/Q, is fine and sharp (n̄ unit => n in Q), so a local hom to N exists (quoted standard fact); I^k filtration separated and degreewise stationary; lifts f_k by formal étaleness; equivariance by uniqueness of lifts; algebraization degreewise; equalizer V(J) with J ⊂ ∩I^k = 0. Orbit map D(M)_T -> D(Q)_T is faithfully flat since Z[M] is free over Z[Q] (Q a subgroup). M is indeed never used.
4. X^N_M = X^{N∩M'}_M: ACCEPTED. (i) limit reduction fine (A(N)_T affine cofiltered limit, equivariance is an equality in a colimit, hence at a finite stage). (ii) easy direction. (iii) Z-FPR with Z = N^x a subgroup, then Thm 3.20 on affine U. (iv) sheaf + mono gives descent of membership. Purity via Prop 15.1 (ii) gives every pure magnet in M'.
5. Descent of the action to D(M'): ACCEPTED. R closed in affine U x_S U, ideal M-homogeneous with support in M', so M'-homogeneous; coequalizer in a topos is preserved by D(M') x -. FPR transfer via faithfully flat D(M/Z') -> D(M'/Z'). 5(d) fine.
6. Π(a) ⊂ Π(a') and f.g. case: ACCEPTED. Purity transfer checked against Def 15.2/Prop 15.1 (ii) wording.

## Minor (not errors in the math)
- Citations not re-verified against the Stacks Project: Tag 04AK is the scheme version; for algebraic spaces the l.f.p. <=> limit preserving statement has its own tag (in Lean: `isLimitPreserving_of_lfp`). Tag 02L4 as cited for "closed immersion that becomes iso after fpqc base change is iso": recheck the tag; the fact itself is standard (faithfully flat => ideal sheaf zero).
- Step 3(b): the étale lift u_0 lives on T', so the whole Step 3 should be run over T' (implicit in the note; harmless).
- Step 5(b) epi argument for equivariance of the projections is superfluous (graded maps), harmless.

## Verdict
Claim "print puts no f.g. on M in Thm 15.4 (ii)": ACCEPTED.
Proof of Thm 15.4 (ii) for all abelian groups M (S qc, X separated, l.f.p.): ACCEPTED (math, by hand); Lean not done.
By-products Prop 15.5, Rem 15.6 for arbitrary M: ACCEPTED (follow from Steps 4, 5(d)).
Lean plan §9: PARTIAL (plan only; item 3 depends on whether the Lean proof of `prop51_i_printed` uses FG, unread).
