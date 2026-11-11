# Adversarial check of unrestrict-g2-prop81-prop85.md

Source: [AM] Semigroup Forum print via am.txt. Nothing compiled, no existing file edited.

## Checked against sources
- Print: Prop 3.35 (am.txt 1382, "Assume M is a finitely generated group"), Prop 8.1 (1834), Prop 8.5 (1927-1930), Prop 3.29 (1151, needs X separated): quoted correctly.
- Lean names exist at the stated places: `Prop81Statement` Sec6FPR:357, `Prop81StatementFG` :368, `prop81FG` Sec8Representability:1274, `attractorFixedEquivOfCover` :211, `extSieve_mem` :388, `exists_closed_fixed` :956, `isSheaf_fixedPoints` :1145, `presheaf_fixed_ι` :1236, `isLimitPreserving_of_lfp` Sec8Limits:973, `prop85` :1382, `ofLE_injective` Sec5Etale:1747, `isSheaf_attractor` Foundations:187, `prop85_free` FinalAtlasFree:30, `prop85_atlasFree` FinalCorAtlas:62, `thm68_qc_spaces` ChartFinalSpaces:44 (`[S.IsSeparated]`). I did not check the bodies of these lemmas for FG-freeness. I also did not re-read the Stacks tags online. 0APL (Gabber, fpqc sheaf property for algebraic spaces), 022B and 04AK match what I know of those tags, but I accept them on the prover's reading.

## Prop 8.1: ACCEPTED (paper proof). The fppf route of §1.5 has a gap that can be fixed.
- §1.3 (a)-(e), the fpqc proof: I verified it. Z[M] is free over Z[Z] on coset representatives, so π is affine and faithfully flat, which makes it an fpqc covering. The kernel D(M/Z) and the descent of ψ and of equivariance via 0APL are both sound. §1.4 is sound too: the step "fixed iff A_m is killed for m not in Z" holds because x(a)·t^{m̄} = x(a) in O[M/Z] forces x(a) = 0 when m̄ ≠ 0.
- §1.5 (e'), the first bad step: "ψ_F : D(M_F)_T → X_T, g ↦ g·x" is not defined. D(M_F) is a quotient of D(M), dual to the inclusion M_F ⊂ M. It is not a subgroup, so D(M_F) does not act on x. Lifting g along D(M) → D(M_F) is again only fpqc-local. The ambiguity lies in D(M/M_F) ⊂ D(M/Z), which does fix x, but that does not remove the need for the lift.
  Repair, which uses only the tools the prover names: take T affine and ψ : D(M)_T → X_T, g ↦ g·x. Since X is l.f.p., the existence part of limit preservation (04AK, `isLimitPreserving_of_lfp`) factors ψ through some D(M_F)_T. Apply the injectivity part to the two pullbacks on D(M_F) ×_{D(Z)} D(M_F) = D(M_F) × D(F): they agree after pulling back to D(M) × D(M/Z), so they agree on D(M_{F'}) × D(F') for some larger F'. Then use fppf descent along π_{F'}. Equivariance is handled the same way.
  §1.5 (d') is correct as written.
- Lean plan item 2 (`fixedEquiv_of_lfp`) must follow the repaired (e'). The size hypothesis (H2) and `hM`/`hQ` are size cutoffs, grade 1. I agree.

## Prop 8.5: ACCEPTED
- (A1): the atlas comes from Thm 6.8 over a separated base. Correct, but the Lean route still rests on the stubs behind `thm68_qc_spaces`, as the note says.
- (A2): removing "S separated" works. Steps (1)-(4) check out. Each affine S_k is separated. In (3), bijectivity follows because the composite of the two maps is bijective and the second map is injective by Prop 3.29, which needs only X separated. In (4), gluing works by uniqueness on T_k ∩ T_l, which lies over S_k, together with the Zariski sheaf property of X^{N_c}. Nothing uses S separated.
- Counterexample §2.2 to dropping "S quasi-compact": verified. N^× = 0, and any element of N_c with first coordinate 1 must be a generator. The sign of the weight depends on the convention of Thm 3.20; choose the grading so that the coordinate lies in N. The argument is unaffected.
- Corrigendum remark: "Prop 8.5 takes the same hypotheses [S separated]" overshoots. I agree.
