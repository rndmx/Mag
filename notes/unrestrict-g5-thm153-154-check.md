# Check of unrestrict-g5-thm153-154.md (2026-11-07)

Pure mathematics plus reading Lean sources; nothing compiled, no existing file edited.

## Thm 15.3: ACCEPTED

- Lemma A (Thm 15.3 equivalent to Fact 3.34 for nonempty common-attractor families) re-done by hand. Both directions use only monotonicity and Def 15.2. Correct. Monotonicity is `attractorImage_monotone` (Sec15General.lean:48, `[AddCommMonoid M]`, no hypothesis). Confirmed.
- Affine case for any abelian monoid and any S: `attractorOrder_affine` (Sec15General.lean:83) sits in section GB with `[AddCommMonoid M]` and `[IsAffineHom X.hom]` on `GB.overO S`. `pureEquivRange` (Sec15PureMagnets.lean:116) takes `AttractorOrder Y`. The one-line plan `pureEquivRange (attractorOrder_affine act)` typechecks on reading. Confirmed.
- `thm153_general` exists at FinalNonQCLocal.lean:121 with hypotheses hM, ... Confirmed. The claim that the fidelity row is out of date is plausible. I did not re-read the whole signature.
- The paper gap is confirmed: the printed proof applies Fact 3.34 to the possibly infinite family {N | X^N = Y}, with M an arbitrary monoid. Fact 3.34 (ii) and (iii) need f.g. hypotheses. The wording of the wall is accurate. The scheme-case hand proof is cited from fact334-attempt.md. Neither the prover nor I re-verified it.
- Reservation (minor): the claim "section-artifact" for the fppf `attractorOrder_of_isAffineHom` (section Affine, lines 132-251) is not verified. A grep shows no `contains_M` or `exists_gamma` in that section, but the lemmas it calls from other files were not checked. It stays "expected", as the prover says.

## Thm 15.4 (i): PARTIAL

- S quasi-compact NEEDED: ACCEPTED. I re-checked the counterexample (S = disjoint union of Spec k over n ≥ 1, X = disjoint union of lines A¹, deg t_n = n, M = Z):
  - X → S is affine, qc and l.f.p., so finitely presented.
  - Over the n-th point, X^N is the whole line iff n ∈ N, else the origin. Hence X^N = X^L iff N ∩ Z_{>0} = L ∩ Z_{>0}.
  - kN is pure, because X^{kN} = X^L forces kZ_{>0} ⊂ L, and 0 ∈ L. The X^{kN} are pairwise distinct, since line n lies in X^{kN} iff k | n.
  - So Π(a) is infinite, and the printed step "finite subset E ⊂ M" fails. This is a paper error. The fix "S (or X) quasi-compact" is correct.
- M f.g. UNRESTRICTED: REJECTED as stated (first bad step: §2.4, "None uses ... a finite generating set of M ... deleting them compiles unchanged"). The mathematics is fine: the printed proof works for any abelian monoid, and `finite_pureMagnets_affine` is already `[AddCommMonoid M]`. But the Lean chain uses `[AddMonoid.FG M]` substantively:
  - `exists_finite_degrees_site` (Sec15General.lean:665) calls `exists_gamma` (Sec5Etale.lean:775, section Gamma, `[AddCommGroup M] [AddMonoid.FG M]`).
  - Its statement mentions `contains_M hC` (Sec5Etale.lean:759), proved by `AddMonoidAlgebra.finiteType_of_fg R' M` + `contains_ft`, i.e. it needs FG to put Spec R'[M] inside the site.
  - Section Finite of Sec15General.lean also uses `contains_M` directly (lines 461-546).
  - So deleting the instances does not compile. Removing FG needs a replacement for `contains_M`: a size lemma "#R'[M] ≤ max(#R', #M, ℵ₀) < cutoff", under a hypothesis like hM of `thm153_general`. That is a size cutoff (grade 1 harmless if proved), not a section artifact.
  - `[AddCommGroup M]` is only needed by the typing of `jr`/`eM`/`mapR`. These look generalizable to `AddCommMonoid`, but this is unverified.
- Verdict: S qc needed (paper error); M f.g. removable on paper, Lean plan must be corrected as above.

## Thm 15.4 (ii): PARTIAL

- S quasi-compact NEEDED: ACCEPTED. id_X is an S-affine strongly-FPR atlas in the counterexample, since the FPR maps are identities and A is a singleton. Same infinite Π(a).
- M non-f.g. WALL: ACCEPTED as a wall. The section hypotheses quoted (Prop 5.1 §5 "finitely generated", Cor 11.6 §11 "finitely generated") match what is recorded elsewhere in the repo. I did not re-read pp. 154 and 171 page images. The paper-level remark "statement wider than proof" stands. Step 3 of the reduction (fpqc descent via Tag 0APL) is only a sketch, and the prover says so. Step 4 is correctly identified as open. The Lean FG dependence is real (see `contains_M` above), consistent with the wall.
- Site coproducts harmless: PLAUSIBLE, not verified. `exists_cofan_of_size` exists (FinalNonQCAtlas.lean:49, taking a cardinal μ). I did not read its hypotheses in full. The bound "finite max of sizes below cutoff is below cutoff" is standard, provided the cutoff is an infinite cardinal larger than ℵ₀ (`B.aleph0_lt_cutoff` asserted, not checked).

## Summary
- Thm 15.3: ACCEPTED (WALL located correctly; affine case unrestricted for any monoid).
- Thm 15.4 (i): PARTIAL. S qc counterexample accepted. "M f.g. is a section artifact" REJECTED: `exists_gamma`/`contains_M` use `AddMonoid.FG` for site membership of Spec R'[M]. It needs a size lemma, not deletion.
- Thm 15.4 (ii): PARTIAL. S qc counterexample accepted; non-f.g. wall accepted; coproduct discharge plausible, unverified.
