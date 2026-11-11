# Check of unrestrict-g1-fact319-prop331iii.md

Adversarial check, done 2026-11-07. Pure math and reading Lean only; nothing compiled, no existing file edited.

## Fact 3.19: ACCEPTED (math), Lean plan PLAUSIBLE

- I read the Lean proof `isLocallyOfFinitePresentation_repMap_spaces` (Sec11SpacesFact.lean:239-326) in full. Steps 0-3 of the note match lines 251-304. The two limit squares come from `limit_square hrlp lN`/`lM`, with `isLimit_cN` and `isLimit_cM` at l. 214 and 223.
- Correction to the note: Step 4 (the injectivity half) is NOT in the existing proof. The existing proof only proves surjectivity, because it concludes through `Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`, which needs Zx and Zy to be algebraic spaces. For a bare functor X^N, injectivity is genuinely needed. The note's argument for it is correct: apply half (I) of `limit_square ... lN` to vvS x and vvS x', which agree after f and after pullback to T, then conclude with `vv_inj`. This is new code, though it is short.
- "M a group is unused": I checked the one suspicious name. `sp_inv` (Sec11Schemes.lean:103) is the inverse of ΓSpecIso, not a group inverse. In the argument read, I found no use of negation in M. The `[AddCommGroup M]` headers (Sec11SpacesLift.lean:24, Sec11Schemes) would have to be copied with `[AddCommMonoid M]`. I accept that this is plausible, but it is not verified to typecheck.
- Size: `SM B M` gives #M < cutoff, and `contains_alg` (Prop337General.lean:49) puts Spec R[P] in the site when #P < cutoff. This is a harmless cutoff (grade 1).
- I did not re-read Tags 049J and 04AK live. The note's description of them is the standard one.
- Verdict: the printed statement holds unrestricted, as a limit-preserving transformation `attractorMap f N` for any commutative monoid M.

## Prop 3.31 (iii): ACCEPTED

- Sec3Remaining.lean:1103 is the only place `[AddMonoid.FG Z]` appears in the Prop331 section. Its only consumer is `contains_M` at l. 1152 inside `contains_of_inj`. Lines 1101-1189 were read, and the grep over the file found no other FG or countability use in the section.
- `contains_alg` with #(Z×Z) < cutoff replaces `contains_M` directly, and the existing `size_Spec_lt_of_mk_le_max` line stays. For Z = M^gp, #M^gp ≤ max(#M, ℵ0), so the cutoff on M is enough. Grade 1.
- The printed hypotheses (M cancellative, Z = M^gp, N = Y, X separated) correspond to `hf`, `hY`, and `HasDensePullback` via `hasDensePullback_of_separated`. I did not re-read those two lemmas.

## Prop 3.32 (iii): ACCEPTED (Lean plan PLAUSIBLE)

- `prop332_iii_of` (Sec3Final.lean:1090) takes `hZ`: every φ in AttractorPt (biAct (actAlong f aX)) (f(N) × f(L)) has a χ in AttractorPt (actAlong f aX) (f(N) ⊓ f(L)) with the same toPoint. There is no atlas.
- `prop332_space_final` (SDR4Final.lean:33) states that `iterOfInf` is bijective for any algebraic space, under `[AddCommGroup M] [AddGroup.FG M]`, with no separatedness.
- `iterOfInf` is defined at Sec3Intersections.lean:455 as `(iterEquivBi T).symm (χ.toBi ...)`. So surjectivity gives χ.toBi _ = φ (iterEquivBi is injective, and proofs are irrelevant), and then toPoint follows. This yields `hZ`.
- The atlas `hat` and the hypothesis `hb` of `prop332_iii_atlas` (l. 1228) therefore disappear. FG of Z = M^gp is printed, and the AddGroup.FG instance comes from `AddGroup.fg_iff_addMonoid_fg`, as at Sec3Final.lean:958.
- I did not check whether importing SDR4Final together with Sec3Final in a new file creates import cycles or name clashes.

## Summary
- Fact 3.19: ACCEPTED. The unrestricted proof is correct, but the injectivity half is new code and not "verbatim" from the existing proof.
- Prop 3.31 (iii): ACCEPTED. FG Z only serves the site cutoff.
- Prop 3.32 (iii): ACCEPTED. `prop332_iii_of` combined with `prop332_space_final` removes the atlas and `hb`.
