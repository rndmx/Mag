Both statements are proved and compile with `lean -o`, with no `sorry`. Neither file has been through `lake build`.

**Source:** the printed statements in the extracted text of the Semigroup Forum version (`am.txt`). The Prop 3.37 quotes were also checked against the page image in `corrections-verified.md`.

## Thm 8.3(v), relative form
- **Statement:** under the Thm 8.3 hypotheses, X^N is representable by `r`, and if X → S is quasi-compact, so is X^N → S. S is arbitrary, so the loss of non-qc S is fixed.
- **Lean:**
  - `AlgMag.thm83_v`, `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Thm83v.lean:38`
  - `AlgMag.thm83_v_of_repr`, same file, line 28: the same conclusion for any `Thm83Repr`, with no separatedness needed
- **Axioms:** `#print axioms AlgMag.thm83_v` gives [propext, Classical.choice, Quot.sound].
- **Added assumptions:** none beyond the agreed correction of Thm 8.3: M a f.g. group, X separated, and N f.g. or X limit preserving. This form also carries the `N^×`-FPR atlas printed in Thm 8.3.
- **Form of the conclusion:** it is stated on `terminal.from`, the same form as `thm83_iv` and `thm83_vi`.

## Prop 3.37, corrected
- **Statement:**
  - M is an arbitrary commutative monoid, as printed.
  - X is a separated algebraic space, locally of finite presentation over S.
  - `Ni : ι →o AddSubmonoid M` is a directed, nonempty family with N_i ≤ N and union N. The N_i need not be f.g.
  - T is quasi-compact.
  - Conclusion: X^N(T) = colim X^{N_i}(T), as a real colimit in the category of types: `IsColimit (prop337Cocone Ni hle T)`.
- **Lean, all in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Prop337General.lean`:**
  - `AlgMag.prop337_colimit`, line 538: the colimit statement
  - `AlgMag.prop337_exists`, line 452: surjectivity for qc T
  - `AlgMag.P337.exists_ofLE_affine`, line 377: T affine, by the printed proof
  - `AlgMag.P337.ofLE_inj`, line 414: injectivity for any T, for arbitrary M
  - `prop337Diagram`, line 522, and `prop337Cocone`, line 530
- **Axioms:** `#print axioms` on `prop337_exists` and `prop337_colimit` gives [propext, Classical.choice, Quot.sound].
- **Proof:** it follows the print: R[N] = colim R[N_i], Tag 049J, equivariance by density. Then, as in the verified correction, take a finite affine cover, a common index, and glue using the injectivity.
- **The older `prop337`:** I left it in place. The new statement replaces its M f.g. and "some f.g. P" restrictions.

**Remaining added assumptions for Prop 3.37:**
- `hM : #M < B.cutoff` is the site's size cutoff, with no counterpart in the paper. It puts A(N)_T and A(M)_T × A(N)_T in the site, and they are needed there because the printed density step works on the universal point. It is the same condition as `SM B M`, and for M f.g. it is automatic.
- `ι : Type u` loses no generality, since the N_i are a family in `AddSubmonoid M`.
- `Nonempty ι` is part of "directed"; the empty colimit would be false for N = 0.
- T quasi-compact is the verified correction.

## Suspected paper errors
- **Prop 3.37, no new error:** "Let T → S be a scheme" and "For any scheme T" are the errors already recorded in `corrections-verified.md` (votes 2, 3 and 5). The counterexample there remains a hand check and is not in Lean. A formal counterexample was not part of this task.
- **Thm 8.3(v), none:** the printed relative statement holds under the agreed hypotheses.

## Blockers
None.

## Files and build
- **Repo changes:** the two new files above, plus two imports appended to `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag.lean`. I did not edit `STATUS.md` or `fidelity-grades.md`, so the Thm 8.3(v) and Prop 3.37 rows there are now stale.
- **Duplicated code:** `Prop337General.lean` restates some Sec5Etale lemmas in namespace `AlgMag.P337`, such as `jr`, `eM`, `faceCoact` and `isKey_descend`. The originals require `AddCommGroup M`, or M f.g. through `contains_any`, and I could not edit existing files.
- **Oleans:** in `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\p337v\AlgMag`.

---

Cor 10.3 for spaces is stated and proved as the printed square, with `X'` affine. Cor 13.3 no longer assumes attractors are schemes. Prop 10.1 did not reach general G. All new files compile, using `lean -o` into `scratchpad\c103\out`, with no `lake build`; imports are appended to `AlgMag.lean`. Proofs of the `sorryAx` results below are conditional until a full-Stacks build. Nothing was recompiled against real Stacks, and I did not walk the constants myself.

**Cor 10.3 (spaces)**
- **Name:** `AlgMag.SpacesLift.cor103_square`, `AlgMag\FinalCor103Square.lean:64`
- **Statement:** `X' = Spec A₁` and `i : X = Spec A → X'` is a first order thickening. `aX', aX, aY, aZ` are actions on functors, `Y` and `Z` are algebraic spaces, and `i, a, b, f` are `EquivariantHom`. `f` is formally smooth and `a ≫ f = i ≫ b`. Then there is an `l : EquivariantHom aX' aY` with `i ≫ l = a` and `l ≫ f = b`.
- **Axioms:** `[propext, sorryAx, Classical.choice, Quot.sound]`. Per `notes\REQUIRES_FULL_STACKS.md:14`, the `sorryAx` comes only from the Stacks stubs for 07SY and 04AM.
- **Remaining added assumptions:** `X'` affine (agreed) and the size cutoff `SM B M`.
- **Printed hypotheses unused:** M f.g., X' → S qcqs and Y → Z locally of finite type.
- **Departure from the printed proof:** the filler comes from integrating `g⁻¹αg`, not from Prop 10.1 + Prop 9.13. This is the existing route, recorded in `REMARKS.md:28`.
- **Existing file:** `AlgMag\FinalMiscCor103.lean` (`cor103_spaces`) is the ring-coaction form and is not imported. I left it alone. The new theorem recovers the coaction from the action at the universal point.

**Cor 13.3**

Case 1, X affine over S, with no representability hypothesis:
- **Name:** `AlgMag.Dil.cor13_3_affine`, `AlgMag\FinalCor133.lean:40`
- **Statement:** `(Bl_Y^D X)^N → S` is smooth and `b^N` is the dilatation of `X^N` with center `Y^N`. The attractors come from Thm 3.20.
- **Axioms:** `[propext, Classical.choice, Quot.sound]`
- **Added assumption:** `X → S` affine only.

Case 2, general X, attractors as spaces rather than schemes:
- **Name:** `AlgMag.DilSp.cor13_3_spaces`, `AlgMag\FinalCor133Spaces.lean:143`
- **Statement:** it follows the printed proof. `Bl` is smooth by MRR 2.16, `(Bl)^N` is smooth by Cor 11.2 for spaces, and then Prop 13.1 applies. The conclusion is `(Bl)^N → S` smooth, `b^N` a dilatation, and the canonical iso with any model `B'`.
- **Axioms:** `[propext, sorryAx, Classical.choice, Quot.sound]`, through Cor 11.2 for spaces (same stubs).
- **Remaining added assumptions:**
  - `(Bl_Y^D X)^N` is an algebraic space, and `X^N` is a sheaf representing the attractor.
  - `Y^N` is any presheaf representing the attractor.
  - Site conditions `SM B M`, `hM`, `hN`; a model `B'` is taken as input, as in Prop 13.1.
- **Why the assumption stays:** the print writes `Bl_{Y^N}^{D^N} X^N` and needs `(Bl)^N` flat, so it reads these as spaces. Printed step: "Now since BlYDNN X N and (BlYD X )N are flat over S, they belong to SpacesSS reg. So by Yoneda". Yoneda needs an object, and §13 gives no representability. Without Thm 8.3 hypotheses I found no route to one, and no counterexample either.
- **Bridge lemma:** `isSpDil_of_isDilatation` (`FinalCor133Spaces.lean:36`) is clean.

**Not done (Cor 13.3)**
- The Thm 8.3 corollary with no representability hypothesis (`thm83_free` applied to X, Y, Bl) was drafted but never compiled. No scratchpad overlay has both `FinalCorAtlas` and `SecLeftover1615Spaces`, so I removed it.

**Prop 10.1: not feasible at printed generality**
- **Added:** `AlgMag.Sec10Printed.prop101_of_H1`, `AlgMag\FinalProp101H1.lean:43`. Axioms `[propext, Classical.choice, Quot.sound]`.
- **Limit of that theorem:** the H¹ hypothesis is only formal, because `H1_vanish` already proves it for D(M). It still covers D(M), schemes and `Spec` rings only. This does not fix the "H¹ absent" grade in substance.
- **General G, formal part:** this already exists as `LiftTorsor.exists_invariant`, with the torsor as input.
- **Blocker for concrete G flat with spaces Y, Z:** a concrete model of `p_*Hom(a^*Ω, C)` on `T` with `X'×_S T` non-affine, and the G-action on `C ⊗ O_T`.
  - Nothing in the repo does this; the existing model is tested on `D(P)` only.
  - Even restricting to G affine over S looks like a separate project of the order of 2000 lines. That is my estimate, not attempted.

**Suspected paper errors:** none new beyond the agreed ones. The proof of Cor 13.3 inherits the implicit representability quoted above.

**Files:**
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\FinalCor103Square.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\FinalCor133.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\FinalCor133Spaces.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\FinalProp101H1.lean`

---

**Prop 15.1 and Prop 16.15(ii): results (2026-11-06)**

Everything below compiled with `lean -o`, with no sorry in my files and no lake build. Axioms are `[propext, Classical.choice, Quot.sound]` unless a line says otherwise. Source was the published version, read through `am.txt`. I appended my three imports to `AlgMag.lean`.

## Prop 15.1

All forms are in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\PrintedProp151.lean`, namespace `AlgMag.Prop151`. Each states `IsPure N ↔ ∀ L < N, X^L < X^N`, and none assumes `AttractorOrder`.

| Lean name | Line | Hypotheses |
|---|---|---|
| `prop151_of_inter` | 37 | Any commutative monoid and any functor. The only input is `X^N = X^L → X^{N∩L} = X^N`, the step the print takes from Prop 3.32. |
| `prop151_affine` | 57 | X affine over S, any commutative monoid M, S arbitrary. |
| `prop151_group_scheme` | 136 | X a separated scheme, M a **countable** abelian group, f.g. removed. |
| `prop151_embed_scheme` | 148 | X a separated scheme, M embedded in a f.g. abelian group (the 3.32(iii) case). |
| `prop151_of_prop332` | 167 | X a separated algebraic space, M a f.g. group, no atlas, with Prop 3.32(ii) on points as the hypothesis `h332`. |

`prop151_of_prop332` is meant to take the result of the agent working on 3.32(ii). It needs no further proof once that result exists.

New supporting file: `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\GenM332Scheme.lean`.
- `AlgMag.GenM.prop332_scheme` (line 478) is Prop 3.32(ii) for schemes with M a countable group.
- `AlgMag.SQ.uniqueSums_of_torsionFree` shows every torsion-free abelian group has unique sums, with no f.g. assumption.
- `AlgMag.SQ.exists_desc_gen` is the descent without f.g.
- About 250 lines are restated from `Sec3SchemeQuotient.lean`, because the section variables there force `AddMonoid.FG M` on every theorem. I did not edit that file.

## Prop 16.15(ii)

All forms are in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\PrintedProp1615ii.lean`, namespace `AlgMag.Leftover`.

- **`prop1615_ii_formal_scheme` (line 93):** for G → S a smooth group scheme, as printed, and any abelian group M. G^[α⟩ → S and G^[α⟩_{e_S} → S are formally smooth as transformations of functors. There is no representability hypothesis and no site cutoff.
- **`prop1615_ii_formal` (line 67):** the same statement for a smooth group algebraic space, with cutoff `SM B M`. Axioms include **`sorryAx`**, inherited through `isFormallySmooth_attractorMap_spaces` and `lift103`, the existing [S] stub route.
- **`isFormallySmooth_attractor_terminal` (line 48):** the X^N → S step for spaces, also with `sorryAx` from the same route.

## Remaining added assumptions

**Prop 15.1**
- **M countable:** this is the site cutoff in `specObj`. Replacing it with `#M < cutoff` would need a rework of `specObj`, not new mathematics.
- **Other cases not covered:** I did not prove the general case of separated algebraic spaces, or a monoid outside cases (i)–(iii). The step that fails is in the suspected errors below.

**Prop 16.15(ii)**
- **Smooth versus formally smooth:** the new statements give formal smoothness only. Local finite presentation at the functor level is not stated, because the functor form of Fact 3.19 is still absent.
- **Representability for smoothness as spaces:** it is still needed beyond G affine (`prop1615_ii`, `prop1615_ii_spaces`). The print cites Cor 11.10, which reads "that X^N and X^F are representable by algebraic spaces", and 16.15 supplies nothing for that.
- **Not done:** I did not derive representability from a Thm 8.3 atlas, because the kernel would also need to be shown to be an algebraic space.

## Suspected paper errors

1. **Prop 15.1, proof.** "Then X^N = X^{N∩L} by Proposition 3.32." §15 says only "Let M be an abelian monoid. Let X be a separated algebraic space". Prop 3.32 requires one of three conditions: X affine, M a f.g. group, or M cancellative with M^gp f.g. So the citation does not cover the statement as printed. I have no counterexample, so this is a gap in the proof and the statement is not shown false. Thm 15.3's reliance on Prop 3.34 is a separate matter that I did not address.
2. **Prop 16.15(ii), proof.** "By Corollary 11.10, G^[α⟩ → S and G^[α⟩ → G^0 are smooth." Cor 11.10 assumes the representability that 16.15(ii) does not state, and it does not give the map to S. Cor 11.2 is the right source for that map, as `REMARKS.md` already records. Without representability only the formal statement follows.

## Blockers

- **Spaces, Prop 15.1:** waits on Prop 3.32(ii) for spaces. It then follows from `prop151_of_prop332`, for M a f.g. group.
- **Spaces, Prop 16.15(ii):** `sorryAx` stays until the [S] stub route through `lift103` is replaced with real Stacks modules.

## Compile setup

- **Overlay:** `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\p1516\out`, made of hard links to the existing oleans. C: has 69 GB free.
- **Not yet joint-built:** my oleans are in that overlay, so `AlgMag.lean` has not been compiled with the new imports.