fable-math
Written: C:\Users\Arnaud\Desktop\algmag-stacks\notes\chart-qs-repair.md (pure math, no Lean edited; finished 22:32, before the 22:50 target).

Contents, by section:
1. Standing fact (Q): for X quasi-separated, the equalizer of two points on an affine W is a quasi-affine scheme (pullback of Δ_X = qc mono lft, ZMT 05K0). This is the only thing `exists_pull` (AlgMag/ChartPointL11Image.lean:91) and `ChartDeligneCore.ChartOf` used separatedness for; "affine" becomes "finite union of principal affine opens" at all six call sites (L11Generic:77,198; L11Local:197,198; L11Image:243; L11Stable:59). Lemma 1.1 rewritten step by step on that basis; tower (ChartTowerChart:276,367) same.
2. Step 5 (Lemma 4.2): the sketch in chart-qs-proof.md ("X \ closure(pr_1 F) is separated") is **false as a method**: counterexample X = A^1/R, R = Δ ∪ {(x,−x), x≠0} (Knutson), Δ(X) closed yet X not separated. Route to use: keep the Lean 04S6 route (`ChartStratum.affineStratum`, ChartStratum.lean:47) replacing (a) `exists_stabIdeal`/`exists_generic_stabilizer` (ChartStratumStab.lean:31,214) by the §4.4 Claim of thm68-ii-proof.md (reviewed correct), (b) `hsepR` (ChartStratum.lean:82–99) by the peer's `ChartStratumQS.isQuasiSeparated_quotient` (ChartStratumQS.lean:79). Output is directly a nonempty G-stable affine open; no dense separated open needed.
3. Deligne block: χ_k is equivariant as an output of the Theorem 4.1 induction applied to (C/a^k, m) and Z^(k) (Lemma 4.4), so `chi_univ` (ChartDeligneCompat.lean:107) becomes `chi_univ' (hequiv : IsEquivariant χ)`, vacuous; compatibility in k and with φ_n by `ChartQS.thm41_unique_equivariant` (compiled); equalities into the affine open U need nothing of X; `le_idl_chi/theta` hsep only via ChartOf, removed by (Q).
4. Globalization: SpacesLimitThm68.lean:186–189 just needs `hqs`; line 190 needs "the f.p. model X_0 → S_0 can be chosen quasi-separated" (Stacks limit descent of qc diagonal, tag unverified) with a fallback proof by descending the étale groupoid (V, R) with R quasi-affine and taking X_0 = V_0/R_0; lines 233–279 pass hsep through; `[S.IsSeparated]` stays.
5–7. Rest of chart-qs-proof.md rechecked: Steps 1, 2, 3, 4 arguments OK; Steps 2 and 4 must state output-compatibility clauses (φ|D(b)=τ, φ|V(b^l)=ψ_l) and Step 4 hides a sub-step on (D/b^l)^c ≠ D/b^l (Step 3 with c, then with b); third-pass prose "agreement locus is open" must mean the isomorphism locus W of the equalizer (compiled result unaffected).
8. Named hypotheses (Prop defs) for composition: `QuasiAffineEqualizer`, `GenericStabilizerQS`, `AffineStratumQS`, `StrataOverQS`, `ChartLemmaQS`, `QSModelDescends`.

No `#print axioms` (no Lean written). What remains: Lean agents to implement §1 (exists_pull_qs), §2(a) Claim, §3 chi_univ', §4 exists_charts_at_qs with the Props above; the unverified Stacks tag numbers (05K0, 051S, 086U, 07ST, limit descent of quasi-separatedness) to be checked in the tree.

---

top
`ChartQSTop` compiles with no errors and no `sorry` in the file, and Thm 6.8(ii) and its qc clause now depend only on the named hypothesis `ChartLemmaQS`. It finished at 22:29, ahead of the 23:08 limit. `ChartLemmaQS` itself is not proved; the peers and the remaining steps of `chart-qs-proof.md` have to discharge it.

**File:** `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\ChartQSTop.lean`, namespace `AlgMag.ChartQSTop`. The import is appended to `AlgMag.lean`.

**Oleans:**
- `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\qstop\o\ChartQSTop.olean`
- a copy in the shared overlay at `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\cma\ov\AlgMag\ChartQSTop.olean`, so peers can import it. This is one added file in that directory.

**Statement (the only hypothesis peers must discharge):**
- `ChartLemmaQS B S hS M` (line 51), used at `S = ⊤_ Scheme`, `hS = hZ`. It assumes:
  - `AddMonoid.FG M`, `IsAffine S`, and `LocallyOfFiniteType (terminal.from S)`
  - any `X` with `IsAlgebraicSpace` and `Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X`
  - `Space.IsFiniteType (terminal.from X)`, an action `actX`, and a closed point `p : ChartPoint X`
- It concludes `∃ U actU f u, IsChartQSAt actX p U actU f u`.
- `IsChartQSAt` (line 37) is `IsChartAt` without the stabilizer field: affine, equivariant, étale, `lies_over`. So the lemma is asked at closed points only, and `G_u = G_x` is dropped.

**Theorems, all without `hsep`:**

| Theorem | Line | Content |
|---|---|---|
| `exists_atlas_of_chartLemmaQS` | 71 | Finite family of charts gives an atlas, via decent spaces, Jacobson and `closedPointsDetectCovers` |
| `atlas_pullback` | 107 | Atlas part of Lemma 6.7(i), with no `Z`-FPR input |
| `atlas_of_limit_qs` | 127 | `exists_stage`, then the stage is qs by `hWfp.2.2`; Stacks 084W is not used |
| `exists_atlas_of_fp_qs` | 171 | No separatedness of `p` |
| `exists_charts_at_qs` | 205 | Charts at one point of `X` |
| `exists_family_qs` | 251 | **Globalization:** `[S.IsSeparated]`, `ChartLemmaQS` gives an `EtaleChartFamily` from affine schemes, for `X` qs and l.f.p. |
| `thm68_ii` | 283 | **Thm 6.8(ii):** the family, and a `Z`-FPR atlas for each coproduct in the site |
| `thm68_ii_qc_final` | 298 | **Qc clause:** a `Z`-FPR atlas that is `IsSAffineAtlas`. The name differs from the existing `thm68_ii_qc` at `SpacesLimitThm68.lean:347`, which it uses. |

**Other hypotheses of `thm68_ii` and `thm68_ii_qc_final`:**
- `hZ`, `hM` and `hMZ` (the site contains `⊤_`, `Spec ZMon M`, `Spec ZMon (M ⧸ Z)`)
- `hX`, `hlfp`, `hqs : Space.IsQuasiSeparated (toT1 X)`
- `hirr : IrreducibleFibres (M ⧸ Z) S`, the Lean form of `M/Z` torsion-free
- `[AddGroup.FG M]`, `[S.IsSeparated]` (the agreed addition)
- `hq` for the qc clause

**`#print axioms`**, for `exists_atlas_of_chartLemmaQS`, `exists_family_qs`, `thm68_ii` and `thm68_ii_qc_final`: `[propext, sorryAx, Classical.choice, Quot.sound]`.

`sorryAx` comes only from the Stacks stubs in the `cma/ov` overlay. The walker lists 21 stub roots for both `thm68_ii` and `thm68_ii_qc_final`, none in `AlgMag`:
- the `FinitePresentationDescent` limit lemmas and the `MorphismDescentSituation` one
- `stageLimitIso`, `stageSystem_*` and `contains_specAdjoinFinsetDiagram_objSE`
- `isDecentSpace_of_isAbsolutelyQuasiSeparated`
- `jacobsonSpace_points_of_exists_jacobson_atlas`
- the relocalize lemmas

These are Stacks statements, but I did not re-compare the stubs here. `exists_isSeparated_mapAt...` is only reachable through the `limitDataZ.sepDesc` field and is not used logically. The other roots are the same kind as those compared in `notes/chart-stubs.md`.

**What remains:**
- **`ChartLemmaQS` itself.** The inputs are Deligne with quasi-affine `Z ×_X V`, `NoetherianAlgebraization` (Step 4) and Lemma 4.2 (Step 5) in `notes/chart-qs-proof.md`.
- **Absolute versus relative quasi-separatedness.** The hypothesis is the absolute form. If a peer proves it from `IsQuasiSeparated (terminal.from X)`, the conversion runs the other way from `Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated`, so it would need a short bridge lemma. The absolute form is what `ChartStratumCore` already uses.

---

alg
**Step 4 is not finished.** `NoetherianAlgebraization X` is proved for any algebraic space, but only from a named hypothesis, `LocalModelStep X`. I stopped at 22:36, ahead of the 23:08 deadline, because the next piece did not look feasible in the time left; nothing is overrun.

All names below are in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\ChartQSAlg.lean`. It compiles with no sorry, and `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem except `eq_on_kernelPair_flat`, which I did not print separately but `existsUnique_pushout_flat` depends on it. The olean is in `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\qsa\ol`. I appended `import AlgMag.ChartQSAlg` to `AlgMag.lean`, and did not edit any other existing file.

**Already covered by peers (not redone)**
- Step 3: `ChartQS.eq_of_agree_pow`.
- Equalities in Step 2: `ChartQS.eq_of_agree_basicOpen_of_agree_thickening`.
- Completion gluing: `ChartQS.existsUnique_pushout` with the `complMap`/`compl_*` lemmas.

**New theorems**

| Name | Line | Content |
|---|---|---|
| `eq_on_kernelPair_flat` | 48 | Kernel-pair agreement for a flat `Y → T`, without `C → Γ(Y)/a^k` onto |
| `existsUnique_pushout_flat` | 139 | Step 1 in full: `Y` may be the completion of an étale algebra |
| `noetherianAlgebraization_of_exists` | 199 | Uniqueness in `NoetherianAlgebraization` holds for any `X`, so only existence remains |
| `noetherianAlgebraization_of_localModel` | 241 | `LocalModelStep X → NoetherianAlgebraization X`, with restriction to the system by descent |
| `hthick_of_psi` | 366 | Thickening agreement follows from points `ψ_k` on `V(b^k)` |
| `map_le_jacobson_localization` | 328 | `a` lies in the Jacobson radical after inverting `1 + a` |
| `eq_zero_of_mem_pow` | 353 | Krull: an element in all `a^k` is zero, for `a` in the Jacobson radical |

**Named hypothesis for peers: `ChartQSAlg.LocalModelStep X` (line 212)**

For a compatible system on `W` (noetherian, `I`-complete), it asks for:
- an ideal `b` and a point `τ` on `D(b)`;
- a flat `Y → W` from an affine, covering `V(b)`, with a point `θ`;
- compatibility of `τ` and `θ`, agreement on the kernel-pair thickenings, and both restricting to the system.

Plugging it in requires `ChartQS.effective_of_noetherian`'s `hC` to be `noetherianAlgebraization_of_localModel hX (h : LocalModelStep C.Z)`.

**New on paper: a simpler route than `S(X,Z)`, not formalized and with no independent check**

It needs no 07ST filtration and no induction inside `S`. It is recorded in the file header. Write `C = Γ(W)`, and argue by noetherian induction on `|X|`.

1. Take `U` an affine open, `b`, and `τ` from Lemmas 3.4 and 4.3 (non-graded). The induction on the smaller closed thickenings gives `ψ_l` on `C/b^l`.
2. Let `D` be the `b`-completion of `C`. Take étale charts over `D/b` and lift them to étale `D'` over `D`. Stacks 057R does this directly as `Stacks.Etale.exists_etale_lift_of_isClosedImmersion` (`StacksFrontier/AlgebraicGeometry/Etale/LiftAcrossClosedImmersion.lean:138`), with no henselian input.
3. Let `Y` be the `b`-completion of `D'` with `1 + I` inverted, and get `θ` as the limit of the étale lifts. `Y` is flat and still covers `V(b)`, because generizations lift, and `I` lies in the Jacobson radical of `Y`.
4. `θ = φ_k` on `Y/I^k` follows from Step 3, since `b` is in the Jacobson radical of `Y/I^k`.
5. `θ = τ` on `D(b)Y`: for `β ∈ b^n`, the elements `τ(f)β` and `θ(f)β` lie in `Γ(Y)` and agree modulo every `I^k` by the Lemma 4.3 formula, so Krull gives equality.

Gluing is then `existsUnique_pushout_flat`, with `hthick_of_psi` for the thickenings.

**What remains for `LocalModelStep`**
1. Lemma 3.4 and Lemma 4.3 in non-graded form, including the formula for `τ(f)β`. This hits the `ChartOf` affine obstruction described in `notes/chart-qs-proof.md` (Lemma 4.3 needs `Z ×_X V` affine, but it is only quasi-affine). This is the hard part, and `U` also needs an affine open of `X` to exist.
2. Construction of `Y` and `θ`. `ChartPoint.exists_affine_chart` applied to `ψ_1`, then 057R, then the limit of étale lifts. Site membership of the lift must be checked, and I did not attempt any of this in Lean.
3. Several charts: `Y` must be a finite disjoint union, or `existsUnique_pushout_flat` must be extended to finite families. Its glue currently uses `Fin 2`.
4. The noetherian induction over closed thickenings of `|X|`.

---

strat
**Result: not closed. Lemma 4.2 and §1 for quasi-separated X now compile, but each depends on a named hypothesis.** Those hypotheses are the unproved core of Lemma 4.2 and Lemma 1.1. I stopped at 22:39 because neither can be finished by 23:08.

## Compiled files
All are new, in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`, and contain no `sorry`. They are not yet appended to `AlgMag.lean`.

**`ChartQSStratCore.lean`** (compile with `cs/run.sh`)
- `exists_stable_affine_of_orbit_qs` (:59) and `exists_stable_affine_of_chart_qs` (:216): separatedness is replaced by `IsQuasiSeparated (terminal.from X)`.
- `affineStratum_qs` (:287) is Lemma 4.2 for quasi-separated X, given `GenericStabilizerQS` (:49).
- `affineStratum_closedStable_qs` (:372) is meant to be the `h42` input of `ChartQS.effective_of_stratum`. The types look the same, but I did not compile the composition.
- `#print axioms`: `propext, sorryAx, Classical.choice, Quot.sound`. A walk of used constants shows `sorryAx` comes only from these 14 Stacks stubs, all already used by `ChartStratum.affineStratum`:
  - `isOpenSubspace_preimage`, `hasSheafify_bigFppfOver`, `bootstrap04S6QuotientSheaf`
  - `isPullback_toQuotientSheaf`, `isLocallySurjective_toQuotientSheaf`, `exists_fppf_isPullback_pullback_toQuotientSheaf`
  - `isQuasiCompact_of_comp_of_isQuasiSeparated`, `exists_single_fppf_lift_of_isLocallySurjective`, `of_isPullback_yoneda_map_of_fppf`
  - `exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace`, `isDecentSpace_of_isAbsolutelyQuasiSeparated`
  - `isLocalAtTarget_isAffineHom_fpqc`, `pointsRange_preimage`, `isAffineSpace_of_isClosedImmersion_of_isSurjective`

**`ChartQSStratGeneric.lean`**
- `exists_generic_of_ideal` (:29) gets the generic stabilizer from any ideal that describes the stabilizer.
- `genericStabilizerAt_of_closedGeneric` reduces `GenericStabilizerAt` to `StabClosedGeneric` (:77).
- `genericStabilizerAt_of_separated` is a sanity check that the separated case satisfies the hypothesis.
- `GenericStabilizerAt` (`ChartQSStratCore.lean:37`) only asks for étale charts p, which is all the proof uses and makes it weaker than the Claim in §4.4.
- `#print axioms`: `propext, Classical.choice, Quot.sound`.

**`ChartQSStratPoint.lean`**
- `exists_stabilizer_of_ideal` (:31).
- `exists_stabilizer_closedPoint` (:114): the stabilizer of a closed point is `D(M/Z₀)`, with no separatedness.
- `exists_orbit_mono_closedPoint` (:126).
- `#print axioms` (checked on `exists_orbit_mono_closedPoint`): `propext, Classical.choice, Quot.sound`.

**`ChartQSStratOrbit.lean`** (compile with `scratchpad/qsstrat/k.sh`, the `l11` overlay)
- `isQuasiSeparated_toBase_XP` (:116).
- `exists_orbitInput_qs` (:154) is the §1 output for quasi-separated X, given `Lemma11QS` (:34).
- `#print axioms`: `propext, Classical.choice, Quot.sound`. The overlay's stubs were not reached.

## Named hypotheses for peers
- **`ChartQSStrat.GenericStabilizerQS`:** implied, one action at a time, by `StabClosedGeneric` through `genericStabilizerAt_of_closedGeneric`. A one-line wrapper over all M and X is still missing.
- **`ChartQSStrat.StabClosedGeneric`:** the stabilizer is closed in `D(M)_W` over a nonempty open W of an étale chart.
- **`ChartPoint.Lemma11QS`:** `lemma11` plus `orbit_lfp` for quasi-separated X.

## What remains
1. **`StabClosedGeneric`, not started in Lean.** The route below may avoid ZMT, generic flatness and SGA 3 VI_B 1.4.2, but it is new and unchecked:
   - Take a dense affine open U₀ of X (stub 086U) and shrink V so that p lands in U₀.
   - On the open A = {(h, v) : h·p(v) ∈ U₀} of `G_W`, the stabilizer is the equalizer of two maps to the affine U₀, so it is closed in A. Hence E is locally closed in `G_W`.
   - Over K, a locally closed subgroup is closed, by the translate argument over an algebraically closed field. This also needs its closure to be a subgroup, by the `hmul` argument.
   - Spread out: the closure of E minus E misses the generic fibre, so Chevalley lets you shrink V until E is closed.
2. **`Lemma11QS`, not started in Lean.** `notes/chart-qs-repair.md` §1 asks to replace "E affine" by a finite affine cover in `exists_pull`. That touches `ChartPointL11Generic`, `L11Local`, `L11Image`, `L11Stable`, `ChartPointOrbitInput` and `ChartPointLemma11`, about 90 KB of proofs. It also needs ZMT for "quasi-finite separated over affine implies quasi-affine", or the hypothesis `QuasiAffineEqualizer`.

I also tried to reduce Lemma 1.1 to a separated open, and that fails. A stable separated neighbourhood need not exist: with μ₂ swapping the two origins of the doubled line, every stable open containing an origin is non-separated.

---

main
**Partial result: `ChartLemmaQS` is not assembled.** The Deligne block for quasi-separated X compiles through Core, Lim, Open and Compat. It stops at `ChartQSIndTheta`, which does not compile, so everything after it is uncompiled.

**Compiled, no sorry** (in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`, oleans in `scratchpad\cma\ov`). The checked `#print axioms` results, for `le_idl_theta` and `lift_smul`, are propext, Classical.choice and Quot.sound.

All names are in namespace `AlgMag.ChartMain.DeligneQS`:
- **`ChartQSIndCore.lean`** replaces the "Z ×_X V affine" assumption:
  - `ChartOf` (:119) is now an affine étale surjective E → Z that covers Z ×_X V after an étale cover of the test object.
  - `Lift` (:704) is now defined on all maps to V, not one chosen chart.
  - This rewrites `exists_chartOf` as far as the block needs. `exists_cross` (:442), `lift_unique` (:811), `lift_exists` (:837) and `lift_smul` (:920) are all proved with it.
  - The Lean `ChartOf` differs from `chart-qs-repair.md`'s "finite affine cover". It avoids a maximum over pieces and needs no `QuasiAffineEqualizer`.
- **`ChartQSIndLim.lean`, `ChartQSIndOpen.lean`:** mechanical copies of `ChartDeligneLim` and `ChartDeligneOpen` on the new Core. This duplicates about 950 lines, because `Ctx` is a different type.
- **`ChartQSIndCompat.lean`:**
  - Review gap 4 is closed. `chi_univ` is removed and χ's equivariance becomes the hypothesis `EquivAlong`, which `ChartQS.OpenStratumMap` already provides.
  - `le_idl_chi` (:91) and `le_idl_theta` (:142) have no `hsep`.
- I appended `import AlgMag.ChartQSIndCompat` to `AlgMag.lean`.

**Written but not compiled** (moved out of the repo to `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\qsi\wip\`):
- **`ChartQSIndTheta.lean`:**
  - This is the blocker. It was still running after about 24 minutes, when I stopped it at the deadline.
  - A test copy with `maxHeartbeats` 400000 on the first half times out at `whnf` on `cmp_n` (line 82). That limit is far below the 4000000 the theorem sets, so this shows slowness only, not a real failure.
  - `cmp_n`'s `lift_cross` and `le_idl_chi` calls are my first suspects, unconfirmed. Next try: mark `Lift` irreducible or pass the implicit arguments explicitly.
- **`ChartQSIndInst.lean`:** `openStratumMap_qs` and `strataOver_qs`, which give `ChartQS.StrataOver` from `HasCharts`.
- **`ChartQSIndCharts.lean`:** `pullbacksQC_of_isQuasiSeparated` and `hasCharts_of_pullbacksQC`, intended to prove `HasCharts` from quasi-separatedness with S affine, with no new hypothesis.
- **`ChartQSIndMain.lean`:** `effective_of_lft_qs`, which is Thm 4.1 existence for qs X. Its hypotheses are `hch` (`HasCharts`), `hC` (`NoetherianAlgebraization`, Step 4) and `h42` (`AffineStratum`, Step 5).

**Named hypotheses, for composing with peers:** `DeligneQS.HasCharts` and `PullbacksQC` are defined in the uncompiled files above.

**Remaining:**
1. Fix `cmp_n` so `ChartQSIndTheta` compiles.
2. Compile Inst, Charts and Main, in that order.
3. Move the four files back into `AlgMag/`.
4. Write the `ChartQSTop.ChartLemmaQS` assembly, which is not started. It is the bookkeeping of `chartLemmaFG_of_section5`, using `exists_orbitInput_qs`, `Lemma11QS` and a §5 named hypothesis for qs X. Nobody has yet built the tower or §5 without `hsep` (`exists_affineTower`, `exists_section5_input`, `exists_chart_at_point`).

Thm 4.1 itself needs no separate induction work: the peer's `ChartQS.effective_of_noetherian` already does it, and `ChartQSIndMain` only feeds it.