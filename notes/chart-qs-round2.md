deligne
`ChartLemmaQS` is proved for every `B S hS M`, and Thm 6.8(ii) with its qc clause no longer has `ChartLemmaQS` as a premise. All of it still depends on `sorryAx` through Stacks stubs, and it was checked only by `lean -o` against the overlay, with no full `lake build`.

All files are in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`, and none contains `sorry`.

**Main results**
| Lean name | Location | Content |
|---|---|---|
| `AlgMag.ChartMain.DeligneQS.chartLemmaQS` | `ChartQSIndClose.lean:22` | Proves `ChartQSTop.ChartLemmaQS B S hS M`, composing peers' `ChartQSL11.lemma11QS_holds` and `ChartQSStabGen.genericStabilizerQS` |
| `thm68_ii_proved` | `ChartQSIndThm68.lean:30` | Thm 6.8(ii) with no chart-lemma premise |
| `thm68_ii_qc_proved` | `ChartQSIndThm68.lean:42` | Qc clause, an S-affine Z-FPR atlas |

**My piece**
- **`ChartQSIndTheta.lean`:** now compiles in about 5 minutes at `maxHeartbeats 400000`. The original `rw` steps were what timed out.
  - **Fix:** I replaced them with `lift_congr` and `sec_square`.
  - **New lemmas:** `cmp_n'` and `cmp_Y_piece` state the result with a generic `W`, and `rh_Y` handles the ring algebra.
  - **Result:** `cmp_n` is at line 91, `tau_theta` at line 244.
- **`ChartQSIndInst.lean`:** `openStratumMap_qs` and `strataOver_qs` now also take `[IsAffine S]`, which `exists_ideal` needs. Every caller already has it.
- **`ChartQSIndCharts.lean`:** I fixed the pullback `simp` steps.
- **`ChartQSIndMain.lean`:** `effective_of_lft_qs` compiles after adding `open AlgMag.ChartAssembly`.
- **`ChartQSIndStrata.lean`:** this new file proves `strataOverQS` at line 24, which discharges the named Prop `ChartQSAsm.StrataOverQS`. It also adds `chartLemmaQS_of_lemma11_generic` at line 44.

All seven files are appended to `AlgMag.lean`. The oleans are in `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\cma\ov\AlgMag\`.

**`#print axioms`**
- **No `sorryAx`:** `openStratumMap_qs`, `strataOver_qs`, `hasCharts_of_pullbacksQC`, `effective_of_lft_qs` and `strataOverQS` depend only on `[propext, Classical.choice, Quot.sound]`.
- **With `sorryAx`:** `chartLemmaQS`, `thm68_ii_proved` and `thm68_ii_qc_proved` depend on `[propext, sorryAx, Classical.choice, Quot.sound]`.

A walk over used constants finds 21 `sorryAx` roots for `chartLemmaQS` and 41 for each Thm 6.8(ii) form. None of the 41 is in an `AlgMag` module; they are all stubs in `StacksFrontier`, in these groups:
- `FinitePresentationDescent` and `isFinitePresentation_*`
- the `stageSystem_*` and `stageLimitIso` family
- the `Bootstrap04S6` carriers
- the relocalize lemmas
- `isDecentSpace_of_isAbsolutelyQuasiSeparated` and `jacobsonSpace_points_of_exists_jacobson_atlas`
- `isGRing_*` and `artinApproximationGRing`
- `isSeparated_of_isPullback`, plus isolated lemmas such as `isAffine_of_isThickening`

**Added assumptions, already in `ChartQSTop`**
- `[S.IsSeparated]`
- `[AddGroup.FG M]`
- `hirr : IrreducibleFibres (M ⧸ Z) S`, the Lean form of M/Z torsion-free
- the site-membership hypotheses `hZ`, `hM`, `hMZ`

**What remains**
1. **Compare stubs:** I did not compare these 41 stubs with their Stacks statements, so someone needs to. `notes/chart-stubs.md` covers at least `isGRing_of_essFiniteType`; I did not check how many of the others it covers.
2. **Check for stale oleans:** run an uncached rebuild of the `ChartQS*` chain once the lock is free.
   - **What I did to the overlay:** peers' oleans came from the overlay, and I added 276 files from `scratchpad\cm2\out\AlgMag` with `cp -n` (no overwriting), which brought `ChartQSStabGenFinal` in.
   - **Risk:** Lean does not recheck imported proofs here, so a stale olean would go unnoticed.

---

alg
**Step 4 is proved: `NoetherianAlgebraization` holds for quasi-separated X, but `ChartLemmaQS` is not closed.** It still depends on three peer pieces. `chartLemmaQS_of_generic_strata` reduces it to `Lemma11QS`, `GenericStabilizerQS` and `StrataOverQS`.

## Lean names

All files are in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`, compile with no `sorry`, and their imports are appended to `AlgMag.lean`. Oleans are in the `cma/ov` overlay. Names below are in namespace `AlgMag.ChartMain.DeligneQS.ChartQSLocal`, except the last two table rows, which are in `AlgMag.ChartQSAsm`.

| Statement | Lean name | Location |
|---|---|---|
| `ChartQSAlg.LocalModelStep X`, given `Effective` on the tower `Z^(k)` of an affine open | `localModelStep` | `ChartQSLocalMain.lean:97` |
| Induction over closed subspaces, all thickenings at once | `effective_triv` | `ChartQSLocalMain.lean:176` |
| **Step 4:** X qs, locally of finite type (lft) over affine finite-type S, with affine atlas | `noetherianAlgebraization_of_atlas` | `ChartQSLocalFinal.lean:37` |
| Same for every closed `C` of any action; the form `effective_of_noetherian`'s `hC` needs | `noetherianAlgebraization_closed` | `ChartQSLocalFinal.lean:73` |
| `HasCharts`, from qs | `hasCharts_of_qs` | `ChartQSLocalFinal.lean:30` |
| Thm 4.1 existence, with `halg` removed | `effectivityQS_of_generic_strata` | `ChartQSLocalFinal.lean:97` |
| `ChartLemmaQS`, from `h11`, `hgen`, `hstr` | `chartLemmaQS_of_generic_strata` | `ChartQSLocalFinal.lean:123` |

Supporting results:
- **`ChartQSLocalTriv.lean`:** for `M = PUnit`, a complete pair is an adically complete noetherian ring, and `Effective` is algebraization. This makes the non-graded Lemmas 3.4, 4.3 and 4.4 exactly the compiled graded ones.
- **`ChartQSLocalInst.lean`:** the `Ctx` fields, copied from the uncompiled `ChartQSIndInst` and independent of `ChartQSIndTheta`.
- **`ChartQSLocalCmp.lean`:** `tau_thetaY` (:183) gives τ = θ on D(a)Y, using `le_idl_thetaY` and Krull modulo mⁿ. It needs neither χ nor surjectivity.
- **`ChartQSLocalLift.lean`:** `exists_map_chart` (:179), the limit of étale lifts.
- **`ChartQSLocalModel.lean`, `ChartQSLocalEtale.lean`:** `exists_model` (`Etale`:40) builds Y as the b-completion of an étale algebra (057R) with 1+I inverted. It uses one affine E from `ChartOf`, so no finite families are needed.
- **`ChartQSLocalCharts.lean`:** `pullbacksQC_of_isQuasiSeparated`, `hasCharts_of_pullbacksQC`, repaired copies from the uncompiled wip file.
- **`ChartQSLocalMain.lean:28`:** `theta_restrict` gives θ = φₙ on Y/Iⁿ by Step 3.

## `#print axioms`

- **Clean:** `tau_thetaY`, `exists_model` and `localModelStep` give `[propext, Classical.choice, Quot.sound]`.
- **With `sorryAx`:** `effective_triv`, `noetherianAlgebraization_of_atlas`, `noetherianAlgebraization_closed`, `effectivityQS_of_generic_strata` and `chartLemmaQS_of_generic_strata` give `[propext, sorryAx, Classical.choice, Quot.sound]`.
- **Source of `sorryAx`:** a constant walk on `noetherianAlgebraization_of_atlas` finds only two Stacks stubs, both reached through `ChartStratum.exists_affine_open_of_absQS`:
  - `exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace`
  - `isDecentSpace_of_isAbsolutelyQuasiSeparated`
- **Other stubs:** the same walk on `effectivityQS_of_generic_strata` finds those two plus 11 more, none in `AlgMag`. All 13 are in the `ChartQSStratCore` stub list. I did not walk `chartLemmaQS_of_generic_strata`, which also uses `h11` and the assembly.

## Added assumptions

- `[IsAffine S]`, S of finite type over ℤ, X qs and lft, as in `chart-qs-repair.md`.
- `HasAffineAtlas X`, meaning X is quasi-compact. This is the one hypothesis beyond the statement requested.
- The peer's `ChartQSAsm.NoetherianAlgebraizationQS` has no quasi-compactness, and I did not prove that form. It is only used on closed subspaces of a qc X, so `effectivityQS_of_generic_strata` replaces `effectivityQS_of_pieces` with no gap.

## Departures from the notes

- **Route:** I used the `chart-qs-sprint.md` route rather than the `S(X,Z)` induction with the 07ST filtration. It now has a machine-checked proof, so that route needs no independent check at the Lean level.
- **Paper errors:** I found no new ones.

## Remaining for `ChartLemmaQS`

- **`ChartPoint.Lemma11QS` and `ChartQSStrat.GenericStabilizerQS`:** I did not work on these, and `ChartQSStabGen*` are peer files I did not check.
- **`ChartQSAsm.StrataOverQS`:** this needs `ChartQSIndTheta`, `ChartQSIndInst` and `ChartQSIndMain`.

**Likely fix for the `ChartQSIndTheta` timeout (not tested on that file):** I hit the same `whnf` timeout at the same kind of proof. Mine came from `rw [← sec_comp, ← sec_comp, hs]`, `▸` chains and `rw [..., hax]`, because `rw`'s `kabstract` tries expensive defeq checks across the `Γ(Vc …)` types. Replacing them with terms such as `(sec_comp i p z).symm.trans ((congrArg (fun c => (sec c) z) hs).trans …)` and `(hax n).ge …` fixed it. `ChartQSLocalCmp.lean` shows the pattern and compiles in about a minute.

## Build note

Stacks module to add to the sparse build: `StacksFrontier/AlgebraicGeometry/Etale/LiftAcrossClosedImmersion`. I compiled the real source into `cma/ov`, so no stub was needed for 057R.

I also copied `ChartQSAlg.olean` into `cma/ov`.

Compile script: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\qsl\k.sh`

---

stab
Piece done: `GenericStabilizerQS` and Lemma 4.2 for quasi-separated X (`affineStratum_qs`) now compile with no named hypothesis. `ChartLemmaQS` itself is not closed; the other pieces are still open.

**Lean names** (`C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`, namespace `AlgMag.ChartQSStabGen`)

| Statement | Location |
|---|---|
| `genericStabilizerAt` (§4.4 Claim, no `hsep`) | `ChartQSStabGenFinal.lean:106` |
| `genericStabilizerQS B S hS : ChartQSStrat.GenericStabilizerQS B S hS` | `ChartQSStabGenFinal.lean:257` |
| `affineStratum_qs'` (Lemma 4.2 for quasi-separated X, unconditional) | `ChartQSStabGenFinal.lean:262` |
| `affineStratum_closedStable_qs'` (the `h42` input of `ChartQS.effective_of_stratum`) | `ChartQSStabGenFinal.lean:269` |
| `generic_of_open_immersion` (p factors through an affine open D of X) | `ChartQSStabGenTests.lean:348` |
| `exists_charts` (the stabilizer is locally closed) | `ChartQSStabGenCharts.lean:197` |
| `exists_generic_ring` (ring statement) | `ChartQSStabGenMain.lean:431` |
| `hmul_Ik` (closure of `E_K` is closed under products) | `ChartQSStabGenField.lean:392` |
| `exists_translate` (translate argument) | `ChartQSStabGenTrans.lean:96` |
| `JJ_eq_top` | `ChartQSStabGenMain.lean:346` |

- **Files:** seven new files, `ChartQSStabGen{Alg,Field,Trans,Main,Charts,Tests,Final}.lean`, about 2300 lines, no `sorry`. All seven imports are appended to `AlgMag.lean`.
- **Oleans:** `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\cm2\out\AlgMag\`, compiled with `scratchpad\cs\run.sh`.
- **Not done:** the oleans are not copied to the `cma/ov` overlay. `ChartQSLift` is missing from `cm2`, so I wrote a local `eq_of_family` (open covers) in `ChartQSStabGenTests.lean` instead of importing it.

**`#print axioms`**
- `exists_generic_ring`, `generic_of_open_immersion`: `[propext, Classical.choice, Quot.sound]`.
- `genericStabilizerQS`, `affineStratum_qs'`: `[propext, sorryAx, Classical.choice, Quot.sound]`.
- The walker, run on `genericStabilizerQS` and `affineStratum_closedStable_qs'`, finds `sorryAx` only in Stacks stubs:
  - `genericStabilizerQS`: `exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace`, `isDecentSpace_of_isAbsolutelyQuasiSeparated`, `isOpenSubspace_preimage`.
  - `affineStratum_closedStable_qs'`: those same three, plus the 04S6 stubs already listed in the `strat` section of the sprint report.

**Hand check of the sprint's locally closed route: correct.** Two simplifications and one naming point:
1. **`StabClosedGeneric` is not instantiated.** It is bypassed, and `GenericStabilizerAt` is proved directly with `D(M/Z)`. That is stronger, since the stabilizer is then closed over `D(s)`.
2. **No algebraically closed field or Chevalley.**
   - The closure ideal `Ik` is closed under products, using injectivity of the tensor product over K on the charts `E_i ×_K E_j`.
   - `exists_stab_subgroup` over K then gives `Ik = I(D(M/Z))`.
   - The ideal J of the complement of `E_K` in `K[M/Z]` has zero annihilator, so it contains a nonzerodivisor F.
   - F and its translate by g are both nonzerodivisors on `L₀ ⊗ K[M/Z]`. That gives a field point y with y and gy in E, hence g in E, so `J = ⊤`.
   - Spreading out is just clearing denominators in `1 ∈ J`.
   - All stabilizer tests run on locally closed subschemes of `D(M×M)_V`, which lie in the site. No fraction field is needed there.
3. **Density is replaced.** For the affine open I use the image of the étale chart: `orbSub` of the trivial `PUnit` action, over an affine open of S. This gives absolute quasi-separatedness from relative quasi-separatedness, and D meets the chart by surjectivity. The density of `exists_denseRange…` is not used.

**Added assumptions:** none beyond `GenericStabilizerQS` as stated. **Suspected paper errors:** none.

**What remains for `ChartLemmaQS`** (`AlgMag/ChartQSTop.lean:51`), none of it touched here:
- `Lemma11QS`
- the tower and §5 without `hsep`
- `LocalModelStep`
- `ChartQSIndTheta` and later, in the state the sprint report gives
- the assembly itself

---

l11
**`Lemma11QS` is proved with no hypotheses, so this piece of `ChartLemmaQS` is closed.** `ChartLemmaQS` itself is not closed; the other pieces are listed at the end. All five new files compile with no `sorry`. The oleans are in `scratchpad\cma\ov\AlgMag`. I appended `import AlgMag.ChartQSL11Lemma` to `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag.lean`, and that line has not been built through the root file.

## Statements
All in namespace `AlgMag.ChartQSL11`, in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`:
| Name | Location | Content |
|---|---|---|
| `lemma11QS_holds : ChartPoint.Lemma11QS B S hS` | `ChartQSL11Lemma.lean:412` | Discharges the named hypothesis of `exists_orbitInput_qs` |
| `exists_orbitInput_qs'` | `ChartQSL11Lemma.lean:419` | §1 of `notes/ahr-specialized-proof.md` for `X` quasi-separated, no extra premise |
| `lemma11_qs` | `ChartQSL11Lemma.lean:106` | Lemma 1.1 |
| `orbit_lfp_qs` | `ChartQSL11Lemma.lean:335` | The orbit map is locally of finite presentation |
| `exists_chart_affine_pull` | `ChartQSL11Generic.lean:37` | A chart over which `O ×_X U` is affine and nonempty |
| `exists_good_basicOpen_qs` | `ChartQSL11Generic.lean:204` | Step B, generic flatness |

Supporting files:
- **`ChartQSL11Pull.lean`:** `exists_pull_qs`, `isQuasiCompact_of_affine`, finite affine covers.
- **`ChartQSL11Stable.lean`:** `image_stable_qs`.
- **`ChartQSL11Flat.lean`:** `goodAt_of_basicOpen_qs`.

## `#print axioms`
- **`lemma11QS_holds` and `exists_orbitInput_qs'`:** `[propext, sorryAx, Classical.choice, Quot.sound]`.
- **`sorryAx`:** a walk from `lemma11QS_holds` finds three stub roots, all Stacks statements and none in `AlgMag`:
  - `isQuasiCompact_of_comp_of_isQuasiSeparated` (03KS)
  - `isQuasiCompact_of_isAffineHom'`
  - `schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact'`
- **Stub check:** I read the real source of the first two this round, but not the third, which `ChartPointL11Image` already used.
- **`exists_orbitInput_qs'`:** the walk was run only from `lemma11QS_holds`, so this theorem may pull in further stubs through `ChartQSStratOrbit`.
- **Added assumptions:** none beyond those already in `Lemma11QS`.

## Departures from `notes/chart-qs-repair.md` §1
No Zariski's Main Theorem or `QuasiAffineEqualizer` is needed. "Finite affine cover at all six call sites" was not enough for step B, so the argument differs at each of these points; it is my own and has had no independent read:
- **Quasi-compactness:** only the quasi-compactness of `O ×_X T` is used.
- **Step A:** the kernel of `Γ(T) → Γ(O_T)` is the finite intersection of the kernels to an affine cover. Flat base change commutes with that intersection (`mem_map_iInf_ker`). `T[M] ×_X T₂` is handled locally on the test object.
- **Step B:** the epimorphism argument needs one affine fibre product, and a cover does not give that.
  - Take `y` generic in the closure of the image of `O ×_X U₀ → U₀`.
  - Then `y` is the image of a point `η` and is not a specialization of any other image point, by injectivity.
  - So `y` lies outside the closure of the image of the complement of an affine open containing `η`.
  - A principal open of `U₀` around `y` makes the fibre product affine.
- **Step C:** the shear uses the scheme `W ×_T T[M]` in place of `Gk M W`. `GoodAtQS` is tested on non-affine `W`.

No paper errors found.

## What remains for `ChartLemmaQS`
These belong to the other pieces, as listed in `notes/chart-qs-sprint.md`; I did not touch them:
- `ChartQSIndTheta` and the Deligne block after it
- `LocalModelStep`
- `StabClosedGeneric` / `GenericStabilizerQS`
- the tower and §5 without `hsep`
- the final assembly

The stratum files also need compiling in this overlay. I recompiled `ChartQSStratPoint` and `ChartQSStratOrbit` into `cma/ov`, which is needed to compose with `ChartQSTop`.

---

tower
**`ChartLemmaQS` is not closed outright, but the Tower, §5 and assembly piece is done.** `ChartQSTop.ChartLemmaQS` now follows from four named hypotheses, all owned by other pieces. Nothing in this piece uses `hsep`, and all three new files compile with no `sorry` in `AlgMag`.

## Theorems
All are in namespace `AlgMag.ChartQSAsm`; paths are under `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`.

| Statement | Lean name | Location |
|---|---|---|
| Closed immersion with nilpotent kernel on affines is surjective | `surjective_of_ker_pow` | `ChartQSAsmTower.lean` |
| Chart relation is affine (`ChartTowerChart` affine relation) | `isAffine_relation_of_nilpotent` | `ChartQSAsmTower.lean:70` |
| `X_n` is affine | `exists_affine_thickening_qs` | `ChartQSAsmTower.lean:137` |
| Tower §2, any algebraic space | `exists_affineTower_qs` | `ChartQSAsmTower.lean:203` |
| Bridge to §5 | `exists_section5_input_qs` | `ChartQSAsm.lean:48` |
| Chart at a closed point, `X` decent | `exists_chart_at_point_qs` | `ChartQSAsm.lean:102` |
| §5 output, `X` decent, given effectivity | `section5Output_qs` | `ChartQSAsm.lean:232` |
| Orbit with explicit `N`, from `Lemma11QS` | `exists_orbit_data_qs` | `ChartQSAsm.lean:282` |
| Theorem 4.1 existence for qs `X` (named Prop) | `EffectivityQS` | `ChartQSAsm.lean:404` |
| Assembly, mirrors `chartLemmaFG_of_section5` | `chartLemmaQS_of_props` | `ChartQSAsm.lean:437` |
| `EffectivityQS` from its three inputs | `effectivityQS_of_pieces` | `ChartQSAsmFinal.lean:51` |
| **`ChartLemmaQS` from the four pieces** | `chartLemmaQS_of_pieces` | `ChartQSAsmFinal.lean:88` |

`chartLemmaQS_of_pieces` takes these hypotheses:
- `h11 : ∀ [IsAffine S], Lemma11QS B S hS`
- `hgen : GenericStabilizerQS B S hS`
- `halg : NoetherianAlgebraizationQS B S hS`
- `hstr : StrataOverQS B S hS M`

## Departure from the repair note
`notes/chart-qs-repair.md` §1 says the relation of the tower chart is only quasi-affine. In fact it is affine for any algebraic space:
- `R_n = V_n ×_{X_n} V_n` is a thickening of `R_0 = V_0 ×_O V_0`.
- `R_0` is affine because `O` is, so `R_n` is affine by Stacks 06AD.

So the tower needs neither (Q), ZMT nor quasi-separatedness. The chart-at-point lemma and §5 need only `IsDecentSpace`.

## `#print axioms`
- `exists_orbit_data_qs`: `[propext, Classical.choice, Quot.sound]`.
- Every other theorem printed, including `chartLemmaQS_of_props` and `chartLemmaQS_of_pieces`: `[propext, sorryAx, Classical.choice, Quot.sound]`.
- A walk from `chartLemmaQS_of_pieces` finds 19 `sorryAx` roots, all Stacks stubs and none in `AlgMag`:
  - 06AD (`isAffine_of_isThickening`), new this round
  - `exists_affine_elementaryEtaleNeighborhood'`
  - `artinApproximationGRing`, `isGRing_of_essFiniteType`, `isGRing_basic_examples`
  - `isLocallyOfFinitePresentation_of_isLocallyOfFiniteType`
  - `isDecentSpace_of_isAbsolutelyQuasiSeparated`
  - the 04S6 family and the other `ChartQSStratCore` stubs

## Added assumptions
None beyond `ChartLemmaQS`'s own. The stabilizer field is proved inside but dropped, because `IsChartQSAt` does not ask for it.

## What remains (peers)
1. **`Lemma11QS`** (`ChartQSStratOrbit.lean:34`): not started in Lean.
2. **`GenericStabilizerQS`** (`ChartQSStratCore.lean:49`): `StabClosedGeneric` is not started.
3. **`NoetherianAlgebraizationQS`** (`ChartQSAsmFinal.lean:33`): `ChartQSAlg.noetherianAlgebraization_of_localModel` reduces it to `LocalModelStep`, which is still open.
4. **`StrataOverQS`** (`ChartQSAsmFinal.lean:41`): this is `ChartQSIndTheta`, blocked on the `cmp_n` slowdown, followed by Inst and Charts in `scratchpad\qsi\wip`.

## Build state
- **Stub added:** the sparse build lacks `StacksFrontier/AlgebraicGeometry/Thickenings/Affine` and its input `Limits/AffineFromFiniteSurjective`. I stubbed the 06AD statement, source at `scratchpad\qsasm\stub\StacksFrontier\AlgebraicGeometry\Thickenings\Affine.lean`. The real module exists in the Stacks tree (`Thickenings/Affine.lean:39`) and must be added to the build.
- **Oleans:** they are in `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\cma\ov\AlgMag\`. I also recompiled `ChartQSStratPoint`, `ChartQSStratOrbit` and `ChartQSStratCore` into that overlay.
- **Compile script:** `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\qsasm\k.sh`.
- **`AlgMag.lean`:** I appended `import AlgMag.ChartQSAsmFinal`.