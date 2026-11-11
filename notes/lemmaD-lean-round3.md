**Steps 1-2 and gaps G1, G3 are proved and compile, with no sorry and one stated hypothesis; `SDLocS_InvChart` itself is not closed.** That hypothesis is Stacks 00UD, used only in `SDR3Orbit_step2`. Every printed theorem has `#print axioms` = `[propext, Classical.choice, Quot.sound]`. I ran no `lake build`, and I appended my five imports to `AlgMag.lean` but did not rebuild it.

**Proved** (namespace `AlgMag.SD`, files in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`)

| Piece | Lean name | File:line | Statement |
|---|---|---|---|
| G1 | `SDR3Orbit_surj` | `SDR3OrbitNakayama.lean:29` | Weakened H1: `∃ s ∉ q, ∀ y, ∃ b, ι s·y − b ∈ I·D`, by Cayley-Hamilton on `D/B`. |
| G1 | `SDR3Orbit_uniform`, `SDR3Orbit_main` | `SDR3OrbitNakayama.lean:82`, `:199` | `SDLocA_uniform` and `SDLocA_main` under weakened H1. `SDR3Orbit_main` needs `maxHeartbeats 2000000`. |
| G3 | `SDR3Orbit_ker_sq` | `SDR3OrbitClopen.lean:32` | For an unramified algebra with a section, `J ⊂ J²`. |
| G3 | `SDR3Orbit_clopen` | `SDR3OrbitClopen.lean:66` | `π : T →ₐ[K] K`, `π d` a unit, `T_d` unramified and f.p. over `K`. Then there is an idempotent `ε` with `π ε = 1` and `ker π · ε = 0`, so `εT = K`. `T` need not be finite type. |
| Referee step 4 ("degree 0") | `SDR3Orbit_idem_deg0` | `SDR3OrbitClopen.lean:244` | Idempotents have degree 0 for a `UniqueSums` grading. |
| Step 1, graded field | `SDR3Orbit_gradedField` | `SDR3OrbitField.lean:72` | A graded field whose degrees form a free group has a graded augmentation to degree 0. |
| Step 1, `qA ⊂ I` | `SDR3Orbit_q_mem` | `SDR3OrbitField.lean:287` | `q A ⊂ I`, by maximality of the closed orbit. |
| Step 1, closed orbit | `SDR3Orbit_closedOrbit` | `SDR3OrbitField.lean:301` | A residue field `K` of `q` and `φ : A → K`, where `φ` vanishes on a homogeneous element exactly when it lies in `I`. |
| Step 1, kernel | `SDR3Orbit_Ω_ker`, `SDR3Orbit_prime` | `SDR3OrbitField.lean:423`, `:439` | `ker(A → K[Γ]) = I`, so `I` is prime. |
| Step 1, freeness | `SDR3Orbit_lat_free` | `SDR3OrbitField.lean:448` | Subgroups of `Lat r` are free. |
| Step 1, constancy | `SDR3Orbit_const` | `SDR3OrbitPoint.lean:122` | An invariant `x` pulled back along the orbit point `c₀ = c₁·[δ]` over `𝔸(L)_V` is constant. Uses the fppf cover `D(Γ) → D(L)` via `ext_Pt`, with `L` written as `PUnit ×_{Γ/L} Γ`. |
| Step 1, chart | `SDR3Orbit_chart`, `SDR3Orbit_residue` | `SDR3OrbitPoint.lean:171`, `:190` | `W'` is étale and surjective over `V`, and an étale scheme over a field has a point in a finite separable extension. |
| **Step 1, assembled** | **`SDR3Orbit_step1`** | `SDR3OrbitStep.lean:205` | See below. |
| Step 2 | `SDR3Orbit_step2` | `SDR3OrbitStep.lean:150` | Étale `R'` over `A₀` with a prime `P'` over `q` and `τ : R' → κ'`, where `ker τ = P'` and `τ` is compatible with `ρ`. |
| Step 2, ideal | `SDR3Orbit_bcOrbit` | `SDR3OrbitStep.lean:34` | `θ : R'⊗B → κ'` and `I'` taken as a kernel, not a second maximal ideal. It supplies `hI`, `hIq`, `hmax` for `SDR3Orbit_main`. |

**`SDR3Orbit_step1` output:**
- the closed orbit data, and a finite separable `κ'/K`;
- `V' = Spec κ'` in the site, which also proves G4 (site membership) for `Spec K` and `Spec κ'`;
- a chart `f : U → X` and `u₀ : V' → U` with `f(u₀) = x` at the orbit point;
- on `𝔸(L)_{V'}`, `x ∘ c₀ = f(pr ≫ u₀)`, which is the section `s₀` of Step 2;
- `L` as an explicit closure, and `t'`, `c'` tied to `φ`.

**Added assumptions**
- `SDR3Orbit_Stacks00UD` (`SDR3OrbitStep.lean:141`) is the named Prop for `Algebra.exists_etale_liesOver_residueFieldRingEquiv`, stated in one universe. That module's source is in the Stacks package, but no built olean was found for it. To discharge it, build the module and match the universe. It is a hypothesis only of `SDR3Orbit_step2`.
- `hfree` (all subgroups of `Γ` free) is a hypothesis of `SDR3Orbit_closedOrbit` and `SDR3Orbit_step1`. It holds for `Lat r` by `SDR3Orbit_lat_free`.

No paper errors were found. One small correction to the note: constancy needs the fppf cover only because a character of `L` need not extend to `Γ`, as with `L = 2ℤ`.

**What remains for `SDLocS_InvChart`, none of it in this piece**
- Steps 3-9: the saturated open `V`, the coaction on `Γ(V)`, `C'`, `d`, the isolation step, the fibre `e₀ = 1⊗ε`, the bijection and the factorization.
- Three connections to Step 2:
  - a ring-level map `R'⊗A → κ'[OM]` matching `SDR3Orbit_bcOrbit` with the scheme map over `𝔸(L)_{V'}`, which I did not write;
  - replacing `U` by an affine open around `u₀`, since `step1` gives the coproduct atlas point only;
  - finding the `s ∉ q` of weakened H1, which belongs to the fibre step.
- Peer files `SDR3Asm*` and `SDR3Coact*` appeared while I worked, including `SDR3AsmG3.lean` and `SDR3AsmOrb.lean`. I did not read them, so they may overlap G3 and Step 1. There are no name clashes with the `SDR3Orbit` prefix.

**Not verified:** oleans are hard-linked from `scratchpad\sla\ol`, `sdl\ol` and `.lake/build`, and I did not check them against current sources.

**Other files**
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag.lean` (imports appended)
- `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sr3\k.sh` (compile script)
- `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sr3\ol` (oleans)

---

**Result: my piece (Steps 2-3 and G4) is proved and compiles. `SDLocS_InvChart` itself is not closed.** There is no sorry, no stub and no added axiom. Every theorem below has `#print axioms` = `[propext, Classical.choice, Quot.sound]`, printed directly except `SDR3Coact_saturated` as noted. Files are in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`, namespace `AlgMag.SD`.

**Entry point for peers: `SDR3Coact_main` (`SDR3CoactMain.lean:32`).**
- **Inputs:**
  - `Z` in the site with `AAction Λ (yoneda Z)`
  - `r : Z → W` with `W` affine
  - `Λ` countable and finitely generated
  - `U₀` a quasi-compact open of `Z`
- **Output:**
  - `Vo` in the site and an open immersion `k : Vo → Z` with `U₀ ⊆ range k`
  - the restricted action on `Vo`, compatible with `k`, and `Vo` quasi-compact
  - a `Coact Γ(Vo) Λ` with `Σ π^*(y_d) χ^d = a^* y`

**Other theorems**

| Name | File:line | Statement |
|---|---|---|
| `SDR3Coact_liftAction` | `SDR3CoactLift.lean:69` | Step 2: `x` invariant gives an `AAction` on `W' = W ×_X U`, lifting `g^δ c` on `W`, with `W' → U` unchanged |
| `SDR3Coact_a` | `SDR3CoactSite.lean:78` (def) | Step 2: the action as a morphism `D(Λ) × Z → Z` |
| `SDR3Coact_sat` | `SDR3CoactSite.lean:153` | `V = a(π⁻¹U₀)` satisfies `a y ∈ V ↔ π y ∈ V`, via the scheme-level `SDR3Coact_saturated` (`SDR3CoactRing.lean:122`) |
| `SDR3Coact_isOpen_sat` | `SDR3CoactSection.lean:134` | `V` is open (`π` is flat and lfp, `a = ι ≫ π`) |
| `SDR3Coact_isCompact_sat` | `SDR3CoactSection.lean:162` | `V` is quasi-compact |
| `SDR3Coact_restrict` | `SDR3CoactLift.lean:103` | A saturated open is a site object with the restricted action |
| `SDR3Coact_φ_bijective` | `SDR3CoactGamma.lean:94` | Step 3: `Γ(V)[Λ] → Γ(π⁻¹V)` is bijective for `V` quasi-compact |
| `SDR3Coact_base_bijective` | `SDR3CoactBase.lean:61` | The affine case, for a base change of `Spec A[Λ] → Spec A` |
| `SDR3Coact_ofRing` | `SDR3CoactRing.lean:40` | Counit and coassociativity, read on `Γ(Y)` and `Γ(Y₂)`, give a `Coact` |
| `SDR3Coact_coact` | `SDR3CoactSection.lean:55` | The coaction on `Γ(Z,O)` for `Z` quasi-compact |
| `SDR3Coact_isHom_zero` | `SDR3CoactLift.lean:168` | Step 9 input: `a ≫ s = π ≫ s` puts `s^*y` in degree 0 |
| `SDR3Coact_contains_of_lft` | `SDR3CoactAffine.lean:88` | G4: locally of finite type with quasi-compact source over a site scheme is in the site |
| `SDR3Coact_contains_of_finiteType` | `SDR3CoactAffine.lean:93` | G4 for algebras: a finite type (for instance étale) `R`-algebra is in the site |

`SDR3Coact_saturated` compiled with the printed axiom list above. It was printed in `SDR3CoactRing.lean`.

**Departures from the note**
- **Weaker hypothesis:** Step 3 needs only quasi-compact `V`, not qcqs. `ℤ[Λ]` is free, so the components are sections of `O` and no equalizer argument is needed. This proves more than the note asked, so no flat base change stub was used.
- **G4 for `Spec κ(q)`:** I did not write a separate lemma for this. `BigFppfSite.residueField_spec_contains` already exists and is used in `AppendixA.lean:336`. `Spec κ'[Λ]` follows from `contains_of_finiteType`. For a saturated open, `SDR3Coact_restrict` uses `contains_of_mono`.

No added assumptions beyond the inputs listed, and no paper errors found.

**What remains for `SDLocS_InvChart`** (`SDLocSFactor.lean:117`), not in my piece and not stated as named Props:
1. Step 1: the orbit point, the lift to `U` and 00UE.
2. The graded map `B → Γ(V)`. `p : W' → W` must be shown equivariant at the level of `Coact`, i.e. `SDExist_IsGraded`. `SDR3Coact_liftAction` gives equivariance on points only.
3. Steps 4-8: `C'` via `toNormalization`, `T`, `ε` (G3), `d` (G2), the second étale step, the fibre of `D`, and the bijection with the G1 repair.
4. Step 9 assembly into the exact `SDLocS_InvChart` shape, with `SDR3Coact_isHom_zero` as input.

**Verification notes**
- `lake build` was not run.
- Each file compiled with `lean -o`, in dependency order.
- `grep` finds no sorry, axiom or `native_decide` in `SDR3Coact*.lean`.
- `import AlgMag.SDR3CoactMain` is appended to `AlgMag.lean`, which I did not rebuild.

**Files**
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDR3CoactGamma.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDR3CoactRing.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDR3CoactAffine.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDR3CoactBase.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDR3CoactSite.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDR3CoactSection.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDR3CoactLift.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDR3CoactMain.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag.lean`
- Compile script: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sr3.sh`
- Oleans: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sr3\ol`

---

**Status: `SDLocS_InvChart X (Lat r)` is proved conditional on one named Prop, `SDR3Asm_ChartInput X r` (Steps 1-3).** It is not proved unconditionally. `hL` in `prop331_space`, `prop332_space` and `prop151_space` is discharged on the same condition. There is no sorry or axiom in my files, and every file compiled with `lean -o`, with no `lake build`.

`#print axioms` is `[propext, Classical.choice, Quot.sound]` for `SDR3Asm_closure`, `SDR3Asm_assemble`, `SDR3Asm_invChart`, `SDR3Asm_localFactorAll`, `SDR3Asm_prop331`, `SDR3Asm_prop332` and `SDR3Asm_prop151`.

**Final theorems (`AlgMag/SDR3AsmFinal.lean`)**

| Statement | Lean name | Line | Hypotheses |
|---|---|---|---|
| Base-change presentation `W ×_Q V ≅ Spec(R₃ ⊗_{R'} (R' ⊗_R A))`, `g`, its invariance and the `X`-identity | `SDR3Asm_assemble` | 44 | Data of Steps 4-9 |
| Outcome of Steps 1-3 at a point | `SDR3Asm_Data` | 157 | Definition |
| The named input | `SDR3Asm_ChartInput` | 182 | Definition |
| `SDLocS_InvChart X (Lat r)` | `SDR3Asm_invChart` | 193 | `SDR3Asm_ChartInput X r` |
| `hL : SDLocS_LocalFactorAll X` | `SDR3Asm_localFactorAll` | 225 | `∀ r, SDR3Asm_ChartInput X r` |
| Prop 3.32 (ii) | `SDR3Asm_prop332` | 229 | `hX` and the input |
| Prop 3.31 (ii) | `SDR3Asm_prop331` | 236 | `hX` and the input |
| Prop 15.1 | `SDR3Asm_prop151` | 243 | `hX`, `hsep` and the input |

**Steps proved (all in `AlgMag/`)**

| Step | Result | Lean name | File:line |
|---|---|---|---|
| 4 | Graded integral closure, via `SDExist_comp_integral_free` | `SDR3Asm_closureCoact` | `SDR3AsmAlg.lean:108` |
| 4 | `𝒱 → Spec C'` is an open immersion, from `toNormalization` at `⊤` | `SDR3Asm_zmt` | `SDR3AsmZMT.lean:42` |
| 4 | Section over `D(a)` | `SDR3Asm_section` | `SDR3AsmOpen.lean` |
| 4 | `C_a = C'_a` | `SDR3Asm_torsion` | `SDR3AsmOpen.lean:74` |
| 4 | Equivariance: `V` is stable in `Spec C'` | `SDR3Asm_stable` | `SDR3AsmStable.lean:39` |
| 5 (G2) | Element `d₀` | `SDR3Asm_d₀` | `SDR3AsmAlg.lean:122` |
| 5 (G3) | `ε` lifted to `d'` of degree 0, using the peer's `SDR3Orbit_clopen` | `SDR3Asm_G3` | `SDR3AsmG3.lean:156` |
| 6 | `SDExist_isolate` with `d − c`, `c ∉ q` | `SDR3Asm_isolate` | `SDR3AsmIso.lean:26` |
| 7 | The two idempotents agree on the fibre, argued elementwise | `SDR3Asm_star` | `SDR3AsmFib.lean:49` |
| 5-9 | Algebraic form, through the peer's `SDR3Orbit_main` | `SDR3Asm_alg` | `SDR3AsmMain.lean:151` |
| 4-9 | Package for an abstract `D` | `SDR3Asm_pkg` | `SDR3AsmPkg.lean:64` |
| 4-9 | Package for `𝒱 → Spec B` | `SDR3Asm_closure` | `SDR3AsmPkg.lean:260` |

**What remains: discharge `SDR3Asm_ChartInput`.** It has not been connected to the peers' files `SDR3Orbit_step1`, `SDR3Orbit_step2`, `SDR3Orbit_bcOrbit` and `SDR3Coact_main`. The fields of `SDR3Asm_Data` still needing a bridge are:
1. **Section `s₀`.** It must be over `Localization T` with `T` the image of `R' ∖ P'` in `(R'⊗A)/I`, and I need `I` prime. The peers give the section on `Spec κ'[L]`, so this needs `(B/I')_{P'} ≅ κ'[L]`, plus `SDR3Orbit_prime` for `I'`.
2. **`SDR3Asm_ActsOnPoints cV`.** This is the action on field-valued points read on `Γ(𝒱)`. It should follow from `actV` and the `SDR3Coact_lift` identity in `SDR3Coact_main`.
3. **Grading compatibility `hV`** between `cV` and `SDExist_bc`.
4. **`Etale f` and `IsSeparated f`** for `𝒱 → Spec(R'⊗A)`, using the monomorphism `W' → Spec A × U`.
5. **`ψ` data.** Degree 0 should follow from `SDR3Coact_isHom_zero`; also needed are `U` affine and the `hX` compatibility from `SDLocS_chart`.

The peers' `SDR3Orbit_step2` also depends on their named Prop `SDR3Orbit_Stacks00UD`, and bridging item 1 inherits it.

**Departures from the referee's text and caveats**
- **Added assumptions:** none beyond `SDR3Asm_ChartInput` (`hX` and `hsep` are as in `SDFinal`). No paper errors found.
- **`d'` (G3):** it is taken as the degree 0 part of a lift in `C'`, so no grading on `T` is needed. The peers' `SDR3Orbit_idem_deg0` is used only for `e`.
- **Step 7:** it runs with an ideal and a multiplicative set instead of `κ'' ⊗ T`. The closed orbit is chosen above `P₂B + (R₂ ⊗ I)` by `SDR3Asm_orbit_above`.
- **Peer dependency:** my files import the peers' `SDR3OrbitNakayama`, `SDR3OrbitClopen`, `SDR3OrbitField` and `SDR3CoactAffine`. I compiled against the peers' oleans as of about 23:50, not rebuilt from their current sources.
- **Heartbeats:** `SDR3Asm_alg` uses `set_option maxHeartbeats 2000000`.
- **`AlgMag.lean`:** the 11 imports are appended, but it was not rebuilt.

**Files (in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`)**
- `SDR3AsmAlg.lean`
- `SDR3AsmFib.lean`
- `SDR3AsmIso.lean`
- `SDR3AsmOrb.lean`
- `SDR3AsmMain.lean`
- `SDR3AsmG3.lean`
- `SDR3AsmZMT.lean`
- `SDR3AsmOpen.lean`
- `SDR3AsmStable.lean`
- `SDR3AsmPkg.lean`
- `SDR3AsmFinal.lean`

Other paths:
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag.lean`
- Compile script: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sra\k.sh`
- Oleans: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sra\ol`