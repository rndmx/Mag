**Finding: the finite-level plan is correct, but the description in round 1 is imprecise and one proved lemma does not fit its use.** I found no mathematical obstruction. There are four real gaps, all repairable (G1–G4). I checked this by hand against the sources and did not compile anything or edit any file.

## The corrected argument
Let (R, q) be a base with A₀ = R, and let A be Z^r-graded.

1. **Orbit.** Let I be the maximal homogeneous ideal over q. Then q·A ⊂ I by maximality, I is prime, and (A/I) localized at q is κ(q)[Λ] with Λ free. The point x̄ : Spec κ(q) → X lifts to an affine étale U over a finite separable κ'/κ(q).
2. **First étale step.** Use 00UE to get R' with prime P and residue field κ'. Set B = R'⊗A and I' = ker(B → κ'[Λ]). This gives the equivariant section s₀ on Spec κ'[Λ]. It is defined only on that locally closed orbit, not on V(I').
3. **V and C'.** Take V = 𝕋·V₀ containing s₀(ξ), with ξ the generic point. It then contains all of s₀(orbit), because a stable open of D(Λ)_κ' is empty or everything. C = Γ(V,O) is graded and C' is its graded integral closure. 𝔫 = ker(C' → κ'[Λ]) is a homogeneous prime over P.
4. **Fibre T.** Set T = C' ⊗_B κ'[Λ], which is the localization at R'∖P of C'/I'C'. Spec T ∩ V is étale over κ'[Λ], and s₀ is a clopen section of it. So V(𝔫T) is clopen in Spec T, and there is an idempotent ε ∈ T₀ with εT = κ'[Λ]. Degree 0 follows as in referee gap 5.
5. **d.** Build d₀ ∈ C'₀ with D(d₀) ⊂ V and d₀ ≡ h mod 𝔫, h ∉ P, as described in G2. Lift ε to d' ∈ C'₀ up to s ∉ P. After inverting h and s in R', put d = d₀d'/(hs). Then d is integral over R', D(d) ⊂ V, d−1 ∈ 𝔫, and d̄ = ε in T₀.
6. **Second étale step.** `SDExist_isolate` gives R'', P'', P', e₀ and h with h·e₀ = u·d·e₀. Set D = e₀·(R''_h ⊗ C'). Then Spec D ⊂ D(d) ⊂ V_R'', so D is étale over B₂ = R''_h⊗A. It is also integral over B₂, hence finite, flat and finitely presented, and it is graded because e₀ has degree 0.
7. **Fibre of D.** Put T'' = κ(P'')⊗T. A prime of T'' has e₀ ∉ it iff it lies over P' (`huniq`) iff d̄ = 1 iff ε = 1. The middle step uses that κ''[d̄] has only one prime with d̄ = 1. Equal support gives e₀ = 1⊗ε in T'', so D⊗_{B₂}κ''[Λ] = κ''[Λ].
8. **Bijection.** G1 and `SDExist_surj` give surjectivity after inverting an invariant. `SDExist_inj_one`, using the prime ker(D → κ''[Λ]), then gives injectivity element by element. A finitely generated kernel makes h uniform, so B₃ ≅ D₃ as graded rings.
9. **Factorization.** O(U) → C lands in degree 0, so it factors O(U) → D₃,₀ = (B₃)₀ = R₃. This gives y on Spec R₃ with y∘π = x, because F∘pr_W = (U→X)∘pr_U on W'.

## Gaps and repairs

**G1 (real): `SDExist_surj` cannot be applied as stated.**
- H1 requires y − b ∈ I·D for every y, with no denominator. The fibre computation only gives this after inverting some s ∉ q, because D/ID is compared with B/I only at q.
- Inverting first forces I, hIq and hmax to be rebuilt on each localized ring.
- **Repair:** weaken H1 to ∃ s ∉ q, ∀ y ∃ b, ι(s)y − b ∈ I·D. Apply Cayley–Hamilton to multiplication by s on M = D/L, using `LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul`. This gives r ≡ ι(s)ⁿ mod I with rM = 0, and r ∉ I by hIq.
- Finding s: M' = D/(L+ID) is finitely generated and killed by P, and M'_P = 0. So s is a product of annihilators of generators.
- Alternatively, define I = ker(B → κ[Λ]) so that it localizes, and prove hmax directly.

**G2 (real, wording): "d is nilpotent on the other points of V(IC')" is false as stated globally, and "1" needs normalizing.**
- V(IC') has points over primes strictly containing P, where nothing is controlled. So d is controlled only on the fibre over P.
- The requirement is d̄ = ε in T₀. Nilpotence on other points of the fibre plus the value 1 on V(𝔫) is also enough for step 7.
- d exists only after inverting h and s in R'. Alternatively, generalize `SDExist_isolate` from d−1 ∈ 𝔯 to d−s ∈ 𝔯 with s ∈ R∖q.
- 𝔞 + 𝔫 = C' is also false at finite level, since it holds only over P. Do not use it. Instead, `comp_mem_of_stable` gives a homogeneous a ∉ 𝔫 with D(a) ⊂ V. Then a ≡ β/s mod 𝔫 with β ∈ B homogeneous and β ∉ I, and `exists_inv_of_homog` gives ι(h) = βb'. Set d₀ = a·b'·s.

**G3 (real, missing from the "remains" list): ε and its properties.**
- εT = κ[Λ] is not covered by any existing lemma. It needs "a section of a separated étale map is clopen", plus `PrimeSpectrum.isClopen_iff`.
- This can be done algebraically: on T[1/d₀] the kernel J of T[1/d₀] → κ[Λ] is finitely generated, and J = J² because the algebra is unramified with a section.
- It is also the only place where the two idempotent roles are actually combined, so it should be its own lemma.

**G4 (real, Lean): site membership.**
- LocalFactor needs V = Spec R₃ as an object of the site, but `SDExist_isolate` gives R' abstractly. A lemma is needed: an étale or finite type R-algebra S has #S ≤ max(#R, ℵ₀), which is below the cutoff (`contains_iff`).
- The same bound handles Spec κ(q) and Spec κ'[Λ] if X is evaluated on them.
- The stated reason for avoiding strict henselization is wrong: #O^sh ≤ max(#R, ℵ₀), so it does fit the site. The real gain is that no limit argument is needed, so Step 4's spreading out disappears. Correct the note.

**Minor points, all routine:**
- **Global sections.** Γ(𝕋×V) = C[Z^r] is flat base change for qcqs V. Since D(d) ⊂ V, also C_d = C'_d. So O(U) → C → C_d = C'_d → D₃ stays algebraic, which avoids comparing actions on non-affine V.
- **R'' base change.** R''⊗C' need not be an integral closure. Only V_R'' → Spec(R''⊗C') open immersion (base change) and integrality over B₂ are used. Use `SDExist_bc` for the grading on R''⊗C', with `hc` for the R'-linear structure.
- **W'.** W' → Spec A × U is a monomorphism, so W' is separated and no 03KN is needed beyond scheme-ness. U must be replaced by an affine open around u₀ before W' is formed. Choose U before R', and take I' as a kernel rather than from a second `exists_maximal_homIdeal`.
- **Generality of statements.** Algebra lemmas must be stated for a general `Coact` with `IsInv`, since after R' the ring is not a monoid algebra. LocalFactor quantifies over all q, and the construction does not use closedness of q.
- **Not checked.**
  - The `UniqueSums (Lat r)` instance. A transfer through ULift and Pi from `TwoUniqueSums` should work.
  - Whether Mathlib has 00UE. If it does not, use R[x]/(f) localized at f' with f a monic lift of a minimal polynomial.
  - The dropped fields of `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, which are not needed.
  - The `IsAlgebraicSpace` atlas definition, because my search was truncated before it. The plan needs an étale surjective family of schemes, or a single scheme, in the site.

**Items that hold as written:**
- `SDExist_isolate`: the proof is valid and h·e₀ = u·d·e₀ is the right output.
- `SDExist_inj_one` is correct. It uses only flatness, surjectivity up to h₁ and a prime over q.
- `SDExist_desc_of_local` matches the shape of `DescZr`.
- `SDExist_UniqCoact` matches the signature of `SDUnique_uniq_coact`, so that discharge should work. This is by reading only, not tested.
- `SpacesDescentUnique` feeds `UniqZr` directly through `AddGroup.FG (Lat r)`.
- `IsInvPt` tests on every T' in the site, including non-affine ones, so the lifted action on 𝕋×W' is available.
- Tag 02LM is rightly avoided.

**Files read:**
- C:\Users\Arnaud\Desktop\algmag-stacks\notes\lemmaD-lean-round1.md
- C:\Users\Arnaud\Desktop\algmag-stacks\notes\prop331-332-spaces-proof.md
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDExistMain.lean
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDExistIsolate.lean
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDExistNakayama.lean
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDExistGlue.lean
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDExistBaseChange.lean
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDExistIntegral.lean (declaration signatures only)
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SpacesDescentUnique.lean
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDTorus.lean (lines 25–149)
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SpacesDescentProps.lean (search excerpts only)
- C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Sec3SchemeQuotient.lean (lines 195–264)

SDTorusRing.lean was not read, and SpacesDescentScheme.lean only as search excerpts.

VERDICT: OK

---

**Result: items 1 and 2 of "What remains for `SDExist_LocalFactor`" are proved and compile.** There is no sorry, no stub and no added axiom. They are purely algebraic, and `SDExist_LocalFactor` itself is not closed.

Every theorem printed below has `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The ones not printed (`SDLocA_exists_equiv`, `SDLocA_etale_bc`, `SDLocA_integral_bc`) feed the printed ones.

**Theorems** (namespace `AlgMag.SD`, files in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`)

| Name | File:line | Statement |
|---|---|---|
| `SDLocA_uniform` | `SDLocABijective.lean:30` | Item 1. Take `B → D` graded, finite, flat and f.p., onto mod the closed orbit `I`, with a prime `𝔯` of `D` satisfying `ι a ∈ 𝔯 → a ∈ q`. Then one `h ∉ q` gives `∀ y, ∃ b, ι h·y = b` and `b ↦ 0 → ∃ n, (ι h)^n·b = 0`. |
| `SDLocA_bijective` | `SDLocABijective.lean:135` | `B_h → D_h` is bijective, stated with `IsLocalization.Away.map`. |
| `SDLocA_section` | `SDLocABijective.lean:185` | There is a ring map `s : D → B_h` under `B`. This replaces "rank 1, so B ≅ D". |
| `SDLocA_corner` | `SDLocAFinite.lean:26` | Item 2, abstract. If `T` is integral over `S`, `T_x` is étale over `S`, `e` is idempotent and `e = u·x·e`, then `T/(1−e)` is étale, finite and flat over `S`. |
| `SDLocA_exists_equiv` | `SDLocAFinite.lean:93` | `(R''⊗B) ⊗_B X ≃ R''⊗X` as `R''⊗B`-algebras. |
| `SDLocA_etale_bc`, `SDLocA_integral_bc` | `SDLocAFinite.lean:117`, `:126` | Base change of étale and of integral along that square. |
| `SDLocA_finite` | `SDLocAFinite.lean:135` | Item 2, concrete. `D = (R''⊗C)/(1−e)` is étale, finite, flat and f.p. over `R''⊗B`, given `C` integral over `B` and `C_x` étale over `B`. |
| `SDLocA_of_isolate` | `SDLocAFinite.lean:172` | Turns the output of `SDExist_isolate` into the input of `SDLocA_finite`, in `R'_h ⊗ C` (`h` here is the element from `SDExist_isolate`). The image of `e₀` is idempotent and `e₂ = u'·(1⊗d)·e₂`. |
| `SDLocA_quot`, `SDLocA_quot_comp`, `SDLocA_span_hom` | `SDLocAMain.lean` | Grading on a quotient by a homogeneous ideal, and `(1−e)` is homogeneous when `e` has degree 0. |
| **`SDLocA_main`** | `SDLocAMain.lean:103` | The form for the scheme-side agent, combining all of the above. |

**`SDLocA_main` (entry point for the scheme-side agent)**

Inputs the scheme side must supply:
- gradings `cB`, `cC` with `R` in degree 0 (`hcB`, `hcC`)
- `B → C` graded (`hBC`)
- `cB.IsInv (algebraMap R B)` (`hιB`)
- `Algebra.IsIntegral B C`
- `Algebra.Etale B (Localization.Away x)`
- `e` idempotent in `R''⊗C`, of degree 0 (`he`, `he0`), with `e = u·(1⊗x)·e` (`hu`; `SDLocA_of_isolate` supplies `he` and `hu`)
- the closed orbit `I` of `R''⊗B` (`hI`, `hIq`, `hmax`; `exists_maximal_homIdeal` should supply these)
- `H1`: `D → B/I` is an isomorphism on the corner, meaning `D` is onto mod `I`
- a prime `𝔯` of `D` over `q`

Output: `h ∉ q`, the two elementwise statements, and `s : D →+* (R''⊗B)_{h⊗1}` under `R''⊗B`. The algebra structure is `SDLocA_alg`, an `abbrev` at `SDLocAFinite.lean` that must be used with `letI`.

**Departures and added assumptions**
- **Rank step:** the note's rank-1 argument is replaced by graded Nakayama plus flatness, continuing the previous round's finite-level variant, which still has no referee pass.
- **Weaker conclusion than requested wording:** the bijection is proved after inverting `h ∈ R''`, not on `B₂` itself. The kernel statement carries a power `(ι h)^n`, because the f.g. kernel lives in the localization. To get a literal bijection, replace `R''` by `R''_h`, which is the note's "pass from `R'` to `R'_h`".
- **Added assumptions:** none beyond the inputs listed above, which the scheme side must supply. No paper errors found.

**What remains for `SDExist_LocalFactor`**
- **Item 3, the scheme side, is untouched.**
  - `W'`, the lifted action, the residue extension and the saturated open `V`.
  - The coaction on `Γ(V,O)`, with `C' = toNormalization` and the element `d`.
  - Factoring through degree 0.
- **New obligations from `SDLocA_main`:**
  - `e` has degree 0 in `R''⊗C`, which should follow from `d` being degree 0, but I did not prove it as a lemma.
  - `C_d` étale over `B`.
  - `H1`, which is the "R = B/I" step of 3(iv). That includes removing the complementary factor from the section on the closed orbit, and it is not done.

**Not verified:** `lake build` was not run, per the rules. The oleans are hard-linked from `scratchpad\sdx\ol`, which I did not check against current sources. I appended the three imports to `AlgMag.lean` but did not rebuild it.

**Files**
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDLocABijective.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDLocAFinite.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDLocAMain.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag.lean` (imports appended)
- Compile script: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sla.sh`
- Oleans: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sla\ol`

---

**Status: item 3 is not finished, so `prop331_space`, `prop332_space` and Prop 15.1 are not unconditional.** They compile but take the hypothesis `hL : SDLocS_LocalFactorAll X`. `SDExist_LocalFactor` itself is not proved, only reduced to the named Prop `SDLocS_InvChart`. There is no sorry, and I used no stubs and no `lake build`.

**Proved in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDFinal.lean`**

| Lean name | Line | Statement |
|---|---|---|
| `SDLocS_uniqueSums_lat` | 28 | `UniqueSums (Lat r)` |
| `SDLocS_uniqCoact` | 35 | discharges `SDExist_UniqCoact X` via `SDUnique_uniq_coact`, for `X` an algebraic space |
| `SDLocS_uniqZr` | 41 | `UniqZr X`, unconditional |
| `SDLocS_descZr` | 49 | `DescZr X`, given `hL` |
| `lemmaD_space` | 54 | `DescentProp X`, given `hL` |
| `prop332_space` | 58 | Prop 3.32(ii), given `hL` |
| `prop331_space` | 65 | Prop 3.31(ii), given `hL` |
| `prop151_space` | 72 | Prop 15.1, given `hL` and `hsep : IsSeparatedOver X` |

- **Named hypothesis:** `SDLocS_LocalFactorAll X` (line 45) means `∀ r, SDExist_LocalFactor X (Lat r)`.
- **Prop 15.1:** `hsep` is inherited from `prop151_of_descent`. I did not re-check it against the print.

**Proved in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDLocSFactor.lean`**

| Lean name | Line | Statement |
|---|---|---|
| `SDLocS_chart` | 32 | `W' = W ×_X U` is a site object, étale over `W`, with its universal property |
| `SDLocS_factor` | 65 | an invariant map from graded affine `W` to any site object `U` factors through degree 0 (it does not need `U` affine) |
| `SDLocS_point_of_factor` | 93 | the same factorization on `X`-points |
| `SDLocS_lift_action` | 104 | the lifted action on `W'`, on points only, with `pr_U` unchanged |
| `SDLocS_localFactor` | 130 | `SDLocS_InvChart X Γ → SDExist_LocalFactor X Γ`, with `UniqueSums Γ` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]` for all of the following:
- `SDFinal.lean`: `lemmaD_space`, `prop332_space`, `prop331_space`, `prop151_space`
- `SDLocSFactor.lean`: `SDLocS_chart`, `SDLocS_lift_action`, `SDLocS_factor`, `SDLocS_point_of_factor`, `SDLocS_localFactor`

Helper results such as `SDLocS_uniqCoact` were not printed separately, but the printed theorems depend on them.

**What remains: `SDLocS_InvChart`** (`SDLocSFactor.lean:117`), for `Γ = Lat r`. I did not state the peer's algebra as a Prop, because `SDLocS_InvChart` already absorbs it and the peer's file is unfinished. These steps are not started:
1. **Orbit point:** show `x` restricted to the closed orbit `k[Λ]` is constant, using the fppf surjection `𝕋 → D(Λ)`. Then lift it to `U` with the residue extension (00UE), taking `U` from `exists_affine_coproduct_atlas`.
2. **Action as a morphism:** turn `SDLocS_lift_action` into a morphism `𝕋 × W' → W'`, and build the saturated open `V = 𝕋·V₀`. It is open because the action map is flat and finitely presented.
3. **Coaction on `Γ(V,O)`:** prove `Γ(V × Spec ℤ[Λ]) = Γ(V)[Λ]` for qcqs `V`. I found no ready flat base change for global sections in Mathlib (only a quick grep; `isPushout_appTop_of_isPullback` is the nearest hit, and I did not read its hypotheses), so this probably needs its own lemma.
4. **`C'` and `d`:** use `toNormalization` for `C'`, check equivariance, construct `d` and connect it to `SDExist_comp_integral_free` and `SDExist_isolate`. Then show `C'_d` is étale, and that `D = A₂/(1−e₂)` is finite, flat and finitely presented.
5. **Assembly:** combine these with the peer's section, then build the base-change presentation `W ×_Q V ≅ Spec(R' ⊗ A)` from the lines in `SDExist_uniq_bc`.

**State of the peer's algebra:** `AlgMag\SDLocABijective.lean` was still being edited and had `sorry` when I read it, so nothing here imports it. Its `SDLocA_uniform` matches the kernel and surjectivity steps. That is why step 5 can reuse it once it compiles.

I stopped here because of the expected size of steps 1–4, not a mathematical obstruction. No paper errors and no added assumptions beyond `hL` and `hsep`. No Stacks module was missing from the sparse checkout.

**Other files**
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag.lean`: the two imports are appended; it was not rebuilt.
- `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sdl\k.sh`: compile script.
- `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sdl\ol`: oleans. `SpacesDescentUnique` was recompiled here against the current source and now compiles cleanly.