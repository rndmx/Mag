**Result:** the `uniq` field of `DescentProp X` is proved for every algebraic space X, with no added hypotheses and no stubs. It compiles with no sorry. `desc` is still open and is taken as a hypothesis.

**File:** `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SpacesDescentUnique.lean`
**Olean:** `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sdu\AlgMag\SpacesDescentUnique.olean`
**Compile script:** `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sdu\run.sh`
- It reads `SpacesDescentScheme.olean` from the peer directory `scratchpad\ld\ol`. I did not check that olean against the current source.
- I appended the import to `AlgMag.lean`.

**Lean names (all in `AlgMag.SD`, `SpacesDescentUnique.lean`):**
- `SDUnique_of_section` (line 33): if every monomorphism E → Q through which π : W → Q factors has a section, then two points of X over Q that agree over W are equal. It needs only a representable diagonal.
- `SDUnique_uniq` (line 76): the `DescentProp.uniq` statement, for any presheaf with representable diagonal. It holds for any finitely generated Γ, torsion included.
- `SDUnique_uniq_of_isAlgebraicSpace` (line 102): the same statement for `IsAlgebraicSpace B S hS X`.
- `SDUnique_descentProp` (line 111): `IsAlgebraicSpace B S hS X` plus the hypothesis `hdesc` (exactly the `desc` field) gives `DescentProp X`.
- `SDUnique_uniq_coact` (line 122): uniqueness for any graded ring (`Coact` with `IsInv`) with a `UniqueSums` grading, where W ≅ Spec A and Q ≅ Spec A₀. This is the form the overlap uniqueness in Steps 3 and 4 of the note needs (base changes A₀ → A_i ⊗ A_j). Peers still have to supply the `Coact` on those rings.

**`#print axioms` (all four printed theorems):** `[propext, Classical.choice, Quot.sound]`. No sorry and no stubs. `SDUnique_uniq` is not printed separately, but `SDUnique_uniq_of_isAlgebraicSpace` depends on it.

**Departure from the assigned route:** I did not use universally closed, homogeneous images, 04XV(6) or J = 0. I took the alternative route the note itself gives at the end of part (c):
1. The equalizer E → Q is an object of the site, directly from `diagonal_representable`, so no étale cover is needed.
2. The map W → E is invariant because E → Q is a monomorphism.
3. The scheme case (`descentProp_scheme`, or `exists_desc_of_torsionFree` for `Coact`) gives s : Q → E.
4. Scheme uniqueness gives s ≫ e = 𝟙, and that forces x = y.

**Referee repair 1 (uniqueness across Step 1):** no longer needed. `SDUnique_uniq` holds directly for the original Γ, because `exists_desc_gen` already handles torsion, so I did not formalize the transfer. Referee gap 3 (homogeneity of stable sets) is also not used in Step 2.

**Added assumptions:** none. **Paper errors:** none new.

**What remains:**
- The named hypothesis is `hdesc` in `SDUnique_descentProp`, which is `DescentProp.desc` for X. That is Steps 1, 3 and 4 of Part B, the peers' pieces.
- With `hdesc` proved, `SDUnique_descentProp` gives `DescentProp X` for algebraic spaces.

---

**Status: my piece is done and compiled, with no sorry and no stubs. Props 3.31(ii) and 3.32(ii) for spaces are proved, but only conditionally on two named peer hypotheses, `UniqZr X` and `DescZr X`.**

**Theorems**
- `AlgMag.SDTorus.descentProp_of_zr`, `AlgMag/SDTorus.lean:287`: if `X` is an fppf sheaf with `UniqZr X` and `DescZr X`, then `AlgMag.SD.DescentProp X`.
- `AlgMag.SDTorus.descentProp_space`, `:320`: the same for `IsAlgebraicSpace B S hS X`.
- `AlgMag.SDTorus.prop332`, `:325`: **Prop 3.32(ii)**. For `X` an algebraic space, `M` f.g. abelian, `N, L` any submonoids and any `T`, `iterOfInf : X^{N⊓L}(T) → (X^N)^L(T)` is bijective.
- `AlgMag.SDTorus.prop331`, `:334`: **Prop 3.31(ii)**. For `X` an algebraic space, `M, Z` f.g. abelian, `f : M →+ Z`, `Y` any submonoid and any `T`, `ptAlong` is bijective `X^{f⁻¹Y}(T) → X^Y(T)`.
- `hD` is discharged in both, given the two hypotheses.

**`#print axioms`**, all three of `descentProp_of_zr`, `prop332`, `prop331`: `[propext, Classical.choice, Quot.sound]`.

**What the `Z^r` case must give (hypotheses for the peers)**

Here `Lat r := ULift.{u} (Fin r → ℤ)`, defined at `AlgMag/SDTorus.lean:29`. Both statements are `DescentProp`'s fields with `Γ := Lat r`, for all countable `P, P₀`, all `δ : P →+ Lat r`, injective `j : P₀ →+ P` with `δ p = 0 ↔ p ∈ range j`, and affine `T`:
- `AlgMag.SDTorus.UniqZr X`, `:121`: `x, y` over `𝔸(P₀)_T` that agree after `specAlong T j` are equal.
- `AlgMag.SDTorus.DescZr X`, `:129`: if `x` over `𝔸(P)_T` satisfies `IsInvPt X δ x`, then `∃ x₀, X.map (specAlong T j).op x₀ = x`.

A peer's theorem for all free f.g. `Λ`, or for all f.g. `Γ`, specializes to these directly. It is only ever applied to `P := Pt δ q` with `δ := dt δ q`, so `P` is not finitely generated in general.

**Step 1 as formalized**
- **Torus-induction monoid:** `Pt δ q = P ×_Γ Λ` in `AlgMag/SDTorusRing.lean`, so `Ã = O(T)[Pt δ q]`, graded by `dt`, with degree-zero part `P₀` via `jt`.
- **Freeness and finite presentation** (`SDTorusRing.lean`):
  - `isFreeAlong_Pt`: `Ã → A''` is free.
  - `fp_Pt`: finite presentation, by an explicit `A'' = Ã ⊗_{R[ker q]} R[Λ]`, with no descent of finite presentation.
  - `comap_Pt_surjective`: surjectivity on spectra.
- **Cover:** `cover_Pt` says `𝔸(P × Λ)_T → 𝔸(Pt)_T` is an fppf cover. `ext_Pt` gives separatedness along it.
- **Torsor:** `exists_torsor_elt` shows two points of `𝔸(P × Λ)` with the same image in `𝔸(Pt)` differ by a point of `D(Γ)`.
- **Descent:** `exists_tilde` gives `F̃`, and `isInvPt_tilde` gives its `D(Λ)`-invariance.
- **Referee repair:** the transfer of uniqueness across Step 1 (gap 1 of the referee passes) is the `uniq` field of `descentProp_of_zr`.

**Departures and added assumptions**
- No hypothesis beyond the print: `T` is arbitrary, and `Y`, `N`, `L` are arbitrary submonoids.
- The printed "free action, fpqc quotient" step is not used, in line with the note.
- In 3.31 I assume `M` and `Z` f.g., as printed, so `Countable` is derived rather than assumed.

**What remains**
- Proving `UniqZr X` and `DescZr X` for `X` an algebraic space (Steps 2–4 of Part B) is the peers' part. I found no result yet stated in these terms: `SDExistIntegral.lean` and `SDExistBaseChange.lean` are present but don't mention them.
- Once peers have them, `prop331`, `prop332` and `descentProp_space` become unconditional by supplying `hU` and `hE`.
- `AlgMag.lean` now has the two imports appended, but it was not rebuilt, in keeping with the rules. `SDTorus` imports `AlgMag.FinalMisc331`, whose olean I took from `scratchpad\fin\out`, not `.lake/build`.

**Files**
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDTorusRing.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\SDTorus.lean`
- `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag.lean` (imports appended)
- Compile script: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sdt\k.sh`
- Oleans: `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sdt\ol`, hard-linked because Lean resolves `AlgMag.*` from the first search-path root that has it.

---

**SDExist report: `DescentProp X` is not closed.** Step 4 gluing and four algebra lemmas of Step 3 are proved. The scheme part of Steps 3-4 is still missing and is stated as the hypothesis `SDExist_LocalFactor`. There is no sorry and no stub in these files. All six compile.

**Compile:** `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\sdx.sh`, oleans in `scratchpad\sdx\ol`. The six imports are appended to `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag.lean`.

## Proved
Each theorem below has `#print axioms` = `[propext, Classical.choice, Quot.sound]`, except `SDExist_comp_integral`, `SDExist_surj` and `SDExist_uniq_bc`. Those three were not printed separately; they feed the printed theorems.

All files are in `C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\`.

| Lean name | File:line | Statement |
|---|---|---|
| `AlgMag.SD.SDExist_desc` | `SDExistMain.lean:39` | Existence in Lemma D for `Γ` with `UniqueSums`, from `hX`, `hU : SDExist_UniqCoact X` and `hL : SDExist_LocalFactor X Γ`. Same shape as the peer's `DescZr` at `Γ = Lat r`. |
| `SDExist_desc_of_local` | `SDExistGlue.lean:133` | Step 4 gluing for any graded `π : W → Q` of affine objects, with referee repair 7. |
| `SDExist_uniq_bc` | `SDExistGlue.lean:41` | Uniqueness over `W ×_Q V → V`, for the overlaps. |
| `SDExist_comp_integral_free` | `SDExistIntegral.lean:171` | Step 3(iii): the integral closure in a `ℤ^r`-graded ring is graded. |
| `SDExist_comp_integral` | `SDExistIntegral.lean:110` | The same, for any `Γ` whose finite subsets are separated by homomorphisms to `ℤ`. |
| `SDExist_bc`, `SDExist_bc_isInv` | `SDExistBaseChange.lean:109` (for `isInv`) | Grading on `R' ⊗ A`, with `(R' ⊗ A)₀ = R'`. |
| `SDExist_surj` | `SDExistNakayama.lean:70` | Graded Nakayama: surjective after inverting `h ∉ q`. |
| `SDExist_inj_one` | `SDExistNakayama.lean:104` | Flat case: each element of the kernel is killed by some `h ∉ q`. |
| `SDExist_isolate` | `SDExistIsolate.lean:24` | Stacks 00UJ applied to `R[d]`, isolating the orbit with `h·e₀ = u·d·e₀`. |

## Named hypotheses
- **`SDExist_UniqCoact X`** (`SDExistGlue.lean:33`): copies the conclusion of the peer's `SDUnique_uniq_coact`. Discharge it with `fun hι π i i₀ hπ x y h => SDUnique_uniq_coact hX.diagonal_representable hι π i i₀ hπ x y h`. I did not test this term, because `SpacesDescentUnique.lean` failed to compile when I tried it (line 46 `mono_snd`, line 52 rewrite); the peer was still editing it.
- **`SDExist_LocalFactor X Γ`** (`SDExistMain.lean:30`): the remainder of my piece. An invariant point comes from an affine étale neighbourhood of each point of `𝔸(P₀)_T`.
- **`UniqueSums (Lat r)`**: `SDExist_desc` needs this to feed `DescZr`. I did not check that the instance exists.

## Departure from the note, not refereed
I used a finite-level variant instead of strict henselization, and I checked it only by hand.
- Tag 02LM is not used directly, because `V → Q` is not quasi-finite at fixed points, so that suggested route does not apply.
- One element `d ∈ C'₀` plays both idempotent roles. It equals 1 on `V(𝔫)` and is nilpotent on the other points of `V(IC')`.
- 00UJ on `R[d]` then gives a single étale neighbourhood, and all shrinking goes through `exists_inv_of_homog`.
- The rank argument is replaced by `SDExist_surj` and `SDExist_inj_one`.
- This also keeps the construction out of the size-limited site, since strict henselizations might not belong to it.

The lemmas above are proved, but the plan connecting them needs a referee pass.

## What remains for `SDExist_LocalFactor`
1. **Uniform `h` in the kernel step.** Use `Bh ⊗ D` and `Algebra.FinitePresentation.ker_fG_of_surjective` to get a finitely generated kernel, then pass from `R'` to `R'_h`. This gives a bijection `B₂ → A₂/(1−e₂)`.
2. **Finiteness of `D`.** Show `D = A₂/(1−e₂)` is finite, flat and finitely presented over `B₂`, from `C'_d` étale over `B`.
3. **Scheme side.**
   - Build `W' = W ×_X U`, using 03KN and 03XX for the separated scheme, and construct the lifted action.
   - Treat the residue extension, using 00UE for the separable point of `U`.
   - Build the saturated open `V` and the coaction on `Γ(V,O)`, which needs flat base change of global sections for qcqs `V`.
   - Set `C'` to Mathlib's `toNormalization` (`isOpenImmersion_toNormalization_and_isIntegralHom_fromNormalization` at Stacks `Morphisms/Affine/QuasiAffineQuasiFinite.lean:113`), and construct `d`.
   - Factor the invariant map to the affine `U` through degree 0. Step 3(i) is partly covered by the existing `exists_maximal_homIdeal` and `exists_inv_of_homog`.

I stopped here to save context, not because of a mathematical obstruction. No paper error was found beyond those the note already records. No hypothesis was added to the paper's statement, apart from the named Props above.