# Chart lemma for quasi-separated X: repair of the sketchy steps (2026-11-06, 22:30)

Pure mathematics, written for a Lean agent. Own argument, no independent read. Conventions as in
`chart-qs-proof.md`: G = D(M) over Z, X a quasi-separated algebraic space of finite type over Z
(after the reduction (R) of `thm68-ii-proof.md` §1), noetherian. "qs" = quasi-separated. Standing
fact used throughout, with no separatedness:

**(Q) Pullbacks of the diagonal.** For W affine (or any qc scheme) and two points p, q ∈ X(W), the
equalizer E := W ×_{X ×_Z X} X → W is representable by a scheme, a monomorphism, locally of finite
type (Δ_X is lft for X lft over Z) and quasi-compact (Δ_X is qc because X is qs). Hence E → W is
separated, quasi-finite, of finite type, so by Zariski's Main Theorem (Stacks 05K0, number from memory)
it factors as an open immersion E → P followed by a finite P → W. W affine ⇒ P affine ⇒ **E is
quasi-affine**: E → Spec Γ(E) is an open immersion with quasi-compact image, and E is a finite union
of principal affine opens D(f_i) ⊂ Spec Γ(E), each affine. In Lean, `isQuasiCompact_of_comp_of_
isQuasiSeparated` (stub, Morphisms/QuasiCompact.lean:139) gives the quasi-compactness. For X
separated, E is affine (closed in W); this is the ONLY thing `exists_pull`
(ChartPointL11Image.lean:91) and `ChartDeligneCore.ChartOf` use. All uses below are local on E, so
"E affine" is replaced everywhere by "E = ⋃ D(f_i), finitely many affine opens, each with its ring".

Named hypothesis for the Lean, if ZMT for schemes over an affine base is not in the tree:
`Prop QuasiAffineEqualizer X := ∀ W affine, ∀ p q ∈ X(W), E(p,q) is quasi-affine` (Stacks 05K0 +
03GH-type lemma "quasi-finite separated over affine ⇒ quasi-affine"; tag numbers from memory).

## 1. Lemma 1.1 with O ×_X U quasi-affine

Statement (unchanged): o : O = Spec k[Z_0] → X the orbit monomorphism; after replacing X by a
G-stable open containing x, o is a closed immersion.

Where the Lean route used `exists_pull hsep` (ChartPointL11Generic:77,198; L11Local:197,198;
L11Image:243; L11Stable:59): each time the fibre product E = O ×_X U (or of two points of X over
affine schemes) was taken affine. Replacement, step by step, with (Q):

1. o is quasi-compact: O affine, X qs (stub `isQuasiCompact_of_comp_of_isQuasiSeparated`). So the
   scheme-theoretic image Y of o exists and is computed on an étale affine cover V → X by the
   scheme-theoretic image of the base change E = O ×_X V → V (stub
   `schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact'`). Here E is the
   pullback of Δ_X along (o ∘ pr_1, pr_2) : O ×_Z V → X × X, so by (Q) E is a quasi-affine scheme,
   E = ⋃_{i ≤ n} D(f_i) with D(f_i) = Spec A_i affine; the scheme-theoretic image of E → V is
   V(∩_i ker(Γ(V) → A_i)) (image of a qc morphism from a finite union of affines: the kernel of
   Γ(V) → ∏ A_i).
2. Generic point argument (§1 of `ahr-specialized-proof.md`): a generic point η of O over a generic
   point y of Y, A = O_{Y,y} → B = O_{O,η}; this is a statement about local rings of E at a point
   lying in some D(f_i), i.e. about the ring A_i and a prime of it. Injectivity: the kernel of
   Γ(V) → A_i lies in ∩_i ker, which defines Y. Nothing changes.
3. Flatness at η, openness of the flat locus in O, G-stability, transitivity of G on O: unchanged
   (all on O and on E locally).
4. Flat f.p. monomorphism is an open immersion: for o itself (Stacks 025G); flatness and f.p. of o
   are checked on E → V, i.e. on each D(f_i) → V.
5. Remove the closed G-stable set |Y| \ |O| from X.

So Lemma 1.1 holds for qs X. For Lean: restate `exists_pull` as
`exists_pull_qs : ∃ E e₂ e₁, QuasiAffine (SCH.map e₁) ∧ IsPullback ...` (or: ∃ finite family
E_i affine over Z, jointly covering E), and push "affine" → "finite affine cover" through the six
call sites; each call site uses only sections over E, rings of affine opens, and the pullback square.

Tower (`exists_affine_thickening`, `isAffine_relation`, ChartTowerChart:276,367): same replacement.
Thickenings X_n of the affine closed O ⊂ X are affine by Stacks 07VT (any algebraic space), so §2 of
the specialized proof is untouched; only the relation V ×_X V of a chart is quasi-affine, not affine.

## 2. Step 5: Lemma 4.2 for qs X

**Error in `chart-qs-proof.md` Step 5.** The sketch "X \ closure(pr_1 F) is dense, stable and
separated" is false as a method: an open U ⊂ X with Δ_U(U) closed in U × U need not be separated.
Example: X = A^1_k / R, char k ≠ 2, R = Δ ∪ {(x, −x) : x ≠ 0} (Knutson's qs, non-locally-separated
space). R is closed in A^1 × A^1 (its closure adds (0,0) ∈ Δ), so Δ_X(X) is closed in X × X, but X is
not separated (R → A^1 × A^1 is not a closed immersion: as a scheme R = Δ ⊔ (antidiagonal \ 0)).
"Closed image ⇒ closed immersion" needs Δ_U to be an immersion, i.e. U locally separated, which a qs
X is not in general. Do not use that route.

**Route to use (reviewed correct in `thm68-ii-review.md`, "§4.4 Claim correct at each step").**
Keep the Lean route (Stacks 04S6 quotient, `ChartStratum.affineStratum`, ChartStratum.lean:47) and
replace its two uses of separatedness:

(a) `exists_stabIdeal` / `exists_generic_stabilizer` (ChartStratumStab.lean:31,214), which call
`Chart.exists_eqLocus hsep` to get the stabilizer as a CLOSED subscheme of D(M) × V. For qs X the
stabilizer Stab_V = (D(M) × V) ×_{X × X} X is, by (Q), a quasi-affine scheme, a subgroup scheme of
D(M) × V over V, of finite type over V. Replacement = Claim of `thm68-ii-proof.md` §4.4, restated:

> **Claim.** V integral affine noetherian, p ∈ X(V), K = κ(η). There are a nonempty open V' ⊂ V and
> Z ⊂ M with Stab_{V'} = D(M/Z) × V' as subfunctors of G × V'.

Proof: as in §4.4 (generic flatness; (⊆) Stab_V ⊂ D(M/Z) × V by flatness over the integral V;
(open) Stab_V → D(M/Z) × V is a finite-type monomorphism, ZMT gives an open immersion into a finite
scheme which equals D(M/Z) × V after shrinking V; (=) T_0 × F_{p'} × F_p decomposition). The output
"Stab_{V'} = D(M/Z) × V' as subfunctors" is exactly the iff that `hmul_of_stabIdeal`, `OrbitLocal`,
`descAction_free` consume, so nothing downstream changes. Inputs: SGA 3 VI_B 1.4.2 (monomorphism of
f.t. group schemes over a field is a closed immersion; used only for Stab_K ⊂ G_K closed, and that
gives Stab_K = D(M/Z)_K by SGA 3 VIII 3.2), generic flatness (EGA IV 6.9.1 / Stacks 051S), ZMT.
Named hypotheses for Lean: `Prop GenericStabilizerQS` (the Claim), or more finely
`Prop ClosedSubgroupOfDiagonalizable_field` (SGA 3 VI_B 1.4.2 + VIII 3.2) and
`Prop GenericFlatness`.

(b) `affineStratum` passes `hsepR : IsSeparatedOver R` (ChartStratum.lean:82–83, 99) into
`exists_stable_affine_of_chart`: R = D(Z) × Y → Y ×_Z Y must be quasi-compact for the 04S6 quotient
Q = Y/R to be qs. That is `ChartStratumQS.isQuasiSeparated_quotient` (ChartStratumQS.lean:79, being
written by a peer): the base change of Δ_Q along Y × Y → Q × Q is R → Y × Y, quasi-compact since R is
qc (D(Z) affine, Y qc) and Y × Y is qs. So Q is qs, decent (stub `isDecentSpace_of_
isAbsolutelyQuasiSeparated`), has a dense open subscheme (stub `exists_denseRange_isRepresentable_
isOpenSubspace_of_isDecentSpace`), hence a nonempty affine open; the torsor D(Z) × Y → Y over it is
affine (07SQ/fpqc descent) and 07VT returns a G-stable affine open of X. Every step from 3 to 8 of
the Lean route is stated for qs X already (review, §4.4 "Lean route (04S6)").

Output: a nonempty G-stable AFFINE open U ⊂ X, which is Lemma 4.2 itself; no dense separated open is
needed anywhere. (A dense G-stable separated open does not exist in general for the purpose stated in
Step 5: one needs only nonempty, since Theorem 4.1 is a noetherian induction on G-stable closed
subsets; and "nonempty stable affine open" is what every stratum needs.)

Named hypothesis so the pieces compose: `Prop AffineStratumQS X act := X ≠ ∅ → ∃ U ⊂ X open,
G-stable, nonempty, affine`, with hypotheses (hX : IsAlgebraicSpace) (hqs : IsQuasiSeparated)
(noetherian, f.t. over Z) only.

## 3. The Deligne block (review gap 4): equivariance of χ from the induction

Setting (Lemma 4.3/4.4, Glue): a = ω(J) ⊂ C, T^(k) = Spec C/a^k, χ_k : T^(k) → Z^(k) ⊂ X. The Lean
`chi_univ` (ChartDeligneCompat.lean:107) proved χ equivariant by `Chart.eq_of_agree_of_iInf hsep` on
G × T^(k), which (review gap 4) is neither a complete pair nor noetherian-with-a-in-the-radical, and
needs X separated. Replacement, in two parts.

**(i) χ_k is equivariant by construction (Lemma 4.4).** Theorem 4.1 is proved by noetherian
induction on G-stable closed subsets of |X|, "for all closed G-stable structures at once", and its
STATEMENT includes "φ equivariant". The induction hypothesis is applied to the complete pair
(C/a^k, m) (Lemma 3.3) and the G-stable closed subspace Z^(k) = V(J^k) (J is G-stable, G flat, so
J^k is G-stable, and Z^(k) is G-stable with |Z^(k)| = |Z| ⊊ |X|), with the system
φ_n | Spec C/(a^k + m^n) : these maps land in Z^(k) because a_n^k = φ_n^*J^k is 0 on C/(a^k + m^n),
and they are equivariant as restrictions of equivariant maps to G-stable closed subschemes. The
induction returns χ_k : T^(k) → Z^(k) EQUIVARIANT. Compose with the equivariant closed immersion
Z^(k) → X. So equivariance of χ_k is an output, not a lemma: in Lean this is the field of
`ChartQS.OpenStratumMap` (chart-qs-proof.md, third pass), and `chi_univ` becomes vacuous: state it
as `theorem chi_univ' (hequiv : IsEquivariant χ) : X.map t'.op χ = smX ... := hequiv ...` (no hsep).

**(ii) Compatibility in k, and restriction to the m-thickenings**, where `le_idl_chi`, `le_idl_theta`
(ChartDeligneCompat:165,214) and ChartDeligneTheta use hsep. Two equivariant points of X on
T^(k) (a complete pair) agreeing on all V(m^n) are equal: `ChartQS.thm41_unique_equivariant`
(ChartQSEquivUnique, compiled, any algebraic space). Apply it to χ_{k+1} | T^(k) and χ_k: both are
equivariant (restriction of equivariant to the G-stable closed T^(k) ⊂ T^(k+1)), and both restrict
on V(m^n) ∩ T^(k) = Spec C/(a^k + m^n) to φ_n | (same object), so they agree. Likewise
χ_k | V(m^n) = φ_n | T^(k) ∩ V(m^n): both equivariant on the complete pair (C/(a^k + m^n), m), and
equal on every V(m^j) (trivially for j ≥ n). Equalities of maps INTO AN OPEN U ⊂ X, e.g. the Lemma
4.3 formula on D(g) ⊂ T^(k): a map W → X factors through the open subspace U iff the open
U ×_X W equals W (no separatedness; "factors through U" is a statement about an open of W), and
two maps W → U are equal iff equal as maps W → X (U → X is a monomorphism). U affine: the equalizer
of two maps W → U is a closed subscheme of W, so "agree on a dense open and on all V(m^n)" is
checked by the Krull/torsion argument of Step 1 of `chart-qs-proof.md` inside the affine U, with no
condition on X.

**(iii) θ on T̂.** θ : Spec Ĉ → X comes from Step 4 (noetherian algebraization, qs X). θ^{-1}(U) = V
by Nakayama (statement about the open θ^{-1}(U) ⊂ T̂, no separatedness), and θ|_V = τ|_V as maps to
the AFFINE U: both given by the Lemma 4.3 formula with the same f.g. modules (Lemma 3.4 uniqueness
over C/a^k); the equalizer is closed in V, contains ... — this is the argument of the specialized
note, inside U, unchanged. `le_idl_theta` is the ideal-theoretic form; its hsep is only to make
Z ×_X V affine (ChartOf) and goes away with the finite affine cover of (Q).

So the Deligne block for qs X = ChartDeligneCore with `ChartOf` replaced by a finite affine cover of
the quasi-affine Z ×_X V (take the maximum of the torsion exponents over the finitely many affine
pieces, as in `thm68-ii-proof.md` §4.5), plus `chi_univ'` as above, plus `thm41_unique_equivariant`
in place of `eq_of_agree_of_iInf`. Named hypothesis: `Prop StrataOverQS` = the output of the block
(`ChartQS.StrataOver`), to be assumed by the effectivity file until the block is rewritten.

## 4. Globalization without X separated (review gap 5)

`SpacesLimitThm68.exists_charts_at` (lines 171–221) uses hsep at:
- line 186–189: to derive `IsQuasiSeparated (toT1 X)` for `isFinitePresentation_toBase` (the
  G-stable qc open W ⊂ X over the affine open S_i ⊂ S is of finite presentation over S_i). For qs X
  this is the hypothesis itself: W qc open of a qs lfp space is qcqs, lfp ⇒ f.p. (Stacks 03KR-type).
  Replace `Space.isQuasiSeparated_of_isSeparated ... hs` by `hqs` directly.
- line 190: `isSeparated_toBase hsep hL`: the model X_0 → S_0 (S_0 of finite type over Z, W = X_0
  ×_{S_0} S_i, from stub `exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits`) is
  made separated via stub `exists_isSeparated_mapAt_of_siteContainsBaseChangeLimits`
  (SeparatedMorphismDiagonalDescent.lean:246). For qs X one needs the qs analogue: **X_0 can be
  chosen quasi-separated** (then the chart lemma over Z for qs X_0 applies, its charts pull back to
  W, affine over S_i, hence over S when S is separated).

  Proof of the qs analogue, if no Stacks statement is in the tree (grep `IsQuasiSeparated` +
  `mapAt`/`siteContainsBaseChangeLimits` in StacksFrontier first; Stacks "Limits of Spaces", descent
  of quasi-compactness of the diagonal, tag from memory 084V-neighbourhood, unverified):
  Δ_{X_0} : X_0 → X_0 ×_{S_0} X_0 is lfp (X_0 lfp over S_0) and X_0 ×_{S_0} X_0 is qc; its base change
  to S_i is Δ_W, quasi-compact. By the limit lemma for the property "quasi-compact" of a morphism of
  finite presentation between qc spaces along S_i = lim of f.t. S_j → S_0 (Stacks, Limits of Spaces,
  "quasi-compact descends", 07SU-neighbourhood, unverified), Δ_{X_j} is qc for some j, i.e. X_j is qs;
  rename X_j =: X_0.
  Fallback proof avoiding that lemma: W has an étale affine presentation V → W with
  R = V ×_W V a quasi-affine scheme (by (Q): R is the pullback of Δ_W, qc mono over V ×_{S_i} V affine)
  with R → V étale, s, t, composition etc. all of finite presentation. Descend (V, R, s, t, c, e, i)
  to S_0 as (V_0, R_0, ...) with V_0 affine f.p., R_0 quasi-affine f.p. (quasi-affine descends in
  limits, Stacks 01ZT-type), s_0, t_0 étale, and the groupoid identities holding (equalities of
  f.p. morphisms descend, stub `eventually_eq_of_baseChange_eq_...`). Then X_0 := V_0/R_0 is an
  algebraic space (étale equivalence relation, Stacks 04S6 / stub `bootstrap04S6QuotientSheaf`),
  with R_0 → V_0 × V_0 quasi-compact (R_0 qc, V_0 × V_0 affine), so X_0 is qs, and X_0 ×_{S_0} S_i = W
  because quotients commute with flat base change (base change of the groupoid is the groupoid of W).
- The action: descends to X_0 as before (the action map and its axioms are f.p. morphisms,
  `eventually_eq_...`); nothing used separatedness there.
- lines 233, 252, 257, 279: `hsep` is only passed through; replace by `hqs : IsQuasiSeparated`.
  `[S.IsSeparated]` stays (review gap 2: needed for the S-affine clause, since the chart is affine
  over the affine open S_i and S_i → S is affine iff S separated). `thm68_ii_of_charts`,
  `thm68_ii_qc` (SpacesLimitThm68:340,347) consume the resulting `EtaleChartFamily`.

Named hypothesis: `Prop ChartLemmaQS := ∀ X qs of finite type over Spec ℤ with D(M)-action, ∀ x,
∃ affine U, D(M)-action, equivariant étale U → X through x` (the h5 analogue for qs X). The
globalization theorem `exists_charts_at_qs` takes it, plus `Prop QSModelDescends` (the bullet
above) if the Stacks tree has no such statement.

## 5. Remaining places in `chart-qs-proof.md` checked (22:30)

- Step 4: "U a nonempty affine open of X (X qs)": a nonempty qs noetherian space is decent and has a
  dense open subscheme (086U), which has a nonempty affine open. OK. "Deligne (Lemma 4.3,
  non-graded) gives τ : D(b) → U" uses Deligne's formula on the noetherian qs X: for algebraic spaces
  it is proved by étale descent from the affine cover V → X with V ×_X V a qcqs scheme (by (Q)); OK.
  "C/b^l is a-complete": a complete noetherian ring modulo an ideal is complete, OK.
  Stacks 07ST filtration needs X decent: qs ⇒ decent, OK.
- Step 1 "Lemma 4.5" is quoted with R flat over C; the compiled `exists_chart_agree` avoids it. OK.
- Step 3 Krull: I ⊂ ∩ a^k Γ(P) with a in the Jacobson radical of C but Γ(P) is only a C-algebra of
  finite type: Krull's intersection theorem gives "I vanishes on an open containing V(a Γ(P))" only
  after localizing at primes of Γ(P) over V(a), i.e. near V(a) ⊂ Spec Γ(P): that is what is
  claimed, and V(a) ⊂ Spec C is all of Spec C only after the images of the P cover. OK as the Lean
  `eq_of_agree_pow` is compiled.
- "Other items, Lemma 1.1": agrees with §1 above.

## 6. Step 4 (noetherian algebraization) rechecked (22:31): two precisions, no error

- **Output compatibilities must be part of the induction statements.** Claim S(X, Z) must read:
  "... then there is φ : Spec D → X with φ|_{D(b)} = τ and φ|_{V(b^l)} = ψ_l for all l" (and Step 2
  likewise: the glued map restricts to the given f on D(a) and to h on Spec C^). Without the output
  clauses, "these glue to D(c) → X by Step 3" and the compatibility on D^c[1/h] cannot be checked.
  With them: the maps Spec D_h → X and Spec D_{h'} → X agree on D(hh') by the Step 2 EQUALITY
  (`eq_of_agree_basicOpen_of_agree_thickening`, any algebraic space, noetherian ring D_{hh'}):
  both restrict to τ on D(b) and to ψ_l on V(b^l).
- **The hidden sub-step in "on its b-completion both algebraize the same system, Step 3".** Let
  ρ : Spec D^c → W → X be the W-route map and l ≥ 1. Its restriction to V(b^l D^c) is a map on
  Spec (D/b^l)^c (c-adic completion of D/b^l, which is NOT D/b^l in general: D = k[s][[t]],
  b = (t), c = (s, t)). It agrees with ψ_l ∘ (Spec (D/b^l)^c → Spec D/b^l) because both agree on
  every V(c^m) (both are the given map on D/(b^l + c^m) = D/c^m... more precisely on D/(b^l + c^m),
  a quotient of D/c^m, through W) and (D/b^l)^c is noetherian c-complete with c in its Jacobson
  radical: Step 3 with the ideal c. Only then, on the b-completion E of D^c[1/h] (noetherian,
  b-complete, b in the Jacobson radical), ρ|_E and the D_h-route map agree on all V(b^l) (both are
  ψ_l pulled back), so Step 3 with b gives ρ|_E = (D_h-route)|_E. Finally on the noetherian ring
  D^c[1/h] itself: agreement on V(b^l) for all l (just shown), and on D(b) (both land in U by the
  Nakayama argument θ^{-1}(U) = V of the specialized note, and are given by the Lemma 4.3 formula
  there; equality of maps into the affine U), so the Step 2 EQUALITY gives ρ = D_h-route on
  D^c[1/h]. This is what Step 2 (existence) over (D, c) needs.
- The outer induction is on closed subspaces Y ⊂ X (all closed subspace structures on each |Y|);
  the inner one (S) is on closed subsets Z ⊂ |X'| for all open subspaces X' ⊂ X at once, since the
  step passes to X \ Z'. Both are noetherian inductions on closed subsets of |X|.
- Step 2 (several generators) rechecked: (C^{a1})^{(a2..ar)} = C^a for C noetherian (completion is
  transitive, exactness of completion for noetherian rings); D(a1) ⊂ D(a) and D(a') ⊂ D(a) so the
  restrictions of f exist; {D(a') ∩ D(a1) of C1, Spec C^[1/a1]} is an fpqc cover of Spec C1[1/a1]
  (C1 → C^ flat with image containing V(a'C1)). OK.
- Step 1 rechecked: D(u)/g^k is the clopen of Spec((B ⊗_C B)/g^k) with the points of the diagonal
  Spec B/g, hence (idempotents lift uniquely along nilpotent thickenings) equals the diagonal of
  the étale B/g^k over C/g^k, on which the two projections agree. OK. R = C1 ⊗_C C1 is flat over C
  and B ⊗_C B is étale over R. OK.

## 7. Third-pass prose on equivariant uniqueness (checked 22:32): compiled, prose imprecise

`thm41_unique_equivariant` is compiled, so only the wording of `chart-qs-proof.md` is at issue. "The
agreement locus is then an open stable set containing V(m)" is wrong as stated for qs X: the
agreement locus (equalizer E → T) is a quasi-affine subscheme by (Q), not an open. The open set
meant is W := {t : E → T is an isomorphism over a neighbourhood of t}, which contains V(m) by
Lemma M of `thm68-ii-proof.md` (or by the `exists_chart_agree` argument), and whose G-stability is
the flat-descent step of Lemma U ("(g, t) with g·t ∈ W ⇒ t ∈ W" is exactly act^{-1}(W) =
pr_2^{-1}(W)). The sentence "the projection of D(c f) lies in the agreement locus" uses that
stability. Any paper write-up must say W, and prove its stability, as Lemma U does.

## 8. Summary of named hypotheses for composition

| Prop | Content | Replaces |
|---|---|---|
| `QuasiAffineEqualizer X` | equalizers of two points on an affine scheme are quasi-affine (ZMT) | `exists_pull`, `ChartOf` |
| `GenericStabilizerQS` | §2(a) Claim | `exists_generic_stabilizer hsep` |
| `AffineStratumQS X act` | nonempty G-stable affine open, X qs | `affineStratum hsep` |
| `StrataOverQS` | output of the Deligne block, `ChartQS.StrataOver` | ChartDeligne* with hsep |
| `ChartLemmaQS` | chart lemma over Spec ℤ for qs X (h5 analogue) | `h5` in SpacesLimitThm68 |
| `QSModelDescends` | the f.p. model X_0 → S_0 can be taken qs | `exists_isSeparated_mapAt_...` |

Errors found in `chart-qs-proof.md`: Step 5 (§2 above, false method, counterexample A^1/R);
Step 4 and Step 2 statements lack the output-compatibility clauses (§6); third-pass prose (§7).
No error found in Steps 1, 3, 4 (argument), the Lemma 1.1 remark, or the stabilizer remark.
