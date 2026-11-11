**Result:** the core mathematics held up, namely the chart lemma for quasi-separated X, and hence the family when S is separated. The note as written is not acceptable: one step is false, one claim is too strong, and its map of Lean changes is wrong in places.

## Checked at source
- **AHR arXiv text, dated Mar 28 2025 (taken as the note's v4):** Thm 10.1 and Cor 10.2 say what the note claims, with X and S quasi-separated. Thm 1.1 also matches.
- **Bhatt, arXiv:1404.7483:** Thm 1.1 and Thm 1.4(1) match, stated for qcqs algebraic spaces. T̂ → T is flat, so the Tor condition holds.
- **Print:** I read the Thm A.2 proof, Def 6.1 and the vote 10 entry of `corrections-verified.md`. The p. 158 wording of Thm 6.8 I saw only as quoted in that entry, and I did not open the page images.

## Steps that survived
- **Lemma M (a)–(d):** correct. In (c) the kernel lies in every J^kÂ, because Â → B̂ → Â/J^k is the quotient map.
- **Corollary M′:** correct.
- **Lemma U:** correct. The riskiest step has a shorter proof: the étale locus is compatible with flat base change, and both `α` and `pr_2` are flat, so `α⁻¹W = pr_2⁻¹W`.
- **§4.1:** correct, subject to the SGA 3 number being unchecked.
- **§4.4 Claim:** correct at each of its steps (⊆, open, =).
- **Gerbe route:** quasi-compactness of `Δ_Q` follows because `𝒰 → 𝒰 ×_Q 𝒰` is surjective.
- **Unchanged in substance:** Lemma 1.1, the proof of Lemma 4.3 on paper, compatibility on V, the Shrinking Lemma, and limit preservation in §5.

## Tests on the line with doubled origin
| Action | Stabilizers | Result |
|---|---|---|
| G_m, weight 1 | origins fixed | Each origin gets its own A¹ chart with C = k[t]. Lemma U is consistent, since the two branches differ on V(t). |
| G_m, trivial | everything fixed | Stratum G_m, then induction on the origins. No problem. |
| μ₂ (char ≠ 2), t ↦ −t, swapping origins | trivial at the origins | O is two points, and A¹ ⊔ A¹ with the swap is a chart. No problem. |
| μ₂ (char ≠ 2), trivial on G_m, swapping origins | stabilizer not closed in G×X | Chart A¹ ⊔ A¹ with free swap exists, and is stabilizer-preserving only at the origins. |

The last row also tests the hypothesis. With Z = 0, `U^{μ₂}` is empty while `X^{μ₂} ×_X U` is not, so the chart is not FPR. This is consistent, because Z = 0 is excluded by the connected-fibres hypothesis. It also confirms that charts and FPR are separate questions.

In all four cases §4.1, Lemma 4.2 and the Claim behave as stated.

## Gaps
1. **§5 step 5 and §2 are false as written.** The note says "If `X → S` is quasi-compact, finitely many charts cover `X`", and "for general separated `S`, finitely many affine opens `S_i` cover the image of `X`". With S = X non-quasi-compact, no finite family of affine charts covers X.
   - The agreed correction (`corrections-verified.md`, vote 10) replaces the clause with "if X is quasi-compact, U may be chosen S-affine". `thm68_ii_qc` already has this form.
   - The note leaves it out of its §0 item 5 list of corrections, and that list is therefore incomplete.
   - The clause with only "X → S quasi-compact" and S non-quasi-compact is not proved by this argument.
2. **§0 item 2, "not stronger than true; no counterexample exists", needs S separated.** For S the plane with doubled origin and X = A²₁, `EtaleChartFamily` (with `isAffineHom`) has no instance. A chart over the origin is affine over S only if removing a codimension 2 fibre leaves an affine scheme.
   - So the Lean target in §6 must carry `[S.IsSeparated]`, as `thm68_family` does. §6 doesn't say this.
3. **§4.5 is wrong about the Lean.** It says "X separated" can only serve to make `V ×_X V` affine. That holds for `exists_chartOf` only. In fact:
   - `chi_univ`, `le_idl_chi`, `le_idl_theta` (`ChartDeligneCompat.lean:107,165,214`) and `ChartDeligneTheta.lean` also take `hsep`.
   - `chi_univ` uses `Chart.eq_of_agree_of_iInf` to prove equivariance.
   - The note marks this section "not confirmed", but the file contradicts it.
4. **The eight-row table in §3 and the §6 change list are incomplete, and neither Lemma U nor M′ covers `chi_univ` as stated.**
   - The target `G × T^(k)` is not a complete pair: `(ℤ[M] ⊗ C)_d` is an infinite direct sum, so 1 + m₀ need not be units and Lemma U does not apply.
   - M′ needs agreement on the D(g), which `chi_univ` does not supply as stated.
   - On paper the fix is to take χ equivariant from the induction (Lemma 4.4). The Lean Deligne block must be rewritten that way, or given a new argument.
   - `grep` finds `IsSeparatedOver` in 33 Chart files, so "the eight rows" is not an established bound.
5. **Globalization is called "unchanged" without checking.** `SpacesLimitThm68.lean:176,186,233,252` all carry `hsep`, and line 186 transfers separatedness to the descended space. A quasi-separated version has to be stated and checked. Descent of the action to S₀ looks standard, but I confirmed it only on paper.
6. **Calling "Cor. 20.2" a "slip" is unverified, and §0 states it flatly.** Only the arXiv numbering was read. Print [3] is the ASENS paper, cited there as to appear with the arXiv DOI, so 20.2 could be the numbering of another version. Say "Cor. 10.2 in arXiv v4; published number unchecked". Under the rule to use published versions, this needs resolving, and the same goes for Bhatt's numbering in Camb. J. Math.
7. **Citations not verified at source:** SGA 3 VI_B 1.4.2 and VIII 3.2, Stacks 025G, 07VT, 07SQ, 086U, 06RC, 01Y3, EGA IV 6.9.1. The contents look right to me, but the numbers are from memory.
8. **Bhatt 1.1 and 1.4(1) are new external hypotheses in Lean, and neither is in the Stacks library.** The note presents them as stubs like the others, but `chart-stubs.md` and `REQUIRES_FULL_STACKS.md` list Stacks statements, and these would have no real file to replace them. The result would stay conditional on them.
   - `notes/chart-qs-proof.md` follows another route: it removes Bhatt 1.1 and replaces Lemma 4.2 with a dense separated open.
   - The two notes conflict on inputs and neither has been reconciled. That note's Step 5 is an admitted sketch, and I did not review its steps.
9. **No independent read of the rest:** Lemma 4.3 and the Thm 4.1 induction are accepted from my pass only. Thm A.1's proof was taken as given, and the note's §7 says the same.

The doubled-origin tests found no counterexample to the chart lemma.

VERDICT: BROKEN