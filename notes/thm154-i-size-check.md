# Check of thm154-i-size.md (2026-11-07)

Read only; nothing compiled, no existing file edited. Print: am.txt (Semigroup Forum version).

## 1. Print on M — ACCEPTED
- am.txt:3239 "Let M be an abelian monoid." is the only §15 standing hypothesis on M.
- Thm 15.4 (am.txt:3284-3292): (i) "X is affine over S" and nothing on M; (ii) adds only "M is a group" (+ atlas).
- §5 (am.txt:1589) "finitely generated abelian group M" is section-local.
So "M f.g." in Lean `thm154_i` is a Lean addition; removing it is a genuine unrestriction for (i).

## 2. Printed proof of (i) for any abelian monoid — ACCEPTED
Steps 1-5 use only sums of degrees; finiteness of E comes from S qc + finite type. Correct.

## 3. FG used only for site membership — ACCEPTED
Sec5Etale.lean:721-830 (section Gamma): FG enters only through `contains_M` (:759). `jr`, `eM`, `mapR`
need only `[AddMonoid M]`. grep of Sec5Etale 1633-2110 and Sec15General 132-724: no group operation
on M (the `neg` at Sec15General:586 is ring negation in a subring induction, harmless).

## 4. Size lemma exists — ACCEPTED
`AlgMag.P337.contains_alg` (Prop337General.lean:49), `contains_iff` (:38), `contains_any`/`contains_M`
under `[hM : Fact (#M < B.cutoff)]` (:212-220): signatures as quoted. Import direction (Prop337General
imports Sec8Limits, Sec5Etale imports Sec3Rest) correct: the lemmas must move upstream.

## 5. Lean plan — PARTIAL (first wrong step: §5.1(c))
- `exists_ofLE_of_pull` (Sec5Etale.lean:2187), used by Sec15General:222 and :602 (thm154_i chain), lies in
  section **PartII** (2112-), which the note declares "untouched" and lists among Magnets/Descent lemmas.
  PartII must also be switched (or the lemma moved into a monoid section). Its proof uses `isKey_descend`,
  `exists_attractorPt_of_key`, `ofLE_universal` (Key section, 1763-1906).
- The note says 1679-1983 "not read" and that the 15.4 (i) chain "does not pass through it except via the
  names listed". False: `exists_ofLE_of_pull` needs the Key chain (`IsKey`, `isKey_descend`,
  `exists_attractorPt_of_key`). grep finds no group operation there, so the fix is mechanical, but the
  risk claim in §6 is wrong as stated; the whole Key section must be generalized, not fenced.
- PartII's other lemmas (IsFace, `faceExt_neg`, 2118-2185) are group/face material: split PartII.
- `exists_affine_cover` (:1489) has no M in its signature: unaffected. OK.
- Bridge instance `[AddMonoid.FG M] → Fact (#M < B.cutoff)`: well-formed (B only in the target is fine
  for `Fact`), proof sketch plausible, not verified (no compile).
- Section Core (847-1076) uses `contains_M` under `[AddCommGroup M] [AddMonoid.FG M]`: works through the
  bridge only if the bridge is declared before line 847 (Generic). Say so explicitly.

## 6. Side claim: Thm 15.3 fppf for X affine, any M — PARTIAL
Follows if section Affine compiles under the monoid variables, which depends on the PartII fix above.

## Net
Mathematics accepted; resulting `thm154_i` (any abelian monoid, S qc, U affine finite type, grade 1)
is right as a target. Plan needs: generalize Key + `exists_ofLE_of_pull` (split PartII), place bridge
in Generic. Unverified until build.
