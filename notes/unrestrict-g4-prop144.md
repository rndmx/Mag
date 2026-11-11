# Prop 14.4, first and second assertions: which added hypotheses are needed (group g4-prop144)

Pure mathematics, 2026-11-07. Nothing compiled, no existing file edited. Source: Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, read from `am.txt` (p. 183–184, lines 3206–3231) with the §6, §8, §12 statements it cites (lines 1753–1762, 1832–1836, 1855–1874, 2904–2916). Lean read: `FinalNonQCGeneral.lean`, `FinalNonQCClauses.lean`, `FinalNonQCAttAlg.lean` (statements), `Sec14Ind.lean` 280–359, `Sec14Strong.lean` 140–219, `Sec14Remaining.lean` 161, `Sec12Topology.lean` 920–1012, `Sec8Theorem83.lean` 89–101 and 1595–1751, `FinalCorAtlas.lean` 72–157, `Sec14Counterexample.lean` 369–374, `AppendixA.lean` 193–196.

## 0. The printed statement (p. 183–184)

"Let M be a finitely generated abelian group.

**Proposition 14.4** Let X be an ind-algebraic space (resp. ind-scheme) over S. Assume that we have a presentation X = colim_i X_i with X_i quasi-separated and locally finitely presented over S. Assume that D(M)_S acts on X via an ind-action on the presentation X = colim_i X_i. Let N ⊂ M be a monoid. Assume that N is finitely generated or that X is separated. Then the attractor functor (T → S) ↦ Hom_{D(M)_T}(A(N)_T, X_T) is representable by the ind-algebraic space (resp. ind-scheme) colim_i X_i^N. Moreover the natural morphism X^N → X is representable by algebraic spaces (resp. schemes). If N = Z is a group the natural morphism X^Z → X is representable by a closed immersion.

*Proof* The first assertion is a direct corollary of Proposition 12.2. To show that X^N → X is representable by algebraic spaces, we notice that if T is an affine scheme and T → X is a morphism, then there exists i such that this morphism is induced by a morphism T → X_i, and then we have T ×_X X^N = T ×_{X_i} X_i^N. If N = Z is a group, the last assertion follows from Corollary 8.1."

The last assertion (closed immersion) is grade 1 with an agreed correction and is not part of this group; it is mentioned only where the same lemma serves it.

## 1. The Lean statements and the hypotheses they add

The fidelity rows name `isIndAlgebraicSpace_attractor`, `prop144_of_atlas`, `prop144_free` (first assertion) and `indAttractorMap_rep_nat`, `indAttractorMap_rep_scheme_nat` (second). These are the *conditional* forms: the first two assume representability of every `X_i^N` (`r`, `hZ`), or an `N^×`-FPR atlas on every term, and `prop144_free` assumes `S` separated and every term quasi-compact. The rows were written before `FinalNonQCGeneral.lean` and `FinalNonQCClauses.lean`, which now discharge all of that:

| Lean | file | printed clause | hypotheses |
|---|---|---|---|
| `prop144_general` | FinalNonQCGeneral.lean:138 | first assertion, ind-algebraic space | `[AddGroup.FG M]`, `hZ : B.Contains (⊤_ Scheme)`, `hM : B.Contains (Spec ℤ[M])`, `hX` (terms algebraic spaces), `hsep` (terms separated over S), `hfp` (terms l.f.p.), `N` any submonoid, `S` any scheme, no atlas |
| `prop144_rep_general` | FinalNonQCClauses.lean:105 | second assertion, algebraic spaces | same |
| `prop144_scheme_general` | FinalNonQCClauses.lean:135 | first + second, resp. ind-schemes / schemes | same, plus `hS'` (terms are schemes) |
| `prop144_closed_general` | FinalNonQCClauses.lean:114 | last assertion, `X` separated alternative | same |

Comparison with the print, clause by clause:

- `M` f.g.: printed ("Let M be a finitely generated abelian group").
- terms algebraic spaces, l.f.p.: printed. (`hX` in `prop144_scheme_general` is redundant given `hS'`, through `isAlgebraicSpace_yoneda`; harmless.)
- terms quasi-separated: not needed in Lean (implied by separated). Dropped, not added.
- `N` arbitrary submonoid: Lean does not need `N` f.g. when the terms are separated. Matches the printed alternative "X separated".
- `hZ`, `hM`: size conditions of the site. Both are theorems of the repo, see §2.1. Harmless, grade 1.
- **`hsep`: every term separated over S.** This is the only hypothesis beyond the print. The print offers *either* "N finitely generated" *or* "X separated"; Lean covers only the second alternative. So the uncovered case is exactly

  (★) `N` finitely generated, some `X_i` quasi-separated but not separated.

"Agreed" check: STATUS.md "Agreed" list, Thm 8.3: "Lean: M f.g., X separated, and N f.g. or X l.f.p. Printed case (b) without separated not covered." The fidelity row for Prop 14.4 already says "only the agreed Thm 8.3 part is excused". Case (★) *is* that part, see §2.3. No decision on it is reopened here; §2.3 records precisely what it reduces to.

## 2. Each added hypothesis

### 2.1 `hZ`, `hM` — harmless (grade 1)

- `hZ : B.Contains (⊤_ Scheme)`: the terminal scheme is `Spec ℤ`. The Stacks site provides `B.contains_terminal` with exactly this type; AlgMag uses it as a term in `ChartQSAsm.lean:417,423,424`, `ChartQSTop.lean:55,73,137`, `ChartQSStratCore.lean:141` (read). So `hZ := B.contains_terminal`.
- `hM : B.Contains (Spec (ZMon M))`: `AppendixA.lean:194` `contains_zmon_of_countable (hS : B.Contains S) (M) [AddCommMonoid M] [Countable M] : B.Contains (Spec (ZMon M))`, and `Sec8Theorem83.lean:94` `countable_of_fg83 : Countable M` for `[AddGroup.FG M]` (the file also has `contains_zmon_N hS N` for submonoids, line 99). So `hM := contains_zmon_of_countable hS M` with `haveI := countable_of_fg83`.

Both are therefore not hypotheses but lemma applications; the printed statement has no counterpart because `Sch/S` has no cutoff. Verified: statements read; the two terms type-check by inspection of the signatures (not compiled).

### 2.2 `hsep` in the printed alternative "X separated" — UNRESTRICTED

Reading of "X separated" for an ind-space: Rem 14.2 (p. 183) defines ind-P as "there exists a presentation X = colim X_i where each X_i has property P". Prop 14.4 fixes one presentation, the one carrying the ind-action, so the only reading that makes the hypothesis usable is: the terms of *that* presentation are separated. That is `hsep`. (If the terms are quasi-compact, any other separated presentation gives the same: by the Hom formula of Rem 14.2 each `X_i` maps by a closed immersion into some separated `Y_j`, and a closed immersion into a separated space is separated. For non-quasi-compact terms the two readings could differ; the print's own proof uses the given presentation, so `hsep` on it is the printed hypothesis.)

Complete proof of the first two assertions in this alternative, with the repo lemma for each step:

1. **Each `X_i^N` is an algebraic space over S.** Print: Thm 6.8 (i) (`X_i` separated, quasi-separated, l.f.p., `M` f.g.) gives an `N^×`-FPR atlas, then Thm 8.3 (a). Lean: `attP_alg hZ hM (hX i) (hsep i) (hfp i) (a.act i) N : IsAlgebraicSpace B S hS (attP (a.act i) N)` (FinalNonQCAttAlg.lean:163), for arbitrary `S`, no atlas: Zariski-locally on `S` it is `thm83_nonqc` (FinalNonQCAtlas.lean:134, `S` separated), glued by Stacks 04SK (`isAlgebraicSpace_of_isCovering_of_atlas_size_le`, with the bound `exists_small_atlas`). The representing object is `attP (a.act i) N` with `attPRep (a.act i) N : RepresentsAttractor (a.act i) N (attP …)`.
2. **Transition maps `X_i^N → X_j^N` are closed immersions.** Print: Prop 12.2 (ii), which asks for an `N^×`-FPR atlas on `X_j` and "N f.g. or X_i separated"; both available here. Lean: `isClosedImm_repAttractorMap hg hf N rX rY` (Sec12Topology.lean:1007) needs only `hf : IsClosedImm hg.hom` and the two representabilities: it exhibits `X_i^N = X_j^N ×_{X_j} X_i` (`isPullback_repAttractorMap`, line 977) and closed immersions are stable under base change. No atlas, no separatedness. Applied as `isClosedImm_indAttractor a N r h` (Sec14Ind.lean:319) with `r i := attPRep (a.act i) N`.
3. **The attractor functor on `Aff/S` is `colim_i X_i^N`.** For `T` affine an element of `X^N(T)` is an equivariant `A(N)_T → X_T`, i.e. compatible points of `X` on the affine schemes `A(N)_{T'}`, `T' → T`; since `X = colim X_i` *as a functor on affine schemes*, each such point comes from some `X_i`, and the surjectivity/injectivity fields of the ind-presentation are: `surj` (every attractor point of `X` is `indPt` of an attractor point of some `X_i`: Sec14Ind.lean 280–299, using `existsUnique_attractorPt_of_isClosedImm` to pull a point back along a closed immersion once its `toPoint` lies in an earlier term) and `inj` (two points of `X_k^N` with the same image agree in a later `X_l^N`, by `isClosedImm_injective (p.closed hkl)`, lines 300–315). Lean: `isIndAlgebraicSpace_attractor a N r hZ'` (Sec14Ind.lean:327) with `r := attPRep`, `hZ' := attP_alg …`. This is `prop144_general`.
4. **`X^N → X` representable by algebraic spaces.** Print's argument: `T` affine, `T → X` factors through some `X_i`, and `T ×_X X^N = T ×_{X_i} X_i^N`. Lean: `p.surj T y` gives `i, x`; the fibre product `fibreProduct (attToX (a.act i) N) (yonedaEquiv.symm x)` is an algebraic space by `isAlgebraicSpace_of_isPullback` (three algebraic spaces, diagonal of `X_i` representable); the identification of its `T'`-points with `{ψ ∈ X^N(T') : ψ.toPoint = y|_{T'}}` is `indAttractorFibreEquiv` (naturality `indAttractorFibreEquiv_nat`, Sec14Strong.lean:161), which again uses only the closed-immersion descent of step 3. Lean: `indAttractorMap_rep_nat a N (fun i => attPRep …) (fun i => attToX …) (fun _ _ _ => rfl) (fun i => attP_alg …) hX`, which is `prop144_rep_general`.
5. **Resp. ind-schemes / schemes.** If `X_i ≅ yoneda U_i`, then `X_i^N` is a scheme: Thm 8.3 (vii) in the form `scheme_of_repr r e` (FinalNonQCClauses.lean:32: `X^N → X^{N^×}` affine and `X^{N^×} → X` closed, both from `thm83_repr_general`, FinalNonQCGeneral.lean:55, `S` arbitrary). Then `isIndScheme_attractor` (Sec14Remaining.lean:161) and `indAttractorMap_rep_scheme_nat` with `representable_fibreProduct` (Sec14Final.lean:45). This is `prop144_scheme_general`.

Verified by me: the printed text of 14.4, 12.2, 8.1, 8.3, 6.8 (am.txt); the Lean *statements* of every lemma named above and the proof bodies of `isIndAlgebraicSpace_attractor`'s `surj`/`inj` fields, `indAttractorMap_rep_nat`, `prop144_*_general`, `thm83_repr_general`, `isClosedImm_repAttractorMap`. Not verified: that `FinalNonQC*.lean` compile in the current build (no lake run; `notes/finish-proofs-report.md` line 268 reports EXIT 0 with axioms `[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` coming from the Stacks stubs of `notes/chart-stubs.md` plus the 04SK stub). The stub dependence is a build matter, not a mathematical restriction.

Conclusion for this alternative: no hypothesis beyond the print. The Lean form is *stronger* than the print on two points, both already in REMARKS-type territory: (a) `N` need not be finitely generated when the terms are separated (printed as "or"; Lean needs neither `N` f.g. nor limit-preservation once `hsep`, `hfp` hold), (b) the transition-map step (Prop 12.2 (ii)) holds with no atlas and no separatedness.

### 2.3 `hsep` in the printed alternative "N finitely generated" — WALL (the agreed Thm 8.3 gap), with an exact reduction

**Exact reduction, unrestricted.** Steps 2–5 of §2.2 use nothing about the `X_i` except the representability of each `X_i^N` by an algebraic space (and, for the scheme clause, by a scheme). So the following holds for every ind-presentation with any ind-action, any `N`, any `S`, with no separatedness, finite presentation or atlas:

> If each `X_i^N` is an algebraic space, then the attractor functor is the ind-algebraic space `colim X_i^N`, and `X^N → X` is representable by algebraic spaces (by schemes if the `X_i^N` and `X_i` are schemes).

In Lean this is already a one-line corollary of `isIndAlgebraicSpace_attractor` and `indAttractorMap_rep_nat` instantiated at `r := attPRep`, `j := attToX`, `hj := rfl` with hypothesis `hrep : ∀ i, IsAlgebraicSpace B S hS (attP (a.act i) N)`; see §4. This is exactly the content the printed proof attributes to Prop 12.2, and it is where the "r, j, hZ never discharged" complaint of the fidelity row is answered: `r`, `j`, `hj` are canonical, and `hZ` is the single genuine input.

**The wall.** In case (★) the single input, "each `X_i^N` is an algebraic space", is Thm 8.3 case (b) for a quasi-separated, non-separated `X_i`. In the print this needs an `N^×`-FPR atlas (Thm 8.3's standing hypothesis; also Prop 12.2 (ii)(b)). Prop 14.4 does not assume one, and Thm 6.8 produces one for non-separated `X_i` only under (ii) "M/Z torsion-free" with `Z = N^×`. So the printed proof of the first assertion ("a direct corollary of Proposition 12.2") is incomplete in case (★) whenever `M/N^×` has torsion: neither the representability of `X_i^N` nor the atlas that Prop 12.2 (ii)(b) requires is supplied by the printed hypotheses. Example of the shape: `M = ℤ/2`, `N = 0`, the doubled-origin line (`Sec14Counterexample.lean`) — there `X^0` happens to be the open `t ≠ 0`, so the *statement* survives in that instance; only the closed-immersion clause fails, which is the agreed last-assertion correction.

I found no counterexample to the first or second assertion in case (★), and no proof. The agreed record is: Thm 8.3 printed case (b) without separatedness "not covered" (STATUS.md Agreed list); Thm 6.8 (ii) for non-separated `X` is blocked on the chart lemma (`notes/partial-state.md` line 6; printed input AHR Cor 20.2). Prop 14.4 in case (★) is the same wall and nothing else. When `M/N^×` is torsion-free the print does provide the atlas by Thm 6.8 (ii) and the wall is only the Lean one (`thm83_repr`, Sec8Theorem83.lean:1595, takes `hsep : IsSeparatedOver X` even with an atlas; `thm68_ii_proved` needs `[S.IsSeparated]`).

So for (★): WALL, located exactly at the representability of `X_i^N`; the ind-part is unrestricted.

## 3. Verdicts

- **Prop 14.4 first assertion.** Alternative "X separated": UNRESTRICTED proof; `prop144_general` (and `prop144_scheme_general` for ind-schemes), with `hZ`, `hM` discharged by `B.contains_terminal` and `contains_zmon_of_countable hS M` (grade 1 size conditions). Alternative "N f.g." with non-separated terms: WALL = representability of `X_i^N` (agreed Thm 8.3 (b) gap); the printed proof is incomplete there when `M/N^×` has torsion (no atlas is available for Prop 12.2 (ii)(b)); no counterexample found. The reduction to that representability is unrestricted.
- **Prop 14.4 second assertion.** Same split: UNRESTRICTED under "X separated" via `prop144_rep_general` / `prop144_scheme_general` (the `r`, `j`, `hZ` of `indAttractorMap_rep_nat` are discharged by `attPRep`, `attToX`, `attP_alg`); WALL in (★), same point.

Proposed grades once the two corollaries of §4 are in: first and second assertion 1 (the only remaining difference from the print is the excused Thm 8.3 case). Nothing for the corrigendum from this group beyond what is already agreed; the incomplete-proof observation of §2.3 is a REMARKS item ("the first assertion relies on Thm 8.3 for each `X_i`, whose atlas hypothesis Prop 14.4 provides only through Thm 6.8").

## 4. Lean plan (new file, nothing existing touched)

```lean
import AlgMag.FinalNonQCClauses

namespace AlgMag.Final
-- same variables as FinalNonQCClauses: B S hS, M [AddCommGroup M] [AddGroup.FG M],
-- P Xi p a, hX hsep hfp as there

/-- Prop 14.4, exact reduction: only representability of the `X_i^N` is used. -/
theorem prop144_of_rep (N : AddSubmonoid M)
    (hrep : ∀ i, IsAlgebraicSpace B S hS (attP (a.act i) N))
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i)) :
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) ∧
      IndAttractorMapHasPropNat a N (fun {Z' _} _ => IsAlgebraicSpace B S hS Z') :=
  ⟨isIndAlgebraicSpace_attractor a N (fun i => attPRep (a.act i) N) hrep,
   indAttractorMap_rep_nat a N (fun i => attPRep (a.act i) N) (fun i => attToX (a.act i) N)
     (fun _ _ _ => rfl) hrep hX⟩

/-- Prop 14.4, printed alternative "X separated", no site hypotheses. -/
theorem prop144_printed_sep (N : AddSubmonoid M) :
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) ∧
      IndAttractorMapHasPropNat a N (fun {Z' _} _ => IsAlgebraicSpace B S hS Z') :=
  haveI : Countable M := countable_of_fg83
  ⟨prop144_general B.contains_terminal (contains_zmon_of_countable hS M) a N hX hsep hfp,
   prop144_rep_general B.contains_terminal (contains_zmon_of_countable hS M) a hX hsep hfp N⟩
-- likewise prop144_scheme_general with hS'.
end AlgMag.Final
```

Points to check at compile time (not done): `Countable M` must be in scope before `prop144_rep_general`'s `haveI` type ascription unifies; the exact argument order of `prop144_general` (`hM` before `a N hX hsep hfp`) and of `prop144_rep_general` (section variables `hM a hX hsep hfp`, then `N`); `contains_zmon_of_countable` takes `M` explicitly. For case (★) nothing can be written now: it waits on an `attP_alg` for quasi-separated terms, i.e. on Thm 8.3 (b) / Thm 6.8 (ii) for non-separated `X`.
