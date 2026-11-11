# Unrestricting Thm 15.3 and Thm 15.4 (group g5-thm153-154), 2026-11-07

Pure mathematics only. Nothing compiled, no existing file changed, `.lake` not touched.

[AM] = Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, read from `HDR/SemigroupForum-Proof.pdf` through `am.txt` (pp. 184–186 for §15; pp. 140, 144–145, 150, 154–157, 159 for the tools). Where I write "verified" I mean I checked the step myself, by hand; where I write "recorded" I mean I read it in the repo's notes and did not redo it.

Agreed decisions, not reopened: X locally of finite presentation over S is accepted wherever "finitely presented" is printed; Thm 6.8 needs S separated; Props 3.31 (ii), 3.32 (ii) hold for all algebraic spaces (`SDR4Final.lean`, M a f.g. group).

Standing hypotheses of §15 (p. 184): "Let M be an abelian monoid. Let X be a separated algebraic space over S endowed with an action a of A(M)_S. Let m(a) be the set of magnets of a, i.e. the set of all submonoids of M." The base S is the base scheme fixed in §3 (p. 140, "Let us fix a base scheme S"), with no quasi-compactness convention anywhere. So "X separated" and "X an algebraic space" are never added hypotheses below.

---

## 1. Theorem 15.3

### 1.1 Print

"Theorem 15.3 We have a canonical bijection between Π(a) and the set {X^N ⊂ X | N ∈ m(M)} with the convention that we identify X^N and X^L if and only if X^N(T) = X^L(T) ⊂ X(T) for all T/S (cf. Proposition 3.30). The bijection sends a pure magnet N ∈ Π(a) to the attractor X^N. The reciprocal bijection sends Y ∈ {X^N ⊂ X | N ∈ m(M)} to the pure magnet E(Y) := ⋂_{N ∈ m(M) | X^N = Y} N."

Printed proof, first sentence after the definition of E(Y): "By Proposition 3.34, we have Y = X^{E(Y)}." (Proposition 3.34 is Fact 3.34, p. 150.) The same citation is used a second time for E(X^N) = N.

Definition 15.2 / Prop 15.1 (ii), p. 184: N is pure iff "For any L ∈ m(a), X^N = X^L ⇒ N ⊂ L."

### 1.2 Lean versions and what they add

| Lean | hypotheses beyond the print |
|---|---|
| `pureEquivRange` (Sec15PureMagnets.lean:116) | none, but it is abstract: it takes `AttractorOrder Y`, i.e. monotonicity (Prop 3.29) plus `sInf_of_const` (Fact 3.34 for a family with a common attractor). |
| `thm153_strong` (Sec15Final.lean:221) | M a f.g. abelian group; one S-affine equivariant atlas U → X with U locally of finite type over S; X limit preserving; `(⋂J)^×`-FPR for finite subfamilies. |
| `thm153_lfp` (Sec15Final.lean:520) | M f.g. abelian group; an S-affine strongly-FPR atlas; X l.f.p. |
| `thm153_of_atlas` (Sec3Intersections.lean:609) | as `thm153_lfp` plus S quasi-compact. |
| `thm153_free` (FinalCorAtlas.lean:53) | M f.g. abelian group; X l.f.p. and quasi-compact; S separated; stubs. |
| `thm153_nonqc` (FinalNonQCFact.lean:294) | M f.g.; X l.f.p.; S separated; stubs. |
| `thm153_general` (FinalNonQCLocal.lean:121) | **M f.g. abelian group; X l.f.p.; stubs of notes/chart-stubs.md; size cutoffs hM, hZ.** S arbitrary, X not necessarily quasi-compact, no atlas. |

The fidelity row (fidelity-grades.md:92) names only the first four and says "an atlas, f.g. M and l.f.p. are added". `thm153_general` has no atlas and no condition on S: the row is out of date (notes/finish-proofs-report.md:224 records it). So the honest list of additions, after the agreed l.f.p. convention is taken into account for the *other* statements but **not** here (Thm 15.3 prints no finiteness at all), is:

(a) M a finitely generated abelian group, where the print has an arbitrary abelian monoid;
(b) X locally of finite presentation over S;
(c) stubs (chart lemma) and the size hypotheses `hM : B.Contains (Spec (ZMon M))`, `hZ : B.Contains (⊤_ Scheme)`.

(c) is harmless: hM and hZ only say that Spec Z[M] and Spec Z lie below the cutoff, which holds for the cutoff of any site containing S (they are schemes of size ≤ max(ℵ₀, #M)); grade 1 by the usual argument. The stubs are the known chart-lemma debt, not a hypothesis of the statement.

### 1.3 The statement is exactly Fact 3.34 for common-attractor families (verified)

Write Y_N for the image of X^N in X (the print's convention). Monotonicity N ⊂ L ⇒ Y_N ⊂ Y_L holds for every presheaf and every monoid (`attractorImage_monotone`, Sec15General.lean:48, no hypothesis; on paper: compose with A(L)_T → A(N)_T).

**Lemma A.** For a fixed action, the following are equivalent.
1. Thm 15.3 as printed: N ↦ Y_N is a bijection Π(a) → {Y_N}, with inverse Y ↦ E(Y).
2. For every nonempty family (N_i)_{i∈I} with Y_{N_i} = Y for all i, one has Y_{⋂ N_i} = Y.

*Proof.* (2 ⇒ 1) is `pureEquivRange`: Y_{E(Y)} = Y by (2) applied to the family {N | Y_N = Y}; E(Y) is pure because Y_L = Y_{E(Y)} = Y gives E(Y) ⊂ L by definition; E(Y_N) = N for N pure since N ⊂ E(Y_N) by purity and E(Y_N) ⊂ N by definition. (1 ⇒ 2) Let Y_{N_i} = Y for all i and let N := E(Y), pure with Y_N = Y by (1). Purity gives N ⊂ N_i for all i, so N ⊂ ⋂ N_i ⊂ N_{i_0}, and monotonicity gives Y = Y_N ⊂ Y_{⋂ N_i} ⊂ Y_{N_{i_0}} = Y. ∎

Both directions use only monotonicity and the definitions. Nothing else is in Thm 15.3: the injectivity of N ↦ Y_N on Π(a) is immediate from Def 15.2, so the whole content of the theorem is (2), which is Fact 3.34 with the hypothesis "X^{N_i} = X^{N_j} for all i, j" and the conclusion "X^{N_i} = X^{⋂ N_l}", for *arbitrary* families.

### 1.4 Consequence for the print

The printed proof applies Fact 3.34 to the family {N | X^N = Y}. That family is infinite in general (e.g. all L with X^L = X^0), and §15 assumes only "M an abelian monoid", so none of the three cases of Fact 3.34 ("(i) X is affine over S, (ii) M is a finitely generated abelian group, (iii) M is cancellative, M^gp is finitely generated as abelian group, and X^{⋂_{l∈J} N_l} is a separated algebraic spaces for any finite subset J ⊂ I") is available in the generality of the statement. Hence:

- **As printed (arbitrary abelian monoid M, X separated) Thm 15.3 has no proof in the paper.** This is a gap in the print, independent of Lean. The natural wording is "Theorem 15.3. Assume one of the conditions (i)–(iii) of Fact 3.34 holds for all families of magnets with a common attractor. Then ..." or simply "Assume X is affine over S or M is a finitely generated abelian group."
- Moreover the printed proof of Fact 3.34 (ii), (iii) for infinite families is itself invalid (the colimit step, Tag 002H; corrections-verified.md, votes 6 and 7; STATUS.md:292). So the Lean hypotheses (a), (b) are the hypotheses under which Fact 3.34 (ii) for arbitrary families is currently *known*, and they belong to the Fact 3.34 (ii) row, not to Thm 15.3.

### 1.5 Each added hypothesis

**(a) M f.g. abelian group.** Not removable by anything the paper proves: for a non-f.g. monoid, even the two-magnet case (Prop 3.32 (ii), "M is a finitely generated abelian group") is not claimed in print, and Fact 3.34 (ii) is stated with f.g. What *is* available for an arbitrary monoid M is Fact 3.34 (i): X affine over S, any S, any M, by Prop 3.24 (p. 145, "X^{⋂ N_i} = ⋂ X^{N_i}", from Thm 3.20). In Lean this is `attractorOrder_affine` (Sec15General.lean:83, `[AddCommMonoid M]`, X affine over an arbitrary S on the `GB.overO S` site). Hence

> **Thm 15.3 holds as printed, for any abelian monoid M and any S, when X is affine over S**: `pureEquivRange (attractorOrder_affine act)`.

The fppf-site version `attractorOrder_of_isAffineHom` (Sec15General.lean:236) sits in a section with `variable [AddCommGroup M] [AddMonoid.FG M]`. I read its proof and the lemmas it calls (`exists_sInf_affine` :164, `exists_chart_ring` :156, `toPoint_injective_affine` :137, `coeff_inclR`, `coeff_inclR_of_notMem`, `inclR`, `exists_ofLE_of_pull`, `exists_ptOf`): the only algebra on M is `AddMonoidAlgebra`, `AddSubmonoid.inclusion`, `mapDomainRingHom`, `AddSubmonoid.mem_sInf`; no negation, no generating set. So the group and FG instances are section artifacts there. Expected: deleting them compiles (to be checked after the build).

For non-affine X and M not f.g. I have neither a proof nor a counterexample. Attempts: P¹ with D(M) acting through any weight e ∈ M (X^N depends only on whether e, −e ∈ N), disjoint unions of lines with arbitrary weights, and chains of P¹'s all satisfy (2) trivially, because the attractor is determined by membership of finitely many weights in N, and membership is preserved by intersections. A counterexample would need a point whose set of magnets 𝒩_x = {N | x ∈ X^N} is not determined by such memberships; I found none. **Wall:** Fact 3.34 for arbitrary families and an arbitrary monoid, beyond X affine.

**(b) X l.f.p.** Fact 3.34 (ii) as printed has no finiteness hypothesis. notes/fact334-attempt.md (status line 3) records a hand proof of printed Fact 3.34 (ii) for all families when X is a separated *scheme* (fourth pass, "by hand, no independent review"), and leaves non-scheme algebraic spaces open (fifth pass). I did not re-verify that hand proof. If it stands, (b) is removable for schemes, on paper; for algebraic spaces it is the wall already recorded there (descent of the vertex map through étale, not Zariski, neighbourhoods). Where the l.f.p. enters the Lean route: `exists_closure_of_affine_base` (Sec15Final.lean:112) needs a finite set of degrees on an atlas of finite type; the alternative, the print's colimit argument, is false in schemes (`chain_no_point`). No new idea from me here. **Wall**, with the scheme case settled on paper per that note.

### 1.6 Verdict and Lean plan

**WALL**, located precisely: Thm 15.3 ⟺ Fact 3.34 for arbitrary common-attractor families (Lemma A), and the restrictions on Thm 15.3 are exactly the open part of Fact 3.34 (ii) (M non-f.g.; X a non-scheme space without l.f.p.). Paper-level item for the corrigendum: the printed Thm 15.3 cites Fact 3.34 outside its hypotheses; add "X affine over S, or M a finitely generated abelian group" (the first case needs no further hypothesis).

Lean plan (new file, after the build):
1. `thm153_affine [AddCommMonoid M] ... : pureMagnets (attractorImage act) ≃ Set.range (attractorImage act) := pureEquivRange (attractorOrder_affine act)` — Thm 15.3 for X affine over S, any monoid, any S. One line.
2. `attractorOrder_iff_equiv`: Lemma A (1 ⇒ 2), ten lines from `attractorImage_monotone`; it records that nothing beyond Fact 3.34 is ever needed.
3. Remove `[AddCommGroup M] [AddMonoid.FG M]` from sections `Affine` and `Finite` of Sec15General.lean (existing-file edit, after the build); then `thm153_of_isAffineHom` for any M on the fppf site.
4. Replace `thm153_free` by `thm153_general` in fidelity-grades.md:92 and STATUS.md:215.

---

## 2. Theorem 15.4 (i)

### 2.1 Print (p. 185)

"Theorem 15.4 Assume moreover that X is finitely presented over S. Assume additionally that one of the following conditions is satisfied (i) X is affine over S, (ii) M is a group and there exists an S-affine strongly-FPR atlas for X (e.g. the action is Zariski locally linearizable), then Π(a) is a finite poset."

Proof of (i): "Write X = Spec_S(A), then we have an M-grading A = ⊕_{m∈M} A_m. Because of X is finitely presented over S, there exists a finite subset E ⊂ M such that A is generated locally by homogeneous elements of degree in E. Now for any monoid N, we have X^N = X^{⟨N∩E⟩}. This implies that Π(a) is finite."

### 2.2 Lean

- `finite_pureMagnets_affine` (Sec15PureMagnets.lean:328): ideal model `affineY 𝒜`, `[AddCommMonoid M]`, `[Algebra.FiniteType R₀ A]`. Any monoid, finite type only, affine base.
- `thm154_i` (Sec15General.lean:715): U a site object with `[IsAffineHom U.hom.hom]`, `[LocallyOfFiniteType U.hom.hom]`, `[CompactSpace S]`, and the section variables `[AddCommGroup M] [AddMonoid.FG M]`; conclusion `(pureMagnets (attractorImage aU)).Finite ∧ (Set.range (attractorImage aU)).Finite`.

Added beyond the print: **S quasi-compact** and **M a f.g. abelian group**. Not added: "finitely presented" is weakened to locally of finite type (the Lean statement is stronger); the "poset" clause is the inclusion order and carries no content; X is a scheme in the site, which is the print's X (affine over S).

### 2.3 S quasi-compact: NEEDED (verified counterexample; paper error)

Setup: k a field, S = ⊔_{n≥1} Spec k, M = Z, X = ⊔_{n≥1} A¹_k with the n-th line over the n-th point, A = ⊕_n k[t_n], deg t_n = n (the sign convention does not matter: replace N by −N).

Printed hypotheses, each checked: M is an abelian monoid; X → S is affine (preimage of an affine open, a finite set of points, is a finite disjoint union of lines), hence separated; X → S is finitely presented in the relative sense (locally of finite presentation on each fibre, quasi-compact and quasi-separated since affine); the grading is an action of A(M)_S by Prop 2.22; (i) holds.

Attractors, by Thm 3.20 (p. 144, J_N "generated by {A_m | m ∈ M ∖ N}"): over the n-th point A_m = k·t_n^{m/n} for n | m, m ≥ 0, else 0. If n ∈ N then every jn (j ≥ 1) lies in N, so J_N = 0 and X^N is the whole line; if n ∉ N then t_n ∈ J_N and X^N is the origin. Hence X^N = X^L ⟺ N ∩ Z_{>0} = L ∩ Z_{>0}. (Thm 3.20 is local on S, so computing pointwise is legitimate; `GB.Zatt` holds for any S and M per fidelity-grades.md:6.)

Pure magnets, by Prop 15.1 (ii): for k ≥ 1 the magnet kN satisfies X^{kN} = X^L ⟹ L ∩ Z_{>0} = kZ_{>0} ⟹ kN ⊂ L, so kN is pure. These are pairwise distinct: Π(a) is infinite. The printed sentence that fails is "there exists a finite subset E ⊂ M such that A is generated locally by homogeneous elements of degree in E": each point needs the degree n. Lean: `exists_closure_of_affine_base` (Sec15Final.lean:112) proves exactly the local statement, over an affine T₀, with no condition on S; the global E needs finitely many T₀, which is `isCompact_univ.elim_finite_subcover` in `exists_finite_degrees_site` (Sec15General.lean:669).

Same conclusion as corrections-verified.md votes 1, 4, 8; STATUS.md:295 lists it under "To review". Fix: add "S quasi-compact" (or "X quasi-compact"; either suffices, since only the finitely many affine opens of S meeting the image of X contribute degrees). Remark 15.6, Conj 15.7 and Rem 15.8 inherit the hypothesis.

### 2.4 M f.g. abelian group: UNRESTRICTED (the existing proof works for any monoid)

The printed proof uses only the grading and Thm 3.20, valid for any abelian monoid M (Thm 3.20 and Prop 2.22 are stated for a commutative monoid). The ideal-model theorem `finite_pureMagnets_affine` is already stated with `[AddCommMonoid M]`. For `thm154_i`, I read the whole chain: `exists_finite_degrees_site` (:656), `exists_gamma` (Sec5Etale.lean:775), `exists_chart_degrees` (:634), `exists_closure_inter` (:537), `theta_comp_eq` (:456), `thetaN` (:450), `finiteType_chartα` (:619), `exists_toPoint_of_sieve` (:102), `attractorOrder_of_isAffineHom` (:236) and its lemmas (§1.5 above), `finite_pureMagnets_of_inter`, `isPure_pureOf`, `map_pureOf`. None uses negation, torsion, rank or a finite generating set of M; the degree sets are `Finsupp.support`s of coaction coefficients, finite for any M. The `[AddCommGroup M] [AddMonoid.FG M]` of section `Finite` are inherited variables. Expected: deleting them in sections `Affine` and `Finite` of Sec15General.lean compiles unchanged (not checked: build running). If some upstream lemma in Sec5Etale.lean (`exists_gamma`) carries the group instance in its own section, the same inspection applies there; its statement only needs the coaction ring map into `AddMonoidAlgebra (chartA T U) M`.

### 2.5 Verdict

**NEEDED with counterexample (S quasi-compact; paper error, fix "S quasi-compact")**, and **UNRESTRICTED** for the other addition: M an arbitrary abelian monoid, by the existing proofs with the section variables removed. After both, the row is grade 1 (finite type in place of finite presentation, which is stronger).

Lean plan: (1) delete the two instance variables in Sec15General.lean sections `Affine`, `Finite` (and in Sec5Etale.lean around `exists_gamma` if present); (2) nothing else; `thm154_i` then reads: U affine and of finite type over a quasi-compact S, M any abelian monoid.

---

## 3. Theorem 15.4 (ii)

### 3.1 Print

As quoted in 2.1, case (ii): "M is a group and there exists an S-affine strongly-FPR atlas for X (e.g. the action is Zariski locally linearizable)". Proof: "Case (ii) follows from case (i) and the following result", Prop 15.5 (p. 185): "Let U → X be an S-affine strongly-FPR atlas. Let a_U denote the action of D(M)_S on U. Then for all submonoids N, L of M, we have U^N = U^L ⇒ X^N = X^L; moreover Π(a_X) ⊂ Π(a_U)." Its printed proof invokes Prop 8.3 [Thm 8.3], "Proposition 3.32 or Proposition 3.24", Prop 5.1, Cor 11.6, Tags 05WT, 0AHE, 05W6, 05W5, and Prop 3.29.

Def 6.1 (iv), (vi) (p. 156): an equivariant atlas is "étale and surjective and U = ⊔_{τ∈A} U_τ is the disjoint union of D(M)_S-stable S-affine schemes; ... S-affine if A may be chosen finite"; strongly-FPR = Z-FPR for all subgroups Z ⊂ M, Z-FPR meaning U^{D(M/Z)_S} → U ×_X X^{D(M/Z)_S} is an isomorphism.

### 3.2 Lean

- `thm154_ii_lfp` (Sec15Final.lean:531): `[CompactSpace S]`, `[AddCommGroup M] [AddMonoid.FG M]` (section `Strong`), `[IsAffineHom U.hom.hom]`, `IsStronglyFPRAtlas aU aX f`, `IsAlgebraicSpace`, `IsSeparatedOver X`, X l.f.p.
- `thm154_ii` (Sec15General.lean:737): same with `IsLimitPreserving X` and `ChartsOfFiniteType X` in place of l.f.p.
- `thm154_ii_of_linearizable` (:549): finite index set A and an `IsColimit (Cofan.mk V j)` in the site; `thm154_ii_of_linearizable_qc` (:620): `[HasFiniteCoproducts (BigFppfOver B S hS)]` and X quasi-compact.

Added beyond the print: **S quasi-compact**, **M finitely generated**, and in the linearizable variants the **site coproduct**. Not added: X separated and an algebraic space (§15 standing), l.f.p. (printed f.p. implies it), X qc in the `_qc` variant (printed f.p. includes qc).

### 3.3 S quasi-compact: NEEDED (verified)

The counterexample of 2.3 satisfies (ii): M = Z is a group, and id_X : X → X is an S-affine strongly-FPR atlas: étale, surjective, A a singleton with U_1 = X stable and S-affine (Def 6.1 (iv)); for every subgroup Z the map U^{D(M/Z)} → U ×_X X^{D(M/Z)} is the identity (Def 6.1 (ii), (iii)). Π(a) is infinite as computed. Paper error, same fix.

### 3.4 M finitely generated: the print's own proof needs it; WALL without it

The printed statement says "M is a group". The printed proof of Prop 15.5 uses, in order:
- "Proposition 3.32" to reduce to N ⊂ L: Prop 3.32 (ii) is stated for "M is a finitely generated abelian group" (p. 149) — on the affine U one may use Prop 3.24 instead, which needs nothing, so this use is harmless;
- Prop 5.1, whose section hypothesis is "an action of D(M)_S for some finitely generated abelian group M" (p. 154);
- Cor 11.6, in §11 which opens "Let S be a scheme and let M be a finitely generated abelian group" (p. 171);
- Thm 8.3, in §8 which opens "Let M be an abelian group" (p. 159); I did not re-audit whether its proof uses Prop 5.1 and hence f.g.

So the printed proof establishes (ii) for finitely generated groups only, and the statement is wider than its proof. This is a second paper-level imprecision in Thm 15.4: the honest wording is "(ii) M is a finitely generated group and ...", which is also the standing assumption of every FPR result the proof rests on.

Can "finitely generated" be removed by a new argument? Reduction I verified as far as marked:
1. U → S is affine and S is quasi-compact, so U is quasi-compact; U → X is étale and X is l.f.p., so U is l.f.p. over S, hence of finite presentation. Over each of finitely many affine opens of S, O(U) has finitely many homogeneous generators, so there is a finite E ⊂ M with the coaction O(U) → O(U)[M] landing in O(U)[M'], M' := ⟨E⟩ a finitely generated subgroup. (Verified: this is exactly `exists_finite_degrees_site`.)
2. R := U ×_X U → U ×_S U is a closed immersion since X is separated (Stacks 03KL-type base change of the diagonal; standard), equivariant; O(R) is an equivariant quotient of O(U) ⊗ O(U), hence M'-graded: the action on R also factors through D(M'). (Verified.)
3. X is the coequalizer of R ⇉ U in fppf sheaves, so the action D(M) × X → X is invariant under K := D(M/M') acting on the first factor. D(M) → D(M') is faithfully flat (Z[M] is free over Z[M'] on coset representatives) but is fppf only when M/M' is finitely generated; it is an fpqc covering, and X satisfies the fpqc sheaf condition (Stacks Tag 0APL, Prop. 66.17.1 (Gabber), read today: "Let S be a scheme. Let X be an algebraic space over S. Then X satisfies the sheaf property for the fpqc topology."). So the action descends to an action of D(M') on X through which the given action factors. (Verified at the level of a sketch; the K-invariance passes from D(M) × U to D(M) × X because D(M) × U → D(M) × X is an epimorphism of sheaves.)
4. **The missing identity:** X^N_M = X^{N∩M'}_M as subfunctors of X, for every magnet N ⊂ M. The inclusion ⊃ is monotonicity. On U it holds by Thm 3.20, since A_m = 0 for m ∉ M'. On X, a point φ : A(N)_T → X_T is K-invariant and must descend along A(N)_T → A(N∩M')_T = Spec of the degree-0 part of O_T[N] for the M/M'-grading. This is a descent of an invariant map along a non-free quotient with a **non-finitely-generated grading group**, the situation Lemma D (SDR4Final) handles only for f.g. groups. I have no proof and no counterexample. If 4 held, then U^N_M = U^L_M ⟺ U^{N∩M'}_{M'} = U^{L∩M'}_{M'} ⟹ X^{N∩M'}_{M'} = X^{L∩M'}_{M'} (`prop155` for M') ⟹ X^N_M = X^L_M, which is Prop 15.5 for M, and Π(a_X) ⊂ Π(a_U) is finite by (i) (any monoid, §2.4).

**Wall** at step 4. Recommendation: state (ii) with "M a finitely generated group", which is what the paper proves and what the Lean has.

### 3.5 Site coproducts in the linearizable variants: harmless (grade 1)

`thm154_ii_of_linearizable` needs one `IsColimit (Cofan.mk V j)` for a finite family W : A → site, and `thm154_ii_of_linearizable_qc` assumes `HasFiniteCoproducts (BigFppfOver B S hS)`. Both follow from `exists_cofan_of_size` (FinalNonQCAtlas.lean:49): for A finite take μ := max(ℵ₀, max_a size (W a)); each size is < `B.cutoff` (site objects), ℵ₀ < cutoff (`B.aleph0_lt_cutoff`), a finite maximum of cardinals below the cutoff is below it, #A ≤ ℵ₀ ≤ μ, and `hU` holds by choice of μ. `HasFiniteCoproducts` then follows by `hasColimitOfIso`/`HasColimit.mk` on each `Discrete (Fin n)` diagram. So the coproduct hypothesis is a Lean-universe artifact, dischargeable from an existing lemma; the printed "e.g." clause (Fact 7.3) is covered without restriction once this is done. The main form `thm154_ii_lfp` carries no coproduct hypothesis.

### 3.6 Verdict

**NEEDED with counterexample (S quasi-compact)**; **WALL for M non-f.g.** (the print's own proof covers f.g. only; statement should say so); **site coproducts harmless** (grade 1, `exists_cofan_of_size`).

Lean plan (new file): `instance : HasFiniteCoproducts (BigFppfOver B S hS)` from `exists_cofan_of_size`, then `thm154_ii_of_linearizable_qc` with the instance argument removed; nothing else changes.

---

## 4. Summary table

| Statement | added hypothesis | verdict |
|---|---|---|
| Thm 15.3 | M f.g. abelian group; X l.f.p.; stubs | WALL = open part of Fact 3.34 (ii) (Lemma A: the theorem is equivalent to Fact 3.34 for arbitrary families). Affine X: UNRESTRICTED for any M (`attractorOrder_affine` + `pureEquivRange`). Print gap: Thm 15.3 cites Fact 3.34 outside its hypotheses. |
| Thm 15.4 (i) | S qc | NEEDED, counterexample verified (paper error) |
| Thm 15.4 (i) | M f.g. abelian group | UNRESTRICTED: section variables only; any abelian monoid |
| Thm 15.4 (ii) | S qc | NEEDED, same counterexample with id_X as atlas |
| Thm 15.4 (ii) | M f.g. | WALL (step 4 of §3.4); printed proof itself needs f.g. via Prop 5.1, Cor 11.6 |
| Thm 15.4 (ii), linearizable forms | site coproducts | harmless, `exists_cofan_of_size` |

Stacks tags read today on stacks.math.columbia.edu: 0APL (fpqc sheaf property of algebraic spaces). All other citations are to [AM] by page or to Lean declarations by file and line, read in this session.
