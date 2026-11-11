# Equivariant atlases: what the theory uses, and the right definition

Source: Algebraic Magnetism, Semigroup Forum 113 (2026) 126-201, publisher version
(am.txt line numbers in brackets; pages from running heads). Magnet language only.
Synthesis of three reader reports (A: §5-7, App. A; B: §8, 12, 13, 14; C: §13-16, global grep),
re-checked against the text where the readers disagreed. Nothing compiled, no existing file touched.

Convention. "S-affine": U -> S affine (Def 6.1(iv) as printed, Thm 3.20, Lean `IsAffineHom`).
"affine": U is an affine scheme (absolute). Option (a) = keep Def 6.1 as printed and add
"S separated" to Thm 6.8 and wherever it propagates. Option (b) = pieces are affine schemes.

## 0. The problem, restated

Def 6.1(iv) [1683-1686]: an equivariant atlas is an etale surjective f : U -> X with
U = disjoint union of D(M)_S-stable S-affine schemes; "S-affine atlas" if the index set may be
chosen finite. Thm 6.8 [1753-1762] asserts existence of a Z-FPR atlas for every S.

Counterexample (corrections-verified.md 599-622, re-derived by hand by A and by me): S = affine
plane with doubled origin, X = one chart V_1 = A^2, M = 0. If U -> X is etale and U -> S is
affine then U x_S V_1 = U and U x_S V_2 = U \ F are affine, F = fibre over the origin, nonempty of
codimension 2 in the regular scheme U; Hartogs gives O(U) = O(U \ F), so U \ F = U, contradiction.
So no S-affine etale scheme over X meets the origin: Thm 6.8 as printed is false for this S,
and Conj 6.9 (i), (ii) are refuted for arbitrary S.

Appendix A (p. 199) proves something true: "we reduce to the case where S is affine", then
produces etale neighbourhoods U(x) -> X with U(x) an affine scheme (Spec(A) from [3, Cor 20.2],
affine finite quotient U_0/F, affine base change along X -> X/F). It never uses or proves that
U(x) -> S is affine. The gap is exactly the word "S-affine" in Def 6.1(iv).

## 1. One fact that settles most of the table

Transfer lemma (reader B, verified by hand; not in print). Let S be any scheme, U an affine
scheme with an action of D(M)_S. Since D(M)_S x_S U = D(M) x_Z U, this is a D(M)-action on the
affine Z-scheme U for which U -> S is invariant, i.e. an M-grading of the ring O(U) (SGA3 I 4.7.3).
Then for every S-scheme T and every submonoid N of M,

    (U/S)^N(T) = (U/Z)^N(T)  inside Hom(A(N)_T, U).

Proof sketch. One must show: every D(M)_T-invariant morphism phi : A(N)_T -> S (S with trivial
action) factors through the projection A(N)_T -> T. Locally on T (affine T', point t) choose an
affine open W of S containing phi(1_t); phi^{-1}(W) is a stable open of A(N)_{T'} meeting the
zero section A(N^x)_kappa(t) of the fibre; every orbit closure in A(N)_kappa is A(F)_kappa for a
face F containing N^x, so a stable open meeting A(N^x)_kappa contains the whole fibre. Shrinking
T', phi(A(N)_{T'}) is inside W, and the ring map O(W) -> O(T')[N] has invariant, hence degree-0,
image O(T'). So phi factors through T'. Glue. No hypothesis on N or S.

Consequences, for an affine piece U over arbitrary S:
- Thm 3.20: (U/S)^N is the closed subscheme (U/Z)^N = V(O(U)_m : m outside the saturation data)
  of U, viewed over S through U -> S.
- Cor 3.22 (U^N -> U^L closed immersion for N in L), Lemma 3.26: apply them over Spec Z.
- U^N -> U^{N^x} is a morphism of affine schemes, hence affine (Stacks 01S7). This replaces the
  print's "affine because U is S-affine" (p. 160 [1895]).
- Prop 5.1: run the printed proof with U x_Z T = Spec_T(O(U) tensor O_T) in place of U x_S T;
  the lifted equivariant F : A(N)_T -> U restricts to the given f_0 on the zero section, so by the
  lemma s o F = (T -> S) o pr, i.e. F is an S-morphism and lies in (U/S)^N(T). Rest unchanged.

So "affine over S" is never what the arguments need about a piece; they need "affine scheme with
a D(M)-action", and the base S is irrelevant to the attractors of such a piece. This is the
conceptual reason (b) is the natural notion, not a device to rescue Thm 6.8.

Two more elementary facts used below:
- If S is separated, an affine scheme over S is S-affine (Stacks 01SG). So (a) and (b) differ only
  over non-separated S, and the finite form of (b) (U one affine scheme) is the printed "S-affine
  atlas" whenever S is separated.
- Every (a)-atlas refines to a (b)-atlas with the same FPR properties: a stable S-affine V is the
  union of the stable affine opens V x_S S_i (S_i affine opens of S); open immersions are strongly
  FPR (Fact 7.1) and FPR is stable under composition, since (V')^H = V^H x_V V' = X^H x_X V'.
  Conversely a (b)-atlas is an (a)-atlas when S is separated. Hence nothing is lost by (b).

## 2. Table: property of the pieces actually used, statement by statement

| Statement (page) | Property of pieces used in the proof | Index set / S-affine needed? | Under (b) | Under (a) | S separated needed independently? |
|---|---|---|---|---|---|
| Prop 5.1 (155) | U = Spec of M-graded algebra; lifting of graded maps to R[N] | no finiteness; printed for S-affine | holds for affine U via transfer lemma (one added sentence) | unchanged | no |
| Def 6.1, Rem 6.2 (156-7) | finite disjoint union of (S-)affine is (S-)affine | - | finite atlas = one affine scheme U; U S-affine iff (S separated or...) | unchanged | only to pass from affine to S-affine |
| Prop 6.3, Rem 6.4-6.6 (157) | none | - | ok | ok | no |
| Lemma 6.7 (157) | affineness closed under affine base change | (ii) finiteness only | verbatim ("affine scheme") | unchanged | no |
| Thm 6.8 (158) | App. A produces affine schemes over affine opens of S, glued | finite clause needs X qc | TRUE for all S; U one affine scheme if X qc; S-affine if also S separated | needs S separated (counterexample) | no, except the S-affine clause |
| Conj 6.9 (158) | - | (ii) finite | (i) open for all S; (ii) with X qc, "finite atlas" | both parts need S separated | - |
| Fact 7.1, Def 7.2 (158-9) | none / S-affine stable opens (natural, keep) | - | ok | ok | no |
| Fact 7.3 (159) | pieces = S-affine stable opens | - | refine each V by V x_S S_i (one line) | unchanged | no |
| App. A: Thm A.1, A.3-A.5 (196-9) | none | - | ok | ok | no (reduction to S affine is legitimate: local properties) |
| Thm A.2 (196, proof 199-200) | affine etale neighbourhoods Spec(A), affine quotients, affine base change | "final claim obvious": X qc => finitely many | this is exactly what the proof proves | proof has a gap for S-affine unless S separated | no |
| Rem A.7 (199) | "disjoint sum of affine schemes" | - | matches (b) literally | - | no |
| Prop 8.1 (159) | U_tau^Z -> U_tau closed immersion (Thm 3.20) | any index set | verbatim (fixed locus is base-independent) | unchanged | no |
| Thm 8.3 (159-60) | Prop 5.1; Thm 3.20; U^N -> U^{N^x} affine | any index set | via transfer lemma; "morphism of affine schemes is affine" | unchanged | no |
| Prop 8.5 (161) | ONE S-affine piece U = Spec_S(A), finitely many homogeneous generators, fp over S | finite index, S-affine, graded O_S-algebra | localize to affine opens of S (unrestrict-g2 note §2.4), where (a)=(b) | unchanged | no; needs S QUASI-COMPACT (counterexample: S = disjoint union of Spec k, weights (1,n) in Z^2) |
| Sect. 9 (166) | U = Spec of graded O_S-algebra | S-affine pieces of a finite atlas | same localization as Prop 8.5 (S qc) | unchanged | no (not re-read in depth; same pattern as 8.5) |
| Prop 12.1 (178) | nothing directly; via Thm 8.3 | - | as 8.3 | unchanged | no |
| Prop 12.2(ii) (178-9) | Lemma 6.7(i); Prop 5.1; Lemma 3.26 on U_i x_Y X -> U_i | any index set | via transfer lemma | unchanged | no |
| Sect. 13 preamble, Cor 13.3 (181-3) | nothing; silently uses an N^x-FPR atlas of X_{S'} via 12.2(ii) | - | no S hypothesis propagates | "S separated" would propagate | no; independent gap: add representability / atlas hypothesis |
| Prop 14.4 (184) | nothing; via 12.2(ii) and 8.1, atlas of X_j from Thm 6.8 | - | no S hypothesis propagates | "S separated" would propagate | no; independent gap: 6.8 does not cover "N f.g., X_i non-separated, M/N^x with torsion"; say "assume each X_i has an N^x-FPR atlas" |
| Thm 15.4 (185) | (i): X = Spec_S(graded A), finitely many degrees; (ii): case (i) on U, Prop 15.5 | (ii): finite, S-affine | finite atlas = affine U; run (i) on U over affine opens of qc S | unchanged | no; needs S QUASI-COMPACT independently (same Z^2 example makes P_0 infinite for X affine over S, fp, S non-qc) and the parenthetical needs "X quasi-compact and ZLL" |
| Prop 15.5 (185-6) | U qcqs; Prop 5.1; Thm 8.3; X separated (Prop 3.29) | finite (qcqs) | via transfer lemma | unchanged | no (X separated is the standing §15 hypothesis) |
| Rem 15.8 (186) | Conj 6.9(ii) | - | "6.9(ii) implies 15.7" with X qc | needs "S separated" | - |
| §16.7 toric (194-5) | pieces A(N_alpha), base Spec Z | - | ok | ok | no |

Reading of the table. Only three proofs use "S-affine" for a purpose that an affine scheme does
not immediately provide: Prop 8.5, the p. 166 argument, and Thm 15.4(ii), all through "finitely
many homogeneous generators of a graded O_S-algebra". All three ALSO need S quasi-compact for an
independent reason (reader B's counterexample for 8.5, the same example for 15.4(i)). Over a
quasi-compact S one localizes to finitely many affine opens S_j, where an affine scheme over S_j
is S_j-affine and the printed argument runs verbatim. So after the hypotheses these statements
need anyway, (a) and (b) give the same proofs there. Everywhere else the pieces are used only
through Thm 3.20 / Cor 3.22 / Lemma 3.26 / Prop 5.1, which the transfer lemma extends to affine
pieces over any S. No statement in the paper needs S separated for a reason of its own.

## 3. The best definition

Recommendation: (b). An equivariant atlas is an etale surjective equivariant f : U -> X with U a
disjoint union of D(M)_S-stable affine schemes.

Why (b) is natural and not a rescue:
1. It is what Appendix A proves and what Remark A.7 already says ("disjoint sum of affine
   schemes"); it is also the standard notion of a presentation of an algebraic space (etale cover
   by affine schemes, Stacks), so Def 6.1 becomes "a presentation whose charts are stable".
2. Attractors of an affine scheme do not see the base (transfer lemma). The theory of §3 for
   affine objects is intrinsically about M-graded rings; "affine over S" was only a way of saying
   "a graded O_S-algebra", and over a non-separated S that is not the right local notion (an affine
   scheme over the doubled plane is not S-affine, yet its attractors are perfectly computed by
   Thm 3.20 over Z).
3. It gives Thm 6.8 and Thm A.2 for every base S, Conj 6.9(i) for every S, and loses nothing:
   (a)-atlases refine to (b)-atlases, and over separated S the two notions coincide.
4. It costs: one sentence in Prop 5.1 (or a remark after Thm 3.20 stating the transfer lemma),
   one line in Fact 7.3, and the localization step in Prop 8.5 / p. 166 / Thm 15.4(ii), which
   those statements need anyway because of S quasi-compact.

Why not (a): it imports "S separated" into Thm 6.8, A.2, Conj 6.9, Prop 14.4, §13, Rem 15.8 for
no mathematical reason; the proofs never use it. The author's objection to unmotivated
restrictions applies exactly here.

"Affine over some affine open of S" is equivalent to "affine scheme" (an affine scheme over an
affine S_i is S_i-affine, and conversely) and so adds nothing; it is correctly excluded.

What is kept from the print: the term "S-affine" stays for Thm 3.20, Rem 3.23, Lemma 3.26 and
Def 7.2 (Zariski locally linearizable: covering by S-affine stable opens), where it is the natural
hypothesis about X itself, not about atlas pieces. The finite-index notion is renamed "finite
atlas" (U a single affine scheme); the phrase "S-affine atlas" is retired, with the remark that
a finite atlas is S-affine when S is separated.

## 4. Corrigendum wording

Def 6.1(iv). Replace by:
"(iv) We say that f is an equivariant atlas if f is etale and surjective and U = coprod_{tau in A}
U_tau is a disjoint union of D(M)_S-stable open subschemes U_tau which are affine schemes.
If A may be chosen finite we say that the equivariant atlas f is finite."

Remark 6.2. Replace by:
"A finite disjoint union of affine schemes is affine, so a finite equivariant atlas is a
D(M)_S-equivariant etale surjective morphism U -> X with U an affine scheme. If S is separated,
U is then affine over S [Stacks 01SG]. Conversely, if V -> S is affine and V is D(M)_S-stable,
the open subschemes V x_S S_i, for S_i running through the affine opens of S, are stable affine
schemes covering V; so an etale surjective equivariant morphism from a disjoint union of stable
S-affine schemes refines to an equivariant atlas, and Z-FPR is preserved by this refinement
(Fact 7.1 and U'^H = U^H x_U U' = X^H x_X U')."

New Remark 3.20bis (after Thm 3.20, or inside Prop 5.1). "Let U be an affine scheme with an action
of D(M)_S, i.e. an M-graded ring O(U) such that U -> S is invariant. For every S-scheme T and
submonoid N of M, (U/S)^N(T) = (U/Z)^N(T): a D(M)_T-invariant morphism A(N)_T -> S factors through
T. Hence Theorem 3.20, Corollary 3.22 and Lemma 3.26 hold for U over S, and U^N -> U^{N^x} is a
morphism of affine schemes, hence affine." (Proof: §1 above.)

Prop 5.1. "Let U be an affine scheme endowed with an action of D(M)_S" in place of "Let U be an
S-affine scheme"; in the proof, "U x_Z T = Spec_T(O(U) tensor O_T)" in place of "U x_S T =
Spec_T(A_T)", and add at the end: "F is an S-morphism by Remark 3.20bis since it restricts to
f_0 on the zero section."

Lemma 6.7. (ii): "finite Z-FPR atlas" twice. Proof: "a disjoint union of affine schemes".

Thm 6.8. Replace the conclusion by:
"Then there exists a Z-FPR atlas U -> X. If X is quasi-compact, U may be chosen to be an affine
scheme (a finite atlas); if moreover S is separated, U is then affine over S."
(Also: 6.8(ii) is the special case "H has connected fibres" of A.2(ii); and the proof of A.2
reduces to S affine, which is legitimate for this statement since the charts are affine schemes
and their FPR property is local on S.)

Conj 6.9. "(i) unchanged. (ii) If X is quasi-compact, there exists a finite strongly-FPR atlas
U -> X." (As printed, both parts fail for the doubled plane; with Def 6.1 corrected, (i) is open
for all S.)

Fact 7.3, proof. "Let (V_j) be S-affine open stable subspaces covering X and let (S_i) be the
affine opens of S. Then U = coprod_{i,j} V_j x_S S_i -> X is an equivariant atlas, strongly FPR
by Fact 7.1."

Prop 8.5. Statement: "Assume that M is finitely generated as an abelian group, that S is
quasi-compact and that X -> S is quasi-compact, separated and locally of finite presentation.
Then there exists a finitely generated submonoid N_c of N with X^N = X^{N_c} and N^x = N_c^x."
Proof: "The assertion is local on S (Proposition 3.9), so by quasi-compactness we may replace S by
a finite affine cover and assume S affine; then X is quasi-compact and a finite N^x-FPR atlas
U -> X of Theorem 6.8 has U an affine scheme, hence S-affine, and the printed argument applies;
take N_c generated by the finitely many N_{c_j} obtained over the cover." (S separated is not
needed; corrigendum-items.md line 4 overshoots.)

Thm 8.3, proof (p. 160). "The left vertical arrow is affine since U^N and U^{N^x} are affine
schemes (Theorem 3.20 and Remark 3.20bis)."

Prop 12.2(ii), proof. "stable affine schemes U_i".

Sect. 9, p. 166 proof. Same localization as Prop 8.5: assume S affine (the statement there should
carry "S quasi-compact" if it uses a finite atlas; to be checked when that section is revised).

Section 13 preamble and Prop 14.4. Add "assume that X_{S'} (resp. each X_i) admits an
N^x-FPR atlas, e.g. by Theorem 6.8" and, in §13, that the attractors involved are representable
(Theorem 8.3). Independent of (a)/(b).

Thm 15.4. Add "S quasi-compact" to the standing hypotheses of the theorem (otherwise P_0 can be
infinite even in case (i)); (ii): "M is a group and there exists a finite strongly-FPR atlas for X
(e.g. X quasi-compact and the action Zariski locally linearizable)". Proof of (ii): apply (i) to
U x_S S_j over the finitely many affine opens S_j of S; P_0(a_U) injects into the product of the
P_0(a_{U x_S S_j}) since attractors are determined locally on S.

Prop 15.5. "Let U -> X be a finite strongly-FPR atlas." Proof step 1: "U being affine, it is
quasi-compact and quasi-separated". Prop 5.1 as corrected.

Rem 15.8. "Conjecture 6.9(ii) implies Conjecture 15.7 for X quasi-compact."
Conj 15.7: "(i) or (ii)" ("(iii)" does not exist).

Typos found on the way (independent): Rem 6.2 "U -> S" should read "U -> X"; "Proposition 8.3"
for Theorem 8.3 in Props 12.1, 15.5; "Corollary 8.1" for Prop 8.1 in 14.4; "Proposition 6.7" for
Lemma 6.7 in 12.2; "numbered as Theorem A.2" (p. 157) inaccurate.

## 5. Impact on the Lean formalization

Current encoding (read, not run):
- Sec6FPR.lean 237-249: `IsAffineDecomposition` has `isAffineHom : ∀ a, IsAffineHom ((V a).ι ≫ structMap U)`,
  i.e. Def 6.1(iv) as printed; `IsZFPRAtlas` (314) = `IsEquivariantAtlas ∧ IsZFPR`;
  `IsSAffineAtlas` (309) = atlas ∧ `HasFiniteAffineDecomposition`.
- ChartAtlas.lean 31-40: `EtaleChartFamily` has `isAffineHom : ∀ a, IsAffineHom (structMap (U a))`;
  `coprod_decomposition` (74) turns it into an `IsAffineDecomposition`.
- ChartQSIndThm68.lean 30-36: `thm68_ii_proved` already returns `∀ a, IsAffine ((SCH).obj (U a))`
  (absolute affine charts) and `[S.IsSeparated]` is used only to convert `IsAffine` into
  `IsAffineHom` (Stacks 01SG). ChartFinalSpaces.lean 31, 44 and FinalNonQCAtlas.lean carry
  `[S.IsSeparated]` for the same reason.

Under (b):
1. Replace `isAffineHom` by `isAffine : ∀ a, IsAffine ((SCH).obj (U a))` in `EtaleChartFamily`,
   and by `isAffine : ∀ a, IsAffineOpen (V a)` in `IsAffineDecomposition`. `coprod_decomposition`
   becomes simpler (an affine open of a coproduct, not a composite affine morphism).
2. Drop `[S.IsSeparated]` from `thm68_family_spaces`, `thm68_qc_spaces`, `thm68_ii_proved`,
   `thm68_ii_qc_proved` and FinalNonQCAtlas: the conversion step disappears; the statements then
   match the corrected Thm 6.8 for all S. Keep a one-line corollary `isAffineHom_of_isSeparated`
   giving the printed S-affine form when `S.IsSeparated`.
3. Rename `IsSAffineAtlas` to `IsFiniteAtlas` (finite affine decomposition); add the lemma
   "finite atlas => U affine scheme" and, under `S.IsSeparated`, "=> IsAffineHom (structMap U)".
4. Downstream consumers (Sec8Representability, PrintedProp51, PrintedProp85, and whatever uses
   Thm 3.20 on pieces) currently receive `IsAffineHom` to S. They need the transfer lemma as a
   Lean statement: for `U` affine with a `D(M)_S`-action, the attractor functor over S equals the
   attractor functor over the base of `U` as an affine scheme (equivalently Thm 3.20 applied to
   the graded ring `Γ(U)`). If Thm 3.20 is formalized for `IsAffineHom` over an arbitrary base
   object, it can be instantiated with base `U` itself or `Spec ℤ`, and the transfer lemma is the
   bridge; this is the only genuinely new Lean content. I have not read these files; the amount of
   work depends on whether `Sec8Representability` takes `IsAffineDecomposition` as a black box.
5. PrintedProp85 uses the O(S)-grading of an S-affine chart (unrestrict-g2-prop81-prop85.md §2.5);
   under the corrected Prop 8.5 it should take `[IsAffine S]` (after localization) or
   `[CompactSpace S]` plus a localization lemma. Independent of (a)/(b) in substance, since the
   statement needs S quasi-compact anyway.

Minimal-change alternative in Lean (if the formalization is not to be reorganized now): keep the
`IsAffineHom` fields and `[S.IsSeparated]` as the formalization of the printed (a)-form, and record
in REMARKS.md that the paper's corrected definition is (b), which the Lean `IsAffine` output of
`thm68_ii_proved` already witnesses for all S. The two are equivalent over separated S.

## 6. Checks and limits

Verified by hand in this synthesis: counterexample (Hartogs); transfer lemma and its four
consequences; refinement of (a)-atlases to (b)-atlases with FPR preserved; the localization of
Prop 8.5 and Thm 15.4(ii) over quasi-compact S; that the Z^2-weight example breaks Thm 15.4(i)
for S non-quasi-compact. Cited from memory, not reopened: Stacks 01SG, 01S7, SGA3 I 4.7.3,
[3, Cor 20.2]. Not re-read in depth: §9 (p. 166) and the Lean files beyond the definitions quoted.
