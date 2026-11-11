# Unrestricting Prop 8.1 and Prop 8.5 (group g2-prop81-prop85)

[AM] = Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, read from `HDR/SemigroupForum-Proof.pdf` through `am.txt` (lines cited). Pure mathematics: nothing compiled, no existing file changed, `.lake` not opened. Stacks tags were read today on stacks.math.columbia.edu; only the tags quoted below are used.

Accepted decisions, not reopened: X locally of finite presentation over S; Thm 6.8 needs S separated; Prop 8.5 has l.f.p. and S quasi-compact added (STATUS.md "Agreed", line 281).

---

## 1. Proposition 8.1

### 1.1 Print and Lean

Print, p. 159 (am.txt 1825–1836), standing hypotheses of §8: "Let M be an abelian group. Let S be an arbitrary scheme. Let X be an S-algebraic space endowed with an action of D(M)_S."

> **Proposition 8.1** Let Z ⊂ M be a subgroup. Assume that there exists a Z-FPR atlas for X under the action of D(M)_S (cf. Definition 6.1). Then the attractor space X^Z (which identifies with the fixed space X^{D(M/Z)_S} by Proposition 3.35) is representable by a closed subspace of X.

Printed proof (1838–1850): cartesian square U^Z → X^Z over U → X from Def 6.1; "By Proposition 3.22 the left vertical arrow is a closed immersion of schemes"; Tag 03I2 for closed immersions.

Lean: `Prop81StatementFG` (Sec6FPR.lean:368) and `prop81FG` (Sec8Representability.lean:1274) carry `[AddGroup.FG M]`. `Prop81Statement` (Sec6FPR.lean:357), for arbitrary M, carries instead a site hypothesis `∀ T, Nonempty (UniversalPoint ⊤ T)` (D(M)_T belongs to the site) and is **not proved**.

Added hypotheses beyond the print and beyond the agreed list:
- (H1) `M` finitely generated.
- (H2, in `Prop81Statement` only) D(M)_T is an object of the site for every T.

(H2) is a universe/size cutoff: in the paper every scheme is an object of (Sch/S)_fppf, so D(M)_T is. In Lean, `AttractorPt` (Foundations.lean:93) tests points only on site objects, so without (H2) the Lean attractor is not the paper's functor at all. Grade 1, harmless, as the author already accepts for every site-membership hypothesis of the form `B.Contains (Spec (ZMon M))`.

(H1) is a genuine restriction and is what this section removes.

### 1.2 Where the print needs M finitely generated

The parenthetical cites Prop 3.35, printed (am.txt 1382) with "Assume M is a finitely generated group", proved through the exact sequence 1 → D(M/Z) → D(M) → D(Z) → 1 and the quotient D(M)_T/D(M/Z)_T. Nothing else in the proof of 8.1 uses M f.g.: Def 6.1 (ii) is a statement about D(M/Z)-fixed points for any M; Thm 3.20 (am.txt 1032) is stated for an arbitrary commutative monoid M (§3 opening, am.txt 770: "Let us fix a commutative monoid M"); Tag 03I2 does not see M. So the only question is whether the identification X^Z = X^{D(M/Z)} holds for arbitrary abelian M. It does, with X an algebraic space. The Lean proof `prop81FG` uses FG exactly there: `extSieve_mem_of_equiv` (fppf cover D(M) → D(Z), requires FG) feeding `attractorFixedEquivOfCover` (Sec8Representability.lean:211); the other use, `exists_closed_fixed_of_equiv`, needs FG only to derive the size facts `hM`, `hQ`, which `exists_closed_fixed` (line 956) takes directly as hypotheses.

### 1.3 Prop 3.35 for an arbitrary abelian group M (paper proof)

Setting: S a scheme, X an algebraic space over S with a D(M)_S-action, Z ⊂ M any subgroup, M any abelian group. Write π : D(M) → D(Z) for the restriction of characters along Z ⊂ M, and ev : X^Z → X, φ ↦ φ(1), the map of Remark 3.6 / `AttractorPt.toPoint`.

**(a) π is an fpqc covering.** Z[M] is a free Z[Z]-module on a set of coset representatives of Z in M (the monomials x^m, m in one coset, span Z[Z]·x^{m_0}). So D(M)_T → D(Z)_T is affine, faithfully flat and surjective for every T. By Definition 34.9.1 (Tag 022B: each f_i flat, and every affine open of the target is covered by images of affine opens of finitely many sources) an affine faithfully flat morphism is an fpqc covering: the preimage of an affine open is affine. No finiteness of M/Z is used; π is fppf only if M/Z is finitely generated, which is why the Lean route via `extSieve_mem` needs FG.

**(b) Kernel.** For every T', the kernel of D(M)(T') → D(Z)(T') is the set of characters M → O(T')^× trivial on Z, i.e. D(M/Z)(T'), and D(M) ×_{D(Z)} D(M) ≅ D(M) × D(M/Z), (g, h) ↦ (g, gh). This is presheaf-level group theory, no hypothesis on M. (Lean: `exists_quotient_of_trivialOn`, Sec8Representability.lean:49, already for any M.)

**(c) ev lands in the fixed points.** For φ ∈ X^Z(T), T' → T and h ∈ D(M/Z)(T'), viewed in D(M)(T') with π(h) = 1: h·φ(1) = φ(π(h)·1) = φ(1) by equivariance. (Lean: `AttractorPt.toPoint_mem_fixedPoints`, any M.)

**(d) ev is injective.** Let φ, φ' ∈ X^Z(T) with φ(1) = φ'(1) = x. Then φ∘π = φ'∘π as morphisms D(M)_T → X_T, both being g ↦ g·x by equivariance. X satisfies the sheaf property for the fpqc topology (Tag 0APL, Gabber: "Let S be a scheme. Let X be an algebraic space over S. Then X satisfies the sheaf property for the fpqc topology"). Since π is an fpqc covering of D(Z)_T by (a), X(D(Z)_T) → X(D(M)_T) is injective, so φ = φ'.

**(e) ev is surjective onto the fixed points.** Let x ∈ X(T) be D(M/Z)-fixed in the sense of Def 6.1 (for all T' → T and h ∈ D(M/Z)(T'), h·x_{T'} = x_{T'}; Lean `fixedPoints`, Sec6FPR.lean:71). Put ψ : D(M)_T → X_T, g ↦ g·x. By (b) the two pullbacks of ψ to D(M) ×_{D(Z)} D(M) = D(M) × D(M/Z) are (g, h) ↦ g·x and (g, h) ↦ gh·x = g·(h·x) = g·x, equal. By Tag 0APL and (a), ψ descends to a unique φ : D(Z)_T → X_T with φ∘π = ψ. φ is D(M)_T-equivariant: both g'·φ(π(g)) and φ(π(g'g)) equal g'g·x, and π is an epimorphism of fpqc sheaves, so the two maps D(M)_T × D(Z)_T → X_T agree after the covering D(M) × D(M) → D(M) × D(Z) and hence agree (0APL again, applied to X(D(M)_T × D(Z)_T)). Finally φ(1) = ψ(1) = x. Naturality in T is clear since all constructions are base changes.

So ev : X^Z → X^{D(M/Z)} is an isomorphism of presheaves on Sch/S for every abelian group M. **Verified:** (a)–(e) line by line; Tags 022B and 0APL read on the Stacks site today.

### 1.4 Prop 8.1 for an arbitrary abelian group M

With 1.3 in place, the printed proof goes through unchanged:
1. By Def 6.1 (ii), U^{D(M/Z)} = U ×_X X^{D(M/Z)} (cartesian square). By 1.3 the top-left and top-right corners are U^Z and X^Z.
2. U = ⊔ U_τ with U_τ stable and S-affine (Def 6.1 (iv)). A point of ⊔ U_τ is a decomposition of T and points of the pieces, and the action preserves pieces, so (⊔U_τ)^{D(M/Z)} = ⊔ U_τ^{D(M/Z)}. For U_τ = Spec_S(A_τ), A_τ = ⊕_{m∈M} A_m, a T-point x : A_τ ⊗ O_T → O_T is D(M/Z)-fixed iff x(a)·x^{\bar m} = x(a) in O_{T'}[M/Z] for all a ∈ A_m and all T' → T, iff x kills A_m for m ∉ Z. So U_τ^{D(M/Z)} = V(A_m : m ∉ Z) is a closed subscheme, for any M (this is Thm 3.20 for the magnet Z, am.txt 1032–1037, whose M is an arbitrary commutative monoid). A disjoint union of closed immersions into a disjoint union is a closed immersion. Lean: `exists_closed_fixed` (Sec8Representability.lean:956), which has no FG hypothesis, and `presheaf_fixed_ι` (line 1236).
3. Tag 03I2 (read today: G → F a transformation of presheaves, P preserved under base change, fppf local on the base, with descent for fppf coverings; G a sheaf; F an algebraic space; U → F surjective étale with G ×_F U representable and V → U having P; then G is an algebraic space and G → F is representable with P) applied to P = closed immersion, G = X^{D(M/Z)} (a sheaf: `isSheaf_fixedPoints`, line 1145, any M). The properties of P: Tag 03M4 (closed immersions are étale local on the base, read today) together with descent of closed immersions, as the print cites. Lean: `Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent` with `Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`, already used in `prop81FG`.

**Verdict: UNRESTRICTED.** Proposition 8.1 holds as printed for every abelian group M. The only printed gap is the citation of Prop 3.35, stated for M f.g.; its proof extends to all M by replacing "fppf quotient" with fpqc descent for algebraic spaces (Tag 0APL). A one-line remark in a corrigendum suffices: "Proposition 3.35 holds for every abelian group M: D(M)_T → D(Z)_T is an fpqc covering and algebraic spaces are fpqc sheaves [Tag 0APL]."

### 1.5 A second, fppf-only proof under the accepted l.f.p. hypothesis

The repo has no fpqc sheaf property for algebraic spaces. Since X l.f.p. over S is accepted everywhere, here is a proof of 1.3 (d) and (e) using only fppf covers and limit preservation, both in the repo.

Write M/Z = ⋃_F F over the directed set of finitely generated subgroups F ⊂ M/Z, and M_F ⊂ M for the preimage of F. Then Z ⊂ M_F, M_F/Z = F, M = ⋃ M_F directed, and Z[M] = colim_F Z[M_F], so D(M)_T = lim_F D(M_F)_T (Tag 01YW, as the print uses in Prop 3.37, am.txt 1518).

- π_F : D(M_F)_T → D(Z)_T is an fppf covering: Z[M_F] = Z[Z][x^{e_1}, …, x^{e_r}]^{±} for lifts e_j of generators of F, modulo the relations x^{Σ n_j e_j} = x^z for (n, z) in the relation module {n ∈ Z^r : Σ n_j e_j ∈ Z}, a subgroup of Z^r hence finitely generated. So Z[M_F] is a finitely presented, free (coset basis), faithfully flat Z[Z]-algebra. Lean: `extSieve_mem` (Sec8Representability.lean:388) proves exactly this cover for a f.g. group; it must be restated for "M_F/Z finitely generated" in place of "M finitely generated" — its proof only extends a character of Z to M_F fppf-locally, which is the same computation.
- (d'): φ∘π = φ'∘π in X(D(M)_T). To show φ = φ' it suffices to do so Zariski-locally on T (X^Z is a Zariski sheaf, `isSheaf_attractor`), so take T affine. Then the D(M_F)_T are affine with limit D(M)_T, and X l.f.p. over S is limit preserving (Tag 04AK, read today: for algebraic spaces, locally of finite presentation ⇔ limit preserving; Lean `isLimitPreserving_of_lfp`, Sec8Limits.lean:973, whose `IsLimitPreserving` (Sec5Etale.lean:1912) is formulated for exactly such filtered unions of subrings of a ring R' over an affine T, here R' = O(T)[M] ⊃ O(T)[M_F]). Hence φ∘π_F = φ'∘π_F for some F, and φ = φ' because π_F is an fppf covering and X is an fppf sheaf.
- (e'): given a D(M/Z)-fixed x, define ψ_F : D(M_F)_T → X_T, g ↦ g·x. Its two pullbacks to D(M_F) ×_{D(Z)} D(M_F) = D(M_F) × D(F) agree because F ⊂ M/Z acts trivially on x. ψ_F descends along the fppf covering π_F to φ_F : D(Z)_T → X_T (X fppf sheaf), equivariant for D(M_F) by the same argument. Equivariance for all of D(M): for g ∈ D(M)(T'), the equation g·φ_F(z) = φ_F(π(g)z) is checked Zariski-locally on T', T' affine, and then g factors through some D(M_{F'}) with F' ⊃ F by limit preservation of the representable D(Z)... more simply: the two maps D(M)_{T} × D(Z)_T → X_T agree after the fppf covering D(M_F) × D(Z) → D(Z) × D(Z)? No: use instead that for fixed g ∈ D(M)(T'), the two T'-points g·φ_F(π_F(·)) and φ_F(π(g)π_F(·)) of X over D(M_F)_{T'} are both equal to gg'·x, so they agree on D(M_F)_{T'}, hence on D(Z)_{T'} by descent along π_F. This step uses only the fppf cover π_F, no limit. Then φ_F(1) = x. φ_F does not depend on F (two of them agree by (d')).

So with X l.f.p. both directions are fppf plus limit preservation. **Verified** by hand; (d') is where limit preservation enters, (e') uses only fppf descent.

### 1.6 Lean plan for the unrestricted Prop 8.1

Statement: `Prop81Statement` (Sec6FPR.lean:357) as it stands, with its size hypothesis (H2), plus `hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)` if route 1.5 is used; plus `hM : B.Contains (Spec (ZMon M))`, `hQ : B.Contains (Spec (ZMon (M ⧸ Z)))` for `exists_closed_fixed` (these are the size facts `exists_closed_fixed_of_equiv` derives from FG).

Reuse unchanged (none has FG in its proof, only in the ambient `variable`): `exists_closed_fixed` (Sec8Representability.lean:956), `presheaf_fixed_ι` (1236), `isSheaf_fixedPoints` (1145), `Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent`, `Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`, `AttractorPt.toPoint_mem_fixedPoints`, `isSheaf_attractor` (Foundations.lean:187), `IsZFPR` as `IsPullback` (used at line 1294).

New, in a new file:
1. `extSieve_mem_quot`: `extSieve Z a ∈ topology T` under `AddGroup.FG (M ⧸ Z)` instead of `AddGroup.FG M` (same proof as `extSieve_mem`, with `GB.AZmap` for Z ⊂ M; the fppf witness `pullback f (GB.AZmap φ)` is finitely presented over T when M/Z is f.g.).
2. For general M (route 1.5): `fixedEquiv_of_lfp`: `(fixedPoints (quotientAction act Z)).obj (op T) ≃ AttractorPt act Z T` from `hX`, `hfp`, built as in 1.5 (d'), (e') with `isLimitPreserving_of_lfp` on the filtered system of subrings `O(T)[M_F] ⊂ O(T)[M]` (the `IsLimitPreserving` interface of Sec5Etale.lean:1912 takes exactly a family of injective ring maps `gi i : Ri i → R'` with jointly-finite ranges) and `extSieve_mem_quot` for each M_F.
3. `prop81_general`: copy `prop81FG` lines 1284–1307 with `attractorFixedEquivOfCover hsh hcov` replaced by the equivalence of item 2 and `exists_closed_fixed_of_equiv e` by `exists_closed_fixed hd hQ`.

Without the l.f.p. hypothesis the Lean wall is the fpqc sheaf property (Tag 0APL), or at least "isomorphism is fpqc local on the base" (Tag 02L4, read today) applied to equalizers of maps into X; neither is in `AlgMag/` (grep for `fpqc` in `AlgMag/` finds nothing relevant; `.lake` not searched). On paper this is no wall.

---

## 2. Proposition 8.5

### 2.1 Print and Lean

Print, p. 161 (am.txt 1927–1930):

> **Proposition 8.5** Assume that M is finitely generated as abelian group. Assume that X → S is quasi-compact and separated. Then there exists a finitely generated submonoid N_c of N such that X^N = X^{N_c} and N^× = N_c^×.

(N is the magnet of Thm 8.3, am.txt 1855; S an arbitrary scheme, §8 opening.) Printed proof (1932–1958): N_i = ⟨N^× ∪ ν(N_{≤i})⟩; "By Proposition 3.37 X^N(T) = colim X^{N_i}(T)"; "Let U → X be an S-affine N^×-FPR atlas as in Theorem 6.8"; degrees of finitely many generators give c with U^{N_c} = U^{N_i} for i ≥ c; Prop 5.1 and Tag 03I2 for "isomorphism".

Lean statements (all with `[AddGroup.FG M]`, `hX`, `hsep : IsSeparatedOver X`, `hfp` l.f.p., `[CompactSpace S]`, conclusion `∃ Nc ≤ N, Nc.FG ∧ unitsSub Nc = unitsSub N ∧ ∀ T, Bijective (ofLE hc)`):
- `prop85` (Sec8Limits.lean:1382) and `prop85_printed` (PrintedProp85.lean:361): hypothesis `hat`, an N^×-FPR atlas with `HasFiniteAffineDecomposition` (an S-affine atlas; this also encodes "X → S quasi-compact").
- `prop85_free` (FinalAtlasFree.lean:30) and `prop85_atlasFree` (FinalCorAtlas.lean:62): no atlas, but `[S.IsSeparated]`, `hq : IsQuasiCompactSpace X`, `hZ : B.Contains (⊤_ Scheme)`, `hM : B.Contains (Spec (ZMon M))`, and they rest on stubs through `thm68_qc_spaces` (ChartFinalSpaces.lean:44).

Added hypotheses beyond print and agreed list:
- (A1) the S-affine N^×-FPR atlas, in `prop85`/`prop85_printed`;
- (A2) `[S.IsSeparated]`, in `prop85_free`/`prop85_atlasFree`;
- (A3) `hZ`, `hM`: site membership of Spec Z and D(M) — size cutoff, harmless (grade 1), same as (H2) above;
- (A4) `hq : X quasi-compact` versus printed "X → S quasi-compact": equivalent once S is quasi-compact (agreed), since a quasi-compact morphism to a quasi-compact scheme has quasi-compact source. Harmless.

So the content is (A1) and (A2).

### 2.2 The agreed "S quasi-compact" is really needed (recorded, not reopened)

For the record, the print without S quasi-compact fails, as `corrections-verified.md` line 209 suspected. S = ⊔_{n≥1} Spec k, X = ⊔_n A^1_k, M = Z², N = {(a,b) : a > 0} ∪ {0} (a magnet, not finitely generated, N^× = 0), G_m² acting on the n-th copy with weight (1, n) ∈ N. X → S is quasi-compact, separated, of finite presentation, M is f.g. On the n-th copy, X_n^N = X_n (the weight lies in N), while for a finitely generated N_c ⊂ N only finitely many elements of N_c have first coordinate 1 (each is a generator, since a sum of two elements of N∖0 has first coordinate ≥ 2), so (1, n) ∉ N_c for some n and X_n^{N_c} = {0} ≠ X_n^N by Thm 3.20. Hence X^{N_c} ≠ X^N for every f.g. N_c. Verified by hand.

### 2.3 Removing (A1): the atlas exists

Under (A2) this is `prop85_free`: `thm68_qc_spaces` gives an S-affine strongly-FPR atlas for X quasi-compact, separated, l.f.p. over S separated, and `prop85` finishes. The print's own step ("as in Theorem 6.8") is exactly this. No new mathematics; the only cost is that `thm68_qc_spaces` is on stubs (STATUS.md item 5).

### 2.4 Removing (A2): Prop 8.5 does not need S separated

**Claim.** Let S be a quasi-compact scheme, M a f.g. abelian group, X an algebraic space over S, separated, quasi-compact and locally of finite presentation over S, with a D(M)_S-action, N ⊂ M a magnet. Then there is a finitely generated N_c ⊂ N with N_c^× = N^× and X^{N_c}(T) → X^N(T) bijective for all T → S.

*Proof.* 
(1) *Zariski localization on S.* Let V ⊂ S be open, X_V = X ×_S V, and T a V-scheme. Then D(M)_V ×_V T = D(M)_T, A(N)_V ×_V T = A(N)_T, X_V ×_V T = X_T, and the actions agree, so (X_V)^N(T) = X^N(T) for every magnet N, compatibly with the maps X^{N'} → X^N (they are precomposition with A(N')_T → A(N)_T). This is `drop-separated-proof.md` §1.2 Step 1, checked there and again here. X_V → V is separated (Tag 03KL), quasi-compact and l.f.p. (base change).

(2) *Affine pieces of S.* S quasi-compact: choose finitely many affine opens S_1, …, S_n covering S. Each S_k is separated (Tag 01KN), so the corrected Thm 6.8 applies to X_{S_k} → S_k (quasi-separated, l.f.p., separated, quasi-compact): there is an S_k-affine N^×-FPR atlas U_k → X_{S_k}. Then the printed proof of Prop 8.5, i.e. `prop85` over the base S_k, gives a finitely generated N_k ⊂ N with N^× ⊂ N_k (the print's N_i contain N^×, and `prop85` returns `unitsSub Nk = unitsSub N`) and (X_{S_k})^{N_k}(T) = (X_{S_k})^N(T) for every T → S_k.

(3) *One monoid.* Let N_c := ⟨N_1 ∪ … ∪ N_n⟩ ⊂ N. It is finitely generated, and N^× ⊂ N_c ⊂ N gives N_c^× = N^× (`unitsSub_of_between`, Sec8Limits.lean:1333). For T → S_k, the composite X^{N_k}(T) → X^{N_c}(T) → X^N(T) is bijective by (2) and (1); the second map is injective because X is separated (Prop 3.29, `ofLE_injective`, Sec5Etale.lean:1747); so X^{N_c}(T) → X^N(T) is bijective for every T lying over some S_k.

(4) *Gluing.* Let T → S be arbitrary and T_k = T ×_S S_k, a Zariski covering of T. Injectivity of X^{N_c}(T) → X^N(T) is Prop 3.29 again. Surjectivity: given ψ ∈ X^N(T), by (3) there are unique φ_k ∈ X^{N_c}(T_k) over ψ|_{T_k}; on T_k ∩ T_l (which lies over S_k) uniqueness gives φ_k = φ_l, so the φ_k glue to φ ∈ X^{N_c}(T) (X^{N_c} is an fppf, hence Zariski, sheaf: Prop 3.2, `isSheaf_attractor`), and ofLE(φ) = ψ because X^N is separated as a presheaf. This is word for word the last block of `prop85` (Sec8Limits.lean, from `exists_affine_cover` on), with the cover T ×_S S_k in place of the affine cover of T. ∎

**Verified:** (1)–(4) by hand. Step (2) uses only the agreed form of Thm 6.8 over an affine base; nothing in (1), (3), (4) uses separatedness of S. The print's own words at this point, "U is an S-affine scheme of finite presentation over S", are what fail over a non-separated S (doubled-origin plane, `corrections-verified.md` vote 10); the repair is to run that paragraph over each affine S_k.

**Verdict: UNRESTRICTED** relative to the agreed hypotheses. (A1) follows from Thm 6.8 (S separated case: `prop85_free`); (A2) is removable by Zariski localization on the quasi-compact base. The corrigendum wording for Prop 8.5 should therefore be: "Assume M finitely generated, S quasi-compact, and X → S quasi-compact, separated and locally of finite presentation." It should not import "S separated" from Thm 6.8; `corrigendum-items.md` line 4 ("Prop 8.5 takes the same hypotheses") overshoots.

### 2.5 Lean plan

- (A1): already done, `prop85_free` / `prop85_atlasFree`; they become sorry-free when the stubs behind `thm68_qc_spaces` are built.
- (A2): needs the change of base site to an open V ⊂ S, the same infrastructure as `drop-separated-proof.md` §1.3 items 1–3 (`ιV : BigFppfOver B V hV ⥤ BigFppfOver B S hS`, restricted `IsAlgebraicSpace`/`IsSeparatedOver`/`IsLocallyOfFinitePresentation`/`AAction`, and `AttractorPt act_V N T ≃ AttractorPt act N (ιV T)` commuting with `ofLE` and `baseChange`). Then:
  1. `S.affineCover` finite subcover (`isCompact_univ.elim_finite_subcover`, as in `exists_finset_degrees`, Sec8Limits.lean:1259);
  2. on each piece, `prop85_free` with `[S_k.IsSeparated]` from `IsAffine` (instance `isSeparated_of_isAffine`-type, as `drop-separated-proof.md` §1.3 item 5 notes), giving `N_k`;
  3. `N_c := ⨆ k, N_k`, `AddSubmonoid.FG` of a finite sup, `unitsSub_of_between`;
  4. the gluing block of `prop85` (Sec8Limits.lean, from `obtain ⟨I, W, π, hW, hmem⟩ := exists_affine_cover T`) with the pulled-back cover and `ofLE_injective hX hsep`.
  Items 1–4 are short once the site-change functor exists; that functor is the whole cost, and it is shared with the Prop 3.31/3.32 localization plan, so it should be written once.
- Alternative without site change: redo `exists_finset_degrees` with charts that are affine schemes rather than `IsAffineHom` over S. Not recommended: the grading `GB.gradingOf (Uk k).2` is an O(S_k)-algebra grading of an S_k-affine chart, so the lemma would have to be reproved over each affine open of S anyway, which is the localization in disguise.

---

## 3. Summary

| Statement | Added hypothesis | Verdict |
|---|---|---|
| Prop 8.1 | M finitely generated | UNRESTRICTED: holds for every abelian M; Prop 3.35 extends to all M by fpqc descent (Tag 0APL), or, with X l.f.p., by fppf covers D(M_F) → D(Z) plus limit preservation (Tag 04AK) |
| Prop 8.1 | D(M)_T in the site | size cutoff, harmless |
| Prop 8.5 | S-affine N^×-FPR atlas | UNRESTRICTED: Thm 6.8 over affine opens of S |
| Prop 8.5 | S separated | UNRESTRICTED: Zariski localization on the quasi-compact S, then gluing with Prop 3.29 and Prop 3.2 |
| Prop 8.5 | S quasi-compact (agreed) | NEEDED: counterexample §2.2 |
| Prop 8.5 | site membership `hZ`, `hM` | size cutoff, harmless |
