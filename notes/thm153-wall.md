# Theorem 15.3 in the §15 generality: what is closed now, and the exact new wall (2026-11-08)

Pure mathematics, nothing compiled, no existing file edited. Magnet language only.

Source: [AM] = Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), read through `am.txt` (Prop 3.24 p.146, Prop 3.29-3.32 pp.147-150, Fact 3.34 p.150, Prop 3.37 p.153, Prop 5.1 p.155, Def 6.1 / Thm 6.8 pp.156-158, Prop 8.1 / Thm 8.3 pp.159-160, §15 pp.184-185). Starting point: `notes/thm153-close.md` (Lemmas A-E there are re-used by name). "Verified" = redone here. "Quoted" = taken from a note, a Lean name, or a Stacks tag without redoing.

Standing reductions from thm153-close.md (verified there, used here): Thm 15.3 ⟺ (F) + (C) (Lemmas A, B); (F) holds (Prop 3.32 (ii) for spaces = `SDFinal.prop332_space`, M f.g. group); cancellative M reduces to M^gp (Lemma E); x ∈ X^N(T) ⟺ o_x factors through A(N)_T (Lemma C); one may replace X_T by the orbit closure Z of x (Lemma D). All pointwise statements below are for T = Spec R affine, x ∈ X(T), and may be checked étale-locally on T (X^N is an fpqc sheaf on T and X^N → X is a monomorphism, Cor 3.30, so local sections glue). By Prop 3.9 everything is over T, so S = T affine, in particular separated.

---

## 1. W2 (M a non-f.g. group) is closed when X is locally of finite presentation, with no atlas (verified)

Throughout §1: M any abelian group, X separated over S and l.f.p. over S, no quasi-compactness, no atlas. Limit tool: for Y → S l.f.p. (scheme or algebraic space) and W = lim W_α a directed limit of qcqs S-spaces with affine transitions, Hom_S(W, Y) = colim Hom_S(W_α, Y) (Stacks 01ZC for schemes; the Limits of Spaces analogue, quoted as "01ZC for spaces"). In particular two maps W_α → Y that agree after W → W_α agree after some W_β → W_α.

**1.1 Lemma D of `prop331-332-spaces-proof.md` for a non-f.g. grading group, X l.f.p.** Setting of that note: P a monoid, δ : P → Γ a homomorphism to an abelian group, P_0 = δ^{-1}(0), W = A(P)_T → Q = A(P_0)_T. Claim: if X is l.f.p. and separated, every D(Γ)-invariant F : W → X factors uniquely through Q, even for Γ not f.g.
Proof. Write Γ = ⋃ Γ_α (f.g. subgroups), P_α := δ^{-1}(Γ_α) ⊃ P_0, W_α = A(P_α)_T, so W = lim W_α (R[P] = colim R[P_α], transitions dual to inclusions, affine). F factors through some F_α : W_α → X (limit tool). Invariance: F_α ∘ act_α and F_α ∘ pr_2 on D(Γ_α) × W_α agree after D(Γ) × W → D(Γ_α) × W_α (they become F ∘ act and F ∘ pr_2; the projections are equivariant), hence after some D(Γ_β) × W_β → D(Γ_α) × W_α; F_β := F_α ∘ (W_β → W_α) is D(Γ_β)-invariant. Lemma D (Γ_β f.g., all algebraic spaces, `SDFinal.lemmaD_space`) gives f : Q → X with F_β = f ∘ π_β, hence F = f ∘ π. Uniqueness: π is dual to the split injection R[P_0] ⊂ R[P], so schematically dominant, and X is separated. ∎

**1.2 Prop 3.32 (ii) and (F) for any abelian group M, X l.f.p. separated.** Run §2 of that note verbatim with Γ = N^gp + L^gp (possibly non-f.g.), using 1.1 instead of Lemma D: (X^N)^L = X^{N∩L}. Hence (F) as in thm153-close §1. Prop 3.31 (ii) likewise for f : M → Z any homomorphism of abelian groups (K = f(M) + Y^gp non-f.g. allowed): X^{f^{-1}Y}_M = X^Y_Z.

**1.3 Reduction of a pointwise statement to a f.g. group.** Fix T affine and x ∈ X(T). Let Z ⊂ X_T be the orbit closure (Lemma D), quasi-compact; choose a quasi-compact open V ⊂ X_T containing Z and put X' := D(M)_T·V, the image of D(M) × V under the action. X' is open (the action map is isomorphic to pr_2, and pr_2 : D(M) × X_T → X_T is universally open: a qc open of the limit D(M) × X_T = lim D(M_α) × X_T comes from a finite level, where pr_2 is flat l.f.p.), quasi-compact, D(M)-stable, separated and l.f.p. over T, and contains Z. Every equivariant A(N)_T → X_T with value x at 1 lands in Z (Lemma D of thm153-close) hence in X'; so x ∈ X^N(T) ⟺ x ∈ X'^N(T) for every magnet N. Now X' is qcqs and l.f.p. over T, so the action X' × D(M) = lim X' × D(M_α) → X' factors through a_α : X' × D(M_α) → X' for a f.g. subgroup M_α ⊂ M, and the action axioms, which hold after X' × D(M) × D(M) → X' × D(M_α) × D(M_α), hold at a finite level β ≥ α (limit tool; the unit axiom is immediate). So the D(M)-action on X' is pulled back from a D(M_β)-action along D(M) → D(M_β), dual to the inclusion f : M_β → M. By 1.2 (Prop 3.31 (ii) for f, Z := M non-f.g., M := M_β): X'^N_M = X'^{N ∩ M_β}_{M_β} for every magnet N ⊂ M.

**1.4 Consequence.** For X l.f.p. separated over S and M any abelian group, (C) (indeed every common-attractor family statement) for the pair (X, M) follows from the same statement for (X', M_β) with M_β f.g., X' qc separated l.f.p. over the affine T. The latter is W1 restricted to l.f.p. spaces, which is closed by Thm 6.8 (M_β f.g., X' qc l.f.p. qs over T; gives an S-affine Z-FPR atlas) and `fact334_free` (quoted, on the Thm 6.8 stubs), or independently by §3 + §4.1 below. So: **Thm 15.3 holds for every cancellative M and every separated X locally of finite presentation over S, without atlas and without quasi-compactness** (modulo the two quoted inputs). This removes the "S-affine strongly-FPR atlas", "S quasi-compact" and "M^gp f.g." hypotheses of the conditional row of thm153-close §3.

What 1.1-1.4 do not give: anything for X not l.f.p. (the limit tool is the only place where l.f.p. enters, and it enters in every step).

---

## 2. Quasi-affine orbit closure, sharp case (verified)

Setting of W1: M = Z^r, 𝕋 = D(M)_T, N_1 ⊃ N_2 ⊃ … with N_1 sharp (the unit case reduces to this by fact334-attempt R0-R1, which use only descent along a torsor and separatedness; quoted), Q = ⋂ N_k, f_k : A(N_k)_T → Z equivariant with f_k ∘ π_{1k} = f_1, v := f_1(vertex) ∈ Z(T) fixed.

If Z is quasi-affine, then Z → Z' := Spec O(Z) is an equivariant open immersion (O(Z) is M-graded, and the canonical map is equivariant). Prop 3.24 for Z' gives q' : A(Q)_T → Z' equivariant with q' ∘ π_1 = f_1. The open q'^{-1}(Z) ⊂ A(Q)_T is 𝕋-stable and contains the vertex section (q'(vertex) = v ∈ Z); a stable open containing the vertex section is all of A(Q)_T (every point of A(Q)_T lies in the closure of the big torus of its fibre, whose generic point generizes the vertex point of that fibre). So q' lands in Z and x ∈ Z^Q(T). ∎  (Not a scheme hypothesis: Z may be a non-scheme quasi-affine space? No: a quasi-affine algebraic space is a scheme. So this is a special case of the fourth pass; recorded because its proof is three lines and chart-free.)

---

## 3. The equivariant-section lemma and the conditional theorem (verified, from Part B Step 3-4)

**Lemma S.** Let T = Spec R, N ⊂ Z^r a sharp submonoid (not necessarily f.g.), W = A(N)_T, 𝕋 = D(Z^r)_T, J ⊂ R[N] the ideal of N∖0, V = V(J) ≅ T the vertex. Let P → W be an étale, separated, 𝕋-equivariant morphism from an algebraic space with 𝕋-action, and s_0 : V → P an equivariant section over V. Then there is an étale cover {T_i → T} and equivariant sections σ_i : W_{T_i} → P_{T_i} with σ_i|_V = s_0.

Proof. This is Steps 3-4 of Part B of `prop331-332-spaces-proof.md` (Lean: `SDExist*`, assembled in `SDFinal`), with W' := P. Their Step 3 (ii) constructs a lifted action on W' from an invariant map; here the action on P and the equivariant section are hypotheses, and the rest never uses how they arose. Checklist against the text: (i) over B_0 = O^{sh}_{T,t̄}, B = B_0[N], the unique maximal proper homogeneous ideal is m B + J, V(I) = Spec k is the vertex point, B/I = k[Λ] with Λ = 0; s_0 provides the equivariant section over V(I). (ii) P is étale and separated over Spec B, and a qc open containing s_0(V(I)) saturates to a stable qc open 𝒱 (𝕋 flat f.p.). (iii) graded integral closure C' of B in Γ(𝒱, O): uses only that the grading group Z^r is torsion-free (03GG with B → B[Z^r] smooth), and 03GW (𝒱 → Spec B of finite type, separated, quasi-finite: étale) for 𝒱 → Spec C' open; no finiteness of N or R enters. (iv)-(v) idempotents in the degree-0 part and rank 1: verbatim, giving σ : Spec B → P equivariant with σ|_{V(I)} = s_0. Step 4: σ lands in a qc open of P, l.f.p. over W, so it comes from σ_i over Spec B_i = W ×_T T_i, T_i → T an affine étale neighbourhood of t̄ (01ZC); equivariance holds at a finite level because the equalizer of two sections of a separated étale morphism is open and closed and a limit of nonempty qc schemes is nonempty; σ_i|_V = s_0 at a finite level for the same reason (both are sections over V = Spec A_i which agree after Spec B_0). ∎

Remark (used twice below). Let E ⊂ W be a 𝕋-stable subset which is open and closed and contains V. Then E = W. Indeed for t ∈ T the fibre W_t = Spec κ(t)[N] is irreducible (N ⊂ Z^r); its generic point generizes the vertex point over t, so lies in the open E; E is closed, so E ⊃ W_t. (Stability is not even needed here.) Hence two equivariant sections of a separated étale P → W that agree on V agree everywhere.

**Theorem (conditional).** Setting of §2 (M = Z^r, N_1 sharp, Q = ⋂ N_k, v = f_1(vertex), Z separated over T, no finiteness). Assume

> (E) étale-locally on T, v has a 𝕋-equivariant étale neighbourhood u : U → Z with U affine over T and a lift ṽ : T → U of v (automatically 𝕋-fixed: U^𝕋 = Z^𝕋 ×_Z U by Prop 6.3, M torsion-free).

Then x ∈ Z^Q(T). In particular (C) holds for x, and if (E) holds at every fixed point of every orbit closure, Thm 15.3 holds for (X, M).

Proof. Shrink T so that ṽ exists. For each k put P_k := A(N_k)_T ×_Z U, a scheme (fibre product of schemes over an algebraic space), étale and separated over A(N_k)_T, with the 𝕋-action t·(w, u') = (tw, tu') (well defined since u is equivariant and f_k is equivariant), and the equivariant section s_0 = (vertex, ṽ) over V (both f_k(vertex) = v and u(ṽ) = v; equivariant because both are fixed). Lemma S gives, after an étale cover of T, equivariant sections σ_k of P_k, i.e. equivariant lifts f̃_k : A(N_k)_T → U of f_k with f̃_k(vertex) = ṽ. Compatibility: f̃_k ∘ π_{1k} and f̃_1 are two equivariant sections of P_1 → A(N_1)_T (the first because π_{1k} is equivariant and f_k ∘ π_{1k} = f_1) agreeing on V; by the Remark they agree. So x̃ := f̃_1(1) ∈ U(T) lies in U^{N_k}(T) for all k. U is affine over T with a D(Z^r)-action, so Prop 3.24 gives x̃ ∈ U^Q(T): an equivariant q̃ : A(Q)_T → U with q̃(1) = x̃. Then q := u ∘ q̃ is equivariant with q(1) = u(x̃) = f_1(1) = x, so x ∈ Z^Q(T) over the cover, hence over T (sheaf + monomorphism). ∎

Note that the extension q is not unique a priori beyond Prop 3.29, and that the theorem uses neither Hahn series nor fpqc descent along 𝕋 × Spec Λ: with an equivariant affine chart, the whole difficulty of the fourth and fifth passes disappears. The scheme case is not recovered this way (a scheme need not satisfy (E)); it keeps its own proof.

**Where (E) is known.** (a) Z locally of finite presentation over T: this is the étale local structure theorem of Alper-Hall-Rydh at the point v of [Z/𝕋], whose stabilizer 𝕋 is linearly reductive; in [AM] it is what Romagny's appendix extracts from [3] for Thm 6.8 (an equivariant atlas by stable affines, Def 6.1 (iv)), and an equivariant atlas with a chart through v is exactly (E) (quoted; AHR/appendix not re-read). Together with §1 this gives Thm 15.3 for all l.f.p. separated X and cancellative M, independently of `fact334_free`. (b) Z quasi-affine: §2 (U = Z' itself is not étale over Z, but the argument of §2 replaces the theorem). (c) The weaker (E') "(E) for Z^{N_1} in place of Z" suffices: x ∈ (Z^{N_1})^{N_k} = Z^{N_k} by Prop 3.32, and (Z^{N_1})^Q = Z^Q; (E') holds whenever Z^{N_1} is representable and Z^{N_1} → Z^0 is affine (take U = Z^{N_1} ×_{Z^0} V for an étale affine V → Z^0 through v; V → Z^0 is equivariant since 𝕋 acts trivially on Z^0). But representability of Z^{N_1} (Thm 8.3) itself requires an N_1^×-FPR atlas, i.e. (E)-type charts; so (E') is not a genuinely weaker input in the paper's framework.

---

## 4. The exact new wall

**(W1*) Equivariant affine étale charts at a fixed point of a non-l.f.p. orbit closure.** Precisely: T affine, 𝕋 = D(Z^r)_T, Z a quasi-compact separated algebraic space over T with 𝕋-action which is the scheme-theoretic closure of one orbit 𝕋·x, x ∈ Z^{N_1}(T) with N_1 ⊂ Z^r sharp, v = lim_{N_1} x ∈ Z^𝕋(T). Does v have, étale-locally on T, a 𝕋-equivariant étale neighbourhood U → Z with U affine over T? Equivalently: does the closed point of the quotient stack [Z/𝕋] over the closed point of T have an étale neighbourhood of the form [U/𝕋], U affine, with the same stabilizer (the étale local structure / Luna slice statement, without the finite presentation hypothesis)?

Status of (W1*): yes when Z is l.f.p. (AHR), yes when Z is a scheme? — unknown and not needed (the scheme case of Thm 15.3 has its own proof). For Z neither l.f.p. nor a scheme, (W1*) is a case of Rydh's Question 2.13 (approximation of [Z/𝕋] by finitely presented stacks: equivariant charts spread out from finite level, so a negative answer to (W1*) gives a stack with affine stabilizers not of approximation type, and conversely an equivariant approximation Z = lim Z_λ would give (E) at finite level). No example is known either way; in particular **no counterexample to Thm 15.3 can be written down today**: it would have to be a separated, non-l.f.p., non-scheme orbit closure whose fixed point violates (E), and it would settle Rydh's question.

**What Thm 15.3 now reduces to, in the printed generality with M cancellative:** (W1*) for the orbit closures of X, for M^gp finitely generated (§1 reduces non-f.g. M^gp to this when X is l.f.p.; when X is not l.f.p. and M^gp is not f.g., (W2) remains as stated in thm153-close §4, since the limit tool of §1 is unavailable and Lemma D for non-f.g. Γ is not known there).

**(W3)** M not cancellative: unchanged (no tool).

---

## 5. Verdict

- Proved in the printed generality (M cancellative), new: Thm 15.3 for every separated X locally of finite presentation over S, any abelian group M^gp, no atlas, no quasi-compactness of X or S (§1; quoted inputs: `SDFinal.lemmaD_space`, the Limits-of-Spaces form of 01ZC, and either Thm 6.8 + `fact334_free` or AHR for (E)).
- Proved, new: (E) ⇒ (C) at the point, with a short chart-free proof via Prop 3.24 (§3); the scheme-case machinery (Hahn series, diagonal, fpqc descent along 𝕋 × Spec Λ) is not needed once an equivariant affine chart exists.
- Not proved, not refuted: X separated, not l.f.p., not a scheme, M^gp = Z^r: Thm 15.3 ⟸ (W1*). This is the exact new wall; it is the étale local structure of [Z/𝕋] at a fixed point without finite presentation, and any counterexample would answer Rydh's Question 2.13 in the negative.
- Smallest honest statement with no new hypothesis beyond the print: "Theorem 15.3 holds if X is locally of finite presentation over S, or affine over S, or a scheme [fourth pass, unreviewed]; in general it holds whenever every fixed point of every orbit closure in X admits an equivariant affine étale chart."

Stacks tags cited, not re-read: 01ZC, 03GG, 03GW, 0APL. Lean names quoted: `SDFinal.lemmaD_space`, `SDFinal.prop332_space`, `SDExist*`, `fact334_free`. External: Alper-Hall-Rydh étale local structure (via [AM] appendix / Thm 6.8), Rydh J. Algebra 422 (2015) Question 2.13 (quoted from the earlier notes).
