# AHR Cor. 10.2 for D(M): specialized proof

**Note on the Lean formalization (2026-11-06).** This note predates it, and §4.2 and §7 below describe the plan on paper. The Lean proof departs from them in two places. Lemma 4.2 uses Stacks 04S6 (quotient of an algebraic space by a free action, `AlgMag/ChartStratumFlat.lean`, `ChartStratumQuotient.lean`) instead of Stacks 06RC (dense open gerbe): no quotient stack appears. Input I1 (Bhatt Thm 1.1) is replaced by Stacks 0GHK, the restricted section form for A noetherian and X separated, locally of finite type (`AlgMag/ChartSplit.lean`, `ChartEffectiveAlg.lean`, `ChartEffectiveMain.lean`).

**Target (Theorem).** M f.g. abelian, G = D(M), S finite type over Z, X a separated algebraic space of finite type over S with G-action, x a closed point. Then there is U affine and (U,u) -> (X,x) étale, G-equivariant, with κ(u) = κ(x), G_u = G_x.

## 0. Result and status

**The Theorem is proved below, given the published inputs of §7.** Stacks do not appear, and neither do Tannaka duality or a cotangent complex. The chain has been checked only by its author (this note): nothing here is refereed, and no independent read has been done.

Which published route is shortest:

- **Route P, pure citation.** AHR Thm 5.6 at W_0 = G_x, with three substitutions: Thm 1.10 is replaced by the graded completion (§3), the map to [X/G] comes from Hall–Rydh Thm 8.4(i)(b) ([X/G] has affine diagonal, so T need only be noetherian), and algebraization comes from AHR20 Thm A.17/A.18 with T = Spec C_0, X_1 = [X/G], X_2 = BG. The affine clause of A.17 keeps W -> BG affine. This is the shortest route on paper. It rests on two long black boxes.
- **Route S, the proof below.** The same four steps with those two black boxes opened and cut down for D(M).
  - The induction is the one in Hall–Rydh's proof of Thm 8.4: stratify, treat U and the thickenings of Z, glue.
  - For D(M), a stratum is an affine G-stable open, so their Main Lemma 6.1 reduces to a ring map.
  - Their functor formalism reduces to one pullback system.
  - Their gluing Cor. 7.3 is replaced by Bhatt Thm 1.1 + Thm 1.4(1).
  - The Artin step is A.17 written out in graded polynomial coordinates.
  - Route S is the better one for Lean, since its inputs are few and sharply stated (§7).

Search result: one web search found no separate simplified proof for tori or D(M) beyond AHR itself. AHHLR (arXiv:2205.08623) Thm 1.2 and Thm 2.3 generalize the statement; I read those statements, and they do not shorten this case. One search does not establish that no such proof exists.

The notes `ahr-diagonalizable-*.md` are superseded on the main point. Their "gap (N)/G2" is not a gap on this route: normality, Sumihiro, pinching and Keel–Mori are not used. Their claim that gluing on Spec C \ V(I) is "unavailable in general" is false; noetherian induction makes it available (§4). What I reuse from them after rechecking: Shrinking Lemma 1.3 (§6) and the reduction R2 (§1).

## Conventions

- Everything is M-graded and G = D(M) is over Z. Homogeneous ideals are the G-stable ones.
- R1: the S-structure plays no role, so forget S and work over Z.
- A **complete pair** (C,m) is a noetherian M-graded ring C with homogeneous ideal m such that C_d -> lim (C/m^n)_d is bijective for all d.

## 1. Reductions: the point and the orbit

**AHR.** Thm 5.6 Step 1 is a limit reduction to excellent S. Here it is unnecessary (S is of finite type over Z).

**D(M), rational point.** κ(x) is a finite field. Let f in Z[t] lift the minimal polynomial of a generator of κ(x)/F_p. Then Z' = Z[t]/(f), localized suitably, is étale over Z at a point with residue field k := κ(x). Replacing X by X ×_Z Z' (compose the final chart with the étale equivariant map to X) makes x rational with residue field k. Stabilizers and k are unchanged.

**Orbit.** The stabilizer H ⊂ G_k is closed (X separated), so H = D(M/Z_0) for a subgroup Z_0 ⊂ M. The orbit map gives a monomorphism o : O := G_k/H = Spec k[Z_0] -> X.

**Lemma 1.1.** After replacing X by a G-stable open containing x, o is a closed immersion.

*Proof.*
- Let Y be the scheme-theoretic image of o, a closed G-stable subspace.
- Take a generic point η of O over a generic point y of Y. Then A = O_{Y,y} -> B = O_{O,η} is a local map of artinian rings. It is injective because Y is the scheme-theoretic image and the fibre of the monomorphism over y is one point.
- Since o is a finite type monomorphism, B/m_A B ⊗ B/m_A B = B/m_A B, so B/m_A B is the common residue field. Nakayama gives surjectivity, so A = B.
- Hence o is flat at η. The flat locus is open and G-stable in O, and G is transitive on O over k̄, so o is flat everywhere.
- A flat finite-presentation monomorphism is an open immersion. Remove the closed G-stable set |Y| \ |O| from X. ∎

**What remains:** nothing. Note that x need not be fixed; no slice or coinduction step is needed, and D(Z_0) with μ_p in it causes no problem (the failed slice reduction F1 of the old notes is simply avoided).

## 2. Step (1): the deformation

**AHR.** Thm 1.11/5.1: deform h_0 : W_0 -> G_x to thickenings, using vanishing of Ext^2(L, -).

**D(M).** The theorem has W_0 = G_x (h_0 an isomorphism), so W_n := X_n, the n-th thickening of O in X, with ideal I (G-stable, as G is flat). X_n is affine (Stacks 07VT, thickening of affine). Write O_n = Γ(X_n). There is nothing to deform.

## 3. Step (2): the graded completion

**AHR.** Thm 1.10 (effectivity) via Prop 4.16 and Lemma 4.12, Lemma 4.9, and Thm 1.6/4.5 (coherent completeness).

**D(M).** Define C_d := lim (O_n)_d, C := ⊕ C_d, T := Spec C, m := ker(C -> k[Z_0]).

**Lemma 3.1 (Gordan/Dickson).** If B is an M-graded f.g. algebra over a noetherian ring, then B_0 is f.g. and each B_d is finite over B_0.

*Proof.* It suffices to take a polynomial ring with degree map N^n -> M. The kernel monoid K is generated by the minimal nonzero elements of K (finite by Dickson), because if a ≥ b in N^n and a, b ∈ K, then a-b ∈ K as M is a group; torsion in M is harmless. Each fibre is a finite union of K-translates by Dickson. Take the degree-d part of a graded surjection; it is exact. ∎

**Lemma 3.2.** C is noetherian, (C,m) is a complete pair, and C/m^{n+1} = O_n as graded rings. Also C_0/m_0 = k, a finite field.

*Proof.*
- B := ⊕_i I^i/I^{i+1} is generated over k[Z_0] by the finite module I/I² (coherent on affine O). So B is f.g. over k, graded by N × M.
- By Lemma 3.1, B_0 is f.g. over k and B_d is finite over B_0.
- C_d carries the filtration F^i = ker(C_d -> (O_{i-1})_d). Surjectivity of the transition maps gives gr_F C_d = B_d (degree d part). This filtration is complete with noetherian associated graded, so C_0 is noetherian and C_d is finite over C_0 (the theorem cited in AHR Lemma 4.9 as [God56, Thm 4]). Homogeneous lifts of generators of B generate C over C_0. So C is noetherian.
- f.g.-ness of the Rees algebra makes the F-topology on C_0 adic (the argument of AHR Thm 4.1), so finite submodules are closed.
- B is generated in i = 1 over i = 0, so F^i = m^i + F^N for all N; closedness gives F^i = m^i. ∎

**Lemma 3.3 (graded Krull).** If (C,m) is a complete pair and N is f.g. graded, then ∩ m^n N = 0, and C/b is a complete pair for each homogeneous ideal b.

*Proof.* Elements of 1 + m_0 are units (geometric series, using completeness). If E = ∩ m^n N, then E = mE by Krull/Artin–Rees. For homogeneous generators e_i of E, write e_i = Σ a_ij e_j with a_ij homogeneous of degree d_i - d_j. Then det(1 - (a_ij)) ∈ 1 + m_0 is a unit and kills E. Completeness of C/b: surjectivity by Mittag-Leffler, injectivity from ∩ m^n(C/b) = 0. ∎

**Lemma 3.4 (Grothendieck existence for graded rings).** Let (C,m) be a complete pair. A compatible system of f.g. graded C/m^n-modules N_n (with N_{n+1}/m^n = N_n) has N := ⊕_d lim (N_n)_d f.g. graded with N/m^n N = N_n. Also Hom_gr(N,N') = lim Hom_gr(N_n,N'_n).

*Proof.* Homogeneous generators of N_1 lift compatibly. This gives L = ⊕ C(-d_i) -> N_n, surjective by nilpotent Nakayama. The kernels K_n surject onto one another. Put K := ⊕ lim (K_n)_d ⊂ L (L is degreewise complete). Exactness of lim on surjective systems gives N = L/K, and K -> K_n is onto, so N/m^nN = N_n. Homs: lift over L, then pass to the quotient; injectivity by Lemma 3.3. ∎

This replaces all of AHR §4 (it is AHR Thm 4.5's argument, with vector bundles being graded free modules). **What remains:** nothing.

## 4. Step (3): effectivity, the hard point

**AHR.** Step (3) is Tannaka duality [HR19]; for X a non-affine target this is Hall–Rydh Thm 8.4, whose proof stratifies X and glues along T with Cor. 7.3.

**Why naive descent fails.** G × Spec Â -> Spec C is an fpqc cover, but the cocycle lives on a non-noetherian ring: a⊗1 - 1⊗a is in ∩ t^n (k[[t]] ⊗_{k[t]} k[[t]]) (old notes). The cure is that one does not descend from the completion alone. Over the open stratum the map is already known, and the difference element then also lies in a power-torsion ideal. That is exactly what Lemma 4.5 uses.

**Theorem 4.1 (equivariant effectivity).** Let X be a separated noetherian algebraic space with G-action and (C,m) a complete pair. Every compatible system of equivariant maps φ_n : Spec C/m^n -> X extends to a unique equivariant φ : Spec C -> X.

*Uniqueness.* For two extensions the equalizer is closed (X separated), defined by a homogeneous ideal contained in ∩ m^n = 0 (Lemma 3.3).

*Existence* is by noetherian induction on G-stable closed subsets of |X|, for all closed G-stable structures on them at once.

**Lemma 4.2 (affine stratum).** If X ≠ ∅ there is a nonempty G-stable affine open U ⊂ X.

*Proof.*
- Let 𝒳 = [X/G] and let 𝒳_red -> 𝒳 be the reduced closed substack, with X' -> X its pullback (a G-stable thickening; X_red need not be G-stable when μ_p ⊂ G). Inertia of 𝒳 is quasi-compact (it is closed in G × X).
- Stacks 06RC gives a dense open 𝒰 ⊂ 𝒳_red which is a gerbe, over an algebraic space Q that is reduced (06QK-type descent; see §7). Shrink Q to an affine integral open with generic point ξ. Let U' be the preimage in X'.
- U'_ξ is nonempty and of finite type over κ(ξ), so it has a point u' over a finite extension K. In the gerbe 𝒰_K, the point defined by u' is an fppf cover, so its pullback, the orbit map G_K -> U'_K, is an fppf cover with fibres the stabilizer H_K. H_K is closed, so H_K = D(M/Z'), and U'_K = D(Z') is affine.
- By fpqc descent U'_ξ is affine. By limits (Stacks 07SQ) U' is affine over some affine open of Q. By 07VT, the open U ⊂ X with the same points is affine. It is G-stable. ∎

**Setup for the induction.**
- Let U be as in Lemma 4.2 and Z = |X| \ U with J the ideal of the reduced closed substack structure of [Z/G], so J is G-stable. Then |Z| ⊊ |X|.
- Put T = Spec C and a_n := J·(C/m^n) (this is φ_n^*J's image), a := ⊕ lim (a_n)_d, a homogeneous ideal of C. Then a + m^n/m^n = a_n.
- ω(F) denotes the Lemma 3.4 module of the system φ_n^*F, for F equivariant coherent on X.
- T_U := T \ V(a), T^(k) := Spec C/a^k.

**Lemma 4.3 (map on the open stratum).** There is a canonical equivariant T_U -> U.

*Proof (Deligne's formula).*
- For f ∈ O(U)_d, there are N and an equivariant ψ : J^N -> O_X(d) extending f. (Deligne's formula gives ψ; the two pullbacks of ψ to G × X agree on G × U, so after raising N they agree.)
- Let N' = ω(J^N), with ν : N' -> C of image a^N and Ψ = ω(ψ) : N' -> C(d).
- ker(φ_n^*J^N -> C/m^n) is a Tor_1(O/J^N, C/m^n), which is killed by a_n^N. So by Lemma 3.3, a^N ker ν = 0.
- Thus for homogeneous g ∈ a, ν_g : N'_g ≅ C_g, and s_f := Ψ ν_g^{-1}(1) ∈ (C_g)_d is defined. These glue on T_U and are independent of N.
- f ↦ s_f is a graded ring map (multiplicativity from J^N ⊗ J^N' -> J^{N+N'} and Lemma 3.4). U is affine, so this is an equivariant map. ∎

**Lemma 4.4 (map on the closed stratum).** By induction there are compatible equivariant maps T^(k) -> Z^(k) := V(J^k), since (C/a^k, m) is a complete pair (Lemma 3.3), its truncations map to Z^(k), and |Z| ⊊ |X|. Uniqueness makes them compatible in k.

**Glue.** Let Ĉ be the a-adic completion and T̂ = Spec Ĉ. By **Bhatt Thm 1.1**, the system T^(k) -> X extends to θ : T̂ -> X. (This is non-equivariant, which is why it cannot be fed by the induction. Note: no circularity, since it is an independent theorem.) Its failure mode for schemes is not relevant: Bhatt's statement holds for qcqs spaces and any adically complete ring.

*Compatibility on V = T̂ \ V(aĈ).*
- θ^*J·Ĉ + a^kĈ = aĈ for k ≥ 2, and Nakayama (a in the radical of Ĉ) gives θ^*J·Ĉ = aĈ. So θ^{-1}(U) = V.
- Both θ|_V and (T_U -> U)|_V are given by the formula of Lemma 4.3: the f.g. Ĉ-modules θ^*J^N and N' ⊗ Ĉ have the same truncations mod a^k (uniqueness in Lemma 3.4 over C/a^k), so they coincide with compatible ν, Ψ. So they agree.

**Bhatt Thm 1.4(1)** applies to the flat map T̂ -> T with closed subscheme V(a) (flat gives Tor-independence, and the preimage of V(a) is V(a)): T is the pushout in qcqs spaces of T_U and T̂ along V. This yields φ : T -> X.

*φ extends φ_n, and φ is equivariant.* Use:

**Lemma 4.5 (separating).** Let C be noetherian, a an ideal, R a flat C-algebra, and r ∈ R with a^s r = 0 and r ∈ a^k R for all k. Then r = 0.

*Proof.* Flatness gives (0:a^s)_R = (0:a^s)_C R and a^kR ∩ (0:a^s)_C R = (a^k ∩ (0:a^s)_C)R. Artin–Rees gives a^k ∩ (0:a^s)_C ⊂ a^{k-c}(0:a^s)_C = 0 for k ≥ s + c. ∎

(This is the content of "separating" in Hall–Rydh Lemma A.2 and Cor. 7.3(i)(a), whose hypothesis ker(O_T -> j_*O_U) ∩ ∩I^n = 0 is the same. I did not read their A.2.)

- Two maps G × T -> X, action then φ and φ then action, have closed equalizer (X separated). They agree on G × T_U (Lemma 4.3 is graded) and on G × T^(k) (induction). Apply Lemma 4.5 with R = O(G) ⊗ C, flat. The ideal generated by a is the same under both pullbacks, since a is homogeneous.
- Likewise φ|_{Spec C/m^n} = φ_n, with R = C/m^n after replacing a by its image (noetherian ring, R = itself). ∎

**Remark (a replacement for Thm 1.4(1), for Lean).** Instead of Bhatt's pushout, use T_U ⊔ T̂ -> T, an fpqc cover, and X's fpqc sheaf property (Gabber, Stacks 0APL, read). The only nontrivial overlap is T̂ ×_T T̂: the equalizer is closed, contains the part over T_U and contains all V(a^kR); Lemma 4.5 with R = Ĉ ⊗_C Ĉ shows it is everything. This is my own argument and it uses X separated. So Bhatt Thm 1.4(1) is **not needed** if 0APL is available; only Bhatt Thm 1.1 is.

**Test.** X nodal cubic, weights ±1, C = k[a,b]/(ab): U = G_m (the open orbit), Z = the node, T_U = two copies of G_m, T̂ = Spec k[[a,b]]/(ab). The pushout gives the expected chart, with no T-stable affine neighbourhood of x in X needed.

**Applying 4.1.** With (C,m) from §3 and φ_n = the isomorphisms Spec C/m^{n+1} = X_n ⊂ X, we get φ : T -> X equivariant.

**What remains:** only the inputs named above.

## 5. Step (4): equivariant Artin approximation

**AHR.** Thm 5.8 = AHR20 Thm A.18 (A.17 approximates with Gr-isomorphism, then versality promotes to all n), using T = Z's quotient, X_1 = X, X_2 = BGL_m.

**D(M), formal étaleness.** Let (V,v) -> (X,x) be an affine étale chart with κ(v) = k and A = O_{V,v}, and u ∈ T the identity of O. The map X_n ≅ T_n identifies m_x with m_u and I^j ⊂ m^j, so A/m_x^j = O_{T,u}/m_u^j for all j. So Â := Ô_{X,x} -> E := Ô_{T,u} is an isomorphism.

**Coordinates.**
- Choose homogeneous x_i ∈ C: lifts of a generator of k, of generators of Z_0 and inverses in k[Z_0], and generators of m/m². Let P = Z[x_i] with these degrees.
- P_0 is f.g. and P_d is finite over P_0 (Lemma 3.1). p_0 := ker(P_0 -> C_0/m_0 = k) is maximal.
- Q := P ⊗_{P_0} P̂_0, noetherian, each Q_d finite over P̂_0, compact since k is finite.
- Q -> C is surjective: Q_d -> C_d is continuous with compact image, dense since P -> C/m^n is onto. So C = Q/(f_1..f_s), f_ℓ homogeneous.
- Let (r_tℓ) be homogeneous generators of the syzygies of f over Q.
- Let 𝔫 be the prime of u in Q and Ξ := Q̂_𝔫. E = Ξ/(f). Syzygies over Ξ are generated by r (flatness).
- Fix N ≥ 1 and at least the Artin–Rees constants of (f) ⊂ Ξ for 𝔫 and of Syz ⊂ Ξ^s.

**Functor.** F(R), for a P_0-algebra R: tuples (f̃_ℓ ∈ (P⊗R)_{d_ℓ}, r̃_tℓ, with Σ r̃_tℓ f̃_ℓ = 0, φ̃ : Spec(P⊗R/(f̃)) -> X equivariant). F is limit preserving (P_d finite, X locally of finite presentation, equalities of maps descend). The data (f, r, φ) is in F(P̂_0).

**Approximate.** **Artin 1969, Cor 2.2** (as quoted in AHR §3.4; A.12 of AHR20; P_0 is essentially f.t. over Z, excellent Dedekind) gives ξ̃ ∈ F((P_0)_{p_0}^h) with ξ̃ ≡ ξ mod p̂_0^{N+1}. It spreads to an étale (P_0',p') -> (P_0,p_0) with trivial residue extension. Put **W := Spec (P ⊗ P_0')/(f̃)**, affine of finite type over Z, graded, φ̃ : W -> X equivariant. W/(p') = C/p̂_0C has quotient k[Z_0], giving a closed G-stable O ⊂ W on which φ̃ is the orbit; w := identity. B̂ := Ô_{W,w} = Ξ/(f̃) (étale with trivial residue extension).

**Lemma 5.1 (A.17(6) in this case).** If f̃ ≡ f and r̃ ≡ r mod 𝔫^{N+1}, then in(f̃) ⊂ in(f) in gr_𝔫 Ξ. Hence length B̂/𝔫^j ≥ length E/𝔫^j.

*Proof.* Let θ, θ̃ : Ξ^s -> Ξ be pairing with f, f̃, and v = θ̃(a) of order n.

Claim: a may be changed by Syz(f̃) to lie in 𝔫^{n-c}Ξ^s, for c the Artin–Rees constant.
- Let t be the maximal order of a modulo the span of r̃ (finite if v ≠ 0, by Krull). Suppose t < n - c.
- θ(a) = v + (f - f̃)a has order ≥ t + c + 1 (for N ≥ c). So by Artin–Rees a = b + ρ with b ∈ 𝔫^{t+1}Ξ^s, ρ ∈ Syz(f).
- ρ = a - b has order ≥ t, so ρ = Σ c_j r_j with c_j of order ≥ t - c_2. Then ρ̃ = Σ c_j r̃_j satisfies ρ - ρ̃ ∈ 𝔫^{t+1} (for N ≥ c_2). So a - ρ̃ ∈ 𝔫^{t+1}Ξ^s, a contradiction.

With this a, v - θ(a) = (f̃ - f)a has order ≥ N + 1 + n - c > n. So in(v) ∈ in(f). ∎

**Étale.** Â -> B̂ (induced by φ̃) composed to B̂/𝔫^{N+1} equals Â = E -> E/𝔫^{N+1} = B̂/𝔫^{N+1}, since ξ̃ ≡ ξ. With N ≥ 1 this is onto on cotangent spaces, so Â -> B̂ is surjective. Lengths: E/𝔫^j surjects onto B̂/𝔫^j and Lemma 5.1 gives the reverse inequality. So Â ≅ B̂. φ̃ is of finite type with this completion and the same residue field, so it is étale at w.

**What remains:** Artin's theorem as input.

## 6. Finish: shrink

**AHR.** Prop 5.3 and moduli-space shrinking; Thm 10.1.

**Shrinking Lemma (old note 1.3; proof rechecked).** Let Y = Spec A with G-action, Ω ⊂ Y a G-stable open, O ⊂ Y a closed G-stable subscheme inside Ω. Then there is h ∈ A_0 with O ⊂ D(h) ⊂ Ω.

*Proof.* I := radical ideal of Y \ Ω. Since Y \ Ω is stable, the coaction of g ∈ I is nilpotent mod I·A[M], so all homogeneous components of a power g^e lie in I. Let J be generated by these, for g running over generators of I. J is homogeneous with V(J) = V(I). From I_O + J = A, take degree 0: 1 = i + h, h ∈ J_0. ∎

**Conclusion.** Ω := étale locus of φ̃ on W, open and G-stable, contains w and so O. Take U := D(h). Then U is affine and étale over X, equivariant. u := w has κ(u) = k. H ⊂ G_u since O ≅ G_k/H with u the identity, and G_u ⊂ G_x = H by equivariance. Compose with §1's étale map. ∎

## 7. Inputs

### Used and read at source
| # | Statement | Where used | Mathlib / Stacks grep |
|---|---|---|---|
| I1 | Bhatt arXiv:1404.7483 Thm 1.1: X(A) = lim X(A/I^n), X qcqs space, A I-complete | §4 glue | Not found; only the proper case (Stacks 0A4Z/0GHK, `Spaces/MorphismAlgebraizationLocallyFiniteType.lean`), which does not imply it. **Main missing input.** |
| I2 | Artin 1969 Cor 2.2, only as quoted in AHR §3.4 and AHR20 A.12 (original not read) | §5 | No such theorem found; `RingTheory/Smoothing/PopescuTheorem` is listed in `StacksFrontier.lean` (not opened; check its status), and `Curves/NodalEtaleChartFromCompletion.lean` mentions approximation. **Hypothesis unless Popescu there is complete.** |
| I3 | Stacks 06RC dense open gerbe | §4.2 | Present: `exists_openSubstack_dense_isGerbe` (used in `Stacks/ChowLemmaNoetherianGerbe.lean`). Needs [X/G] as a stack: "quotient stack" appears under `Stacks/` (`AlgebraicStackFlatPresentation` etc.), not inspected in depth. |
| I4 | Stacks 0APL Gabber fpqc sheaf | §4 Remark (replacing Bhatt 1.4(1)) | Discussed in `Spaces/Descent/Fpqc/Integral.lean`, `EtaleSheafAlgebraicCriterion.lean`; the exact theorem form not opened. |
| I5 | Stacks 07SQ, 07VT affine descent | §2, §4.2 | Present: `Spaces/AffineOfUniversallyClosedSurjection*.lean`; 07SQ is referred to there. |

Optional alternative to I4 + Lemma 4.5: Bhatt Thm 1.4(1), not found in Lean.

### Used from memory, not read this session (standard; check before relying)
- Deligne's formula colim Hom(J^N, F) = Γ(U,F) on noetherian spaces (tag not checked; `AffineDevissage/Sections.lean`, `Torsion.lean` matched a grep, not opened).
- Hopf ideals of k[M]: closed subgroups of D(M)_k are D(M/Z) (SGA3 VIII 3.2).
- Flat f.p. monomorphism = open immersion (Mathlib `AlgebraicGeometry/Morphisms/FlatMono.lean` by name).
- Filtered complete ring with noetherian gr is noetherian (cited in AHR Lemma 4.9 as [God56]; Bourbaki).
- Existence of étale charts with trivial residue extension at a rational point; Q reduced under a gerbe.
- completion isomorphism + finite type ⇒ étale.
- fpqc descent of affineness for spaces (the Stacks files `isAffineHom_isLocalAtTarget_fpqc` appear to give it).

### To be built, elementary (not in the libraries as graded statements)
- Lemmas 3.1–3.4, 4.5, 5.1, Shrinking: graded commutative algebra. Mathlib has Gordan's lemma in `GroupTheory/Finiteness.lean` (line 626), well-quasi-order/Dickson material (`Set.PartiallyWellOrderedOn`), `RingTheory/Filtration.lean` (Artin–Rees, Krull), `RingTheory/AdicCompletion/*`, flatness of completion (`AdicCompletion/AsTensorProduct.lean`), `RingTheory/Henselian.lean` (no henselization construction found), `HopfAlgebra/MonoidAlgebra.lean`.
- D(M) action on spaces and equivariant coherent sheaves: no "Diagonalizable" hit in Mathlib; no group-of-multiplicative-type file by name in Stacks. Must be set up, preferably as: action = coaction by Z[M]; on affines = M-grading.
- Lemma 1.1, 4.3, 4.4: moderate, on existing `Spaces/` foundations.

Not needed at all, against the original plan: Tannaka duality (0 hits anyway), good moduli spaces, cotangent complex, normalization, Sumihiro, Keel–Mori.

**Smallest set of big inputs:** I1 (Bhatt 1.1), I2 (Artin approximation), I3 (generic gerbe, already present), I4 (Gabber, seemingly present).

## 8. Flags

1. Lemma 4.3's Tor-kernel and the V-compatibility are where an error would most likely hide; §4 is my specialization and has had no independent check. I recommend one independent read of §4 alone, proposed not launched.
2. Lemma 4.2 uses "reduced stack of [X/G]" with G non-smooth (flat presentation only). 06RC needs only a reduced algebraic stack, so this is fine, but the identification of the G-stable thickening X' should be written explicitly in any final version.
3. I read Hall–Rydh §8 (Thm 8.4 and proof), statement of Cor 7.3 partly, not §§5–6. The comparison "same induction" is at the level of the proof outline shown there.
4. Bhatt is quoted from arXiv v1 (2014), the only arXiv version found. The published version was not checked.

## 9. Sources read

AHR arXiv:1912.06162v4 (Thm 1.1, 1.6, 1.10, 1.11, §3 to §5, Thm 10.1, Cor 10.2); AHR20 arXiv:1504.06467 (Thm A.17, A.18, Cor A.19); Hall–Rydh arXiv:1405.7680 (Thm 1.1, §8, Cor 7.3 opening); Bhatt arXiv:1404.7483 (§1); AHHLR arXiv:2205.08623 (Thm 1.2, Thm 2.3 statements); Stacks 0APL, 06RC, 06QK, 07SQ, 07VT (site text). PDFs and text in the session scratchpad.
