# Equivariant affine étale charts for a torus on a normal algebraic space

Status: written proof, no independent check yet. No Lean. The proof below is mine; every outside input is listed in §8 with whether I read it.

## 0. Result

**Theorem N.** Let T = D(Z^r) be a split torus, X a separated algebraic space of finite type over Z (e.g. over F_q, or over an affine f.t. Z-scheme S) with T-action, and x a T-fixed point, closed, with residue field k. Suppose the completed local ring Ô of X at x is a domain (e.g. X normal at x). Then there are an affine scheme U with T-action, a T-equivariant morphism U -> X and a T-fixed point u over x, with U -> X étale, κ(u) = k.

Consequences, using the two earlier notes (§6): closed non-fixed points, and non-normal X through Theorem B of ahr-diagonalizable-attractors.md. The gaps (N), G1 and G2 of the earlier notes are closed by this proof if it survives checking. Sumihiro is not used.

**Literature finding.** The statement is not new: AHR Cor. 10.2 (arXiv:1912.06162v4, read) covers it, for quasi-separated X and multiplicative-type T. Its proof applies the local structure theorem to [X/T], so it passes through Tannaka duality. A citation therefore already suffices for the mathematics. I found no published direct or stack-free proof for normal spaces, and no treatment of the normal case that is simpler than AHR's; the searches are not exhaustive. What is new here, to my knowledge, is §3: a function-field descent that replaces Tannaka duality in the one step where the earlier notes were stuck.

## 1. Set-up (T-graded completion)

Reductions. T ×_S X = T_Z × X, so S can be forgotten. Note R2 (graded note §1): an étale O over Z at a point with residue field κ(x) makes x rational; normality and the domain condition are preserved, and charts compose. Replace X by the component through x (T-stable, as T is connected). If X is normal at x it is normal near x; with Ô a domain, X is integral near x and we shrink X by removing the T-stable closed union of the other components. Let K = k(X).

X_n = n-th infinitesimal neighbourhood of x. It is T-stable and affine, so O/m^n is M-graded, M = Z^r. Define

C_d = lim (O/m^n)_d, C = ⊕_d C_d ⊂ Ô.

(C -> Ô is injective, since a finite sum is zero in all O/m^n iff each component is.)

**Lemma 1.1 (checked again, graded note Lemma G).** C is noetherian, generated over the complete local noetherian ring C_0 by finitely many homogeneous T_i of nonzero degree, and the completion of C at m_C (the homogeneous maximal ideal) is Ô, with C/m_C^n = O/m^n.

Proof. Let W = W(k); it maps uniquely to each O/m^n. Lift homogeneous generators of m/m^2 through the surjective maps (O/m^n)_d -> (O/m^{n-1})_d. This gives P = W[T_1..T_n] -> O/m^n, surjective for all n. Gordan/Dickson give P_0 f.g., P_d finite over P_0, and m^ℓ ∩ P_d ⊂ m_0^{f(ℓ)} P_d (attractors note 1.4), so lim (P/m^ℓ)_d = P_d ⊗ P̂_0. The kernels have finite length, so Mittag-Leffler gives surjectivity of P ⊗_{P_0} P̂_0 -> C and of the kernels' limit onto each finite level; that gives the identification C/m_C^n = O/m^n. ∎

Coaction. Let B = lim (O/m^n)[M], i.e. series Σ c_δ e^δ, c_δ ∈ Ô, c_δ -> 0. It is noetherian and flat over Ô[M], and mB lies in its Jacobson radical. Let ρ: Ô -> B be the limit of the gradings, ρ(y) = Σ y_δ e^δ, y_δ ∈ C_δ the homogeneous components. ρ is flat: it is the inclusion Ô ⊂ B followed by the shear automorphism of B (c ↦ ρ(c), e ↦ e, inverse with e^{-1}).

**Lemma 1.2.** With ϕ: Spec Ô -> X, β: Spec B -> T × Spec Ô, a the action: ϕ ∘ Spec ρ = a ∘ (1 × ϕ) ∘ β.

Proof. Both agree on V(m^n B) = T × X_n. Since X is separated, the equalizer is a closed V(J) with J ⊂ ∩ m^n B = 0 (Krull). ∎

## 2. Homogeneous rational functions lie in Frac C

Call f ∈ K homogeneous of degree d if f is regular on a dense T-stable open with a^*f = e^d ⊗ f.

**Lemma 2.1.** K is generated as a field by homogeneous elements.

Proof. The stabilizer at the generic point ξ is D(M/M')_K for a subgroup M' ⊂ M. S = D(M/M') acts trivially on X (equalizer closed, S × X flat over integral X, so generic fibre schematically dense). So T' = D(M') acts, with M' free. The stabilizer group of T' on X is of finite type over X and trivial at ξ, so trivial over a dense open; T-saturating, over a dense T-stable open X_4 (T is commutative, so stabilizers are constant along orbits). The action there is free, so X_4/T' is an algebraic space and X_4 a T'-torsor over it (Stacks 06PH). Take a dense open affine Q_0 in X_4/T' (Stacks 06NH, then an affine open), small enough that the torsor, trivial at the generic point by Hilbert 90 for split tori, is trivial. Then X_3 = T' × Q_0 is open dense in X and O(X_3) = O(Q_0)[M']. ∎

**Lemma 2.2.** Let f ∈ K be homogeneous of degree d. Write f = y/z in Frac Ô, y,z ∈ Ô (Ô domain, Spec Ô -> X flat, so K ⊂ Frac Ô). For any δ with z_δ ≠ 0:

f = y_{δ+d} / z_δ.

So f ∈ Frac C, and it is a fraction of homogeneous elements with degree difference d.

Proof. The morphism in 1.2 is flat, so the rational function f pulls back to the total ring of fractions of B, and the two descriptions agree: ρ(y)/ρ(z) = e^d y/z. (ρ(z) and z are nonzerodivisors of B by flatness of ρ and of Ô -> B.) So ρ(y) z = e^d y ρ(z) in B. Coefficients of e^{δ+d}: y_{δ+d} z = y z_δ. ∎

**Corollary 2.3.** K ⊂ Frac C (inside Frac Ô), compatibly with ϕ. This closes the point recorded in attractors note §5 as verified only for factorial Ô.

The components y_δ need not be algebraic over K: compare F4 of the graded note. That is why they are taken in C and not in O^h. Nothing here needs them algebraic.

## 3. The missing step: Spec C -> X exists, without Tannaka

**Theorem 3.1.** There is a unique morphism ψ: Spec C -> X extending ϕ along Spec Ô -> Spec C. It is T-equivariant.

Proof. Let η = Spec Frac C. By 2.3 we have η -> Spec K -> X. Let Γ ⊂ Spec C × X be the scheme-theoretic image of η -> Spec C × X (quasi-compact). We show pr: Γ -> Spec C is an isomorphism.

Let P = T × Spec Ô = Spec Ô[M], and π: P -> Spec C the action, c_d ↦ c_d e^d. It is the composite of the flat map to T × Spec C and the action of T on Spec C (smooth, by shearing).

*π is surjective.* Let p ∈ Spec C. Its orbit map T_{κ(p)} -> Spec C sends the generic point to P^*, the largest homogeneous ideal in p, which is prime and proper. Every proper homogeneous ideal lies in m_C: its degree-0 part lies in m_{C_0} because C_0 is local, and nonzero degrees lie in m_C. So P^* is in the image of Spec Ô -> Spec C, which is flat local. Taking a point of the fibre product gives (t, ω) with π(t, ω) = p.

*Pull-back.* Let g = a ∘ (1 × ϕ): P -> X and η_P = η ×_{Spec C} P, a localization of the domain Ô[M] (nonempty since C -> Ô[M] is injective). Claim: on η_P the map η_P -> η -> X equals g. As X is separated and η_P integral, compare at the generic point of P, where both factor through Spec K (g is flat). So compare two field maps K -> Frac Ô[M], enough on homogeneous f of degree d (2.1). Through η: by 2.2, f = b/a with a ∈ C_δ, b ∈ C_{δ+d}, sent to (b e^{δ+d})/(a e^δ) = e^d f. Through g: (1 × ϕ)^* a^* f = e^d f. Equal.

By flat base change of scheme-theoretic images (Stacks 089E) applied to P × X -> Spec C × X, Γ ×_{Spec C} P is the scheme-theoretic image of η_P -> P × X. This map factors through the graph of g, a closed immersion as X is separated, and η_P -> P is schematically dominant as P is integral. So Γ ×_{Spec C} P = graph(g) ≅ P. Isomorphisms descend along the fpqc π (Stacks 041K). So Γ ≅ Spec C, and ψ := pr_X ∘ pr^{-1}.

The same base change along Spec Ô -> Spec C gives ψ|Spec Ô = ϕ. Equivariance: both maps T × Spec C -> X agree at the generic point of the integral T × Spec C (same computation), and X is separated. Uniqueness: Spec Ô -> Spec C is schematically dominant and X separated. ∎

This is exactly the step where attractors §6(d) and graded §6 item 3 failed. Those attempted descent of the morphism along R_0 = P ×_{Spec C} Spec Ô, non-noetherian and badly behaved. Here one never compares on R_0: the function field gives the map at the generic point, and the closure Γ is what descends. In AHR this step is Tannaka duality with coherent completeness (proof of Thm 5.6, Step 3, and §1.7, read).

## 4. Algebraization (elementary at this level)

AHR Thm 5.8 with Z = [Spec C / T] would apply here, but it is a stack statement resting on [AHR20, Thm. A.18], which I did not read. Direct version below; the only input is Néron–Popescu approximation in the form AHR Thm 3.8 (read).

Choose Ŝ = W[[x_1..x_m]] -> C_0 surjective. Ŝ is the completion of S_0 := O[x]_{(p,x)}, with O/Z étale at a point with residue field k. S_0 is excellent. Let 𝒫 = Ŝ[T_1..T_n] -> C be surjective with homogeneous kernel J (1.1), and R = W[[x,T]] the completion at (m_Ŝ, T), so R/JR = Ô.

Choose homogeneous generators g = (g_j) of J and homogeneous generators φ = (φ_i) of the syzygies of g over 𝒫. As R is flat over 𝒫, they stay generators over R. Let c be an Artin–Rees constant in R: I ∩ m^n ⊂ m^{n-c} I for I = JR, and Syz ∩ m^n R^l ⊂ m^{n-c} Syz. Fix N ≥ c+2.

Functor on S_0-algebras A: F(A) = {g', φ' polynomials over A in T with the same (finite) monomial supports as g, φ, satisfying φ' · g' = 0, together with a T-equivariant ψ': Spec A[T]/(g') -> X}. It is limit preserving because X is of finite presentation over Z and the conditions are equalities of morphisms. ξ = (g, φ, ψ) ∈ F(Ŝ) by §3. AHR Thm 3.8 for (S_0^h, m) gives ξ^h ∈ F(S_0^h) with ξ^h ≡ ξ mod m^N. Descend to an étale neighbourhood (E, e) of S_0, κ(e) = k, E affine.

U' = Spec E[T]/(g') is affine and graded (homogeneous by the supports). u' = V(m_e, T) is a closed fixed k-point, and ψ'(u') = x. Its completion is R/I', I' = (g'), g' ≡ g mod m^N, φ' ≡ φ mod m^N.

**Lemma 4.1.** in(I') = in(I) in gr R. So R/I and R/I' have the same Hilbert–Samuel function.

Proof. Let w = Σ b_j g'_j ∈ m^n. Suppose e := ord b < n - c. Then Σ b_j g_j = w - Σ b_j (g'_j - g_j) ∈ m^{e+c+1}, so by Artin–Rees it equals Σ b'_j g_j with b' ∈ m^{e+1}. Then b - b' ∈ Syz ∩ m^e, so b - b' = Σ r_i φ_i with r_i ∈ m^{max(e-c,0)}. Replace b by b'' = b - Σ r_i φ'_i, which still represents w since φ'·g' = 0. Now b'' = b' + Σ r_i(φ_i - φ'_i), and r_i(φ_i - φ'_i) ∈ m^{max(e-c,0)+N} ⊂ m^{e+1} because N ≥ c+2. So b'' has order ≥ e+1. Iterating, w ∈ m^{n-c} I'. So Artin–Rees holds for I' with the same c. Now if w ∈ I has order o, take a representation b of order ≥ max(o-c,0). Then w' = Σ b_j g'_j has w - w' ∈ m^{max(o-c,0)+N} ⊂ m^{o+1}, so in(w) = in(w') ∈ in(I'). The symmetric argument, using the Artin–Rees bound for I', gives the converse. ∎

**Étaleness.** Modulo m^N the data coincide: E[T]/(g', m_e^N) = C/m_{Ŝ}^N C and ψ' = ψ there. So Ô -> R/I' induced by ψ' is the identity modulo m^2 under the identification, hence surjective on cotangent spaces, hence surjective. With equal Hilbert functions (4.1), it is an isomorphism. Therefore ψ' is étale at u' (f.t. morphism, isomorphism on completed local rings, equal residue fields).

**Shrink.** The étale locus Ω is open and T-stable. The radical ideal of U' \ Ω is homogeneous (T smooth) and not in m_{u'}, so, u' being fixed, it contains f of degree 0 with f(u') ≠ 0. U := D(f) ⊂ Ω is affine and T-stable. This proves Theorem N. ∎

Where the hypotheses enter: Ô domain only in §2-3; separatedness in 1.2 and §3; f.t. over Z in limit preservation and excellence.

## 5. Tests

1. **T trivial, X Hironaka-type normal space.** C = C_0 = Ô, ψ = ϕ, no T_i. §4 becomes ordinary Artin approximation and gives an ordinary étale chart. No circularity, and the non-scheme point is handled.
2. **Twisted line bundle over a non-scheme.** Z̃ -> Z free involution σ, Z̃ a scheme, Z not a scheme at z̄ (char ≠ 2 for the sign). X = (Z̃ × A^1)/(σ, -1) with G_m scaling A^1, x = (z̄, 0). Locally Ô = Ô_Z[[s]], C = Ô_Z[s], deg s = 1. Degree-1 elements of K have the form s·e with e anti-invariant in k(Z̃). Lemma 2.2 gives e ∈ Frac Ô_Z, as it must, since the double cover splits over Ô_Z. Then ψ: Spec Ô_Z[s] -> X is the evident map through Z̃ × A^1, and §4 returns a chart V × A^1, V étale over Z̃. Matches the expected answer, on an example where Zariski methods cannot apply.
3. **Artin–Schreier (attractors §5).** X = A^1, weight 1, char p, V: y^p - y = x. C = k[x], ψ = id, and K(V) is not in Frac C, correctly. The output chart comes from C, not V, so the T-non-homogeneous cover that blocked the Galois approach never appears.
4. **F3 of the graded note (y^2 = 1 + t).** Same: never lifted, no contradiction.
5. **F4 of the graded note.** O^h is not stable under taking components. Harmless: components are used only in C.
6. **Nodal cubic, x the node.** Ô = k[[a,b]]/(ab) is not a domain, so Theorem N does not apply directly; the hypothesis is really used in 2.2. Spec C = {ab = 0} -> X does exist, as seen on each branch; this is the pinching case of Theorem B.
7. **Sanity of Γ.** Line with doubled origin, G_m weight 1: normal, non-separated; 1.2 and the closed-immersion step of §3 fail as written, as they should. (A chart exists anyway by AHR. This proof simply does not cover it.)

Not tested: a normal space with G_m having a loop of orbits through x. Such an example should arise as a free quotient of a non-projective toric threefold (Jurkiewicz type), but I did not construct one. Nothing in §§2-4 uses absence of loops; ψ need not be injective.

## 6. Status of the full target

Using the earlier notes (which I reread, found no error on the steps used, but which are themselves unrefereed):

- (⋆) for normal X: Theorem N.
- (N) in Theorem B: apply Theorem N at each x_i', after the étale base change for residue fields, with disjoint union. Sumihiro is no longer needed, and mixed characteristic (G1) is covered.
- So (⋆) for all separated X by Theorem B, then the target for D(M) by Theorem A.

Unproved beyond the above: nothing new is claimed for non-separated X. Direct treatment of reduced non-normal X (run §§2-3 on the minimal primes of Ô, which would remove pinching) looks plausible but I did not write it. It needs that minimal primes of Ô come from homogeneous primes of C with domain completions.

## 7. Ideas tried or discarded

- Normalization in L·K, L = algebraic closure of k(Q) in (Frac C)_0. Using 2.3 and algebraic closedness of O^h in Ô, I get equivariant étale Y_L -> X at x, but that does not yield affineness. Superseded by §4.
- G_m contraction of X^+ ∪ X^- via quotient Q_+ and Artin's contractibility: Q_+ can be non-separated near the exceptional set when loops exist. Abandoned.
- Induction on rank, Hilbert/Quot of covers, equivariant Chow, equivariant ZMT: not needed, not pursued. Thm 3.20 is not used.

## 8. Sources

Read at source this session: AHR arXiv:1912.06162v4 (§10.1, Thm 10.1, Cor 10.2, Rem 10.3, Thm 3.8, Thm 5.6 statement and Steps 1-3, Thm 5.8, intro); arXiv abstract pages of AHR and of Alper–Hall–Rydh, Luna étale slice, Ann. of Math. 191 (2020), 675-738 (abstract only). Stacks statements returned by the site: 06PH (Lemma 80.11.7), 06NH (Prop 66.13.3), 089E (Lemma 67.30.12), 0C23 (Lemma 15.53.6), 07QY (Thm in §16.13). Tag 041K only through a search summary listing "isomorphism" as fpqc local on the base.

Bibliographic only, from search results, not checked at the journal: the published AHR is Ann. Sci. ENS 59 (2026), 125-198, reported to number the result Theorem 10.2.

Not read (could not be located or not opened; not relied on except as marked): Sumihiro 1975 and Thomason 1987 (no longer needed; Sumihiro known only as quoted in AHR §10.1, Thomason only by citations); Brion 2015 (known only through AHR Rem 10.3: field case, quasi-projective X); [AHR20, Thm A.18]; Conrad–de Jong 2002, whose approximation theorem is the model for §4 (the page of the statement was not retrieved, so Lemma 4.1 is proved directly); Drinfeld (read in the earlier note, not used here). From memory: Gordan/Dickson; closed subgroups of split tori are D(M/M'); Hilbert 90 for split tori; isomorphism on completions implies étale (EGA IV 17.6.3, unread); Artin–Rees and Krull.
