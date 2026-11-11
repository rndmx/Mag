**Deliverable: proofs of Prop. 3.31(ii) and Prop. 3.32(ii) for an arbitrary S-algebraic space X**

## 0. What the print assumes (checked on the page images, pp. 147–149, and the opening of §3, p. 140)

Standing hypotheses of §3: S a scheme, X an algebraic space over S, M a commutative monoid, A(M)_S acting on X. No separatedness, no finiteness on X.

- 3.31(ii): M and Z finitely generated groups, f : M → Z, Y ⊂ Z any submonoid, N = f⁻¹(Y). Claim: X^{N⊂M} = X^{Y⊂Z} (X seen as a D(Z)_S-space via D(Z) → D(M)).
- 3.32(ii): M a finitely generated abelian group, N, L ⊂ M any submonoids. Claim: (X^N)^L = X^{N∩L} (action of Remark 3.11 on X^N).

Neither (ii) assumes X separated. The printed proofs assert the ⋆-action is free and take an fpqc quotient; as stated in the task this is false in general. Below both proofs are replaced by one descent lemma whose proof does not use freeness.

## 1. The descent lemma

Fix a scheme T, a commutative monoid P, a finitely generated abelian group Γ, a monoid homomorphism δ : P → Γ, and P₀ := δ⁻¹(0) (a submonoid). Put W := A(P)_T = Spec_T O_T[P], Q := A(P₀)_T, π : W → Q dual to P₀ ⊂ P. D(Γ)_T acts on W through the Γ-grading of O_T[P] in which X^p has degree δ(p) (coaction X^p ↦ X^p ⊗ χ^{δ(p)}); the ring of invariants is the degree-0 part O_T[P₀], i.e. O_Q = (π_*O_W)^{D(Γ)} (SGA3 I 4.7.3; this is Prop. 2.21/2.22 of the paper).

**Lemma D.** For every algebraic space X over T, composition with π is a bijection
Hom_T(Q, X) → {F ∈ Hom_T(W, X) : F ∘ act = F ∘ pr₂ on D(Γ)_T ×_T W}.
Both directions are compatible with base change T' → T (because Q, W, π are).

**Proof.**

(a) *The quotient stack.* 𝒳 := [W / D(Γ)_T]. D(Γ)_T is a diagonalizable group scheme of finite type, hence linearly reductive over T (Alper 2013, Example 12.4(2), citing SGA3 I.5.3.3). W is affine over T, so by Alper 2013, Theorem 13.2 ("Let G → S be a linearly reductive group scheme acting on a scheme p : X → S with p affine. The morphism [X/G] → Spec_S p_*O_{[X/G]} is a good moduli space"), 𝒳 → Spec_T (π_*O_W)^{D(Γ)} = Q is a good moduli space. A good moduli space is cohomologically affine, hence adequately affine (Alper 2014, Prop. 4.2.1(2)), and 𝒳 → Q is quasi-compact and quasi-separated (W → Q quasi-compact; the diagonal of 𝒳 over Q is affine since D(Γ)_T ×_T W → W ×_Q W is affine), with O_Q ≅ (π_*O_W)^{D(Γ)}; so 𝒳 → Q is an adequate moduli space in the sense of Alper 2014, Def. 5.1.1.

(b) *Invariant maps = maps from 𝒳.* For a sheaf X, Hom(𝒳, X) is the equalizer of Hom(W, X) ⇉ Hom(D(Γ)_T ×_T W, X) (universal property of the quotient stack: 𝒳 is the stackification of the action groupoid, and X is 0-truncated). So Lemma D says exactly that 𝒳 → Q is universal for maps to algebraic spaces.

(c) *Uniqueness (self-contained).* Let u, v : Q → X with uπ = vπ. Let e : E → Q be the equalizer, i.e. the pullback of Δ_X along (u, v). Δ_X is a monomorphism locally of finite type (Stacks Tag 03KN (1)), so e is a monomorphism locally of finite type, hence separated and locally quasi-finite (Tag 0463), hence E is a scheme (Tag 03XX). Since π is invariant and factors through E, we get ρ : 𝒳 → E with e ∘ ρ = (𝒳 → Q). The map 𝒳 → Q is surjective and universally closed (Alper 2014, Thm 5.3.1 (1),(2); elementary here: a closed D(Γ)-stable subset is V(I) with I homogeneous, and π(V(I)) = V(I ∩ A₀) because A₀ is a direct summand of A as A₀-module, so taking degree-0 parts is exact and commutes with base change). Hence e is universally closed (for any base change, e'(Z) = π'(ρ'⁻¹ Z), and ρ' is surjective on points because |e'| is injective and |π'| surjective). A universally closed monomorphism locally of finite type is a closed immersion (Tag 04XV (6), applied to the scheme morphism e). So E = V(J) ⊂ Q with J ⊂ A₀ an ideal, and π factors through V(J) means J A = 0; since A₀ → A is injective (split), J = 0, E = Q, u = v. (Alternative route: E is a scheme and ρ is invariant, so the already-proved scheme case gives ρ̄ : Q → E with ρ̄π = ρ, then eρ̄π = π forces eρ̄ = id by scheme-case uniqueness; a monomorphism with a section is an isomorphism.)

(d) *Existence.* This is Alper–Hall–Rydh, "The étale local structure of algebraic stacks", arXiv:1912.06162v4 (3 Apr 2025), Theorem 3.12: "Let 𝒳 be an algebraic stack. An adequate moduli space π : 𝒳 → X is universal for maps to algebraic spaces." No noetherian, separatedness or finiteness hypothesis. By (a),(b) it gives Lemma D. (No journal version of this paper exists as of today; the arXiv abstract page lists no journal-ref. Its Theorem 3.12 is explicitly stated as removing the noetherian hypothesis of Alper 2013, Thm 6.6, and the "locally separated or Zariski-locally affine diagonal" hypothesis of Alper 2014, Thm 7.2.1.)

For the record, the mechanism of that proof in our concrete situation, which I verified step by step except for the one black box named below: existence is étale-local on Q (by (c) and the sheaf property of X). Take an étale atlas U → X_T with U a scheme and set W' := W ×_X U. Because F is invariant, the action lifts to W' by g·(w, u) := (g w, u) (well defined since F(gw) = F(w)); W' → W is equivariant, étale, surjective, stabilizer-preserving, and F' : W' → U is invariant. If W' → W has an equivariant section s over W ×_Q Q' for some étale Q' → Q, then F|_{W×_Q Q'} = (W×_Q Q' → U → X) ∘ s factors through Q' because U is affine (an invariant map from an affine scheme to an affine scheme lands in the degree-0 part of the ring). The existence of such a section over an étale neighbourhood of each point of Q is where the pair (W ×_Q Spec O^h_{Q,q}, closed orbit of the fibre) must be henselian for representable étale maps: AHR Theorem 3.10 together with Proposition 3.11 (the latter rests on Hall–Rydh). **This henselian-pair statement is the only step I did not reprove; everything else in (a)–(d) I checked.** The elementary facts I did verify and which feed it: every fibre of π has a unique closed orbit (if V(I₁) ∩ V(I₂) = ∅ in a fibre Spec C with C₀ = k(q), then 1 = a₁ + a₂ with aᵢ ∈ Iᵢ homogeneous ideals, and the degree-0 parts give a unit in some Iᵢ); on each torus-stratum W_Φ = D(Φ^gp)_T (Φ a face of P) the action is through the free action of D(δ(Φ^gp)) with fppf quotient D(Φ^gp ∩ ker δ)_T, so F descends stratum by stratum by honest fppf descent — this is the correct version of the printed "free action, fpqc quotient" step, valid only stratum-wise; and over the minimal stratum of each stratum of Q the quotient is exactly the Q-stratum (face generated by a face Ψ of P₀: F(Ψ)^gp ∩ ker δ = Ψ^gp). ∎

## 2. Proof of Prop. 3.32(ii)

Let T → S be a scheme. By Prop. 3.9 and Yoneda, an element of (X^N)^L(T) is a map Φ : A(L)_T → (X_T)^N, i.e. an element of X^N(A(L)_T), i.e. a T-morphism F : A(N)_T ×_T A(L)_T → X_T with F(ga, b) = g·F(a, b); D(M)-equivariance of Φ for the action of Remark 3.11 (t·f = t ∘ f = f ∘ t) says F(a, hb) = h·F(a, b). So
(X^N)^L(T) = {F : A(N)_T ×_T A(L)_T → X_T : F(ga, hb) = gh·F(a,b) for all g, h ∈ D(M)(T')},
functorially in T (this is the print's displayed identification).

Put Γ := N^gp + L^gp ⊂ M (finitely generated), P := N × L, δ(n, l) := l − n ∈ Γ, so P₀ = {(k, k) : k ∈ N ∩ L} ≅ N ∩ L. The D(Γ)_T-action on A(N)_T ×_T A(L)_T defined by δ is g ⋆ (a, b) = (g⁻¹a, gb) (on functions, X^{(n,l)}(g⋆(a,b)) = g(l − n)X^{(n,l)}(a,b)), and π : A(N)_T ×_T A(L)_T → A(N∩L)_T, dual to k ↦ (k, k), is the composite "A(N) × A(L) → A(N∩L) × A(N∩L) → A(N∩L)" of the print, i.e. π(a, b) = ab.

*F is ⋆-invariant.* D(M)_T → D(Γ)_T is faithfully flat of finite presentation (Z[Γ] → Z[M] is free, Γ ⊂ M finitely generated). For g ∈ D(Γ)(T'), choose fppf-locally a lift g̃ ∈ D(M)(T''); then F(g̃⁻¹a, g̃b) = g̃⁻¹g̃·F(a,b) = F(a,b). So F ∘ ⋆ and F ∘ pr₂ agree after the fppf cover D(M)_T × A(N)_T × A(L)_T → D(Γ)_T × A(N)_T × A(L)_T, hence are equal (X is an fppf sheaf). No freeness is used or needed.

*Descent.* Lemma D gives a unique f : A(N∩L)_T → X_T with F = f ∘ π. f is D(M)-equivariant: for g ∈ D(M)(T'), the two maps f(g·−) and g·f(−) from A(N∩L)_{T'} agree after π_{T'} (f(g·π(a,b)) = f(π(ga, b)) = F(ga, b) = g·F(a,b) = g·f(π(a,b))), hence are equal by the uniqueness in Lemma D over T'. So f ∈ X^{N∩L}(T).

*Inverse.* For f ∈ X^{N∩L}(T), F := f ∘ π satisfies F(ga, hb) = f(gh·ab) = gh·f(ab). The two assignments are inverse (F ↦ f ↦ f∘π = F; f ↦ f∘π ↦ f by uniqueness) and functorial in T by the base-change compatibility of Lemma D. Hence (X^N)^L = X^{N∩L}. ∎

## 3. Proof of Prop. 3.31(ii)

θ : Hom^{D(M)_T}(A(N)_T, X_T) → Hom^{D(Z)_T}(A(Y)_T, X_T), φ ↦ φ ∘ A(f), where A(f) : A(Y)_T → A(N)_T is dual to f|_N : N → Y; θ is well defined since D(Z) → A(Y) → A(N) and D(Z) → D(M) → A(N) are both dual to N → Z.

Let ψ be D(Z)-equivariant and F : D(M)_T ×_T A(Y)_T → X_T, F(g, y) := g·ψ(y). Put K := f(M) + Y^gp ⊂ Z (finitely generated), P := M × Y, δ(m, y) := f(m) − y ∈ K, so P₀ = {(m, f(m)) : m ∈ N} ≅ N and π : D(M)_T × A(Y)_T → A(N)_T is π(g, y) = g·A(f)(y) (dual to n ↦ (n, f(n))). The D(K)_T-action given by δ is the print's ⋆: k ⋆ (g, y) = (k∘f · g, k|_Y⁻¹ · y).

*F is ⋆-invariant.* D(Z)_T → D(K)_T is fppf (Z[K] → Z[Z] free). Lift k fppf-locally to z ∈ D(Z)(T''). z acts on A(Y) through z|_Y = k|_Y and on X through z∘f = k∘f ∈ D(M). Hence F(k⋆(g,y)) = (k∘f)g·ψ(k|_Y⁻¹ y) = (k∘f)g·ψ(z⁻¹·y) = (k∘f)g·(z∘f)⁻¹·ψ(y) = g·ψ(y) = F(g,y), fppf-locally, hence everywhere.

*Descent.* Lemma D gives a unique φ : A(N)_T → X_T with F = φ ∘ π. φ is D(M)-equivariant (check after π: φ(g'·π(g,y)) = φ(π(g'g, y)) = g'g·ψ(y) = g'·φ(π(g,y)), then uniqueness over T'). θ(φ)(y) = φ(π(1, y)) = F(1, y) = ψ(y). Conversely for φ ∈ X^N(T) and ψ := θ(φ), F(g,y) = g·φ(A(f)y) = φ(π(g,y)), so the descended map is φ. Functorial in T. Hence X^{N⊂M} = X^{Y⊂Z}. ∎

## 4. Honesty report

- Verified by me: the exact print hypotheses; both identifications of functors; the gradings, the identification of degree-0 parts with N∩L resp. N; the invariance computations (which replace freeness by fppf surjectivity of D(M) → D(Γ), D(Z) → D(K)); equivariance of the descended maps; Lemma D (a), (b), (c) in full; in (d) the lifted-action construction, étale-locality, the unique-closed-orbit and stratum-wise fppf descent facts.
- Not reproved, cited: AHR arXiv:1912.06162v4 Thm 3.12 (and its inputs Thm 3.10, Prop 3.11) for the henselian-pair/section step of existence. This is a preprint with no journal version; the published alternatives (Alper 2013 Thm 6.6: 𝒳 locally noetherian, target quasi-separated; Alper 2014 Thm 7.2.1: target locally separated or Zariski-locally affine diagonal) do not cover the print's generality (P = N×L non-finitely generated, T arbitrary, X arbitrary). If one is willing to add "X quasi-separated and S noetherian", Alper 2013 Thm 6.6 suffices after reducing to P finitely generated by Tag 04AK (X locally of finite presentation).
- Added hypotheses used: none. The author's "X locally of finite presentation over S" is not needed for either (ii); separatedness is not needed. The statements hold for arbitrary submonoids N, L, Y.
- Counterexample status: no step fails; the only false statement in the print is the freeness claim, and freeness is never needed.

References: Alper, Good moduli spaces for Artin stacks, Ann. Inst. Fourier 63 (2013) 2349–2402 (Example 12.4(2), Thm 13.2; numbering from the author's copy https://sites.math.washington.edu/~jarod/papers/gms.pdf, to be checked against the print); Alper, Adequate moduli spaces and geometrically reductive group schemes, Algebraic Geometry 1 (2014) 489–531, doi 10.14231/AG-2014-022 (Def 5.1.1, Prop 4.2.1(2), Thm 5.3.1); Alper–Hall–Rydh, The étale local structure of algebraic stacks, https://arxiv.org/abs/1912.06162 v4 (Thms 3.10, 3.12, 3.14, Prop 3.11); Stacks Project tags 03KN, 0463, 03XX, 04XV, 04AK (https://stacks.math.columbia.edu/tag/03KN etc.); SGA3 I 4.7.3, I 5.3.3. Local files used: C:\Users\Arnaud\Desktop\HDR\SemigroupForum-Proof.pdf (pp. 140, 147–149), C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Sec3SchemeQuotient.lean (statement of exists_desc / desc_unique, for the scheme-case alternative in (c)); extracted texts in C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\alper\ (gms.txt, ams.txt, a1912.06162.txt).

# Opus review

**Verdict summary**

- Attempt 1 is null: there is nothing to accept.
- Attempt 2 is not refuted. Its reductions of 3.31(ii) and 3.32(ii) to Lemma D are correct. Lemma D as written has one fixable gap, in the proof of (c), and existence rests entirely on a preprint with no journal version that I could find.
- I replace that preprint with a direct proof below. It uses only Stacks tags and needs no added hypothesis.

## A. Step-by-step audit of Attempt 2

**Print hypotheses: confirmed against the text extraction of pp. 147–149.** I did not reopen the page images.
- 3.31(ii): M and Z are finitely generated groups, Y is a magnet.
- 3.32(ii): M is a finitely generated abelian group, L and N are arbitrary.
- No separatedness is assumed. Only the (iii) cases assume it.

**§2 and §3: I recomputed these and accept them.**
- Degree-0 parts: P₀ = {(k,k)} in 3.32, and P₀ = {(m,f(m)) : m∈N} in 3.31.
- π is ab in 3.32, and g·A(f)(y) in 3.31.
- The action formulas are right.
- Invariance by fppf-lifting along D(M)→D(Γ) and D(Z)→D(K) is right, including k∘f = z∘f and z|_Y = k|_Y.
- Equivariance of the descended map and the two inverse checks are right.

**(a) Accepted, but no longer needed.**
- I checked Alper Thm 13.2, Example 12.4(2) and Def 5.1.1 in the extracted author copies. They read as quoted.
- The numbering against the published journal text is unverified. I did not read Prop 4.2.1(2) closely.

**(b) Accepted.**

**(c) Conclusion correct, one unjustified sentence.**
- The attempt says "a closed D(Γ)-stable subset is V(I) with I homogeneous". For its reduced structure this is false when D(Γ) is not smooth.
- Example: μ_p in characteristic p on k[x], with Z = V(x−1). The set is topologically stable because μ_p is infinitesimal, and (x−1) is not homogeneous.
- The set is still V((x−1)^p), so the claim survives as "for some homogeneous I". That requires an argument, which the torus reduction in B.1 below avoids.
- The tags 03KN, 0463, 03XX and 04XV say what is claimed. The last is item (6).

**(d) Formally valid as a citation.**
- AHR arXiv:1912.06162v4, Thm 3.12 reads as quoted, with the "no hypotheses" wording, and its proof uses 04XV and Thm 3.10 + Prop 3.11 as described.
- A web search found no journal version. That is search evidence, not proof of absence.
- Under the "default to not accepting" rule, this one step is an unverified black box: Prop 3.11 is only a pointer to Hall–Rydh [HR23, Prop 5.4]. Hence Part B.
- One detail the attempt skips: for non-quasi-separated X, the map U→X is not quasi-compact. No harm results, because W×_X U is a separated scheme (Step 3 below).

**Side remark on Alper 2013 Thm 6.6 after reducing to finitely generated P.** I did not check it, and it is not used.

**Small tests of the statement:**
- G_m on A², xy: strata and the origin behave as predicted.
- μ_p on k[x]: an invariant map must factor through x^p, as predicted.
- The non-locally-separated quotient of A¹ by x~−x (x≠0) as target: I found no obstruction near the origin, consistent with the lemma.

No counterexample emerged.

## B. Clean proof of Lemma D with no preprint

**Setup.** The question is Zariski-local on T, so take T affine and A = O(T)[P], a Γ-graded ring with A₀ = O(T)[P₀]. Then W = Spec A and Q = Spec A₀. A₀ is a direct summand of A as an A₀-module, and this persists after any base change A₀→A₀' (then (A⊗_{A₀}A₀')₀ = A₀').

**Claim.** For an algebraic space X over T, composition with π is a bijection from Hom_T(Q,X) to the invariant maps W→X.

### Step 1: reduction to Γ = Z^r

Choose a surjection Z^r→Γ. Put A'' = A⊗Z[Z^r], Γ-graded by deg(aχ^z) = deg a − [z].

- A'' has units in every degree, so it is a D(Γ)-torsor over Spec Ã, where Ã = A''₀ = ⊕_z A_{[z]}χ^z (SGA3 VIII 5.1). This is the correct, truly free use of the printed argument.
- If F : W→X is invariant, then (w,t) ↦ F(w) on W×D(Z^r) is invariant for this free action, because F(gw) = F(w). So it descends to F̃ : Spec Ã→X (fpqc sheaf: tag 0APL).
- F̃ is D(Z^r)-invariant, for the Z^r-grading of Ã with Ã_z = A_{[z]}χ^z. Its degree-0 part is A₀.
- Restricting along w ↦ (w,1): if F̃ = f∘π̃, then F = f∘π.

Check on μ_p, k[x]: Ã = k[u,v^±] with u = xχ, v = χ^p, weights 1 and p, degree-0 part k[x^p]. This agrees.

So from now on A is Z^r-graded and 𝕋 := D(Z^r).

A 𝕋-stable subset has homogeneous radical ideal: 𝕋 is smooth, so reduced structures pull back to reduced ones under the action and projection maps.

### Step 2: uniqueness

Same as (c), now with homogeneous I.
- For A₀→B₀' and a homogeneous ideal I, the image of V(I) is V(I∩B₀'). Indeed (A'/I)⊗k(p) has degree-0 part k(p)≠0 over p ⊃ I∩B₀', and it is closed.
- So π is surjective and universally closed on stable closed sets.
- The equalizer E→Q is a monomorphism, locally of finite type (03KN), a scheme (0463, 03XX), and universally closed, hence a closed immersion V(J) (04XV(6)).
- JA = 0 and A₀⊂A give J = 0.

Equality of the two maps on W therefore forces equality on Q, and this holds after any étale Q'→Q.

### Step 3: existence at a strictly henselian point

Fix a geometric point q̄ of Q. Put B₀ = O^{sh}_{Q,q̄} and B = A⊗_{A₀}B₀, with m the maximal ideal of B₀ and k = B₀/m separably closed.

**(i) The closed orbit.** A sum of proper homogeneous ideals has proper degree-0 part, so there is a unique maximal proper homogeneous ideal I. Every proper homogeneous ideal lies in I.
- In B/I every nonzero homogeneous element is a unit, and (B/I)₀ = k. So B/I ≅ k[Λ] with Λ⊂Z^r a free subgroup.
- F|V(I) is invariant under the transitive action, so it is the constant map on the point 1. Thus it factors as V(I)→Spec k→X, by x.
- As k is separably closed and an atlas is étale surjective, x lifts to u₀ : Spec k→U, with U an affine scheme étale over X.

**(ii) Lifted action.** W' := Spec A×_X U is a scheme, separated over Spec A×U (03KN, 03XX), étale over Spec A. Set t·(w,u) = (tw,u), well defined since F is invariant.
- pr_U is invariant.
- Over Spec B, u₀ gives an equivariant section s₀ of W'_B→Spec B over V(I).

Choose a qc open of W'_B containing s₀(V(I)) and saturate it to V = 𝕋·V₀, which is open (the action is flat and finitely presented) and qc.

**(iii) Graded integral closure.** C = Γ(V,O) is Z^r-graded (coaction by flat base change), and B→C is graded.

Let C' be the integral closure of B in C. It is graded: a coaction c ↦ Σc_zχ^z is integral over B[Z^r], and by 03GG, with B→B[Z^r] smooth, the integral closure of B[Z^r] in C[Z^r] is C'[Z^r], so each c_z∈C'. This is where torsion-freeness of the grading is used, and it is why Step 1 is needed: Z[Z^r] is smooth over Z.

By 03GW, since V→Spec B is of finite type, separated and quasi-finite, V→Spec C' is an open immersion, and it is equivariant.

**(iv) Isolating a component.**
- The map C'→B/I induced by s₀ is graded and surjective, with kernel 𝔫. The complement of V is V(𝔞), 𝔞 homogeneous, and V(𝔞)∩V(𝔫) = ∅.
- So 𝔞+𝔫 = C'. Taking degree-0 parts gives b∈𝔞₀ with b≡1 mod 𝔫₀.
- C'₀ is integral over B₀ (take degree-0 parts of monic equations). So B₀[b] is finite over B₀, hence a finite product of local rings (04GG(10)).
- Take its idempotent e∉𝔫₀, so b is a unit on that factor. Then D := eC' is graded with Spec D open and closed in Spec C' and contained in V.
- So D is étale and integral over B, hence finite étale and locally free.
- R = D/ID is finite étale over B/I with the section s₀. So R = B/I × R'', cut out by a stable idempotent e'' of R₀.
- D₀→R₀ is surjective. Lift e'' to an idempotent of D₀, again via a finite subalgebra over henselian B₀ (quotients of finite products of local rings lift idempotents). Replacing D by the complementary factor gives R = B/I.

**(v) Rank 1.** The rank-≠1 locus of D over B is closed and stable. If nonempty, it is V(J) with J proper and homogeneous, so J⊂I and it contains V(I), contradicting R = B/I. So rank is 1 everywhere and B≅D. This gives an equivariant section σ : Spec B→V⊂W'_B.

### Step 4: spreading out and gluing

Write Spec B = lim Spec B_i with B_i = A⊗_{A₀}A_i and Spec A_i→Q affine étale neighbourhoods. Note (B_i)₀ = A_i.

- σ lands in a qc open of W', which is locally of finite presentation over Spec A, so it comes from σ_i at a finite level (01ZC).
- The two maps 𝕋×Spec B_i→W' expressing equivariance are sections of a separated étale morphism, so they have open and closed equalizer. They agree in the limit, hence at a finite level (a limit of nonempty qc schemes is nonempty).
- So pr_U∘σ_i is invariant into the affine U, and it factors through Spec A_i. This yields f_i : Spec A_i→U→X with f_i∘π = F on W×_Q Spec A_i.

Varying q̄, these form an étale cover of Q. By uniqueness (Step 2) applied over Spec A_i×_Q Spec A_j, the f_i agree on overlaps. They glue to f : Q→X, since X is a sheaf. ∎

Base-change compatibility follows from uniqueness.

## C. The propositions

With Lemma D proved as in B, §2 and §3 of Attempt 2 stand verbatim and give:
- Prop 3.32(ii): (X^N)^L = X^{N∩L}, with P = N×L, δ(n,l) = l−n, Γ = N^gp+L^gp.
- Prop 3.31(ii): X^{N⊂M} = X^{Y⊂Z}, with P = M×Y, δ(m,y) = f(m)−y, Γ = f(M)+Y^gp.

## D. Honesty

**Added hypotheses: none.** Local finite presentation of X is not used, because the spreading is along W'→Spec A, which is étale regardless. Separatedness is not used.

**Verified at source (Stacks site, statements only):** 03KN, 0463, 03XX, 04XV, 03GG, 03GW, 04GG, 0APL, 01ZC.

**From memory, not rechecked:** SGA3 VIII 5.1, which the print itself cites, for the torsor in Step 1. It is standard for a graded algebra with units in every degree.

**The Part B proof is mine and new in this run.** Nobody has refereed it, and it deserves one independent adversarial pass, especially Steps 3(iii)–(iv). I re-ran those steps by hand on the examples above only. The AHR theorem is an independent confirmation of the same lemma, and the argument follows its strategy with Hall–Rydh's henselian input replaced by graded integral closure.

**The printed "free action" and "fpqc quotient" claims remain false as stated.** The only surviving use of freeness is the torus-induction torsor in Step 1 and the orbit V(I).

**Sources:**
- [AHR arXiv abstract v4](https://arxiv.org/abs/1912.06162v4)
- [Stacks tag 03GW](https://stacks.math.columbia.edu/tag/03GW)
- [Stacks tag 03GG](https://stacks.math.columbia.edu/tag/03GG)
- [Stacks tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
- [Stacks tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
- [Stacks tag 0463](https://stacks.math.columbia.edu/tag/0463)
- [Stacks tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
- [Stacks tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
- [Stacks tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
- [Stacks tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)

**Local files:**
- C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\am.txt
- C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\alper\a1912.06162.txt
- C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\alper\gms.txt
- C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\alper\ams.txt

# Referee passes

I could not refute Part B. Every step of Lemma D checks out, and the only gaps are unstated details that are easy to fill. I worked through Part B line by line and fetched the statement of each cited tag from the Stacks site. I read Props 3.31 and 3.32 only in the text extraction `scratchpad\am\am.txt`. The PDF has 76 pages, so journal pp. 147-149 cannot be opened by those page numbers.

**Cited tags, all as claimed**
- **03KN:** it gives `i : X×_Z Y → X×_T Y` as representable, locally of finite type, locally quasi-finite, separated and a monomorphism. The diagonal is a special case. It is what makes W' → Spec A×_T U separated.
- **0463:** a monomorphism locally of finite type is separated and locally quasi-finite.
- **03XX:** a separated, locally quasi-finite space over a scheme is a scheme.
- **04XV item (6):** universally closed, locally of finite type and a monomorphism gives a closed immersion.
- **03GG:** with R→S smooth, S⊗_R (integral closure of R in B) is the integral closure of S in S⊗_R B. Here R=B, S=B[Z^r] and "B"=C.
- **03GW:** for f of finite type and separated, f' is an isomorphism over an open U', with preimage the quasi-finite locus.
- **04GG item (10):** a finite algebra over a henselian local ring is a finite product of local rings.
- **0APL:** Gabber's fpqc sheaf property. It is stronger than needed; see gap 2.
- **01ZC:** for f locally of finite presentation, Mor(lim, X) = colim Mor. This is exactly the use in Step 4.

**Points attacked that hold**
- **V is separated, quasi-finite and of finite type over Spec B:**
  - W' is a scheme, by the definition of an algebraic space or by 03XX.
  - W' → Spec A×_T U is separated with affine target, so W' is separated, and W'_B → Spec B is separated étale.
  - V = image of 𝕋×V₀ is qc, and it is open because the action is an automorphism of 𝕋×W' followed by a flat projection.
  - So V → Spec B is qc, étale and separated, and 03GW applies with S' = Spec C' since the base is affine.
- **C' is graded:** ρ(c) is integral over ρ(B) ⊂ B[Z^r]. The structure map B[Z^r] → C[Z^r] is the standard one because B→C is graded. So 03GG gives c_z ∈ C'.
- **ZMT use (03GW):** all of V is the quasi-finite locus, so V → Spec C' is an open immersion. It is equivariant because the target is affine, so this can be checked on global sections.
- **Idempotents:**
  - The map C'→B/I is surjective because B→C'→B/I already is, and V(𝔫) = s₀(V(I)) ⊂ V.
  - b maps to 1 in k, so b is a unit on the factor E_i of B₀[b] through which E→k passes. Hence Spec D ∩ V(𝔞) = ∅.
- **D is finite étale:** see gap 4.
- **Rank:** the rank-≠1 locus is open, closed and stable, and it would contain V(I) if nonempty. Rank 1 with unit gives B ≅ D.
- **Step 1:** the torsor is direct, and I needed neither SGA3 nor the printed freeness claim. A'' is free over Ã on units indexed by Γ, and A''⊗_Ã A'' ≅ A''⊗Z[Γ]. Degree-0 parts and the restriction along t=1 are correct.
- **Step 4:** the equalizer complement is open and closed, the limit argument is valid, and invariant maps into an affine land in (B_i)₀ = A_i.
- **Non-quasi-separated X:** U→X is never required to be quasi-compact.

**Gaps, all harmless, with repairs**
1. **Uniqueness across Step 1.** Step 1 reduces only existence, and Step 2 is run only for Z^r. Add this: if uπ = vπ on W, then uπ̃ and vπ̃ agree on W×D(Z^r), which covers Spec Ã, and π̃ has the same degree-0 part A₀. So the Z^r case applies. Also, after Step 1 the ring Ã is O(T)[P×_Γ Z^r], and Steps 2-4 use only the grading.
2. **0APL is unnecessary.** A'' is finitely presented over Ã, by descent along the fpqc cover Spec A''→Spec Ã, so the torsor is fppf. The fppf sheaf property is enough. Keep or delete the citation.
3. **"Homogeneous radical" for 𝔞.** This needs two lines.
   - The automorphism (t,x)↦(t,tx) preserves 𝕋×V, hence also its complement 𝕋×V(𝔞).
   - 𝕋×V(𝔞)_red is reduced by smoothness, so the coaction factors and 𝔞 is homogeneous. The same argument covers Step 2 and the rank locus.
4. **"Étale and integral, hence finite."** Add that Spec D is open and closed in V, so B→D is of finite presentation (affine source and target, locally of finite presentation). Then finite type plus integral gives finite, and finite plus flat plus finite presentation gives locally free.
5. **e'' ∈ R₀.** This is asserted but not shown. The section s₀ is equivariant, so its image is stable. Then act⁻¹(Spec R'') = 𝕋×Spec R'' gives ρ(e'') = e''⊗1. The decomposition R = B/I × R'' uses the standard fact that a section of a separated étale map is an open and closed immersion. The replacement factor (1−e₁)D still contains V(𝔫) and lies in V.
6. **"F|V(I) constant."** State the reason: the orbit map 𝕋_k → D(Λ)_k is dual to the free extension k[Λ]⊂k[Z^r], so it is an fppf cover. F and x∘structure agree on it. The isomorphism B/I ≅ k[Λ] uses that Λ is free, and this is a second use of Step 1.
7. **Limit bookkeeping.** After the gluing, f∘π = F must be checked. This follows on the étale cover Spec B_i of W, because σ_i is a section of W'→W over Spec A compatible with the map to X. Overlap uniqueness applies Step 2 to the base change A₀→A_i⊗_{A₀}A_j, which Step 2 allows.
8. **Stale text in the note.** §4 and part of (d) still list AHR as an unreproved input, while Part B supersedes it. "Y any submonoid" should be read against the print's "magnet". I did not find the definition of magnet in the extraction, and the proof uses only that Y is a submonoid.

**Not checked at source**
- SGA3 VIII 5.1, which gap 1 and the Step 1 argument above make unnecessary.
- Attempt 2 parts (a) and (d) (Alper, AHR), which are no longer used once Part B is accepted.

**§2 and §3 reductions:** I recomputed the gradings, P₀, the fppf lift invariance and the equivariance of the descended maps. They are correct.

No file was edited. File reviewed: C:\Users\Arnaud\Desktop\algmag-stacks\notes\prop331-332-spaces-proof.md

VERDICT: OK (only harmless repairs)

---

I tried to refute the proof and could not. Lemma D and both reductions hold for arbitrary X, with no added hypotheses and without AHR, Alper or any non-Stacks input. The only gaps are in the write-up.

**Sources checked**
- The journal text of Props 3.31, 3.32 and Remark 3.11 was read in the local extraction, `C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\am.txt`. The PDF has only 76 pages, so the journal page numbers cannot be used as PDF page numbers, and I did not view the page images.
- The proof of 3.32(ii) ends on p. 150, not p. 149.
- The hypotheses match the print: neither (ii) assumes X separated.
- The printed freeness claim is false. For N = L = ℕ, g⋆(a,b) = (g⁻¹a, gb) fixes (0,0). The statements survive.

**Stacks tags, each fetched and compared with its use**
- 03KN(1): i is representable, locally of finite type, locally quasi-finite, separated and a monomorphism. OK.
- 0463 and 03XX: OK, though redundant given 03KN(1).
- 04XV(6): OK, applied to schemes after base change.
- 03GG: integral closure commutes with smooth R→S, for arbitrary R→B. OK, with S = B[Z^r].
- 03GW: needs f of finite type and separated. V→Spec B is étale with V quasi-compact, and it is separated because W' is a separated scheme. Quasi-finite at all points gives V = f'⁻¹(U') ≅ U'. OK, and no noetherian hypothesis is needed.
- 04GG(10): OK.
- 0APL: OK.
- 01ZC: OK, applied to a quasi-compact open of W', which is finitely presented over Spec A, with an affine inverse system.

**Step 1: holds, re-derived by hand**
- A'' = ⊕_γ χ^{z_γ}Ã is free over Ã, and A''⊗_Ã A'' ≅ A''[Γ]. So the torsor claim is elementary and SGA3 VIII 5.1 is not needed.
- Invariance of F̃ follows because q : Spec A''→Spec Ã is an fppf epimorphism.
- Ã₀ = A₀, and π̃∘ι = π.
- The μ_p test is correct.

**Step 2: holds**
- ρ is invariant because e is a monomorphism and eρ is invariant.
- ρ' is surjective because e' is injective and π' is surjective.
- The image of V(I) is V(I∩B₀'), because degree-0 parts commute with base change.
- 𝕋 smooth gives homogeneous radical ideals for stable sets.

**Step 3: holds, checked item by item**
- (i) B/I is a graded field with degree-0 part k and support Λ ⊂ Z^r free, so B/I ≅ k[Λ]. Constancy on V(I) follows by fppf-lifting the universal point along 𝕋→D(Λ).
- (ii) The saturation V is open and quasi-compact, since it is the image of 𝕋×V₀ under a smooth map.
- (iii) C' is graded, as ρ(c) is integral over ρ(B) ⊂ B[Z^r]. Note that V→Spec C' is the 03GW map for the normalization of Spec B in V.
- (iv) Degree-0 parts give b. The chosen factor of B₀[b] is the local factor mapping to k, where b↦1, so b is a unit there. The stable idempotent e'' has degree 0, since ρ(e'') = e''⊗1. Its lift to D₀ works because quotients of finite products of local rings lift idempotents.
- (v) The rank-≠1 locus is clopen and stable. If nonempty it contains V(I), which gives a contradiction. Rank 1 gives B ≅ D.

**Step 4: holds**
- The equalizers are clopen because W'→Spec A is separated étale.
- Emptiness of the quasi-compact complement descends to a finite level.
- (B_i)₀ = A_i, and the map into affine U lands in degree 0.
- Gluing uses Step 2 over Spec A_i×_Q Spec A_j, which is affine and is an allowed base change in Step 2.

**Attempt 2, sections 2 and 3: holds, recomputed**
- The gradings, P₀, π and the invariance by fppf lift are right, as are equivariance of the descended map and the two inverses.
- Remark 3.11 gives t·f = t∘f = f∘t, so F(a,hb) = h·F(a,b) is correct.
- The Yoneda step needs no representability of X^N.

**Stress tests**
- Non-quasi-separated X: W' is still a separated scheme, because Δ_X is a separated monomorphism and Spec A×U is affine. Only a quasi-compact open V is used, and U→X need not be quasi-compact. No break.
- Non-finitely generated P: A enters only through the graded structure. All finiteness is on V→Spec B, and Γ is finitely generated inside M or Z. No noetherian step occurs. No break.
- μ_p and torsion in Γ: these are removed by Step 1. Later steps use only Z^r-gradings, and the smoothness use in 03GG is legitimate. No break.

**Gaps, all harmless**
1. Uniqueness is proved only after Step 1, for Z^r-gradings, but it is needed for the original Γ. Step 1 does not state the transfer.
   - Repair: π̃∘q = π∘pr_W, so uπ = vπ gives uπ̃q = vπ̃q. Then q epi gives uπ̃ = vπ̃, and Step 2 gives u = v.
   - Uniqueness over T' for the equivariance checks in sections 2–3 uses this same statement.
2. Step 3(iv), "idempotent e∉𝔫₀", should read: the primitive idempotent of B₀[b] mapping to 1 under B₀[b]→C'₀/𝔫₀ = k.
3. The word "saturate" and the openness of V need the sentence on smoothness of 𝕋×V₀→W'_B, and the stability of U' in Spec C' needs the action on Spec C' to be stated. The grading of C' supplies that action.
4. The T-morphism property of the glued f is not stated.
   - Repair: with T affine, A_i→B_i is injective, so O(T)→A_i is determined by F.
5. "Zariski-local on T" for existence uses uniqueness to glue. That is fine but should be said, and Part B does not spell it out.
6. Attempt 2 (c), the claim "closed D(Γ)-stable subset is V(I), I homogeneous", is false as written for μ_p. Its "for the record" stratum claims in (d) are unverified, in particular F(Ψ)^gp∩ker δ = Ψ^gp. Both should be deleted in any final text. Attempt 2 section 4's dependence on AHR is also obsolete, so Part B should replace (a)–(d) wholesale.
7. Attempt 2 section 4, "Verified" and the Alper numbering are not used by the Part B route, so they should not be cited.

VERDICT: OK (only harmless repairs)