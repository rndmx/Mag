# Corrections verified 2026-11-06 (3 independent votes each, journal PDF page images)

## vote 1: correct

Quote: p.185, checked on the page image: "Theorem 15.4 Assume moreover that X is finitely presented over S. Assume additionally that one of the following conditions is satisfied (i) X is affine over S, (ii) M is a group and there exists an S-affine strongly-FPR atlas for X (e.g. the action is Zariski locally linearizable), then Π(a) is a finite poset." Failing step in the proof: "Because of X is finitely presented over S, there exists a finite subset E ⊂ M such that A is generated locally by homogeneous elements of degree in E." Base, §3: "Let us fix a base scheme S."

Fix: Add "S quasi-compact" to Thm 15.4. This is sufficient, not necessary: X quasi-compact in the absolute sense also works, since only a finite affine cover of the image of X in S is needed. The same addition is needed in (ii), Rem 15.6 and Conj 15.7, not only in (i). STATUS.md line 295 words it for the whole theorem, which is right. With S quasi-compact, the printed proof of (i) goes through for any M: take E as the union of the degrees over a finite affine cover.

Reason: The counterexample fits every printed hypothesis, and I could not refute it.

Setup: S = ⊔_{n≥1} Spec k, M = Z, X = Spec_S(A), with A = k[t_n] on the n-th point and deg t_n = n.

Hypotheses, each tried as an escape:
- S: §3 fixes only "a base scheme S", with no quasi-compactness convention. §15 adds none.
- X/S finitely presented: the print uses the relative notion, and p.161 reads "by definition X is of finite presentation if it is locally of finite presentation, quasi-compact and quasi-separated", applied to X/S. X→S is affine and of finite presentation on each point. Only an absolute reading of "quasi-compact" would exclude it, and "over S" rules that out.
- Separated and affine over S: yes. Actions of A(M)_S on S-affine X correspond to M-gradings (Prop 2.22).
- Π(a) is one global set, with X^N and X^L compared on all T/S (Thm 15.3), so no local reading of the conclusion is available.

Computation, by Thm 3.20 ("ideal sheaf generated {A_m | m ∈ M \ N}"): on the n-th point, X^N = A^1 if n ∈ N, and {0} otherwise. A nonzero A_m has m ≥ 0 and n | m, and if n ∈ N then all such m lie in N. So X^N = X^L iff N∩Z_{>0} = L∩Z_{>0}.

By Prop 15.1 (ii), N is pure iff N is the smallest magnet in its class, i.e. N ⊂ ℕ. Hence Π(a) is the set of all submonoids of ℕ, which contains kℕ for every k ≥ 1 and is infinite. A sign convention on the weights only replaces ℕ by −ℕ.

Where the proof breaks: the word "locally" is carried into a single global E. On the n-th point the degree n is needed, so no finite E works.

Beyond the proposal:
- Case (ii) fails on the same example: M = Z is a group, and id_X is an S-affine strongly-FPR atlas (Def 6.1, A a singleton).
- Rem 15.6 fails too: X^{kZ} is A^1 exactly on the points with k | n, so these are pairwise distinct for distinct k ≥ 1.
- Conj 15.7 inherits the same failure.

Lean evidence: `thm154_i` (Sec15General.lean:715) assumes [CompactSpace S]. The counterexample appears only in that file's header docstring (lines 26-28); I found no Lean theorem proving the infiniteness, so the computation above is a hand check, not a kernel check. Read-only, nothing compiled. I ran no sub-agents because no agent tool was available in this step; I did this check myself.

Files read: C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\am.txt, am.pdf in the same folder (pp.185-186), C:\Users\Arnaud\Desktop\algmag-stacks\STATUS.md, C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Sec15General.lean.

## vote 2: correct

Quote: Printed p. 153 (checked on the PDF page image): "Proposition 3.37 Assume that X is separated and locally of finite presentation over S. Let N be a magnet of M. Write N = colim_{i∈I} N_i as a directed colimit of submonoids of N. Let T → S be a scheme, then X^N(T) = colim_{i∈I} X^{N_i}(T)." Proof: "For any scheme T, we have A(N)_T = lim_{i∈I} A(N_i)_T by [32, Tag 01YW]. So X(A(N)_T) = colim X(A(N_i)_T) by [32, Tag 049J]."

Fix: Smallest fix: replace "Let T → S be a scheme" by "Let T → S be a quasi-compact scheme" and "For any scheme T" by "For T affine". Add one line to the proof: for T quasi-compact, cover T by finitely many affines and take a common index i. The local factorizations agree on overlaps because X^{N_i} → X^N is a monomorphism for X separated (k[N_i] → k[N] is universally injective, so A(N)_T → A(N_i)_T is schematically dominant). They then glue because X^{N_i} is a Zariski sheaf (Prop 3.2). No quasi-separatedness of T is needed. Equivalent form valid for every T: X^N = colim X^{N_i} as Zariski/fppf sheaves. Downstream: Prop 5.1 (ii) and Prop 8.5 are unaffected. Their conclusions are identities of Zariski sheaves (X^N ×_{X^Q} U^Q and X^{N_c} = X^N), so it suffices to test them on affine T. In the Prop 5.1 (ii) proof, "Let T → S be a scheme" should become "T affine". Lean's `prop337` (T affine, M f.g.) is narrower than this fix; the print does not need M f.g.

Reason: This is a real error of scope, not a misprint or a reading problem: the proof says "For any scheme T" explicitly, and the formula evaluates a presheaf colimit at T. The failure is at Tag 049J, which concerns limits of affine schemes, whereas A(N)_T is not quasi-compact when T is not.

X fits the printed hypotheses. ⊔A^1 over S = Spec k is a separated scheme, locally of finite presentation (l.f.p.), and nothing printed asks for quasi-compactness. Quasi-compactness of X does not rescue the statement either: take S = T = ⊔_n Spec k, and X → S is then of finite presentation.

The one-line counterexample in STATUS.md/Sec5Etale.lean is underspecified and needs completing. It needs a non-finitely-generated N, because if N is f.g. then N = N_i for large i and the claim is trivial. In particular the "weight n on the n-th copy" action with M = Z (the one used for Thm 15.4) does NOT give a counterexample here, since every submonoid of Z is f.g.

A complete counterexample (M is any abelian monoid in §3):
- M = Z^2, N = {0} ∪ {(a,b) : a ≥ 1}, and N_i generated by (1,b) with |b| ≤ i. The N_i are directed with union N, and (1,n) ∈ N_i iff |n| ≤ i.
- X = ⊔_{n≥0} A^1 with coordinate of degree m_n = (1,n) on the n-th copy, and T = ⊔_n Spec k.
- By Thm 3.20, (A^1_m)^L is A^1 if m ∈ L and the origin otherwise.
- The point of X^N(T) sending the n-th Spec k to the point 1 of the n-th copy, i.e. x ↦ X^{m_n} on A(N)_k, lies in no X^{N_i}(T). An equivariant factorization would need X^{m_n} ∈ k[N_i], which fails for n > i.
- So X^N(T) ≠ colim X^{N_i}(T), because a colimit over I does not commute with the infinite product over n.

The rest of the printed proof (equivariance by schematic density and separatedness) is fine. I checked this directly on the print and by hand, not with Lean. No subagents were spawned, because this step has no agent tool. The Lean repo carries the sentence "false when T is not quasi-compact" and the affine-T theorem, but I found no formalized counterexample for 3.37.

## vote 3: correct

Quote: Published p. 153 (read on the page image), Prop 3.37: "Assume that X is separated and locally of finite presentation over S. Let N be a magnet of M. Write N = colim_{i∈I} N_i as a directed colimit of submonoids of N. Let T → S be a scheme, then X^N(T) = colim_{i∈I} X^{N_i}(T)." Proof: "For any scheme T, we have A(N)_T = lim_{i∈I} A(N_i)_T by [32, Tag 01YW]. So X(A(N)_T) = colim X(A(N_i)_T) by [32, Tag 049J]." Standing setup of §3 (p. 140): "Let us fix a base scheme S. ... Let us fix an S-space X. Let us fix a commutative monoid M ... We assume that A(M)_S acts on X"; "a magnet N is by definition a submonoid N ⊂ M".

Fix: Replace "Let T → S be a scheme" by "Let T → S be a quasi-compact scheme". For arbitrary T, the injectivity of colim X^{N_i}(T) → X^N(T) still holds, and X^N is the Zariski sheafification of the presheaf colimit. The correction note must also state the action, because "X=⊔A¹, T=⊔Spec k" alone is not a counterexample. Complete it as follows: k a field, S = Spec k, M = Z², N = {a>0} ∪ {(0,b): b≥0}, N_i = <(0,1),(1,-i)> = {a≥0, b≥-ia}, X = ⊔_{n≥1} A¹_n with the coordinate x_n of degree m_n = (1,-n), T = ⊔_{n≥1} Spec k. The point φ with φ|T_n given by x_n ↦ X^{m_n} lies in X^N(T) and in no X^{N_i}(T). Downstream: Prop 5.1(ii) (p. 156), "Let T → S be a scheme ... Using (i) and Proposition 3.37", should first reduce to T affine or quasi-compact. Its conclusion is Zariski-local on T, so it survives.

Reason: I tried to refute the correction and could not.

1. Does X fit the hypotheses? Yes. ⊔A¹ over Spec k is separated and locally of finite presentation. The print asks for nothing more: it does not ask for quasi-compactness of X, T or S, and it does not ask for M finitely generated. The grading gives a legitimate A(M)-action on X, and T is a scheme over S. The colimit is literally of sets of T-points. The proof confirms this reading: "For any scheme T".

2. Check of the counterexample. N_i is increasing with union N, and N_i ⊂ N. An equivariant map A(P)_k → A¹_n is x_n ↦ cX^{m_n} with m_n ∈ P, or x_n ↦ 0. The weight sign convention does not matter: replace m_n by -m_n and N by -N otherwise. Since m_n = (1,-n) ∈ N, φ exists. Now suppose φ came from X^{N_i}(T). For n>i, the restriction to T_n would be a map from the connected A(N_i)_k to X. Compatibility with φ forces it into copy n, with x_n ↦ X^{m_n} under k[N_i] ⊂ k[N]. That is impossible because m_n ∉ N_i. So surjectivity of the colimit map fails.

3. Caveats on the proposed note.
- The non-finitely-generated N is essential: for M = Z every submonoid is f.g., so N = N_i for large i and the statement is trivially true. The weights must also be unbounded. The action is therefore a necessary part of the counterexample and must be stated.
- The Lean evidence is only the claim in STATUS.md line 293 and the docstring at Sec5Etale.lean:1951. A grep of the .lean and .md files found no Lean declaration of a counterexample, so my check above is by hand. `prop337` and `exists_ofLE_eq` cover T affine and M f.g. only.

4. Where the print's proof breaks. Tag 049J is applied to the limit A(N)_T = lim A(N_i)_T, but the limit-preservation characterization of l.f.p. concerns affine (or qcqs) schemes. It says nothing about X(A(N)_T) when A(N)_T is not qcqs. The tags list has only the tag number, so I did not read the tag text and rely on the standard statement here.

5. The fix is sufficient for any quasi-compact T, without assuming quasi-separated. Take a finite affine cover, descend on each piece and take a common i by directedness. The lifts agree on overlaps because X^{N_i}(U) → X^N(U) is injective for every U (X separated and O_U[N_i] ⊂ O_U[N], the same schematic-density argument as the print). Then glue, since X^{N_i} is a Zariski sheaf. This step is a hand argument, not in Lean, and Lean's M f.g. restriction is not needed for it.

Nothing was edited or compiled.

## vote 4: correct

Quote: Thm 15.4 (p. 185, checked on the page image): "Assume moreover that X is finitely presented over S. Assume additionally that one of the following conditions is satisfied (i) X is affine over S, (ii) M is a group and there exists an S-affine strongly-FPR atlas for X (e.g. the action is Zariski locally linearizable), then ℧(a) is a finite poset." Standing hypotheses of §15 (p. 184): "Let M be an abelian monoid. Let X be a separated algebraic space over S endowed with an action a of A(M)_S." §3: "Let us fix a base scheme S." Faulty proof step: "Because of X is finitely presented over S, there exists a finite subset E ⊂ M such that A is generated locally by homogeneous elements of degree in E."

Fix: Add "S quasi-compact" to Thm 15.4, in both (i) and (ii), not only (i). Remark 15.6 inherits it, and Conjecture 15.7 and Remark 15.8 need it too. With S quasi-compact, the printed proof of (i) works unchanged: finitely many affines cover S, each contributes finitely many homogeneous generators, so E is finite.

Reason: The counterexample meets every printed hypothesis, and I checked it by hand. The source does not limit S: "Let us fix a base scheme S", and I found no quasi-compactness assumption on S in the section 1, 3, 6 or 15 set-up text I read. The Lean `thm154_i` adds [CompactSpace S], and its docstring calls this a hypothesis the statement needs.

Setup: k a field, S = ⊔_{n≥1} Spec k, M = Z, X = ⊔_n A¹_k with the n-th copy over the n-th point, so A = ⊕_n k[t_n] with t_n in degree n. If the paper's convention gives degree −n, replace N by −N; nothing else changes.

Hypotheses:
1. M = Z is an abelian monoid.
2. X → S is affine: the preimage of an affine open, a finite union of points, is a finite disjoint union of A¹'s, which is affine. So (i) holds.
3. X → S is separated, because it is affine.
4. X → S is finitely presented: locally of finite presentation, since each fibre is k[t]; quasi-compact and quasi-separated, since it is affine. This is a relative notion, so S not being quasi-compact does not break it.
5. The action of D(Z)_S is defined fibrewise, and the action axioms hold fibrewise.

Attractors: by the graded description (p. 142-ish Hom-M-graded(A, B[N]); §5 "M-graded morphisms"), a T-point of X^N over the n-th point is a graded map k[t] → O(T)[N]. It sends t to fχ^n if n ∈ N and to 0 otherwise. So over the n-th point X^N is A¹ if n ∈ N and the origin otherwise, and X^N = X^L iff N∩Z_{>0} = L∩Z_{>0}.

Pure magnets: the printed definition is minimal, not maximal: Prop 15.1 (ii) "X^N = X^L ⇒ N ⊂ L", and E(Y) = ⋂{N | X^N = Y}. Take N_k = kN for k ≥ 1. If X^{kN} = X^L then L contains the positive multiples of k, so kN ⊂ L, and kN is pure. The N_k are pairwise distinct, so ℧(a) is infinite. This does not use Thm 15.3 or Fact 3.34.

Where the proof breaks: each point of S needs E_n = {n}, so no finite E works. The word "locally" in the printed sentence hides this.

The correction is too narrow in stating (i) only:
- (ii) fails on the same example: M = Z is a group, and id: X → X is an S-affine strongly-FPR atlas under Def 6.1 (iii), (iv) (one stable S-affine piece, A finite; the FPR isomorphisms are trivial).
- Remark 15.6 is also false: X^{kZ} over the n-th point is A¹ iff k | n, so the set of X^{D(M/Z)} is infinite.
- Conjecture 15.7 is false over this S, and Remark 15.8 ("Conjecture 6.9 implies Conjecture 15.7") fails with it, because Conj 6.9 (ii) holds here via U = X.

Lean evidence is one-sided. `thm154_i` and `thm154_ii` (AlgMag\Sec15General.lean:715, 737) prove the corrected statements. The counterexample appears only in the file header (line 26) and in C:\Users\Arnaud\Desktop\algmag-stacks\STATUS.md:295; a grep of AlgMag\ for an infiniteness statement on pureMagnets found nothing. REMARKS.md has no entry on 15.4. So the falsity rests on the hand check above.

Sufficiency only: S quasi-compact is not necessary. The same S with all weights equal to 1 gives a finite ℧(a).

No sub-agents were available here, so I did this check myself.

## vote 5: correct

Quote: Page 153, Prop 3.37, checked on the page image: "Assume that X is separated and locally of finite presentation over S. Let N be a magnet of M. Write N = colim_{i∈I} N_i as a directed colimit of submonoids of N. Let T → S be a scheme, then X^N(T) = colim_{i∈I} X^{N_i}(T)." Proof: "For any scheme T, we have A(N)_T = lim_{i∈I} A(N_i)_T by [32, Tag 01YW]. So X(A(N)_T) = colim X(A(N_i)_T) by [32, Tag 049J]." Standing hypotheses, §3 opening (p. 140): "Let us fix a base scheme S. In this paper, an S-space is an algebraic space over S. Let us fix an S-space X. Let us fix a commutative monoid M ..."; "In this section, a magnet N is by definition a submonoid N ⊂ M".

Fix: Replace "Let T → S be a scheme" with "Let T → S be a quasi-compact scheme". The proof should then start "for T affine" and reach quasi-compact T by a finite affine cover, as in the reason field. An equivalent statement for arbitrary T: X^N is the colimit of the X^{N_i} as Zariski sheaves, not value by value. Quasi-separatedness of T is not needed. The uses at Prop 5.1(ii) (p. 156) and Prop 8.5 are claims about fppf sheaves (Prop 3.2), so they can be checked on affine T. I expect them to survive, but I did not re-audit those proofs.

Reason: The correction is right. X fits the printed hypotheses: it is separated and l.f.p. over S, and quasi-compactness is never assumed. The recorded form "X=⊔A¹, T=⊔Spec k" omits M, N and the weights, and STATUS.md and Sec5Etale.lean:1951 only assert falsity for non-quasi-compact T. I completed the example as follows.

DATA. Let k be a field and S = Spec k. Let M = Z², a commutative monoid, even a finitely generated group. Let N = {(a,b): b>0} ∪ {(a,0): a≥0}, a submonoid, hence a magnet by the §3 definition. Let N_i be generated by (1,0) and (−j,1) for 0≤j≤i. These are submonoids of N, form an increasing chain, and have union N, since (a,b) with b>0 equals (a,1)+(b−1)(0,1), and (a,1) lies in N_i once i≥−a. The elements of N_i with b=1 are exactly the (a,1) with a≥−i, so w_n := (−n,1) lies in N_n but not in N_{n−1}.

X. Let X = ⊔_{n≥0} Spec k[x_n] with deg x_n = w_n, that is, coaction x_n ↦ x_n⊗X^{w_n}, defined copy by copy. This is an action of A(M)_S in the sense of p. 140. X is a scheme, hence an S-space. Separated: the diagonal is closed, because it is the diagonal on each A¹_n×A¹_n and empty on the off-diagonal pieces. L.f.p.: each A¹_n is of finite type over k. X is not quasi-compact, but the proposition does not ask for that.

T. Let T = ⊔_{n≥0} Spec k, an S-scheme, which is all the print requires. Then A(N)_T = ⊔_n A(N)_k, so X^N(T) = ∏_n X^N(k) and likewise for each N_i.

POINT. Let φ_n: A(N)_k → A¹_n be given by x_n ↦ X^{w_n}. It is well defined because w_n ∈ N, and M-graded, hence equivariant (the graded description is the one in the proof of Thm 3.20). So φ = (φ_n) ∈ X^N(T).

NOT IN THE COLIMIT. Suppose φ comes from ψ = (ψ_n) ∈ X^{N_i}(T). Take n = i+1. k[N_i] is a subring of k[Z²], so a domain, and A(N_i)_k is connected. Hence ψ_n lands in a single copy, and that copy must be the n-th because the composite with A(N)_k → A(N_i)_k is φ_n. Then ψ_n corresponds to a graded map k[x_n] → k[N_i], and w_n ∉ N_i has zero graded piece, so x_n ↦ 0. This agrees with Thm 3.20 (x_n lies in J_{N_i}, so (A¹_n)^{N_i} is the origin). But φ_n sends x_n to X^{w_n} ≠ 0, a contradiction. So X^N(T) ≠ colim X^{N_i}(T), since the map from the colimit is not surjective.

WHERE THE PROOF FAILS. The false step is the Tag 049J sentence, stated "For any scheme T". A(N)_T is not quasi-compact here, and that tag's commutation with limits concerns limits of affine (or qcqs) schemes.

REPAIR, proved by hand. For T affine the printed proof works. Lean confirms this for M a finitely generated group (prop337, Sec8Limits.lean:1077; exists_ofLE_eq, Sec5Etale.lean:1953, N_i f.g.). For T quasi-compact, take a finite affine cover and a common index i by directedness. On overlaps, O[N_i] → O[N] is split injective, so A(N)_W → A(N_i)_W is schematically dominant for every W, and separatedness of X makes the factorizations agree even on non-quasi-compact overlaps. They therefore glue. The same argument gives injectivity of the map from the colimit. This repair is not in Lean beyond affine T.

The hypothesis must go on T, not on X. Taking X = ⊔_n A¹ over S = ⊔_n Spec k with T = S and the same weights gives X affine and of finite presentation over S, and the same failure.

Scope: this was read-only with no compile. Sources were the print at C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\am.txt and am.pdf (printed p. 153, page image rendered to p337.png alongside), and C:\Users\Arnaud\Desktop\algmag-stacks\STATUS.md line 293. The counterexample itself is not formalized in Lean.

## vote 6: correct

Quote: Semigroup Forum p. 150 (page image checked), proof of Fact 3.34: "Furthermore, in the category of rings, Z[∩_{l∈I} N_l] = lim_{J⊂I} Z[∩_{l∈J} N_l]. So A(∩_{l∈I} N_l)_S = colim_{J⊂I} A(∩_{l∈J} N_l)_S." Then: "= Hom_T^{A(M)_S}(colim_{J⊂I} A(∩_{l∈J} N_l)_T, X_T)" and "[32, Tag 002H] and equivariance is clear ⊃ lim_{J⊂I} Hom_T^{A(M)_S}(A(∩_{l∈J} N_l)_T, X_T)". Statement: "Let {N_i}_{i∈I} ⊂ M be magnets such that X^{N_i} = X^{N_j} for all i, j ∈ I. Assume that X is separated and that one of the following conditions holds (i) X is affine over S, (ii) M is a finitely generated abelian group, (iii) M is cancellative, M^gp is finitely generated as abelian group, and X^{∩_{l∈J} N_l} is a separated algebraic spaces for any finite subset J ⊂ I, then, for all i ∈ I, X^{N_i} = X^{∩_{l∈I} N_l}."

Fix: Correct the proof, not the statement. Suggested entry: "Fact 3.34 (ii), (iii), proof. Z[∩N_l] = lim Z[∩_J N_l] gives A(∩N_l)_S = colim A(∩_J N_l)_S only among schemes affine over S, so Tag 002H does not give the mapping property for non-affine X_T. With M = Z² and N_k = {y ≥ 0, kx + y ≥ 0}, the open U = A²_S minus {x = 0, y = 1} receives compatible maps from all A(N_k)_S, but A²_S does not map to it compatibly." Scope to add: this refutes the justification only. U is not A(M)-stable, so it carries no action and is not a counterexample to Fact 3.34. Fact 3.34 (ii), (iii) for infinite families with X only separated remains unproved and unrefuted, including the same colimit among equivariant separated targets. Finite families are unaffected (fact334_finite_scheme for schemes). Infinite families have the Lean fact334_free for X separated, l.f.p. and quasi-compact (S separated), which rests on the Thm 6.8 stubs per notes/fact334-attempt.md. Case (iii) needs its own repair; the Lean results here are finite-family or atlas-conditional. Fact 3.34 (i) is untouched: its printed proof uses Prop 3.24.

Reason: The correction is valid as a correction of the proof.

Print: the ring identity is true, since the transition maps are injective and it is an intersection inside Z[M]. Spec turns it into a colimit only among affine schemes (relatively affine over S). The step needs Mor(colim, W) for W = X_T non-affine. I fetched Tag 002H from the Stacks Project: it is Remark 4.14.4, the formula Mor(colim M_i, W) = lim Mor(M_i, W), valid only when the colimit is taken in a category containing W. The printed "⊃" is exactly the unjustified direction, because the reverse inclusion is what the proof must establish. The proof shares this step for (ii) and (iii). The colimit claim does not involve X, and M = Z² is also a case of (iii).

Witness, line by line (Sec3Remaining.lean, chainN, iInf_chainN, chain_no_point):
1. Magnets: the standing convention of §3 says a magnet is a submonoid. chainN k is a submonoid of M = Z², which is finitely generated, cancellative and its own M^gp.
2. Decreasing: for x < 0 the condition is y ≥ k|x|, which tightens with k; for x ≥ 0 it is just y ≥ 0. Finite intersections are N_{max J}, so the chain is cofinal in the finite subsets J.
3. Intersection: iInf_chainN gives the quadrant over k ≥ 1, and my hand check agrees.
4. Relation: (-1,k) ∈ N_k, and (1,0) + (-1,k) = k(0,1). A K-point with x = 0, y = 1 would give 0 = 1 in a nontrivial ring K, so it is excluded. Applied to residue fields, this shows V(x, y-1) is disjoint from the image of A(N_k)_S.
5. From no point to no colimit: this is only a docstring in Lean, so I checked it by hand. Suppose g: A²_S → U_S is compatible, with j: U_S → A²_S the open inclusion. Then j∘g agrees with the identity on the torus D(Z²)_S, which lies in every A(N_k)_S. The torus is schematically dense in A²_S (Z[x,y] → Z[x^±,y^±] is injective and stays so after flat base change) and A²_S is separated, so j∘g = id. Then A²_S factors through U_S, which is false for S nonempty. U is separated, being open in A²_S. The argument also works in algebraic spaces, since U is a scheme.
The Lean theorem is stated for all k, including k = 0, where N_0 is not sharp; this is harmless. The coordinates are swapped relative to the a, b of the earlier message, which is harmless too.

Printed hypotheses:
- The chain meets every hypothesis on M and the N_i in (ii) and (iii).
- U does NOT meet the standing hypothesis of §3 that A(M)_S acts on X. U is not stable, because the orbit of (0,1) is {x = 0, y ≠ 0}.
- Stabilising does not help. The origin is in every image (N_k is sharp for k ≥ 1), and a stable open containing the origin is all of A². So no open subscheme of A² gives a counterexample, in agreement with notes/fact334-attempt.md item 4.

Hence the witness refutes the non-equivariant colimit, which is what the print asserts before adding "equivariance is clear". It does not refute Fact 3.34 or the equivariant universal property. STATUS.md line 292 is accurately worded because it speaks only of the proof. The print's "colim" names no category. If it is read among affine schemes the identity is true, but then the Hom step fails for non-affine X. If it is read in schemes the identity is false. Either way the step fails.

## vote 7: correct

Quote: Semigroup Forum, printed p. 150 (PDF p. 25), read from the page image, proof of Fact 3.34: "Furthermore, in the category of rings, Z[∩_{l∈I} N_l] = lim_{J⊂I} Z[∩_{l∈J} N_l]. So A(∩_{l∈I} N_l)_S = colim_{J⊂I} A(∩_{l∈J} N_l)_S." Then: "X^{∩_{l∈I} N_l}(T) = Hom_T^{A(M)_S}(A(∩_{l∈I} N_l)_T, X_T) = Hom_T^{A(M)_S}(colim_{J⊂I} A(∩_{l∈J} N_l)_T, X_T) [32, Tag 002H] and equivariance is clear ⊃ lim_{J⊂I} Hom_T^{A(M)_S}(A(∩_{l∈J} N_l)_T, X_T)". The printed relation is ⊃, not =, and the text never says in which category the colim is taken.

Fix: Keep the correction, as a correction to the proof only, for infinite I. Suggested wording: "The ring identity is true, so A(∩N_l) is the colimit in affine schemes. It is not the colimit in schemes, so Tag 002H does not give the ⊃ step for non-affine X_T. The witness is not equivariant, so it does not refute the Fact, or the colimit among equivariant schemes." In STATUS.md line 292, add that chain_no_point proves only the missing-point lemma, and that the failure of the colimit is a by-hand deduction (the docstring). Fact 3.34 (ii),(iii) for infinite families stays unproved with X only separated. It is not shown false. Lean has finite families, the strongly-FPR atlas case (fact334_strong), and X qc l.f.p. on stubs (fact334_free). Printed typos not affected: "a separated algebraic spaces" in (iii).

Reason: The refutation attempt fails, on all three readings of the colim.

Parts of the print that are fine: the set and ring identities hold, because Z[N] is free on N and the Z[N_J] are spanned by subsets of one basis. Finite I is trivial, since the index poset has a top element.

Reading 1, colim in affine schemes: true, since Aff = Rings^op. But Tag 002H (Remark 4.14.4, checked on the live Stacks page) is only the universal property inside a category where the colimit exists, so it needs X_T to be an object of that category. X_T is non-affine in the only cases where this proof is used, because the affine case (i) is handled separately through Prop 3.24. So the step does not apply.

Reading 2, colim in schemes: false, and I rechecked this by hand. Take M = Z^2, N_k = {y >= 0, kx + y >= 0}, k >= 1 (Sec3Remaining.lean:1435), which is within (ii) and (iii). iInf_chainN gives ∩N_k = N^2. In Z[N_k], u = (1,0), v = (0,1), w = (-1,k) satisfy u w = v^k, so no point has u = 0, v = 1 (chain_no_point, for any nontrivial K, so also for residue fields). The section (0,1) of A^2_S is a closed immersion for S nonempty, because A^2_S is separated over S. Let U be its open complement, with inclusion ι. Every A(N_k)_S maps compatibly to U. If A^2_S were the colimit, there would be g : A^2_S -> U, and uniqueness in the universal property would give ι g = id, making ι surjective. That is a contradiction. Lean proves only the no-point lemma and the intersection; this deduction is in the docstring. The conclusion is still right.

Reading 3, colim among A(M)-equivariant schemes: this is the reading that would rescue the proof, since the print uses equivariant Hom and only needs ⊃. The witness does NOT touch it. U is not D(M)-stable, because (0,1) is not a fixed point. The image of A(N_k) is {u != 0} ∪ {0}, and any stable open containing the origin is all of A^2 (notes/fact334-attempt.md §4). But nothing in the print establishes this reading: the only argument given is the ring identity, which yields reading 1. "Equivariance is clear" addresses equivariance of a map assumed to exist, not its existence. The attempt notes (§6) record this as open, and I did not settle it either. So the print has an unjustified step on this reading, not a false one.

Conclusion: the print's step is invalid as written, and "fails in schemes" (STATUS.md:292) is accurate. REMARKS.md's "Forced" is fair for the proof route. The Fact's statement is neither confirmed nor refuted beyond the Lean cases listed in the fix. This check was one agent working alone, with no separate subagents, and nothing was compiled or edited.

## vote 8: correct

Quote: Print, p. 185 (checked on the page image): "Theorem 15.4 Assume moreover that X is finitely presented over S. Assume additionally that one of the following conditions is satisfied (i) X is affine over S, (ii) M is a group and there exists an S-affine strongly-FPR atlas for X (e.g. the action is Zariski locally linearizable), then ℧(a) is a finite poset." Proof: "Because of X is finitely presented over S, there exists a finite subset E ⊂ M such that A is generated locally by homogeneous elements of degree in E."

Fix: Add one hypothesis: "Assume moreover that S is quasi-compact and that X is finitely presented over S." The proof then works as printed: cover S by finitely many affine opens, take a finite E_i on each, and let E be their union. Weaker alternative: require X itself quasi-compact, since its image in S is then quasi-compact and the same argument runs. Remark 15.6, Conjecture 15.7, Remark 15.8 and the sentence in Section 1 inherit the hypothesis. Separate misprint: Conjecture 15.7 refers to "(i),(ii) or (iii)", but the theorem has no (iii).

Reason: Real error, not a misprint or a reading problem. The printed hypotheses allow the counterexample.

Hypotheses of §15 and the theorem:
- §15 fixes only "Let M be an abelian monoid. Let X be a separated algebraic space over S endowed with an action a of A(M)_S."
- S is an arbitrary scheme. A search of the text finds no quasi-compactness assumed on S, only on X/S.
- "Finitely presented over S" is relative. The text defines it as "locally of finite presentation, quasi-compact and quasi-separated" and writes "X/S".

Counterexample: S = ⊔_{n≥1} Spec k, M = Z, X = ⊔_{n≥1} A^1, with x on the n-th copy in degree n.
- X → S is affine, because the fibre over each point is A^1. So (i) holds.
- It is of finite presentation, because over any affine open (finitely many points) X is a finite union of copies of A^1. It is also separated.
- (ii) holds too: M is a group and id_X is an S-affine strongly-FPR atlas, so both cases fail.

Attractors (hand computation): a graded map k[x] → R[N] sends x to rX^n if n ∈ N and to 0 otherwise. So X^N on copy n is A^1 if n ∈ N, and {0} otherwise. Hence X^N determines N ∩ Z_{>0}.

Purity: for each k ≥ 1, the magnet kℕ is pure. If L ⊊ kℕ, then L ∩ Z_{>0} ⊊ kℕ ∩ Z_{>0}, so X^L ⊊ X^{kℕ}, which is condition (i) of Prop 15.1. So ℧(a) contains the infinitely many kℕ and is not finite.

Where the proof breaks: the printed step asserts one finite E from a local statement. "Generated locally" gives a finite E_i on each affine open, and passing to one E needs finitely many opens. In the example the required degrees are all n ≥ 1.

Lean evidence:
- `thm154_i` (AlgMag/Sec15General.lean:715) and `thm154_ii` carry `[CompactSpace S]`.
- The counterexample appears as prose in that file's header and in STATUS.md's Paper corrections, as "Needs `S` quasi-compact". A limited search (file names matching Sec15, Leftover or Final) found no formal counterexample, so its verification is the hand computation above.
- `exists_closure_of_affine_base` (Sec15Final.lean:112) gets a finite E over an affine T_0 with no assumption on S. That matches the diagnosis: the failure is only the local-to-global step.

Not checked, outside this item: Prop 8.5 assumes only X → S quasi-compact and has a similar finiteness step, so it may need the same look.

## vote 9: correct

Quote: Semigroup Forum p. 181, read from the page image. Setup: "let S' be a closed locally principal subscheme of S". Statement: "Proposition 13.1 Assume moreover that X → S, (Bl_Y^D X)^N → S and Bl_{Y^N}^{D^N} X^N → S are flat. Then D(M)_S acts naturally on Bl_Y^D X, moreover we get a canonical isomorphism Θ : (Bl_Y^D X)^N ≅ Bl_{Y^N}^{D^N} X^N." Proof: "Remark first that since D(M)_S → S, X → S, Bl_Y^D X → S are flat, D(M)_S, X and Bl_Y^D X belong to Spaces_S^{S'-reg}". P. 182: "Since Bl_Y^D X → S is flat, by [22, §3.6], we have (Bl_Y^D X)_T = Bl_{Y_{T'}}^{D_{T'}} X_T." And: "Now since Bl_{Y^N}^{D^N} X^N and (Bl_Y^D X)^N are flat over S, they belong to Spaces_S^{S'reg}."

Fix: The statement stands as printed; only the proof needs repair. It holds without flatness of X or of Bl_{Y^N}^{D^N} X^N, so only (Bl_Y^D X)^N → S flat is needed.

Replace the proof's flatness steps as follows.
(1) Action: D(M)_S × Bl is flat over Bl, and Bl is S'-regular by construction. So the universal property of Bl gives the action directly, with no regularity of X or D(M)_S.
(2) Lemma: if Z → S is flat and Z maps over S to an S'-regular B, then Z is S'-regular. Locally, if r g = 0 in C flat over A, then g = Σ c_k y_k with r c_k = 0 in A. Each c_k dies in O_B because r is regular on B, so g = 0. This is `isRegular_of_flat_of_hom`. Applied to (Bl)^N → Bl, it makes (Bl)^N S'-regular.
(3) Bl_{Y^N}^{D^N} X^N is S'-regular by construction.
(4) Drop the base change (Bl)_T = Bl_{Y_T'} X_T. For T S'-regular, A(N)_T is S'-regular, so the universal property of Bl over S gives Hom_S(A(N)_T, Bl) = {f : A(N)_T → X with f over S' factoring through Y}. Equivariance follows from the uniqueness part of the universal property. This is `exists_lift_pt` and `pt_uniq`.

Corollary 13.3 is unaffected: S' is Cartier there and the proof obtains Bl → S smooth.

Reason: I tried to defend the print and could not defend the proof, though the statement survives.

**Flat does not imply S'-regular.** Sec. 13 assumes S' only locally principal, and Cor 13.3 separately says "effective Cartier divisor", so the two are not conflated. I did not read [22] itself. I took S'-regular to mean that T_{S'} is Cartier in T, as `IsRegular` encodes it (Sec13General.lean:55).
- Take S = X = Spec k[ε], S' = V(ε), Y = D, with trivial action. X → S and D(M)_S → S are flat, but ε is a zero divisor on them, so the opening sentence is false.
- The last sentence of the proof uses the same inference.
- The statement is still true here: any S'-regular T has ε both nilpotent and regular, so T is empty. Hence Bl = ∅, both sides are ∅, and all printed hypotheses hold. This is no counterexample to the statement.

**Bl → S flat is unassumed, not implied, and the step using it can fail.** I checked this by hand. Take k[x,y] = O(S), S' = V(x), M = Z, X = S × A^1_t with t of weight 1, N = {0}, D = Spec k[y,t], Y = V(yt).
- Bl = Spec k[x,y,t,u]/(xu − yt) with u = yt/x. It is not flat over S: the fibre over the origin has dimension 2, where flatness would force 1.
- The printed hypotheses still hold: X → S is flat, (Bl)^0 = S because t and u have weight 1, and Bl_{Y^0}^{D^0} X^0 = Bl_{V(x)} S = S. Θ is an isomorphism.
- The printed equality fails for T = V(y), which is S'-regular: (Bl)_T = Spec k[x,t,u]/(xu) has x-torsion, while the dilatation of X_T is Spec k[x,t].
- The next printed line, the Hom equality, still holds, because A(N)_T is regular. So the conclusion survives but this justification does not.

**Lean evidence, read only, not compiled.** `prop13_1` (Sec13General.lean:1469) assumes only [Flat ZB.hom], plus Mono j and representability. `prop13_1_printed` derives the printed form, and its docstring says the proof uses only the flatness of (Bl_Y^D X)^N. The docstring of `isRegular_of_flat_of_hom` says flatness over S alone does not suffice when S' is not Cartier. `prop13_1_spaces` (Sec13Spaces.lean:1571) covers algebraic spaces. STATUS.md records "no checker pass on record" for this row, and I checked the argument by hand above.

STATUS.md's Paper corrections section and REMARKS.md have no entry for Prop 13.1, so this should be added there.

## vote 10: correct

Quote: Thm 6.8 (p. 158, checked on the page image): "Assume that M is finitely generated as abelian group. Let X be a quasi-separated S-algebraic space locally of finite presentation endowed with an action of D(M)_S. Let Z ⊂ M be a subgroup and assume that one of the following assertions holds: (i) X is separated over S, (ii) M/Z is torsion-free. Then there exists a Z-FPR atlas U → X, which may be chosen quasi-compact (in particular S-affine here) if X → S is quasi-compact."
Thm A.2 (p. 196): "(ii) H has connected fibres. Then there exists a Z-FPR atlas U → X (cf. Definition 6.1), which may be chosen quasi-compact if X → S is."
Def 6.1(iv) (p. 156): "U = ∐_{τ∈A} U_τ is the disjoint union of D(M)_S-stable S-affine schemes; moreover in this case we say that the equivariant atlas f is S-affine if A may be chosen finite."
Proof of A.2 (p. 199): "Proceeding as in the beginning of the proof of Theorem A.1, we reduce to the case where S is affine and S, X are of finite type over Z."
Proof of A.1 (p. 198): "The assumptions and conclusion being local over S, we may assume that S is affine."
§6 standing hypothesis (p. 156): "Let S be a scheme."
p. 157: "Note that Theorem 6.8 is numbered as Theorem A.2 in the appendix."

Fix: Thm 6.8 and A.2: add "S separated" (S with affine diagonal is enough, since an affine scheme mapping to such an S is affine over S). Then the charts of the printed proof are S-affine and the atlas exists.
Replace the qc clause with "if X is quasi-compact, U may be chosen S-affine". This is the form proved in Lean (`thm68_qc_spaces`, [S.IsSeparated] plus X qc, on stubs). For S non-qc with X → S qc, the printed proof gives no finite family, so "X → S qc" should not be kept without a new argument.
The proof of A.2 should say that the reduction to S affine is valid only for the chart construction: being S-affine is not local on S.
Conjecture 6.9 ("Let S be an arbitrary scheme") needs the same restriction, because the counterexample has X separated over S.
6.8(ii) against A.2(ii): no mathematical correction is needed. Either state 6.8(ii) as "D(M/Z)_S has connected fibres" or keep it as the special case and drop "numbered as" on p. 157.

Reason: Attempted refutation, assuming the print is right. None of the attempts below succeeds.

Counterexample. Let k be a field, S the plane over k with doubled origin (two charts A²₁, A²₂ glued along A²∖0), X = A²₁ with j : X → S the chart, M = 0 (or any M with trivial action), Z = M.
- Hypotheses hold: S is a scheme, as §6 allows. X is quasi-separated and l.f.p. over S, j is a monomorphism so X is separated over S (case (i)), M/Z = 0 is torsion-free (case (ii)), and j is quasi-compact because j⁻¹(A²₂) = A²∖0.
- FPR is vacuous here, so the theorem reduces to this claim: X has an étale cover by S-affine schemes.
- Suppose U_τ → X is étale, U_τ → S is affine, and the image contains the origin. The preimage of A²₁ under U_τ → S is U_τ, so U_τ is affine. The preimage of A²₂ is U_τ minus the fibre over 0, which must also be affine.
- That fibre is a nonempty finite set of closed points of height 2 in a regular noetherian scheme. The complement of an affine open has pure codimension ≤ 1 (EGA IV 21.12.7), a contradiction.
- So no atlas exists at all under Def 6.1(iv), even with infinite A. The failure is in the existence claim, not only in the qc clause.
- The doubled line does not work: there j is affine, because A¹∖0 is affine. The plane is needed.

Defences tried:
1. S implicitly affine or separated: no. §6 says "Let S be a scheme", and Conj 6.9 says "arbitrary scheme".
2. X → S non-qc or not l.f.p.: no, see the hypotheses above.
3. "S-affine scheme" read as an absolute affine scheme over S. Then the doubled plane is harmless, because U = X = A²₁ is affine. This reading conflicts with the paper's use:
- "Remark 3.23 ... outside the S-affine case" and Prop 3.24 "X is affine over S" treat it as relative.
- Prop 8.5's proof takes "an S-affine N-FPR atlas" and writes U "as the spectrum of a graded O_S-algebra".
- Under this reading the qc clause also fails: for S an infinite disjoint union of Spec k and X = S, X → S is qc but X is not quasi-compact, so no finite union of affines covers it. So the print is false on either reading.
4. Reduction to S affine. The proof borrows it from A.1, where it is justified by "conclusion being local over S". In A.2 the conclusion is not local on S, since the charts must be affine over S. The printed charts are absolutely affine ("Spec(A)"), so they are S-affine exactly when U(x) → S is affine, which holds for S with affine diagonal. This is the precise location of the gap.

Second item, 6.8(ii) against A.2(ii). The two differ, but neither is wrong. M/Z torsion-free implies H is a torus, so its fibres are connected, and 6.8(ii) is a special case of A.2(ii). The converse fails: S = Spec F_p, M = Z/p, Z = 0 gives μ_p, which is connected. So the proof of 6.8 by citing A.2 is valid, and only "numbered as" is imprecise. The proposed correction is right only if this item is treated as a mismatch, not an error.

Lean evidence:
- `thm68_family_spaces` and `thm68_qc_spaces` (ChartFinalSpaces.lean:31, 44) carry [S.IsSeparated], and the second also requires X qc; both are on stubs.
- The STATUS.md row reads "S separated".
- `TorsionResidue` and `isZFPRAtlas_of_family_irreducible` (AppendixA.lean:174, ChartAtlas.lean:221) use the more general fibre form of (ii).
- There is no Lean counterexample for this item. Sec14Counterexample concerns Prop 14.4.
- STATUS.md's Paper corrections section has no entry for Thm 6.8 or A.2, so this correction is unrecorded there.

The counterexample and the Hartogs step are my hand proof, not machine-checked.

## vote 11: correct

Quote: Prop 3.32, Proof (ii), p. 149 (checked on the PDF page image): "The action ⋆ is free because firstly the action of D(N^gp × L^gp)_T on A(N × L)_T given by (λ, β) · (a, b) = (λ · a, β^{-1} · b) is free and secondly because the morphism of groups N^gp × L^gp → N^gp + L^gp given by (n, l) ↦ n + l is surjective [...]" and "So F induces a morphism f from the fpqc quotient [...] So we have an identification (A(N)_T ×_T A(L)_T)/D(N^gp + L^gp)_T = A(N ∩ L)_T."

Fix: Keep the structure of the proof: the identification of (X^N)^L(T) with equivariant maps F, the map f ↦ F = f∘m, and "degree zero part = Z[N∩L]", which is correct. Replace only the sentences from "The action ⋆ is free" to "= A(N∩L)_T". The replacement is: F is invariant under ⋆, and Spec A → Spec A_0, with A = O_T[N×L] graded by (n,l) ↦ n−l and A_0 = O_T[N∩L], is a good quotient but not a torsor. Then F factors through it uniquely, by this argument, with T affine (then glue):
(1) Reynolds: each prime q of A_0 has a closed orbit above it, given by a homogeneous ideal I maximal for I_0 ⊆ q.
(2) For an affine open V of X around the image of a point of the closed orbit, F^{-1}(V) contains m^{-1}(D(h)) for some h ∉ q. If N^gp+L^gp has torsion, do this first for the torsion-free quotient of the grading, then for the torsion part, using integrality of A' → A_0.
(3) O(V) → A_h lands in degree 0, so F descends over D(h); glue these.
(4) Uniqueness: A_0 → A is split.
This is the proof of Lean `prop332_scheme`, for X a scheme.
Statement: true as printed for X a scheme, with no separatedness and arbitrary N, L. For X a non-scheme space, the smallest honest wording of (ii) adds a hypothesis: X a scheme, or X separated with an (N∩L)^×-FPR atlas and either N, L f.g. or X limit preserving. That atlas exists for X separated, quasi-compact, l.f.p. and S separated, via Thm 6.8. The fully printed case, an arbitrary algebraic space, stays unproved; it is neither refuted nor established.

Reason: Real error of proof, not a misprint or a reading problem.
Why it is an error: with M = Z and N = L = ℕ, the action is G_m on A^2 by g⋆(a,b) = (g^{-1}a, gb), which fixes (0,0). The auxiliary G_m^2 action in the printed justification also fixes (0,0), so the first "is free" is false too. The cited SGA3 VIII Th. 5.1 gives a torsor only for free actions, which amounts to A_δ A_{-δ} = A_0; here x has degree 1, y has degree −1, and xy ≠ 1 generates only a proper ideal of A_0. The fpqc sheaf quotient is not A^1: (1,0) and (0,0) have the same image under ab but lie in different orbits. A^1 is only the affine good quotient, whose universal property covers affine targets, and X need not be affine. No other meaning of "free" rescues this: Remark 2.9 uses the word for monoid actions, but this sentence needs the SGA3 meaning. Printed (i) and the degree-zero computation are unaffected.
Is the statement true? Evidence, read-only with nothing recompiled:
- `prop332_scheme` (Sec3SchemeQuotient.lean:1669), for X a scheme, S arbitrary, M f.g., N and L arbitrary, no separatedness. .buildAll.log line 7408 records axioms [propext, Classical.choice, Quot.sound], and the module is tagged [J] joint-build.
- `prop332` and `prop332_weak` (Sec3Intersections.lean:463, Sec3IntersectionsWeak.lean:334), for separated spaces with an atlas, via Prop 5.1 on the face of units of N×L.
- `prop332_free` (FinalAtlasFree.lean:42), for X separated, qc, l.f.p. and S separated, is tagged [S]: it rests on stubs via Thm 6.8 and "waits for AHR". Thm 6.8 also comes later in the paper than Prop 3.32.
STATUS row: PARTIAL.
Gap: printed (ii) allows any S-space, since §3 fixes "an S-space X" and (ii) assumes no separatedness. Step (2) of the repair needs Zariski affine neighbourhoods, so it does not transfer to spaces. Pulling back an étale atlas gives neighbourhoods that are not saturated.
My own hand test, not in Lean: X = A^1/(w ~ −w, w ≠ 0), the non-locally-separated space, with weight-1 G_m action, N = L = ℕ, char ≠ 2. An equivariant F on A^2 lifts near the origin to w = ±ab with one sign, by irreducibility, so F = f∘m. This gives no counterexample, and it is one test rather than a proof.
The statement must use X being a space: for the fppf sheaf quotient of A^2 by the antidiagonal G_m, the quotient map admits no such f. That is outside the paper's scope.
STATUS.md "Paper corrections" also joins a colimit remark to this item. That remark belongs to Fact 3.34 (line 292, `chain_no_point`), not to Prop 3.32 (ii).

## vote 12: partly

Quote: Algebraic Magnetism p. 148 (read on the PDF page image), proof of Prop 3.31 (ii): "Let us consider the action of D(f(M))_T ×_T D(Y^gp)_T on D(M)_T ×_T A(Y)_T given by (g, h) · (g', x) = (g · g', h^{-1} · x), remark that this action is free. So we obtain by composition a free action ⋆ of D(K)_T on D(M)_T ×_T A(Y)_T." Later: "the fpqc quotient as in [9, VIII Th. 5.1]" and "This identifies (D(M)_T ×_T A(Y)_T)/D(K)_T with A(N)_T." Statement: "(ii) M and Z are finitely generated groups".

Fix: Keep the statement of (ii); only the proof changes. Replace "false unless Y^gp ⊂ f(M)" with this exact criterion: for T nonempty, the D(K)_T-action is free iff Y^gp ⊂ f(M) + Y^×. For Y sharp this reads Y^gp ⊂ f(M). Also record that the first printed sentence (freeness of the product action of D(f(M)) × D(Y^gp)) is false for every Y that is not a group, even for M = Z = ℤ, f = id, Y = ℕ.

Proof repair:
- Case Y^gp ⊂ f(M) + Y^×: drop the product claim and argue directly that D(K) acts freely. The printed proof then works, with Spec A → Spec A_0 a D(K)-torsor, and it covers algebraic spaces.
- General case: replace the quotient by the descent along the grading (m, y) ↦ f(m) − y, as in `AlgMag.SQ.exists_desc`. This is proved only for X a scheme (`prop331_ii`, Sec3Final.lean:1008).
- For X a non-scheme algebraic space in the non-free case, (ii) has no proof in print or in Lean.

Reason: The core claim is right: the printed freeness is false, the counterexample is valid, and every use in the paper survives. "False unless Y^gp ⊂ f(M)" is too strong, and the correction misses a second false sentence. I worked alone (no subagent tool here), by hand, with no compile.

**Counterexample M=0, Z=ℤ, Y=ℕ, line by line**
- The §3 standing hypotheses are: S a scheme, X an S-space, M a commutative monoid with an A(M)_S-action, a magnet being any submonoid. All hold, with A(0)_S = S acting trivially on X; for example X = S = Spec k.
- M and Z are finitely generated groups, so printed condition (ii) holds. f=0, and N = f^{-1}(ℕ) = 0.
- K = 0 + ℤ = ℤ, and D(M)_T ×_T A(Y)_T = A^1_T.
- D(K)_T = G_m acts by h^{-1}·x. It fixes the zero section, so the stabilizer there is all of G_m and the action is not free.
- SGA3 VIII 5.1 is cited for a free action, so it does not apply (I did not reopen SGA3). The degree-zero part is still O_T, as printed. But A^1_T → T is not a torsor, and the sheaf quotient has two k-points (two orbits) while T has one. So the printed "identifies" fails for the sheaf quotient.
- The statement itself holds here. By hand, for X a scheme: a stable affine neighbourhood of the vertex's image reduces it to (i). Also, Lean `prop331_ii`.

**Exact criterion (proved by hand)**
- A k fixing (g, x) is trivial on f(M), and trivial on Y^× because x(y) is a unit there. So if K = f(M) + Y^×, then k = 1.
- Conversely, take x_0 equal to 1 on Y^× and 0 elsewhere; it is a monoid map because Y minus Y^× is an ideal. Then D(K/(f(M)+Y^×)), which is nontrivial when the quotient is nonzero, fixes (1, x_0).
- Counterexample to "unless": M=0, Z=ℤ, Y=ℤ gives G_m acting on G_m, which is free although Y^gp ⊄ f(M). The Sec3Final.lean:19 and :1005 docstrings make the same overstatement.
- When the criterion holds, every degree contains a unit X^{(m,y)} with y ∈ Y^×, so A is strongly graded and Spec A → Spec A_0 is a torsor.

**Non-flat quotient map is real, but not in the M=0 example (there A^1_T → T is flat)**
- Take M=ℤ², Z=ℤ³, f(a,b)=(a,a+b,b), Y=ℕ³, N=ℕ², R a field.
- A=R[u1^±,u2^±,s1,s2,s3], and A_0=R[v1,v2] with v1=u1 s1 s2, v2=u2 s2 s3.
- v1, v2 is regular in A_0. In A, v2·(u1 s1)=v1·(u2 s3) with u1 s1 ∉ (v1), and A/(v1,v2) ≠ 0. So v2 is a zero divisor mod v1, and A is not flat over A_0.
- So in general no fpqc argument can replace the free one. `SQ.exists_desc` avoids this and needs a scheme.

**Uses in the paper: all survive** (the grep for "3.31" lists every citation)
- Prop 5.1 (§5 standing: M a f.g. abelian group, X a space): f is M→M/N^×, surjective, so free.
- Prop 12.1 and Thm 12.4: same surjective f, free.
- §16.4 (i): ⟨α⟩→M with Y=[α⟩, so Y^gp = f(M'), free.
- §16.4 (ii): projections of ℤ×ℤ, free.
- Prop 16.10 (i) and (ii), with λ possibly non-primitive in (ii): G is affine, so case (i) of 3.31 applies and (ii) is not needed.
- Prop 3.32 (iii): uses case (iii) of 3.31.
- Rem 3.13 ("e.g. use directly 3.31", f: N→M with Y=L) can be non-free, but it is only a sanity remark "under some working assumptions".

**Prop 6.4**
- It is not in this paper: AM's 6.4 is a remark. It is Prop 6.4 of arXiv:2509.04274v3, which I read only through Lean docstrings, not the print (no local copy found).
- It is the one true non-free use: Y=ℕ, f=d·g with d≥2 or f=0.
- It survives. Its statement only asks for some λ, and f^{-1}(ℕ)=g^{-1}(ℕ). With g(m0)=1, the bijection is proved with no descent (`ptAlong_bijective_of_primitive`). With g=0 it uses separatedness (`ptAlong_bijective_space`), and `prop64_space` assembles this for separated spaces.
- The given f with d≥2 is covered only for schemes (`prop64` via `prop331_ii`).

Lean files: C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Sec3Final.lean, C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\DoubleScalarSpaces.lean, C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\DoubleScalar.lean. Rendered page: C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\verify331\p-23.png

## vote 13: partly

Quote: Semigroup Forum 113, p. 148, Prop 3.31(ii) proof (read on the page image): "Let us consider the action of D(f(M))_T ×_T D(Y^gp)_T on D(M)_T ×_T A(Y)_T given by (g, h) · (g', x) = (g · g', h^{-1} · x), remark that this action is free. So we obtain by composition a free action ⋆ of D(K)_T on D(M)_T ×_T A(Y)_T." Then: "the fpqc quotient as in [9, VIII Th. 5.1]", and "By [9, VIII Th. 5.1], (D(M)_T ×_T A(Y)_T)/D(K)_T is affine with quasi-coherent algebra the degree zero part A_0 in A." Then: "This identifies (D(M)_T ×_T A(Y)_T)/D(K)_T with A(N)_T." Here K = f(M) + Y^gp.

Fix: Proposed wording. Replace "remark that this action is free ... free action" with: "The action of D(K)_T is free if and only if Y^gp ⊂ f(M) + Y^× (T nonempty). This holds in particular if f is surjective or Y^gp ⊂ f(M)." Then A has a unit in every K-degree, namely X^(m,u) with u in Y^×. So A_0 → A is faithfully flat, the map is a D(K)-torsor, [9, VIII Th. 5.1] applies, and the printed proof goes through unchanged.

Do not leave the general case on the printed proof. Either restrict (ii) to that hypothesis, which covers every use inside the paper, or replace the quotient step by the descent in Lean (AlgMag.SQ.exists_desc, along the grading (m,y) ↦ f(m) - y, whose degree zero part is R[N]). That descent is proved for X a scheme only.

The criterion in the proposed correction needs one change: "false unless Y^gp ⊂ f(M)" should read "false unless Y^gp ⊂ f(M) + Y^×". The same wording appears in the docstring of prop331_ii, AlgMag/Sec3Final.lean:19 and :1008.

Also, STATUS.md "Paper corrections" has no entry for 3.31(ii). The correction is recorded only in the Lean docstrings, so it should be added there.

Reason: The print cannot be defended, but the proposed correction overstates the condition, and all uses in the paper survive.

WHAT HOLDS IN THE CORRECTION
- Refuting attempt: M=0, Z=ℤ, Y=ℕ is admissible, since M and Z are f.g. groups and N=0. Then K=ℤ, D(M)=pt, and G_m acts on A^1 by h^{-1}, fixing 0. The action is not free.
- The sheaf quotient A^1/G_m is not pt, so "is affine with algebra A_0" fails as a statement about the fpqc quotient. A_0 = O_T[f^{-1}(Y)] is still correct, as an algebra.
- Non-flat quotient map, which I checked by hand: M=ℤ², Z=ℤ³, f(a,b)=(a,b,a+b), Y=ℕ³, N≅ℕ². The map G_m²×A³ → A² is (u,v,x,y,z) ↦ (uxz, vyz). The generic fibre has dimension 3 and the fibre over 0 has dimension 4, so it is not flat, hence not an fpqc quotient.
- The gap is not formal. The printed step uses only the sheaf property of X, and for a sheaf the conclusion is false. Take X = the fppf sheaf quotient A^1/G_m with trivial action and M=0, Y=ℕ. The quotient map A^1 → X is invariant and not constant. So any repair must use that X is an algebraic space, which §3 does assume ("an S-space is an algebraic space over S").

WHAT NEEDS CHANGING IN THE CORRECTION
- The product action of D(f(M))×D(Y^gp) is free only when Y is a group. This is a stronger failure: it is already false for M=Z=ℤ, f=id, Y=ℕ, where (1,h) fixes (g',0). So the first printed sentence is wrong even in the surjective case.
- For the D(K)-action, the stabilizer of (g',x) with support face F is D(K/(f(M)+F^gp)), and it is largest for F=Y^×. So the action is free iff Y^gp ⊂ f(M)+Y^×.
- This shows "false unless Y^gp ⊂ f(M)" is too strong: M=0, Z=Y=ℤ has Y^gp not in f(M)=0, yet G_m acts freely on G_m.

THE STATEMENT ITSELF
- It is proved in Lean for X any scheme: prop331_ii, Sec3Final.lean:1008, M countable, Z f.g., by a descent that does not use freeness.
- For algebraic spaces with Y^gp not in f(M)+Y^×, I have neither a proof nor a counterexample.
- The separate step "ker(ξ,ξ⋆) ... because the schematic image of p" is harmless without separatedness, since p is faithfully flat and X is a sheaf.

USES IN THE PAPER (all by hand, on the print)
- Prop 5.1 (p. 155) and Prop 12.1: f=M→M/N^× is surjective, so the action is free and the printed proof holds for algebraic spaces. M is f.g. in both §5 and §12.
- Thm 12.4: X is affine, so case (i) applies. It also has f surjective.
- §16.4(i): the map is <α>→M with Y=[α>, not surjective but Y^gp=f(<α>), so the action is free. Separate slip: "≃ (N ⊂ Z)" needs α non-torsion.
- §16.4(ii),(iii): projections, so surjective and free.
- Prop 16.10: f: X^*(T)→ℤ can be non-surjective for non-primitive λ, but G is affine, so case (i) applies with no freeness.
- Prop 3.32(iii) uses case (iii), and Prop 8.4 is a remark citing (iii). Neither uses (ii).

"PROP 6.4"
- It is not in Algebraic Magnetism. The print has no such proposition; §6 has Rem 6.4 (no content, per STATUS.md). According to AlgMag/DoubleScalar.lean, it is Prop 6.4 of arXiv:2509.04274v3. I read that only through the Lean docstring, not its print.
- This is the one use that really is non-free: f: M→ℤ is arbitrary, so the image can be dℤ or 0, with Y=ℕ.
- In Lean it is proved only for X a scheme (prop64, via prop331_ii), while the docstring says the paper allows a separated algebraic space.
- It still survives for separated algebraic spaces, by my own hand argument, not formalized. Write f=d·g with g surjective, d>0.
  - g is covered by the free case.
  - For d: t↦t^d is fppf, and R[s,t]/(s^d-t^d) is free over R[s] and over R[t], so st is a nonzerodivisor and the G_m×G_m part is schematically dense. Separatedness gives invariance, so φ descends along t↦t^d. Equivariance follows along the fppf cover (λ,t)↦(λ^d,t^d).
  - For f=0: an invariant A^1_T→X agrees with the constant map on the schematically dense G_m,T, hence everywhere.

LEAN STATUS OF THE SPACE CASE
Lean does not cover Prop 5.1's printed reduction or §16.4 for spaces: PrintedProp51 and PrintedSec164 are for schemes, and REMARKS.md marks §16.4(i) "to redo". Their survival for spaces is a paper argument. prop331_iii (Sec3Remaining.lean:1345) covers Y ⊂ f(M) only for f injective, with X a separated sheaf.

## vote 14: correct

Quote: Standing, p. 181: "Let S be a scheme and let S' be a closed locally principal subscheme of S." Prop 13.1: "Assume moreover that X → S, (Bl_Y^D X)^N → S and Bl_{Y^N}^{D^N} X^N → S are flat." Proof, p. 181: "Remark first that since D(M)_S → S, X → S, Bl_Y^D X → S are flat, D(M)_S, X and Bl_Y^D X belong to Spaces_S^{S'-reg}". Proof, p. 182: "Since Bl_Y^D X → S is flat, by [22, §3.6], we have (Bl_Y^D X)_T = Bl_{Y_T}^{D_T} X_T." and "Now since Bl_{Y^N}^{D^N} X^N and (Bl_Y^D X)^N are flat over S, they belong to Spaces_S^{S'-reg}."

Fix: Both proof objections stand, and the statement survives, with fewer hypotheses. Only (Bl_Y^D X)^N → S flat is needed, with the attractors representable as printed. Flatness of X and of Bl_{Y^N}^{D^N} X^N can be dropped.

Repaired proof:
(a) Action. Bl is S'-regular by construction, and D(M)_S × Bl → Bl is flat, so D(M)_S × Bl is S'-regular. Then D(M)_S × Bl → D(M)_S × X → X restricted to S' factors through Y, so it lifts to Bl. The action axioms follow because Bl → X is mono on S'-regular objects. No flatness over S is used.
(b) T-points. Let T be S'-regular. A(N)_T → T is flat, so A(N)_T is S'-regular, and the universal property applied directly gives Hom_S(A(N)_T, Bl) = {f : A(N)_T → X with f|_{S'} factoring through Y}. This replaces the base change [22, §3.6], and with it the use of Bl → S flat. Bl^N and Bl_{Y^N} X^N then have the same T-points.
(c) Regularity of (Bl)^N. Bl_{Y^N} X^N is regular by construction. Regularity of (Bl)^N comes from this lemma: if Z is flat over S and maps to an S'-regular object B, then Z is S'-regular. Locally S' = V(a) and S = Spec R. If r in ann_R(a), then r vanishes on B, hence on Z. Flatness gives ann_{O(Z)}(a) = ann_R(a)·O(Z) = 0.
Yoneda on S'-regular objects concludes.

Suggested erratum wording: "flat over S and mapping to Bl_Y^D X, hence S'-regular" in place of "flat, hence S'-regular", and delete the use of Bl_Y^D X → S flat. If S' is effective Cartier, the printed flat ⇒ regular step is true, but the Bl → S flat gap remains. Cor 13.3 is not affected: S' is Cartier there and Bl → S is smooth.

Reason: Checked against the page image of p. 181 and the text of p. 182. I did not rebuild the Lean. [22] was not in the sources: I took its definition of S'-regular (T ×_S S' → T effective Cartier) from memory, and it agrees with the IsRegular docstring in Sec13General.lean.

Counterexample to the step. It meets every printed hypothesis:
- k a field, S = X = Spec k[ε], S' = V(ε). S' is closed and locally principal, which is all §13 assumes. M = Z with trivial action, any submonoid N, Y = D = S' (stable), or Y empty.
- X → S is the identity, so flat. D(M)_S → S is flat.
- A regular T has ε a nonzerodivisor with ε² = 0, so ε = 0 on T and then O_T = 0. Hence Bl_Y^D X is empty (also A[I/ε] ⊂ A_ε = 0).
- X^N = S since X is final over S, D^N = S', Y^N = Y, so Bl_{Y^N}^{D^N} X^N is empty. (Bl)^N is empty.
- The empty maps to S are flat, so all three printed flatness hypotheses hold.
- But X = Spec k[ε] is not S'-regular, because ε is a zero divisor. The same holds for D(M)_S. So the printed "flat ⇒ in Spaces_S^{S'-reg}" is false for X and D(M)_S.
- The conclusion still holds here as empty ≅ empty, so this refutes the step only, not the statement. The correction should not be read as saying 13.1 is false.

Bl → S flat is really unassumed. The hypothesis lists (Bl_Y^D X)^N, not Bl_Y^D X, yet the proof uses Bl → S flat at p. 181 and p. 182. The hypotheses do not imply it, even with S' Cartier:
- S = Spec k[s,t], S' = V(t), X = G_{m,S} with M = Z acting by weight 1 (A = k[s,t][x, x⁻¹], deg x = 1), Y = V(s) in D, N = {0}.
- X → S is flat. X^0, D^0, Y^0 and (Bl)^0 are empty because x is a unit of nonzero degree, so all the hypotheses hold.
- Bl = Spec k[u,t][x, x⁻¹] with s = ut, which is not flat over k[s,t]: the prime (t) contracts to (s,t), so going-down fails.
- The conclusion again holds trivially.

Lean evidence agrees with the repair. Sec13General.lean:1439 `isRegular_of_flat_of_hom` has the docstring "Flatness over S alone does not suffice when S' is not Cartier in S". :1460 `isRegular_attractor` applies it. :1469 `prop13_1` assumes only `Flat ZB.hom` and states "Flatness of X and of Bl_{Y^N}^{D^N} X^N is not needed". :1478 `prop13_1_printed` gives the printed form. Sec13Spaces.lean:1571 `prop13_1_spaces` is the space version, with a flat étale atlas of (Bl)^N. Sec13Dilatations.lean:595 `dilQuotHom_bijective_iff` is the sharp affine form: the map is bijective iff a is regular on the source. All of these keep representability of the attractors as hypotheses, and the print presupposes it too. This correction is not yet listed in the STATUS.md Paper corrections section.

## vote 15: correct

Quote: Semigroup Forum, p. 150, proof of Fact 3.34: "Furthermore, in the category of rings, Z[∩_{l∈I} N_l] = lim_{J⊂I} Z[∩_{l∈J} N_l]. So A(∩_{l∈I} N_l)_S = colim_{J⊂I} A(∩_{l∈J} N_l)_S." Then: "= Hom_T^{A(M)_S}(colim_{J⊂I} A(∩_{l∈J} N_l)_T, X_T)" and "[32, Tag 002H] and equivariance is clear ⊃ lim_{J⊂I} Hom_T^{A(M)_S}(A(∩_{l∈J} N_l)_T, X_T)". (Read from the page image, PDF p. 25.)

Fix: Smallest fix: delete the sentence "So A(∩N_l)_S = colim ..." and the colimit line of the display. Keep the proof as printed for finite I, where the family has a smallest member and only Prop 3.32 is needed.

For infinite I, the display needs the inclusion lim_J X^{∩_J N_l}(T) ⊂ X^{∩_I N_l}(T), and this must be proved another way. The proved route is to add "X locally of finite presentation" for infinite I in (ii). Over affine T, finitely many degrees E generate the atlas, so one finite J has (∩_J N_l) ∩ E ⊂ N for all N in the family, and the family stabilizes (Lean: `fact334_strong`, comment at Sec15Final.lean:136-138). `fact334_free` removes the atlas hypothesis, but it also assumes X quasi-compact and S separated and rests on the stubs of notes/chart-stubs.md. Case (i) is unaffected. Case (iii) needs the same repair; I did not check a Lean form of it beyond the names listed in Sec3Final.lean. Thm 15.3 inherits this condition because it uses the Fact for infinite families.

Possible alternative to adding lfp, by hand and not checked in Lean: in the N_k test case, the extension can be proved for T = Spec of a field, X a separated scheme, with no lfp.
1. All f_k send the vertex to one point x0. This gives local maps O_{X,x0} -> O_{A(N_k),v} inside k(x,y).
2. Their intersection is O_{A²,0}. If h = p/q is reduced and q(0,0)=0, take an irreducible factor π of q. If π is not y, the closure of V(π) ∩ D(y) passes through the vertex for large k, because ord(x^k/y) = kα-β > 0 on a branch. If π = y, then v_k(y)=k tends to infinity while v_k(p) stays bounded, which gives a pole along the w-line. A(N_k) is normal, so either way h is not regular at the vertex.
3. So there is a map Spec O_{A²,0} -> X. The action map G × Spec O_{A²,0} -> A² is fpqc and it hits the missed orbit, through the generic point of y=0.
4. The two pullbacks agree on the preimage of D(y), which is schematically dense because y is a nonzerodivisor on a flat scheme over A². X separated then gives agreement everywhere, and fpqc descent gives an equivariant A² -> X.

This contradicts the wall in notes/fact334-attempt.md items 3 and 6, for this family at field points only. Arbitrary T (non-Noetherian R, where denominators depend on k), general families and non-scheme X are not done. Recommendation: use the lfp fix now, and try this descent route on general T before calling the non-lfp case a side question.

Reason: This is a real error in the proof, not a misprint or a reading problem. The Fact's statement is not refuted.

The ring identity is true, but Spec sends a limit of rings to a colimit only among affine schemes. Tag 002H (Remark 4.14.4, checked live) is only the universal property of a colimit that already exists, so it cannot supply the existence or the identification. Reading "colim" as a colimit in affine schemes does not help, because the display then needs a non-affine target X_T.

Witness checked:
- `chainN k` = {y ≥ 0, kx+y ≥ 0} is decreasing with intersection N² (`iInf_chainN`). It uses M = Z², so it falls under cases (ii) and (iii).
- `chain_no_point` proves that no character of N_k has x=0, y=1, using e₁ + (-1,k) = k•e₂. This is the same family as N_k = {a≥0, b≥-a/k} with coordinates swapped.
- Lean proves only this point statement. The conclusion about colimits is in the docstring, and I checked it by hand. U = A² \ {(0,1)} receives compatible maps from all A(N_k). If A² were the colimit, there would be a map A² -> U whose composite with U ⊂ A² equals the identity on D(y) (Lean's y≠0), hence everywhere because A² is separated and reduced. That is impossible since A² is not contained in U. So the printed colimit is false in schemes over any nonempty base. STATUS.md line 292 is accurate.

Limit of the witness: U is not torus-stable, because the missed orbit {x=0, y≠0} is not closed and any stable open containing the vertex is all of A². So `chain_no_point` refutes the printed justification, but not the inclusion actually needed, which concerns equivariant maps to a separated X. The status of the Fact for infinite I without lfp remains unproved. Lean evidence: finite families for schemes (`fact334_finite_scheme`) and arbitrary families with an atlas (`fact334_strong`). The hand argument in the fix field supports the Fact in the test case; it has not been machine-checked.

Sources: page image C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\p-334.png; C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Sec3Remaining.lean lines 1430-1482; C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Sec15Final.lean; C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\FinalCorAtlas.lean; C:\Users\Arnaud\Desktop\algmag-stacks\notes\fact334-attempt.md. No project files were edited and nothing was compiled; the only files written are a render script and that page image in the scratchpad.

## vote 16: partly

Quote: Prop 3.31(ii), p. 148, read from the page image: "Let us consider the action of D(f(M))_T ×_T D(Y^gp)_T on D(M)_T ×_T A(Y)_T given by (g, h) · (g′, x) = (g · g′, h^{-1} · x), remark that this action is free. So we obtain by composition a free action ⋆ of D(K)_T on D(M)_T ×_T A(Y)_T." Later on the same page: "is the fpqc quotient as in [9, VIII Th. 5.1]". The statement's hypothesis is "(ii) M and Z are finitely generated groups,", with X an S-space, i.e. an algebraic space (opening of §3).

Fix: Smallest fix: in (ii), add "and Y^gp ⊂ f(M) + Y^×". This is exactly the free case.

Replace the two quoted sentences with: "Let K = f(M) + Y^gp. Every degree k in K is f(m) - u with u in Y^×, so the monomial X^(m,u) is a homogeneous unit of degree k in A. So A is strongly K-graded and the action of D(K)_T is free." The rest of the printed proof then stands, and D(M)_T ×_T A(Y)_T → A(N)_T is a D(K)_T-torsor.

Optional addition: "If X is a scheme, the hypothesis Y^gp ⊂ f(M) + Y^× is not needed." The proof is the descent along A_0 → A, which is `prop331_ii` in Sec3Final.lean. It needs Z finitely generated; M only has to be countable.

Uses in the paper:
- Prop 5.1, Prop 12.1 and the §15-16 reduction with Z = M/N^×: f is surjective, so all are covered.
- §16.4(i), f : (α) → M with Y = [α⟩ ⊂ f((α)): covered.
- §16.4(ii), the two projections from Z × Z: covered.
- Prop 16.10(i)(ii): G is affine, so case (i) of 3.31 applies, even when λ is non-primitive.
- Prop 3.32(iii) and Rem 8.4 use 3.31(iii), not (ii).

No use in this paper leaves the free case except through case (i).

"Prop 6.4" does not exist in this paper; there is only Remark 6.4, which is unrelated. It belongs to arXiv:2509.04274v3 (see DoubleScalar*.lean), and I did not read that paper's text. Its printed f = d·g with d ≥ 2 and its f = 0 case are non-free. The Lean docstring repairs this by taking λ dual to the primitive g, and handles g = 0 by separatedness (`prop64_space`). For X a scheme, `prop331_ii` gives any f.

Also correct the Lean docstring at Sec3Final.lean:1004-1007, whose "not free unless Y^gp ⊆ f(M)" is too strong. I recommend adding the hypothesis rather than claiming the full statement for spaces.

Reason: This is a real error in the proof, not a misprint or a reading problem. The proposed correction is right on the core point but overstates the condition, and one of its references is misplaced.

**Why the print is wrong.** The product action fixes (g′, x) under every (1, h) with h in Stab(x). So it is not free unless Y is a group, even in the cases the paper uses. M = 0, Z = ℤ, Y = ℕ is a valid counterexample for D(K): G_m acts on A^1 and fixes 0.

**Exact criterion.** Freeness of D(K) means A_k A_{-k} = A_0. Taking the monomial 1 forces y to be a unit, so the action is free if and only if Y^gp ⊂ f(M) + Y^×. "Unless Y^gp ⊂ f(M)" is therefore too strong: M = 0, Z = Y = ℤ acts freely on D(ℤ) although Y^gp is not in f(M).

**Non-flatness is real.** I worked this example by hand. Take M = ℤ, Z = ℤ², f(m) = (m, 0), and Y generated by (2,0), (3,0), (2,1), (3,1). Then N = {0, 2, 3, ...}, and the degree (0, -1) part of A is the maximal ideal (t², t³) of R[N]. That ideal is not flat, and it is a direct summand of A, so A is not flat over A_0.

Even when the map is flat, as for f = d with d ≥ 2 and Y = ℕ, it is not a torsor. So the descent argument fails there too.

**What survives.** Lean states the conclusion for schemes through a Reynolds and saturated-neighbourhood descent (Sec3SchemeQuotient.lean); I read the statement and docstrings but did not rerun Lean. For algebraic spaces outside the free case, neither the print nor the repo has a proof: STATUS records "(ii) X a scheme, spaces not done". I did not find a counterexample among algebraic spaces. The sheafified quotient A^1/G_m with trivial action shows the non-free case fails for general fppf sheaves, so geometry is needed. The free-case proof works for any fppf sheaf.

Files read: am.txt and the rendered PDF pages for pp. 148, 190 and 192 (C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am331\p-23.png, p-65.png, p-67.png).

## vote 17: correct

Quote: Statement (p. 181, checked on the page image): "Proposition 13.1 Assume moreover that X → S, (Bl_Y^D X)^N → S and Bl_{Y^N}^{D^N} X^N → S are flat. Then D(M)_S acts naturally on Bl_Y^D X, moreover we get a canonical isomorphism Θ : (Bl_Y^D X)^N ≅ Bl_{Y^N}^{D^N} X^N." Setup: "let S' be a closed locally principal subscheme of S". Proof: "Remark first that since D(M)_S → S, X → S, Bl_Y^D X → S are flat, D(M)_S, X and Bl_Y^D X belong to Spaces_S^{S'-reg}". Page 182, from the text extraction with its subscripts restored (the p. 182 image was rendered but not viewed): "Since Bl_Y^D X → S is flat, by [22, §3.6], we have (Bl_Y^D X)_T = Bl_{Y_T}^{D_T} X_T." Also: "Now since Bl_{Y^N}^{D^N} X^N and (Bl_Y^D X)^N are flat over S, they belong to Spaces_S^{S'-reg}."

Fix: Keep the statement of Prop 13.1 exactly as printed; only the proof changes. Do not add "S' Cartier" or "Bl → S flat".

Replacement for the proof:
(1) Only use "T flat over an S'-regular object is S'-regular". Bl_Y^D X and Bl_{Y^N}^{D^N} X^N are S'-regular by construction. So are D(M)_S × Bl_Y^D X and D(M)_S × D(M)_S × Bl_Y^D X, which are flat over Bl_Y^D X. The action map D(M)_S × Bl_Y^D X → X therefore lifts to Bl_Y^D X by the universal property, and the action axioms hold because Bl_Y^D X → X is mono on regular objects.
(2) (Bl_Y^D X)^N is S'-regular by this lemma: if Z → S is flat and Z → B is an S-map with B S'-regular, then Z is S'-regular. Locally, with r a generator, flatness gives Ann_C(r) = Ann_A(r)·C. Ann_A(r) dies in B because r is a nonzerodivisor on B, so it dies in C. Apply it with B = Bl_Y^D X and Z → B the evaluation map at the unit section, (Bl_Y^D X)^N → Bl_Y^D X.
(3) For T S'-regular, A(N)_T is S'-regular, since it is flat over T. Apply the universal property of Bl_Y^D X directly to A(N)_T, in place of the [22, §3.6] base change: (Bl_Y^D X)^N(T) = {equivariant f : A(N)_T → X with f|_{S'} factoring through Y}. The rest of the printed Yoneda argument then goes through.

This also shows that flatness of X and of Bl_{Y^N}^{D^N} X^N is not used; only flatness of (Bl_Y^D X)^N is. That can go in a remark. Separate misprint on p. 181: "Bl_Z^D" should be "Bl_Y^D", and likewise "Bl_Z^D X(T)".

Reason: This is a real error in the proof, with two independent defects. It is not a misprint or a reading problem. The statement survives unchanged.

Defect 1: flat over S does not imply S'-regular.
- S'-regular is taken here to mean that T|_{S'} is an effective Cartier divisor in T. That is the definition in [25] as I recall it, and it matches Lean `IsRegular`; I did not open [22].
- Take S = X = Spec k[ε] and S' = V(ε), which is closed and locally principal as the setup allows. X → S is flat, and D(M)_S → S is flat, but ε is a zero divisor on both. So "D(M)_S, X ... belong to Spaces_S^{S'-reg}" is false.
- The same step is used for (Bl_Y^D X)^N in the last paragraph. There the conclusion is true but the reason given is not; step (2) of the fix supplies the right reason.
- In this example Bl_Y^D X is empty and the proposition holds trivially.

Defect 2: Bl_Y^D X → S flat is used twice but never assumed, and the hypotheses do not imply it, even with S' Cartier.
- Take S = Spec k[s,t], S' = V(t), X = Spec k[s,t,x], M = Z with x in degree 1, N = 0, and Y = V(t, sx), which is stable.
- Then Bl_Y^D X = Spec k[s,t,x,u]/(tu - sx). This is not flat over S, because the fibre dimension jumps at s = t = 0.
- But X^0 = S, (Bl_Y^D X)^0 = V(x,u) = S, and Y^0 = D^0, so Bl_{Y^0}^{D^0} X^0 = S. All three printed hypotheses hold.
- So a Cartier assumption alone would not repair the proof. This example is by hand, not in Lean.

Why the statement survives:
- The action only needs the regularity of Bl_Y^D X and of its products with D(M)_S, which are flat over it.
- The [22, §3.6] base change can be bypassed, because A(N)_T is itself S'-regular.
- (Bl_Y^D X)^N is regular because it is flat over S and maps to the regular Bl_Y^D X. The annihilator argument in step (2) checks this by hand.

Lean agrees, read only and not compiled.
- `isRegular_of_flat_of_hom` and `isRegular_attractor` are in Sec13General.lean:1439 and 1460. `prop13_1` (line 1469) assumes only `Flat ZB.hom`, and its docstring says "Flatness of X and of Bl_{Y^N}^{D^N} X^N is not needed". `prop13_1_printed` is at line 1478.
- The spaces version is `prop13_1_spaces` at Sec13Spaces.lean:1571.
- There are no sorries in Sec13General.lean.
- STATUS.md says "no checker pass on record" for this row. Prop 13.1 is not yet listed under Paper corrections, and REMARKS.md has no §13 entry.

Cor 13.3 is unaffected, because its S' is an effective Cartier divisor and its hypotheses give all the smoothness it needs.

## vote 18: partly

Quote: Statement (p. 179): "Theorem 12.4 Assume that X is smooth over S and that the action a of D(M)_S on X is Zariski locally linearizable (cf. Sect. 7). Assume that N is finitely generated as monoid or that X is quasi-compact over S. Then the morphism X^N → X^{N^*} is an affine space fibration." Proof (p. 180, checked on the page image): "So there exists a quasi-coherent O_S-algebra A = ⊕_{n∈N} A_n graded by the fine and sharp monoid N such that X^N = Spec_S(A). [...] So by [32, Tag 063M] the conormal sheaf I/I² is finite locally free hence projective. [...] The A_0-module (I/I²)_n is projective because it is a direct summand of I/I², and so the surjection A_n → (I/I²)_n admits a section s_n : (I/I²)_n → A_n. Let s : I/I² → A be the direct sum ⊕_{n∈N} s_n, note that s(I/I²)⊕I² = I. Now s induces a morphism of A_0-algebras Φ : Sym_{A_0}(I/I²) → A. It is enough to show that this morphism is an isomorphism. We note that Sym_{A_0}(I/I²) is the sheafification of the presheaf U ↦ Sym_{A_0(U)}(I(U)/I²(U)), cf. e.g. [32, Tag 01CG]. So, using [32, Tag 007V], we reduce to the case where A is a ring."

Fix: Keep the statement of Thm 12.4 unchanged. Repair the proof with one change to its first sentence: "we reduce to the case where X is affine over S and S is affine". This reduction is allowed because the conclusion is Zariski-local on the target and attractors commute with open base change on S. Then A is a ring from the start, I/I² is a finite projective A_0-module, the s_n exist, and the rest of the proof runs verbatim. The proof then gives: over each stable S-affine chart U and each affine open V of S, (U_V)^N = Spec_{U_V^{N^*}} Sym(P) with P finite projective. Do not write "Zariski-locally on S". Trivialising P needs a further localisation on X^{N^*}, and P need not be free even when S is a point. The correct reading of "affine space fibration" is: every point of X^{N^*} has an open neighbourhood V with X^N|_V ≅ A^n_V, which is exactly thm124_affineSpace (AlgMag/Sec12Final.lean:787). The global claim Φ : Sym_{A_0}(I/I²) ≅ A over non-affine S is false and is never part of the statement. Tighten the STATUS.md:188 and :287 wording from "Zariski-local on S" to "Zariski-local on X^{N^*}, after reducing to S affine". No later use needs anything global.

Reason: REFUTATION ATTEMPT 1, could the proof be read so that S is already affine? No. S is general, and A is explicitly "a quasi-coherent O_S-algebra". The passage to "A is a ring" comes only after s and Φ are built, and it uses sheafification, so the print really does treat Φ as a global map of sheaves. "Finite locally free hence projective" is false for sheaves on a non-affine scheme: QCoh(P¹) has no nonzero projectives.

ATTEMPT 2, does the example meet the hypotheses? I checked by hand that it does.
- Setup: S = P¹_k, M = Z, N = ℕ, and A locally O[x,y] with deg x = 1, deg y = 2, x' = x, y' = g y + c x², where g is the transition function of O(2) and c represents a nonzero class in H¹(O(-2)) = k.
- Hypotheses: X = Spec_S A is smooth over S (locally A²_S). It is S-affine and stable, so it is Zariski locally linearizable by Def 7.2. Also X^N = X and X^0 = S.
- Failure: 0 → A_1^{⊗2} = O → A_2 → (I/I²)_2 = O(2) → 0 is non-split (A_2 ≅ O(1)²), so s_2 does not exist. Any graded Φ would force A_2 ≅ O ⊕ O(2), so the claim Φ iso itself fails, not only its construction.
So the proof defect is real.

ATTEMPT 3, does the statement fail? No. This is where the proposed wording overreaches. The term "affine space fibration" is never defined in the paper (it appears only at intro (xii) and in Thm 12.4). Cor 12.5 uses the different term "vector bundle", and the theorem generalises Bialynicki-Birula, where the term means locally trivial. The example X → P¹ is a Zariski-locally trivial A²-bundle, so the statement holds for it. The print's own first step, "we reduce to the case where X is affine over S", is already a Zariski-local reduction that makes sense only for a local conclusion. The same phenomenon occurs with S = Spec k and X the same total space over P¹, where the print's first reduction already handles it. So the print is wrong in its proof, not its statement.

"Zariski-locally on S" is also not the right locality. It is too coarse for a trivial A^n, since P may be non-free over affine S. For non-S-affine X the charts live on X^{N^*}. Lean's thm124_affineSpace is local on X^{N^*}, and thm124_general gives Sym of a finite projective module on Spec B_0 ⊂ X^{N^*}. I read these statements in the Lean files; no compile was run.

LATER USES: a search of am.txt finds 12.4 only at intro (xii), the attribution note (j), the theorem and Cor 12.5, and the §12/§1 mentions of Bialynicki-Birula are descriptive. The only dependent is Cor 12.5, "follows from the proof of Theorem 12.4". It is safe because "vector bundle" is local on S. Moreover A_n = O_S·χ^n, so A_n → (I/I²)_n is a surjection from O_S onto a locally free sheaf of rank ≤ 1 and splits globally, and Lean's cor125_global (FinalCor125.lean:312) gives the global trivial bundle. Nothing needs the global form.

Scope: read-only, no edits or compile. The P¹ check is by hand, as STATUS.md:287 also records it; it is not in Lean. Page image used: C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\p124\thm-55.png.

## vote 19: correct

Quote: Thm 6.8 (p. 158, checked on the page image): "Assume that M is finitely generated as abelian group. Let X be a quasi-separated S-algebraic space locally of finite presentation endowed with an action of D(M)_S. Let Z ⊂ M be a subgroup and assume that one of the following assertions holds: (i) X is separated over S, (ii) M/Z is torsion-free. Then there exists a Z-FPR atlas U → X, which may be chosen quasi-compact (in particular S-affine here) if X → S is quasi-compact."

Def 6.1(iv) (p. 156): "We say that f is an equivariant atlas if f is étale and surjective and U = ∐_{τ∈A} U_τ is the disjoint union of D(M)_S-stable S-affine schemes; moreover in this case we say that the equivariant atlas f is S-affine if A may be chosen finite."

Thm A.2 (p. 196): "Let X be a quasi-separated S-algebraic space locally of finite presentation endowed with an action of a finitely presented diagonalizable group scheme G = D(M)_S. Let H = D(M/Z) be a subgroup scheme and assume that one of the following assertions holds: (i) X is separated over S, (ii) H has connected fibres. Then there exists a Z-FPR atlas U → X (cf. Definition 6.1), which may be chosen quasi-compact if X → S is."

Proof of A.2 (p. 199): "Proceeding as in the beginning of the proof of Theorem A.1, we reduce to the case where S is affine and S, X are of finite type over Z." Also: "It will thus be enough to find an affine, G-equivariant étale neighbourhood U(x) → X of each closed point". Also: "In case (ii) where H has connected fibres (which means that F is infinitesimal)".

Standing hypotheses of §6 (p. 156): "Let M be an abelian group. Let S be a scheme." Conj 6.9 (p. 158): "Let S be an arbitrary scheme." Remark 6.8 link (p. 157): "Note that Theorem 6.8 is numbered as Theorem A.2 in the appendix."

Fix: 1. Hypothesis fix. Add to Thm 6.8 and Thm A.2: "S has affine diagonal (e.g. S separated)". For the quasi-compact clause, the safe form is: if X is quasi-compact (and S has affine diagonal), U may be chosen S-affine. This is the existing Lean form (X qc, S separated).

2. Alternative fix, keeping arbitrary S. Weaken Def 6.1(iv) so that the U_τ are affine schemes, not S-affine ones, and drop "in particular S-affine here". This is what the printed proof actually produces. Its cost is that later uses of an S-affine atlas (e.g. Prop 8.5, Prop 15.5) then need the affine-diagonal hypothesis or a Zariski-local reduction.

3. Scope. The correction must be stated more widely than "the S-affine clause":
- Def 6.1(iv) makes every chart S-affine, so the bare existence of any Z-FPR atlas already fails, not only the quasi-compact clause.
- Conj 6.9(i) and (ii), which say "arbitrary scheme", are refuted by the same example, and need the same hypothesis.

4. 6.8(ii) vs A.2(ii). This is not an error in either statement. Replace "Theorem 6.8 is numbered as Theorem A.2" with "Theorem 6.8 is a special case of Theorem A.2". Alternatively, state 6.8(ii) as "D(M/Z)_S has connected fibres". In A.2, write H = D(M/Z)_S.

5. Side typo found while checking. Rem 6.2 prints "U → S" where it should read "U → X".

Reason: I checked the counterexample by hand against the printed text and the page images (pp. 156, 158, 196, 199). I found no Lean formalization of this example in AlgMag/, and STATUS.md does not yet list it under Paper corrections. Its Lean results (`thm68`, `thm68_i`) assume S affine of finite type over Z, and STATUS line 115 records S separated, so they do not contradict it. I did not spawn agents because none were available in this subagent.

**Setup.** k is a field. S is the plane with doubled origin, S = P1 ∪ P2, with P1 and P2 copies of A^2_k glued along A^2 minus 0. X = P1 with structure map the open immersion. M = 0 and Z = 0, so D(M)_S = S acts trivially. (Any f.g. M with trivial action and Z = M also works.)

**Hypotheses, each checked.**
- Standing: §6 and p. 44 of the text say only "Let S be a scheme" / "fix a base scheme S". I searched for global separatedness conventions and found none. Conj 6.9 even says "arbitrary scheme".
- M is finitely generated.
- X is a scheme, hence an S-algebraic space.
- An open immersion is a monomorphism, so the diagonal of X/S is an isomorphism. X is therefore separated over S, and quasi-separated. So (i) holds.
- M/Z = 0 is torsion-free, so 6.8(ii) holds. H is the trivial group, so its fibres are connected and A.2(ii) holds.
- An open immersion is locally of finite presentation.
- X → S is quasi-compact because X is noetherian. So even the final clause applies.
- D(0)_S is finitely presented diagonalizable.

**Meaning of "S-affine".** It means affine over S. The print uses "Assume that X is affine over S" (Thm 3.20, Cor 3.22) and then "outside the S-affine case" (Rem 3.23). The absolute reading (U_τ an affine scheme) would make "in particular S-affine here" false already for S an infinite disjoint union, X = S. The Lean form agrees: `hasFiniteAffineDecomposition_iff` gives `IsAffineHom`.

**No atlas exists.** Let f: U = ∐U_τ → X be étale and surjective with each U_τ → S affine.
1. Choose u over the origin of P1, with u in U_τ.
2. Because f lands in P1, the preimage of P1 in U_τ is all of U_τ, so U_τ is affine.
3. The preimage of P2 in U_τ is W = U_τ minus F, where F is the fibre over the origin, so W is affine too.
4. U_τ is étale over A^2 and affine, so it is noetherian and regular, hence normal. F is nonempty, closed, and consists of codimension-2 points.
5. By algebraic Hartogs, O(U_τ) = O(W). With both affine, W = U_τ, contradicting F nonempty.

So no atlas in the sense of Def 6.1(iv) exists, S-affine or not. The equivariance and FPR conditions are never needed.

**Why these exact choices.** The plane is essential: with the doubled line, S has affine diagonal and A^1 → S is affine, so there is no counterexample. One chart is also essential: X = S has the atlas U = S. Thus the proposal's wording is the right example, and the exact threshold is affine diagonal: if S has affine diagonal, every affine scheme over S is S-affine.

**Where the proof breaks.** The sentence "we reduce to the case where S is affine" is the failing step. Being S-affine is not local on S for a chart that lives over a single affine open S_i, unless S_i → S is itself affine. The proof does produce affine charts (via the cited [3, Cor 20.2], not rechecked), so the local conclusion is not affected.

**6.8(ii) vs A.2(ii).** The conditions are genuinely different.
- M/Z torsion-free implies that H is a split torus, so its fibres are connected.
- The converse fails: S = Spec F_p, M = Z/p, Z = 0 gives H = mu_p, which is connected, with M/Z not torsion-free.
- The two are equivalent when S has a characteristic-0 point or points of two distinct characteristics.
- Rem 2.5 literally makes D(M/Z) without subscript live over Spec Z, which would make A.2(ii) equal to torsion-free. But "subgroup scheme" of D(M)_S and the proof's "(which means that F is infinitesimal)" show that D(M/Z)_S is meant.

So A.2 is strictly stronger than 6.8 in case (ii). 6.8(ii) follows from A.2(ii), and nothing false results; only the claim that they are the same theorem is inaccurate. Neither form survives the non-separated S example, since M = 0 satisfies both.

**Not settled here.** I did not decide whether the S-affine clause holds for S separated but not quasi-compact with X → S quasi-compact and X not quasi-compact. The recommended fix avoids that case by assuming X quasi-compact.

## vote 20: correct

Quote: Prop 3.32 proof (ii), p. 149 (checked on the page image): "The action ⋆ is free because firstly the action of D(N^gp × L^gp)_T on A(N × L)_T given by (λ, β) · (a, b) = (λ · a, β^{-1} · b) is free and secondly because the morphism of groups N^gp × L^gp → N^gp + L^gp given by (n, l) ↦ n + l is surjective and so D(N^gp + L^gp)_T is a closed subgroup scheme of D(N^gp × L^gp)_T." and "So we have an identification (A(N)_T ×_T A(L)_T)/D(N^gp + L^gp)_T = A(N ∩ L)_T."

Fix: Keep the statement and the printed frame: F ↔ f, F = f∘m, with m : A(N)×A(L) → A(N∩L) the multiplication. Replace only "free action, fpqc quotient". Do not claim A(N∩L) is the fpqc quotient. Claim instead that m is a categorical quotient for invariant maps to X, proved by the descent in AlgMag/Sec3SchemeQuotient.lean. Let A = R[N×L], graded by (n,l) ↦ n−l, with A_0 = R[N∩L]. (1) Reynolds: over a prime q of A_0, a homogeneous ideal I maximal with I_0 ⊆ q gives the closed orbit. (2) For V affine around the image of that orbit, F^{-1}(V) contains m^{-1}(D(h)) with h ∉ q. (3) O(V) → A_h lands in degree 0; glue. (4) Uniqueness: A_0 → A is split. If N^gp+L^gp has torsion, descend first along the torsion-free quotient of the grading, then along the torsion part. Scope to state: this gives prop332_scheme for any scheme X, with no separatedness and no atlas (no sorry in the file; #print axioms line present, not rerun here, no compile). For algebraic spaces, X separated: prop332 needs an S-affine strongly-FPR atlas and N, L f.g. or X limit preserving; prop332_free (X qc, l.f.p., S separated) rests on stubs. So the printed (ii) for an arbitrary S-space X is not established: it is proved for schemes and for the space cases above only. The printed proof remains valid exactly when N^gp + L^gp = N^× + L^×.

Reason: I tried to save the print and could not. Take M = ℤ, N = L = ℕ, which is within hypothesis (ii). Then ⋆ is the action g·(a,b) = (g^{-1}a, gb) of G_m on A². It fixes (0,0), so it is not free. Algebraically, R = ℤ[x,y] with deg x = −1, deg y = 1 has R_1·R_{−1} = (xy) ≠ R_0 = ℤ[xy]. The first printed premise fails as well: G_m×G_m does not act freely on A². The identification fails independently of the word "free". The degree-zero computation is correct, and m is (a,b) ↦ ab. But (1,0) and (0,0) both map to 0 and no unit g relates them, even fppf-locally, so A² → A¹ is not a quotient sheaf map. The fibre over 0 has three orbits. The printed step F ↦ f therefore has no justification. General criterion (by hand): R_m R_{−m} is a monomial ideal of ℤ[N∩L], so it contains 1 only via units. Hence ⋆ is free iff N^gp + L^gp = N^× + L^×. Examples: N, L groups, or N = ℕ, L = ℤ, where A¹×G_m → A¹ is a torsor. In that second example ⋆ is free although the printed first premise is false, so that premise is stronger than needed. The non-freeness is by hand and in Lean comments only; I found no Lean theorem stating it. The statement itself survives for schemes: prop332_scheme is proved, including the non-separated case, and does not use the quotient. I did not settle arbitrary algebraic spaces, nor non-separated spaces. The only caveat to the proposed correction is therefore scope: repaired proof for schemes, atlas or stubs for spaces (STATUS.md marks this "waits for AHR"). STATUS.md line 291 records the correction. Its second clause, on the colimit A(⋂N_l), belongs to Fact 3.34, not Prop 3.32. Source for SGA3 VIII 5.1 requiring freeness is from memory, not opened; the argument does not depend on it. Files read: C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\p332-24.png, C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Sec3SchemeQuotient.lean, C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\Sec3Intersections.lean, C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\FinalAtlasFree.lean.

## vote 21: correct

Quote: Prop 9.11 (Semigroup Forum, p. 165, checked on the page image): "corresponds to a collection (μ_m)_{m∈M} ∈ Hom_{O_B}(F, F) such that only finitely many of the (μ_m)_{m∈M} are nonzero locally and for all m, k ∈ M, [...] and Σ_{m∈M} μ_m = Id_F." Proof, p. 166: "Now μ gives a collection (μ_m)_{m∈M} with μ_m ∈ Hom_{O_B}(F, F), such that only finitely many of the (μ_m)_{m∈M} are nonzero locally." The print writes μ_m. ρ_m is the notation of the Lean files and STATUS.md only.

Fix: Replace the clause in the statement with: "such that for every section s of F over any V, locally on V only finitely many of the μ_m(s) are nonzero". Over affine or quasi-compact V this means finitely many on all of V. Read the last line as Σ_{m∈M} μ_m(s) = s. Make the same replacement in the first sentence of p. 166. Nothing else in the statement or proof changes: the coassociativity and counit computations and the converse all go through, and the converse needs the sectionwise finiteness for μ = Σ μ_m ⊗ X^m to land in the direct sum. The printed wording stays true when F is of finite type, but no such hypothesis should be added, since it would lose the case F = O_B[M].

Reason: This is a real error of wording, not a misprint. The same phrase appears in both the statement and the proof, so it is not a slip of the typesetter. It is a false claim about the endomorphisms, with an obvious intended meaning that is true.

Counterexample: take F = O_B[M] with M infinite and B nonempty, with coaction Δ(X^m) = X^m ⊗ X^m. Then μ_m is the projection onto the summand O_B X^m. On any nonempty T → B, in the Zariski, fppf or any other localization, μ_m sends X^m to X^m ≠ 0. So all infinitely many μ_m are nonzero on every member of every cover, and no reading of "locally" on B rescues the literal sentence.

The forward direction of the correspondence therefore fails as printed: this comodule structure gives a collection that violates the condition. The proof's step also fails at that point. A map F → ⊕_{m∈M} F has finite support only on each section, which does not make finitely many components nonzero as endomorphisms.

Lean evidence: `regular_comp_ne_zero` (Sec9Hochschild.lean:626) proves (regular R M).comp m ≠ 0 for every nontrivial R. Since R[M] ⊗ R' = R'[M], this covers every localization of the base. The corrected form is `coactionEquivDecomposition` with `finite : ∀ x, (support fun m => comp m x).Finite`, and `Decomp` in Sec9OverB.lean and Sec9General.lean has the same field over affine T. STATUS.md lists it under "To review". I did not compile anything, as instructed; I read the Lean source only.

The sectionwise form is plainly what the author meant, and it also gives the infinite sum Σ μ_m = Id its meaning. Literally, that sum makes no sense for infinitely many nonzero μ_m unless it is read on sections.

## vote 22: correct

Quote: Statement, p. 165 (checked on the PDF page image): "An A(M)_B-O_B-module (over B_{spaces,fppf}) structure on a quasi-coherent O_B-module F corresponds to a collection (μ_m)_{m∈M} ∈ Hom_{O_B}(F, F) such that only finitely many of the (μ_m)_{m∈M} are nonzero locally and for all m, k ∈ M, [μ_m∘μ_k = μ_k if k = m; μ_m∘μ_k = 0 if k ≠ m] and Σ_{m∈M} μ_m = Id_F." Proof, p. 166: "Now μ gives a collection (μ_m)_{m∈M} with μ_m ∈ Hom_{O_B}(F, F), such that only finitely many of the (μ_m)_{m∈M} are nonzero locally." The print's symbol is μ_m, not ρ_m.

Fix: Replace the condition in the statement and in the proof line on p. 166 with: "such that for every V in B_{spaces,fppf} and every v in F(V), locally on V only finitely many of the μ_m(v) are nonzero". Over quasi-compact V this means finitely many outright. Read Σ μ_m = Id_F on sections. The printed wording stays true when F is of finite type or M is finite, since then F is locally generated by finitely many sections. Bookkeeping: STATUS.md line 294 puts "(ρ_m)" inside a quotation of the print, and the print has (μ_m)_{m∈M}, so that quote should be fixed. The Lean `Decomp` (Sec9OverB.lean:1213) requires finiteness at each section over an affine T, which is equivalent to this wording.

Reason: Refutation attempts, all assuming the print is right.
(1) Excluded example: §9.3 opens with "Let M be a finitely generated cancellative monoid", so M = N or Z is allowed and infinite. Nothing excludes these.
(2) Is the example a genuine module? Take F = O_B[M] with μ = Δ, X^m ↦ X^m ⊗ X^m. This is quasi-coherent and satisfies coassociativity and counit. It is the regular comodule, Lean `regular`, Sec9Hochschild.lean:603. μ_m is the projection onto O_B X^m.
(3) Literal reading, locally on B: for any nonempty U → B, in Zariski or fppf topology, μ_m(X^m) = X^m ≠ 0 in F(U), so every μ_m|_U ≠ 0. Infinitely many are nonzero on every nonempty U, for any nonempty B. The comodule therefore does not give the printed data, and "corresponds" fails. Lean `regular_comp_ne_zero` (Sec9Hochschild.lean:626) proves μ_m ≠ 0 for Nontrivial R. The step to every U is by hand: apply it with R replaced by O(U), or use base change. Finiteness of the family is not in the Lean theorem; it follows from M infinite.
(4) Charitable reading: "nonzero locally" could mean values on local sections. This is the only way to save the print, and the proof's source supports it: finiteness comes from the target ⊕_{m∈M} F, which gives finite support per section, not per endomorphism. Under this reading the mathematics of 9.11 is right and the rest of the proof is unaffected. But the printed subject is the family μ_m ∈ Hom_{O_B}(F, F), so the reading requires changing the words. The error is in the wording of a side condition. The comodule to idempotents dictionary is sound.
(5) The "locally" must be kept on the section side: for T = ⊔ Spec k non-quasi-compact, a section can have infinitely many nonzero μ_m(v). A fix quantified over all sections without "locally" would be false, while the affine-T form in Lean is fine.
No refutation survives. Evidence: PDF pp. 165-166 read as images, plus Lean source read only, not recompiled.

## vote 23: correct

Quote: Thm 6.8 (p. 158, checked on the PDF image): "Assume that M is finitely generated as abelian group. Let X be a quasi-separated S-algebraic space locally of finite presentation endowed with an action of D(M)_S. Let Z ⊂ M be a subgroup and assume that one of the following assertions holds: (i) X is separated over S, (ii) M/Z is torsion-free. Then there exists a Z-FPR atlas U → X, which may be chosen quasi-compact (in particular S-affine here) if X → S is quasi-compact."

Thm A.2 (p. 196): "(i) X is separated over S, (ii) H has connected fibres. Then there exists a Z-FPR atlas U → X (cf. Definition 6.1), which may be chosen quasi-compact if X → S is."

Def 6.1(iv) (p. 156): "U = ∐_{τ∈A} U_τ is the disjoint union of D(M)_S-stable S-affine schemes; moreover in this case we say that the equivariant atlas f is S-affine if A may be chosen finite."

Section 6 opening: "Let S be a scheme."

Proof of A.2 (p. 199): "Proceeding as in the beginning of the proof of Theorem A.1, we reduce to the case where S is affine and S, X are of finite type over Z." Also from that proof: "The final claim that U → X can be chosen quasi-compact if X → S is quasi-compact is obvious."

Proof of A.1, which A.2 borrows: "The assumptions and conclusion being local over S".

Fix: Add one hypothesis and change the quasi-compact clause, in both Thm 6.8 and Thm A.2.

1. Add "Assume S is separated" (an affine diagonal is enough). Items (i) and (ii) stay as printed.

2. In 6.8, replace the end with "which may be chosen quasi-compact (in particular S-affine here) if X is quasi-compact". Make the same change in A.2.

3. In the proof of A.2, add one sentence after the reduction: since S is separated, an affine scheme over an affine open of S is S-affine, so the charts found over the affine opens of S are S-affine.

Item (ii): no correction is needed. 6.8(ii) is a special case of A.2(ii). If a remark is wanted, write "M/Z is torsion-free (more generally, D(M/Z)_S has connected fibres)".

Consequences for the rest of the paper:
- Conj 6.9 says "Let S be an arbitrary scheme", so it needs the same hypothesis.
- Uses that are local on S need nothing new, because they can reduce to S affine first.
- The use in Prop 8.5 needs only finitely many affine charts, so it survives for S quasi-compact non-separated. This repair is by hand.

Reason: This is a real error, not a misprint, and it is slightly stronger than proposed: the existence clause fails too, not only the S-affine clause.

**Counterexample (by hand, not in Lean).**
- S is the plane over a field with doubled origin, with charts V1, V2 and V1 ∩ V2 = A^2 minus 0. S is quasi-separated.
- X = V1 → S is an open immersion. It is quasi-compact, separated and locally of finite presentation, so (i) holds.
- Take M = 0 or the trivial action, so (ii) holds with Z = M.
- Let U_τ → X be étale, with U_τ S-affine and containing a point over the origin.
- Then U_τ ×_S V1 = U_τ is affine.
- Also U_τ ×_S V2 = U_τ minus f^{-1}(0) must be affine. But f^{-1}(0) is non-empty of codimension 2 in a regular scheme, so this complement is not affine (Hartogs).
- So X has no equivariant atlas at all in the sense of Def 6.1(iv), and any Z-FPR atlas is one by Def 6.1(v). A.2 cites Def 6.1, so it fails as well, even though it does not print "S-affine".
- The same X refutes Conj 6.9 for arbitrary S.

**Why it is not a reading problem.**
- "S-affine" means affine over S. Evidence: Def 7.2; the proof of Thm 8.3, "affine because U is S-affine"; and Lean `hasFiniteAffineDecomposition_iff`, which gives `IsAffineHom`.
- The other reading, "S-scheme whose underlying scheme is affine", avoids this example. But it breaks the quasi-compact clause another way: for S an infinite disjoint union of points and X = S, X → S is quasi-compact and no finite family of affine schemes surjects onto X.

**Where the proof goes wrong.**
- "Reduce to S affine" is copied from A.1, whose claims are local over S.
- The A.2 conclusion is not local over S: an affine chart over an affine open of S need not be affine over S unless S has an affine diagonal.
- The word "obvious" also hides a second gap. With S separated but not quasi-compact, X → S quasi-compact does not give a finite or locally finite family of charts. I found no counterexample to that case, so the fix uses X quasi-compact, which is provable.
- That is the same form as Lean `thm68_qc_spaces` ([S.IsSeparated], `hq`: X quasi-compact, AlgMag/ChartFinalSpaces.lean:44). `thm68` (AlgMag/ChartFinal.lean:43) has `IsAffine S`.
- Lean's restriction is consistent with this correction, but no Lean theorem refutes the print. STATUS.md Paper corrections does not list this item yet.

**Item (ii) is a discrepancy, not an error.**
- If M/Z is torsion-free, D(M/Z) is a split torus, so it has connected fibres. Hence 6.8(ii) follows from A.2(ii).
- The converse fails: take M = Z/p, Z = 0, S over F_p, so H = μ_p is connected.
- In general, a nonzero torsion part must be p-primary with p nilpotent on S, which matches "F is infinitesimal" in the proof.
- So "Theorem 6.8 is numbered as Theorem A.2" is loose, but both statements are true in this respect once S is fixed.

**Not examined:** the quotient construction U1 in case (i) of the proof of A.2. Lean's route avoids it through the chart lemma.

PDF pages rendered to C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am68own (q31-31.png, q33-33.png, q71-71.png, q74-74.png). No project files were edited and nothing was compiled.

## vote 24: correct

Quote: Semigroup Forum p. 149, checked on the page image (C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\p332\p-24.png), Prop 3.32 (ii) proof: "Let us consider the action ⋆ of D(N^gp + L^gp)_T on A(N)_T ×_T A(L)_T given by g⋆(a, b) = (g^{-1}·a, g·b). The action ⋆ is free because firstly the action of D(N^gp × L^gp)_T on A(N × L)_T given by (λ, β)·(a, b) = (λ·a, β^{-1}·b) is free and secondly because the morphism of groups N^gp × L^gp → N^gp + L^gp given by (n, l) ↦ n + l is surjective and so D(N^gp + L^gp)_T is a closed subgroup scheme of D(N^gp × L^gp)_T." Then: "So we have an identification (A(N)_T ×_T A(L)_T)/D(N^gp + L^gp)_T = A(N ∩ L)_T." Statement: "Let L and N be arbitrary submonoids of M. [...] (ii) M is a finitely generated abelian group, [...] then we have canonical identifications (X^N)^L = X^{N∩L}". Standing hypotheses (§3, p. 140): "In this paper, an S-space is an algebraic space over S. Let us fix an S-space X." So X is an algebraic space, with no separatedness assumed.

Fix: Replace the free-action and fpqc-quotient step. Keep the statement for schemes and for spaces with an atlas. Do not claim a proof for a general algebraic space yet.

COUNTEREXAMPLE, LINE BY LINE. Take M = Z and N = L = ℕ, with S and T nonempty. This meets (ii) and the §3 standing hypotheses, and X plays no role in the claim. D(N^gp + L^gp) = G_m acts on A^2 by g⋆(a,b) = (g^{-1}a, gb).
- The point (0,0) is fixed by every g in G_m(T'), and G_m(T') is nontrivial for T' = G_m,T. So ⋆ is not free.
- The "firstly" claim fails too: (λ,β) fixes (0,0) in G_m^2.
- The "secondly" step (closed subgroup scheme) is correct, and so is the degree-zero computation Z[x,y]_0 = Z[xy] = Z[N∩L].
- The failing step is the identification of the fpqc quotient. The sheaf quotient Q has [0,0] ≠ [1,0] in Q(k), since g⋆(0,0) = (1,0) has no solution over any nonzero extension of k. Both points map to 0 under xy, so Q → A^1 is not injective.
- SGA3 VIII 5.1 therefore does not apply.

EXACT RANGE OF THE PRINTED STEP (derived here, T nonempty). ⋆ is free iff N^gp + L^gp = N^× + L^×. If equality fails, take the point (1 on N^×, 0 elsewhere; 1 on L^×, 0 elsewhere). Its stabilizer is D((N^gp + L^gp)/(N^× + L^×)), which is nontrivial. If equality holds, every degree contains a homogeneous unit, so the grading is strongly graded and the printed proof is valid. This covers N, L subgroups, and also N = ℕ, L = Z.

IS THE STATEMENT TRUE?
- Schemes, X with no separatedness: yes. `prop332_scheme` (AlgMag\Sec3SchemeQuotient.lean:1669) covers arbitrary S and T, with no sorry in that file. It appears as replayed in .buildAll.log. I did not compile or re-run axioms.
- Spaces with an atlas: yes. `prop332` (AlgMag\Sec3Intersections.lean:463) assumes X separated with an S-affine strongly-FPR atlas, and N, L f.g. or X limit preserving. `prop332_weak` and `prop332_linearizable` are variants.
- `prop332_free` (AlgMag\FinalAtlasFree.lean:42): X separated, l.f.p., quasi-compact, S separated. It rests on the stubs of notes/chart-stubs.md.
- General algebraic space: not established. Two partial results:
  (a) Alper, Good moduli spaces, Thm 6.6 (read in arXiv 0804.2242): "Suppose X is a locally noetherian Artin stack and φ : X → Y is a good moduli space. Then φ is universal for maps to algebraic spaces." Since [Spec A / D(K)] → Spec A_0 is a good moduli space, this gives (ii) for N, L f.g. and T locally noetherian.
  (b) Uniqueness for all spaces, my own hand argument, not formalized. The equalizer E → Spec A_0 of two maps is a separated, locally quasi-finite monomorphism. Spec A → Spec A_0 factors through it and is universally submersive (Alper 4.16(v)). So E → Spec A_0 is a universal homeomorphism, hence a closed immersion, and A_0 → A injective forces E = Spec A_0.

SHARPNESS. Remark 3.3 lets Definition 3.1 apply to arbitrary functors, but (ii) is false there. Take X = Q, with action t·[a,b] = [ta,b]. The quotient map A^2 → Q is equivariant for G_m × G_m and lies in (Q^N)^L, but it does not factor through xy because [0,0] ≠ [1,0]. So any repair must use geometry of X, and (ii) cannot be extended to fppf sheaves.

REPAIRED PROOF TO PRINT, for schemes (A = R[N×L] graded by (n,l) ↦ n−l, A_0 = R[N∩L], m : Spec A → Spec A_0 dual to m' ↦ (m',m')):
1. Reynolds: a closed orbit lies over each prime q of A_0.
2. For V affine around the image of that orbit, F^{-1}(V) contains m^{-1}(D(h)) with h ∉ q.
3. On D(h), O(V) → A_h lands in degree 0, so F descends locally; then glue.
4. Uniqueness comes from A_0 → A being split.
When N^gp + L^gp has torsion, step 2 runs in two stages: first the torsion-free quotient of the grading, then the torsion part, where the map is integral and fibres are single orbits.

Wording: STATUS.md line 291 says "is not free". It should say "not free in general (free iff N^gp + L^gp = N^× + L^×)". The "A(⋂ N_l) colimit" half of that line belongs to Fact 3.34, not to 3.32.

Reason: The counterexample meets every printed hypothesis of (ii): M = Z is finitely generated, N and L are arbitrary submonoids, and X is any S-space. The print's freeness claim, and its "firstly" claim, fail at the fixed point (0,0), and the fpqc quotient is not A(N∩L). The rest of the printed computation is correct.

The statement itself survives for schemes, with no separatedness needed, through the Reynolds descent in `prop332_scheme`. It also holds for spaces with an atlas, and in the noetherian f.g. case by Alper Thm 6.6. For a general non-noetherian algebraic space, only uniqueness is shown (by my hand argument), so existence remains unsettled, and STATUS.md's PARTIAL is accurate.

Checks: I read the print on the page images and read the Lean sources, but did not compile. Alper was read in the arXiv version, not the publisher's.

## vote 25: correct

Quote: Prop 9.11 (p. 165, checked on the page image): "An A(M)_B-O_B-module (over B_{spaces,fppf}) structure on a quasi-coherent O_B-module F corresponds to a collection (μ_m)_{m∈M} ∈ Hom_{O_B}(F, F) such that only finitely many of the (μ_m)_{m∈M} are nonzero locally and for all m, k ∈ M, [μ_m∘μ_k = μ_k if k = m; μ_m∘μ_k = 0 if k ≠ m] and Σ_{m∈M} μ_m = Id_F." Proof (p. 166): "Now μ gives a collection (μ_m)_{m∈M} with μ_m ∈ Hom_{O_B}(F, F), such that only finitely many of the (μ_m)_{m∈M} are nonzero locally." The print's symbol is μ_m. ρ_m is the Lean and STATUS.md name. Standing hypotheses of §9.3 (p. 164): "Let M be a finitely generated cancellative monoid." and "We assume in this section that the multiplication morphism A(M)_B ×_B A(M)_B → A(M)_B is flat." followed by "For example if M is a group, the multiplication morphism D(M)_B ×_B D(M)_B → D(M)_B is flat."

Fix: Replace the printed clause with a section-wise one: "such that for every affine T in B_{spaces,fppf} and every s ∈ F(T), only finitely many of the μ_m(s) are nonzero". The sum Σ μ_m = Id_F is then read section-wise too. Make the same change in the proof sentence on p. 166: μ lands in the direct sum, so each section over an affine T has finitely many nonzero components. The endomorphisms themselves are locally finite in number only under an extra hypothesis, for example F of finite type. Nothing downstream needs more: Prop 9.13 only uses components of sections over quasi-compact U.

Reason: The counterexample meets every printed hypothesis, and each step holds.

1. Hypotheses. Take M = Z. It is finitely generated, cancellative and infinite, and the flatness assumption of §9.3 is the print's own example ("if M is a group"). M = N would also work, but it needs Prop 2.8 or miracle flatness. Take B = S = Spec k for a field k, or any nonempty B. The empty B must be excluded.

2. The module. Let F = O_B[M] = f_*O_{A(M)_B}, the sheaf direct sum of copies of O_B. It is quasi-coherent, since it is the pushforward along an affine morphism and a direct sum of quasi-coherent modules. For g ∈ A(M)(T) = Hom(M, O(T)), set g·X^k = g(k)X^k. This is O_B-linear and compatible with restriction, so Definition 9.2 holds. It is an action because (gg')(k) = g(k)g'(k) and the unit acts as the identity. The coaction is X^k ↦ X^k ⊗ X^k, which is the comultiplication Δ of Fact 2.2, so coassociativity and the counit axiom are the bialgebra axioms. Prop 9.10 therefore applies.

3. The components. μ_m(X^k) = δ_{mk}X^k, the projection onto the m-th summand. The two orthogonality relations and the section-wise sum Σμ_m = Id hold.

4. The failure. Let V → B be any object of the site with V nonempty. Then O(V) ≠ 0 and X^m ∈ F(V), and μ_m|_V(X^m) = X^m ≠ 0. So every μ_m stays nonzero on every nonempty V, and infinitely many are nonzero on every member of every cover. No covering of B makes the family finite, so the structure in step 2 is not in the printed collection. Hence the printed "corresponds to" is false: the module structure exists, but its data violates the clause.

5. Where the print's step breaks. μ: F → ⊕_m F is a sheaf map. It factors locally through a finite sub-sum only if F is generated by finitely many sections locally. O_B[M] with M infinite is free of infinite rank, so it is not of finite type. The clause does hold when F is of finite type or M is finite.

6. Lean. `regular_comp_ne_zero` (AlgMag/Sec9Hochschild.lean:626) proves the affine statement: for R nontrivial, `(regular R M).comp m ≠ 0`. It says nothing explicitly about "locally". The step to every nonempty V is the base change R → O(V) in step 4, which I did by hand. The corrected form is `Decomposition.finite` and `Decomp.finite` (Sec9OverB.lean:1218), which match the fix. I read the Lean source but did not compile it, as instructed.

Reading of the print: the word "locally" attaches to the μ_m, which the print declares as elements of Hom_{O_B}(F, F), so the literal reading is the refuted one. The intended meaning was probably section-wise, and this is a wording error rather than a damaging one, because the comodule identification in the proof is sound once the clause is read at sections. The correction should say that the clause as printed is false, not that the correspondence fails.

## vote 26: correct

Quote: Semigroup Forum p. 157, checked on the page image.

Rem 6.5: "For example, take M = Z/2Z, S = Spec(Z), X = S endowed with the trivial action of D(M) and U = D(M) endowed with the non-trivial action of itself by multiplication. Then the D(M)-equivariant morphism U → S is smooth of relative dimension zero and so it is étale; but U^{D(M)} = ∅, X^{D(M)} = X and therefore U^{D(M)} ≇ X^{D(M)} ×_X U."

Rem 6.6: "Choose an exact sequence of abelian groups 0 → Z → M → M/Z → 0 with Z ≠ M and M/Z finite. Then f : D(M) → D(Z) is étale, surjective and D(M)-equivariant. Put U = D(M) and X = D(Z). Since U^{D(M)} = X^{D(M)} = ∅, f is FPR. Now f is not Z-FPR because U^{D(M/Z)} = ∅ and X^{D(M/Z)} = X."

Fix: Rem 6.5: replace S = Spec(Z) by S = Spec(Z[1/2]), or any nonempty S on which 2 is invertible. An alternative that keeps S = Spec(Z) is X = S with trivial action and U = D(M)_{Z[1/2]} acting on itself through the restriction of the group to Z[1/2]; then U → S is étale but not an atlas, which Rem 6.5 does not need. The rest of the example is unchanged. Also, "smooth of relative dimension zero" is false over Z, not only "étale". Keep that phrase only after the base is changed.

Rem 6.6: add to the choice of sequence "Z ≠ 0, Z ≠ M, M/Z finite, and [M:Z] invertible on S" (S nonempty). The rest is unchanged.

Sharpening of the proposed correction: for S nonempty with M/Z finite, invertibility of [M:Z] on S is necessary and sufficient for f to be étale, because f is a D(M/Z)-torsor. Finite generation of M is not needed. The Lean statement `rem66` assumes AddGroup.FG M, and STATUS.md already flags this as stronger than necessary.

Possible further note: the opening sentence of Rem 6.5 ("If M is not torsion-free ... not an isomorphism in general") also depends on S. Over F_2 with M = Z/2, the group D(M) = μ₂ has connected fibres, so Thm A.1, as described in Rem 6.4, gives that every étale equivariant morphism is FPR. The torsion must have order prime to some residue characteristic of S. "In general" can absorb this, so no change is forced.

Reason: I tried to defend the print and could not. All three errors are direct; I rechecked them by hand and did not compile anything.

Rem 6.5:
- D(Z/2)_Z = Spec Z[t]/(t²−1). Its fibre at 2 is F_2[t]/(t+1)², which is non-reduced, so U → Spec Z is neither unramified nor smooth at 2. The print's claim fails on the stated S.
- The print fixes S = Spec(Z) explicitly, so no implicit base can rescue it.
- The conclusion U^{D(M)} = ∅ and X^{D(M)} = X does hold over Z. Only étaleness fails, and that is the point of the example, since Prop 6.3 concerns étale morphisms.
- Lean: `not_etale_printed_rem65` (SecLeftoverFPR.lean:267) and the corrected `rem65` and `rem65_zmod2` (lines 304 and 323) say the same. STATUS.md records them as joint-build.

Rem 6.6, invertibility:
- The only defence is that S is left implicit, so "choose" might allow a good S. But §6 opens with "Let S be a scheme", and the étale claim is made for every such sequence.
- Counterexample: M = Z, Z = 2Z, S = Spec F_2. Then f is the squaring map on G_m, which is not étale. Its fibres are copies of μ₂, which is infinitesimal.
- Even if a reader assumed S lies over Q, the Z ≠ 0 error below stands on its own.

Rem 6.6, Z ≠ 0:
- The print allows Z = 0 with M finite and nonzero. Then X = D(0) = S with trivial action, so X^{D(M)} = S ≠ ∅, and "U^{D(M)} = X^{D(M)} = ∅" is false.
- f is then not FPR, and this is exactly the example of Rem 6.5, so the two remarks contradict each other as printed. This holds over any nonempty S, including S = Spec Q.
- For Z ≠ 0, X^{D(M)} = ∅ does hold. D(M) acts on D(Z) through the faithfully flat map D(M) → D(Z), and D(Z)_T is nontrivial for T nonempty, even when |Z| is not invertible. So no hypothesis beyond Z ≠ 0 is needed for this step.
- Lean: `rem66` (line 375) uses h0 : Z ≠ ⊥ at lines 398-400.

Other claims in Rem 6.6: "surjective" holds with no extra hypothesis, since f is integral and injective on rings. "Not Z-FPR" needs only Z ≠ M, as printed.

The Lean evidence is read from source and STATUS.md. The hand arguments above do not depend on it.

## vote 27: correct

Quote: Rem 6.5 (p. 157, checked on the page image): "For example, take M = Z/2Z, S = Spec(Z), X = S endowed with the trivial action of D(M) and U = D(M) endowed with the non-trivial action of itself by multiplication. Then the D(M)-equivariant morphism U → S is smooth of relative dimension zero and so it is étale; but U^{D(M)} = ∅, X^{D(M)} = X and therefore U^{D(M)} ≇ X^{D(M)} ×_X U."
Rem 6.6 (p. 157): "Choose an exact sequence of abelian groups 0 → Z → M → M/Z → 0 with Z ≠ M and M/Z finite. Then f : D(M) → D(Z) is étale, surjective and D(M)-equivariant. Put U = D(M) and X = D(Z). Since U^{D(M)} = X^{D(M)} = ∅, f is FPR. Now f is not Z-FPR because U^{D(M/Z)} = ∅ and X^{D(M/Z)} = X."

Fix: Rem 6.5: replace "S = Spec(Z)" by "S = Spec(Z[1/2])" (any nonempty S on which 2 is invertible works). The rest of the example then holds as printed. The opening claim ("obviously not an isomorphism in general") is unaffected.
Rem 6.6: replace "with Z ≠ M and M/Z finite" by "with Z ≠ 0, Z ≠ M and M/Z finite", and work over a nonempty scheme S on which [M:Z] is invertible, reading D(·) as D(·)_S. Concrete instance: M = ℤ, Z = 2ℤ, S = Spec(ℤ[1/2]). The last two sentences then hold as printed.

Reason: These are real errors in two illustrative examples, not misprints or reading problems. The surrounding claims survive with the smallest fix. Neither remark is cited by number elsewhere in the text (grep for "Remark 6.5/6.6"), so nothing downstream is affected.

Rem 6.5: D(Z/2) over Spec(Z) is Spec Z[t]/(t²−1). Its fibre over F_2 is F_2[t]/(t−1)², which is non-reduced. So the morphism is flat but not smooth, and not étale, at 2, and the sentence "smooth of relative dimension zero and so it is étale" is false as printed. Lean agrees: `not_etale_printed_rem65` (AlgMag/SecLeftoverFPR.lean:267). The fixed-point computation is correct, so only the base needs changing. `rem65_zmod2` (:323) proves the corrected example over Z[1/2], and `rem65` (:304) proves the general version with |M| invertible in R ≠ 0.

Rem 6.6, invertibility: by Def 2.4(iv) (line 483 of am.txt), unsubscripted D(M) is the group scheme over Spec(Z). There, f is a D(M/Z)-torsor (fppf locally a product with D(M/Z)), so f is étale iff D(M/Z)_S → S is étale iff [M:Z] is invertible on S. Over Spec(Z) with Z ≠ M this never holds, so the print fails. Any other base still needs the condition: S = Spec F_p with [M:Z] = p fails too. So invertibility is both necessary and sufficient, not merely convenient.

Rem 6.6, Z ≠ 0: if Z = 0, then M is finite and nonzero, and X = D(0) = S carries the trivial action. Then X^{D(M)} = X ≠ ∅ while U^{D(M)} = ∅, so "U^{D(M)} = X^{D(M)} = ∅" is false and f is not FPR. This is exactly the Rem 6.5 situation. With Z ≠ 0, D(M) acts on D(Z) through the faithfully flat D(M) → D(Z) by translation. A fixed T-point then forces D(Z)_T to be trivial, so T is empty and the claim holds. The same case can also be excluded by taking M infinite, but "Z ≠ 0" is the smallest change.

The remaining claims check out. Surjectivity holds because Z[M] is finite free over Z[Z]. "Not Z-FPR" holds for nonempty S, since D(M/Z) acts freely on D(M) and trivially on D(Z). The M f.g. hypothesis in Lean `rem66` (:375) is a formalization convenience, not a needed correction: STATUS.md line 113 says finite index suffices, so it should not go into the fix. The printed "Z ≠ M" is on the page image; the text extraction's "Z = M" at line 1721 is an extraction artifact. No compile was run; the Lean evidence was read only.

I did this directly, without spawning agents: this subagent session has no agent-spawning tool, and the check was small.

## vote 28: correct

Quote: Rem 6.5 (Semigroup Forum p. 157, checked on the page image): "For example, take M = Z/2Z, S = Spec(Z), X = S endowed with the trivial action of D(M) and U = D(M) endowed with the non-trivial action of itself by multiplication. Then the D(M)-equivariant morphism U → S is smooth of relative dimension zero and so it is étale; but U^{D(M)} = ∅, X^{D(M)} = X and therefore U^{D(M)} ≇ X^{D(M)} ×_X U."

Rem 6.6: "Choose an exact sequence of abelian groups 0 → Z → M → M/Z → 0 with Z ≠ M and M/Z finite. Then f : D(M) → D(Z) is étale, surjective and D(M)-equivariant. Put U = D(M) and X = D(Z). Since U^{D(M)} = X^{D(M)} = ∅, f is FPR. Now f is not Z-FPR because U^{D(M/Z)} = ∅ and X^{D(M/Z)} = X."

Fix: Rem 6.5: replace S = Spec(Z) by S = Spec(Z[1/2]). More generally, take S nonempty and M finite nonzero with |M| invertible on S. Then replace "smooth of relative dimension zero and so it is étale" by "étale, since 2 is invertible on S". The rest of the sentence stands, and so does the general claim "not an isomorphism in general".

Rem 6.6: fix a nonempty scheme S and write D(M)_S, D(Z)_S. Add the hypotheses Z ≠ 0 and [M:Z] invertible on S. The rest reads as printed. Example: M = Z, Z = 2Z, S = Spec Z[1/2], f the squaring map on G_m. No finite-generation hypothesis on M is needed: R[M] is finite free over R[Z], so it is finitely presented. Lean adds M f.g. only for convenience.

Reason: Standing hypotheses of §6: M abelian, S a scheme, X a quasi-separated S-space with a D(M)_S-action. Def 6.1(iv) requires an atlas to be étale, surjective and a disjoint union of stable S-affine schemes. All the examples meet these, since they are affine over S. The only failures are the ones below.

**Rem 6.5, line by line**
- D(Z/2) over Spec Z is Spec Z[t]/(t²−1) = μ₂, by Def 2.4.
- Ω over Z is generated by dt with relation 2t dt = 0. Since t is a unit, Ω = (Z[t]/(t²−1))/2, which is nonzero.
- The fibre at 2 is F_2[t]/(t−1)², which is nonreduced. So U → S is neither unramified nor smooth, and "smooth of relative dimension zero" is false at 2.
- The other assertions hold even over Z. U^{D(M)} = ∅: a fixed point over T≠∅ would force the universal t to equal 1 in the free O_T-module with basis 1, t. And X^{D(M)} = X.
- So only étaleness fails, and the example does not meet the étale hypothesis of the remark. Over Z[1/2] it does, because Z[1/2][t]/(t²−1) = Z[1/2]×Z[1/2].

**Rem 6.6, étale**
- f is a D(M/Z)-torsor, since R[M] is Z-graded... more precisely M/Z-graded over R[Z] with invertible graded pieces. By fppf descent along the faithfully flat D(Z)_S → S, f is étale iff D(M/Z)_S → S is étale, iff [M:Z] is invertible on S.
- The print writes D(M) with no subscript. By Def 2.4 that is over Spec Z, where the index is >1 because Z ≠ M, so it is never invertible. On that reading the étale claim fails for every allowed Z. With the standing general S, it fails whenever [M:Z] is not invertible on S.
- Concrete case: M = Z, Z = 2Z, squaring on G_m over Z is not étale at 2.

**Rem 6.6, Z = 0**
- Z = 0 with M finite nonzero satisfies the printed "Z ≠ M and M/Z finite".
- Then X = D(0) = S with trivial action, so X^{D(M)} = X ≠ ∅, contradicting "X^{D(M)} = ∅".
- f is then not FPR: U^{D(M)} = ∅ but X^{D(M)} ×_X U = U. This is exactly the situation of Rem 6.5, so the print contradicts itself.

**Rem 6.6, corrected version verified**
- Surjective: R[Z] → R[M] is integral and injective.
- Equivariant: yes.
- FPR for Z ≠ 0: a fixed point of X over T≠∅ would force 1·z = 1·0 in the free basis of O_T[M] for some z ≠ 0 in Z, which is impossible. So U^{D(M)} = X^{D(M)} = ∅.
- Not Z-FPR: D(M/Z) acts freely on U, so U^{D(M/Z)} = ∅, using M/Z ≠ 0 and S nonempty. It acts trivially on X, because it is the kernel of D(M) → D(Z).
- S nonempty is a trivial extra hypothesis, since over S = ∅ everything is empty.

**Lean evidence** (read only, not compiled; no sorry in these two files)
- `not_etale_printed_rem65`, `rem65`, `rem65_zmod2` and `rem66` are in AlgMag/SecLeftoverFPR.lean; `not_formallyUnramified_int_zmod2` is in AlgMag/SecLeftoverEtale.lean.
- `rem66` assumes Z ≠ ⊥, Z ≠ ⊤, finite index, index a unit and R nontrivial. This matches the fix, and it also carries the extra AddGroup.FG M. STATUS.md records that finite index suffices.

Neither failure touches the purpose of the remarks: non-FPR étale maps exist for torsion M, and FPR atlases need not be strongly-FPR. Both survive with the added hypotheses.

## vote 29: partly

Quote: Statement, p. 179: "Then the morphism X^N → X^{N*} is an affine space fibration." Proof, p. 180 (checked on the page image): "Since the action a is Zariski locally linearizable, we reduce to the case where X is affine over S." ... "the conormal sheaf I/I² is finite locally free hence projective." ... "The A_0-module (I/I²)_n is projective because it is a direct summand of I/I², and so the surjection A_n → (I/I²)_n admits a section s_n : (I/I²)_n → A_n." ... "It is enough to show that this morphism is an isomorphism." ... "So, using [32, Tag 007V], we reduce to the case where A is a ring."

Fix: Leave the statement of Thm 12.4 unchanged. Change the first sentence of the proof to: "Since the action a is Zariski locally linearizable, we reduce to the case where S is affine and X is affine over S." The rest of the proof then works as printed: A_0 is a ring and I/I² is a finite projective A_0-module. The later reduction via Tag 007V becomes unnecessary but does no harm. Read "affine space fibration", which the paper never defines, as Zariski locally on the target X^{N*} of the form A^n. Over each stable S-affine chart above an affine open of S, the map is Spec Sym(P) with P finite projective. In STATUS.md, replace "Zariski-locally on S" with "Zariski-locally on X^{N*}". Cor 12.5 needs no change. There A_n = O_S·χ^n, so (I/I²)_n is a locally free quotient of O_S, which is an isomorphism on a clopen subset and zero elsewhere. The sections s_n therefore exist globally and are unique.

Reason: This is a real gap in the proof, not a misprint or a reading problem, but the statement is fine. The correction is right about the gap and its counterexample. It is imprecise about where the statement is local.

The gap: the sections s_n are taken while S and X^0 are still non-affine, and the proof only reduces to a ring afterwards. A finite locally free sheaf is not a projective object on a non-affine scheme, and the obstruction to s_n lies in H^1.

The counterexample, checked by hand: take S = P^1_k, M = Z, N = ℕ, A_0 = O, A_1 = O·x, and A_2 = E = O(1)², where 0 → O·x² → E → O(2) → 0 is the twisted Euler sequence. Let A = Sym(Ox ⊕ E)/(x² − ι(1)), which is locally O[x,y] with y' = g y + c x². Then:
- X is S-affine, smooth and G_m-stable, so it satisfies Def 7.2.
- (I/I²)_2 = O(2), and a section s_2 would split E, which is impossible because O(1)² is not O ⊕ O(2).
- So no graded isomorphism Sym(I/I²) ≅ A exists, and the printed global reduction "It is enough to show that this morphism is an isomorphism" has no valid Φ.
- The theorem still holds on the two standard affines of P^1.

Is the statement meant locally? Yes, and the print already forces this: its first sentence localizes on X, which only makes sense for a notion local on the target. But "Zariski-locally on S" is the wrong description. For S = Spec k that condition is empty, and for X non-affine over S the local form exists only around points of X^{N*}. The Lean theorem `thm124_attP` (FixesThm124.lean:75) has exactly this form: around each point over X^{N*} there is a chart, with Sym over every affine open V of S. I read this file but did not compile it.

Is reducing to S affine legitimate? Yes. Being a fibration is local on the target, attractors commute with the base change V ⊂ S, and Prop 3.31 leaves S unchanged. It also supplies the quasi-compactness of S that the agreed correction to Prop 8.5 requires.

Does any later use need the global form? No. A search of am.txt finds only three other mentions: intro item (xii), which just repeats the statement; attribution (j); and Cor 12.5. Cor 12.5 is global on S but is unaffected, by the rank-one argument in the fix and by `cor125_global` (FinalCor125.lean:312). Nothing after §12 cites Thm 12.4 or Cor 12.5. The only global claim lost is the graded vector bundle structure X^N = Spec Sym(I/I²) on non-affine S, and the print never states that as a result.

Not checked: whether the example X is a non-equivariant vector bundle over P^1. The question does not depend on it.

## vote 30: partly

Quote: Semigroup Forum, p. 187, checked on the page image: "(vi) Let a be the action of D(Z/6Z) on D(Z/6Z) × D(Z/6Z) × D(Z/6Z) given by λ · (x, y, z) = (λx, λ²y, λ³z). Then ℧(a) = {Z/6Z, 2Z/6Z, 3Z/6Z, 6Z/6Z}."

Fix: Keep the group, the formula and the four-element list. Change only the space: "Let a be the action of D(Z/6Z) on A(N) × A(N) × A(N) = A³ given by λ · (x, y, z) = (λx, λ²y, λ³z)." The conclusion ℧(a) = {Z/6Z, 2Z/6Z, 3Z/6Z, 6Z/6Z} then holds as printed, for S nonempty. If the space is kept as printed, the only correct conclusion is ℧(a) = {0, Z/6Z}, which is what STATUS.md records. The Lean theorem `pureMagnets_zmod_six` audits the printed reading only, so the corrected A³ form has no Lean statement yet.

Reason: This is a real error in the print, and it is most likely a misprint in the space, not in the list. The Lean result is right about the printed text, but "D(Z/6Z) vs A(Z/6Z)" is not the source of the error.

1. Coordinates are units in the print. On D(Z/6Z)³ the coordinates x, y, z are units of degrees 1, 2, 3 (μ6 coordinates, x⁶ = 1). For a group M, X^N is cut out by the homogeneous elements of degree outside N. Every proper submonoid of Z/6Z misses degree 1, so it kills the unit x and X^N = ∅. Only X^{Z/6Z} = X survives. So there are two attractor spaces, ∅ and X, and ℧(a) = {0, Z/6Z}. `pureMagnets_zmod_six` (Sec15PureMagnets.lean:743) proves this from the units y, z alone. The paper agrees with itself here: Example 15.10(ii) gives {0, Z^n} for D(Z^n) on itself, and Remark 6.5 gives U^{D(M)} = ∅ for D(Z/2Z) on itself.

2. D vs A(Z/6Z) is not the source. Z/6Z is a group, so A(Z/6Z) = Spec Z[Z/6Z] = D(Z/6Z) literally. Swapping those letters changes nothing. No choice of weights can help either: if the coordinates are units whose degrees generate a subgroup H, then X^N = X when N ⊇ H and ∅ otherwise. That always gives at most two pure magnets, never four.

3. The printed list matches A³ exactly (hand computation, no compile). Take X = Spec Z[x,y,z] with degrees 1, 2, 3. The submonoids of Z/6Z are exactly the four subgroups.
- X^{0} is the origin.
- X^{2Z/6Z} = {x = z = 0}, the y-axis.
- X^{3Z/6Z} = {x = y = 0}, the z-axis.
- X^{Z/6Z} = A³.
These are four distinct spaces from four magnets, so all four are pure, which is the printed list including 6Z/6Z = 0. This is also the only setting where the weights (1, 2, 3) do anything.

What remains an inference is the author's intent, since the paper does not state it. A(N)² with weights 2, 3 would give the same list, but A³ stays closest to the printed formula. I read "A(N)" as the likely original because the neighbouring items (ii), (iii), (v) and (vii) all use A(N)-type spaces.

## vote 31: partly

Quote: Semigroup Forum p. 187 (PDF p. 62), read from the page image: "(vi) Let a be the action of D(Z/6Z) on D(Z/6Z) × D(Z/6Z) × D(Z/6Z) given by λ · (x, y, z) = (λx, λ²y, λ³z). Then Ʊ(a) = {Z/6Z, 2Z/6Z, 3Z/6Z, 6Z/6Z}."

Fix: Keep the printed list and action. Change the space to A(N) × A(N) × A(N) = A^3, the notation of (ii), (iii) and (v). The list is then correct. If the space D(Z/6Z)^3 is kept instead, the list must become {0, Z/6Z}, assuming S nonempty. The suggested swap D(Z/6Z) to A(Z/6Z) is not a fix: by Def 2.4 (iv) and §1.1 these are the same object, so it changes nothing.

Reason: The correction is mathematically right for the example as printed, but its diagnosis needs changing.

**Refutation attempt.** I assumed the print is right.
- The coordinate ring of X is Z[x,y,z]/(x^6-1, y^6-1, z^6-1), with x, y, z homogeneous of degrees 1, 2, 3 in Z/6.
- Each of x, y, z is a unit, because x^6 = 1 and likewise for y and z.
- By Def 1.1, a T-point of X^N is an equivariant map A(N)_T -> X_T, that is, a Z/6-graded map from this ring to O_T[N].
- For a proper subgroup N, some coordinate has degree outside N: z has degree 3, which is outside 2Z/6; y has degree 2, which is outside 3Z/6. That coordinate maps to 0.
- A unit mapping to 0 forces T to be empty. So X^N is empty for every N other than Z/6, in every characteristic. Char 2 and char 3, where mu_6 is nonreduced, offer no escape, because the argument is on the grading and not on points.
- All submonoids of Z/6 are subgroups, so there are exactly two attractors: the empty one and X.
- Thm 15.3 gives a bijection between Ʊ(a) and the attractors, so |Ʊ(a)| = 2. Prop 15.1 (i) shows 2Z/6 and 3Z/6 are not pure, since X^0 = X^{2Z/6} = X^{3Z/6}. Hence Ʊ(a) = {0, Z/6}, and the printed four-element list contradicts the paper's own Thm 15.3.
- The other readings do not rescue the print. Example 15.10 (ii) already gives {0, Z^n} for the self-action of D(Z^n), which is the same phenomenon. Any product of copies of D(Z/6) gives at most two elements, because the coordinates are always units.

**Where the proposed diagnosis is off.** The question offered "D(Z/6Z) vs A(Z/6Z)" as a possible misprint. That cannot be the source: the paper defines D(M) as A(M) when M is a group (line 127 of am.txt and Def 2.4 (iv)), so the two are identical.

**Likely source, my inference.** The print's list is exactly right for A^3 = A(N^3) with weights (1,2,3), by hand computation:
- X^0 is the origin.
- X^{2Z/6} is the y-axis, {x = z = 0}.
- X^{3Z/6} is the z-axis, {x = y = 0}.
- X^{Z/6} is A^3.

These are four distinct attractors, so all four subgroups are pure. Nothing in the print confirms that A(N)^3 was intended; the match with the list is the evidence. This A^3 computation is not in Lean.

**Lean evidence.** `pureMagnets_zmod_six` (Sec15PureMagnets.lean:743) is stated for an abstract Z/6-graded algebra A ≠ 0 with homogeneous units in degrees 2 and 3. It does not instantiate the actual ring of D(Z/6)^3, though its hypotheses clearly hold there. The STATUS.md line "two elements, not the four printed" is accurate only for the space as printed, and it needs S nonempty, since for S empty Ʊ(a) = {0}. Lean was not re-run for this check.

C:\Users\Arnaud\Desktop\algmag-stacks\STATUS.md could add the A^3 reading to its Example (vi) correction.

## vote 32: correct

Quote: Algebraic Magnetism, p. 187 (read from the page image): "(vi) Let a be the action of D(Z/6Z) on D(Z/6Z) × D(Z/6Z) × D(Z/6Z) given by λ · (x, y, z) = (λx, λ²y, λ³z). Then ℧(a) = {Z/6Z, 2Z/6Z, 3Z/6Z, 6Z/6Z}." Standing hypotheses, §15, p. 184: "Let M be an abelian monoid. Let X be a separated algebraic space over S endowed with an action a of A(M)_S." Notation, Def. 2.4: "If N = M is an abelian group, then A(M) is denoted D(M)".

Fix: As printed, the example should read ℧(a) = {0, Z/6Z}. The likely intended space is A(N) × A(N) × A(N) = A³ with the same formula, and then the printed four-element list is correct. Proposed wording: "(vi) Let a be the action of D(Z/6Z) on A(N) × A(N) × A(N) given by λ·(x,y,z) = (λx, λ²y, λ³z). Then ℧(a) = {Z/6Z, 2Z/6Z, 3Z/6Z, 6Z/6Z}." The source cannot be "D(Z/6Z) vs A(Z/6Z)": by Def. 2.4 these are the same scheme, so that swap changes nothing. The replacement space must be A(N)³, and that this was the author's intent is my inference, not something the print states. The STATUS.md line ("two elements, not the four printed") is accurate. It could add that the list is right for A³.

Reason: Hypotheses: M = Z/6 is an abelian monoid. X = D(Z/6)³ is affine over Spec Z, so it is separated, and it is nonempty. There is no subscript, so S = Spec Z (Def. 2.4, Rem. 2.5). The formula is a well-defined action of μ_6 on μ_6³. The example meets every standing hypothesis of §15.

Coordinates are units: A = Z[x,y,z]/(x⁶−1, y⁶−1, z⁶−1) is Z/6-graded with deg x = 1, deg y = 2, deg z = 3, and x, y, z are units.

Direct check from the definition of X^N. A T-point of X^N, for T = Spec R, is a graded R-algebra map φ: A_R → R[N].
- The submonoids of Z/6 are exactly {0}, 2Z/6, 3Z/6 and Z/6 (enumerated by script). Here 6Z/6Z = 0.
- If N ≠ Z/6 then 1 ∉ N, so R[N] has zero component in degree 1 and φ(x) = 0. Since x is a unit, R[N] = 0, and hence R = 0 because R embeds in R[N].
- So X⁰ = X^{2Z/6} = X^{3Z/6} = ∅, while X^{Z/6} = X ≠ ∅.

Applying Prop. 15.1(ii), "X^N = X^L ⇒ N ⊂ L":
- N = 2Z/6 fails with L = 0, because X^N = X⁰ but 2Z/6 is not contained in 0.
- N = 3Z/6 fails the same way.
- N = 0 passes trivially.
- N = Z/6 passes, because X^L = X forces L = Z/6.

Therefore ℧(a) = {0, Z/6Z}, and the printed elements 2Z/6Z and 3Z/6Z are not pure. Geometrically, the action is free, so every nontrivial subgroup D(M/N) has empty fixed locus. This is the same behaviour as Ex. 15.10(ii), {0, Zⁿ}, in the paper itself.

Changing the weights cannot rescue the print. For any weights on D(Z/6)³, with G the subgroup they generate, X^N is ∅ unless G ⊂ N, so ℧(a) = {0, G}, which has at most 2 elements.

Check of the repair on A³ (hand computation, confirmed by a script enumeration over monomials): the ideals are J_{Z/6} = 0, J_{2Z/6} = (x,z), J_{3Z/6} = (x,y), J_0 = (x,y,z). These are four distinct closed subschemes. All four subgroups are therefore pure, which is exactly the printed list. This suggests a slip in the space rather than in the list.

Lean: pureMagnets_zmod_six (Sec15PureMagnets.lean:743) is an abstract statement about a Z/6-graded algebra A ≠ 0 with homogeneous units in degrees 2 and 3. Its proof goes through pureMagnets_eq_of_units. It matches the argument above, using y and z instead of x. I read it but did not compile it, as instructed. The instantiation at the coordinate ring of D(Z/6)³ exists only in its docstring, and the A³ list is not in Lean. Both rest on the hand argument above, which is complete on its own. REMARKS.md:56 "Self-actions, Ex (vi)" refers to a different example, in the self-actions paper, not this one.

## vote 33: correct

Quote: Semigroup Forum 113, p. 179, Theorem 12.4: "Assume that X is smooth over S and that the action a of D(M)_S on X is Zariski locally linearizable (cf. Sect. 7). Assume that N is finitely generated as monoid or that X is quasi-compact over S. Then the morphism X^N → X^{N^*} is an affine space fibration."

p. 180, proof (checked on the page image): "So by [32, Tag 063M] the conormal sheaf I/I^2 is finite locally free hence projective." ... "The A_0-module (I/I^2)_n is projective because it is a direct summand of I/I^2, and so the surjection A_n → (I/I^2)_n admits a section s_n : (I/I^2)_n → A_n." ... "Now s induces a morphism of A_0-algebras Φ : Sym_{A_0}(I/I^2) → A. It is enough to show that this morphism is an isomorphism." ... "So, using [32, Tag 007V], we reduce to the case where A is a ring."

Standing hypotheses of §12, p. 178: "Let M be a finitely generated abelian group. Let X be an S-algebraic space locally of finite presentation endowed with an action of D(M)_S."

Def 7.2: "The action of D(M)_S on X is Zariski locally linearizable if there are S-affine open D(M)_S-stable subspaces of X covering X."

Fix: Keep the statement of Thm 12.4 and read "affine space fibration" as Zariski-locally on X^{N^*} of the form A^n. The paper never defines the term. Its only other occurrence is intro item (xii).

Repair the proof with one sentence after "we reduce to the case where X is affine over S": "The assertion is Zariski local on S, so we may also assume S affine." Then A_0 is a ring, I/I^2 is a finite projective A_0-module, the sections s_n exist, and the rest of the proof runs unchanged. The sentence about sheafification and Tag 007V becomes unnecessary.

The conclusion is: over each affine open V of S and each stable S-affine chart, X^N is Spec Sym_{A_0}(P) with P finite projective over A_0, so it is Zariski-locally A^n over X^{N^*}. No global Sym isomorphism over non-affine S should be claimed.

Cor 12.5 needs no change to its statement. Its proof should note that the sections exist globally there (see reason).

Reason: I verified the counterexample by hand, not in Lean.

**Construction.** Let k be a field, S = P^1_k, and glue over charts with coordinates t and s = 1/t.
- A = O[x,y] on U_0 and O[x',y'] on U_1.
- The gluing is x' = x, y' = t^2 y + t x^2, so g = t^2 and c = t in the STATUS.md notation.
- This is an automorphism of k[t,1/t][x,y], with inverse y = t^{-2}(y' - t x'^2).
- It is homogeneous for deg x = 1, deg y = 2, so A is a quasi-coherent N-graded O_S-algebra.

**Printed hypotheses.**
- M = Z is finitely generated, as §12 requires.
- N = ℕ is a magnet (any submonoid is) and is finitely generated, so the "N f.g. or X quasi-compact" hypothesis holds. N is fine and sharp, with N^* = 0.
- X = Spec_S A is locally A^2_S, so it is smooth and locally of finite presentation over S.
- The grading gives the D(Z)_S-action. X itself is an S-affine stable open covering X, so Def 7.2 holds.

**Objects in the proof.** By Thm 3.20, X^N = X and X^0 = Spec_S A_0 = S, with I = ⊕_{n≥1} A_n.

Locally I = (x,y) and I^2 = (x^2, xy, y^2), so I/I^2 has only degrees 1 and 2.
- (I/I^2)_1 = O x.
- (I/I^2)_2 = A_2/O x^2. Its generator satisfies ybar' = t^2 ybar. Sections a ybar = a' ybar' force a = t^2 a'(1/t), which gives dimension 3, so this quotient is O(2).

So I/I^2 = O ⊕ O(2) is finite locally free, but it is not projective in QCoh(P^1). That falsifies "finite locally free hence projective".

**The section s_2 does not exist.** A section would be ybar ↦ y + b x^2 on U_0 and ybar' ↦ y' + b' x^2 on U_1, with b in k[t] and b' in k[1/t]. Compatibility gives t + b' = t^2 b. The t^1 coefficient is 1 on the left and 0 on the right, a contradiction. So 0 → O → A_2 → O(2) → 0 is the non-split generator of Ext^1(O(2),O) = H^1(O(-2)) = k. The printed order of steps is as claimed: the sections are chosen before "we reduce to the case where A is a ring".

**Stronger fact, not in STATUS.md: X → S is not a vector bundle for any structure.**
1. Suppose φ : X ≅ Spec Sym E over S.
2. Translate by the section φ(zero section), so that φ^* sends (E) into I and E ≅ I/I^2.
3. The composite O(2) ⊂ I/I^2 ≅ E → I → A_2 → (I/I^2)_2 = O(2) is the identity, using that the projection onto degree 2 is O-linear and compatible with the grading on I/I^2.
4. That splits A_2 → O(2), which contradicts the previous paragraph.

So a global Sym or vector-bundle reading of Thm 12.4 is false. Only the local reading survives.

**The theorem survives.** The example is Zariski-locally A^2 over S, as the local reading requires. The print's own first step, reducing to stable S-affine opens, already only makes sense for a property that is local on X^{N^*}. So the local reading is the intended one, and it matches classical Bialynicki-Birula. The STATUS.md phrase "Zariski-locally on S" is correct but slightly weak: the fibration is local on X^{N^*}, as `thm124_affineSpace` in Sec12Final.lean states (A^n over an open V of X^{N^*}). The Lean evidence is consistent: `thm124_attP` gives Sym only over affine opens V of S. There is no Lean formalization of the P^1 example itself.

**Later uses.** A text search for "12.4" and "fibration" finds three places besides the statement and proof: intro (xii) at line 242, the inspiration note (j) at line 310, and Cor 12.5.
- Intro (xii) and (j) need nothing global.
- Cor 12.5 claims a global "vector bundle" and says it "follows from the proof of Theorem 12.4". It is safe. Here A_n = O_S e^n is free, so A_n → (I/I^2)_n is a surjection from O_S onto a locally free sheaf of rank at most 1. It is therefore an isomorphism on a clopen locus and zero on the complement, so s_n exists globally.
- Independently, `cor125_global` (FinalCor125.lean) proves N is free and A(N)_S is the trivial bundle.

So no later result needs the global form.

Source: am.txt lines 2872-2873, 2975-3057, 1800-1802 and the rendered PDF p. 180, at C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\amimg124\p-55.png. Lean evidence and the correction entry are in C:\Users\Arnaud\Desktop\algmag-stacks\STATUS.md line 287.

## vote 34: partly

Quote: Rem 2.9 (p.135): "is not free because the orbits of (2, 3) and (3, 4) have non-trivial intersection (e.g. the intersection contains (4, 5)) but are different (e.g. (3, 4) is not in the orbit of (2, 3))."
Fact 15.11 (p.186): "We have mk(Z^n) = n + 1." Same page: "The emptyset generates the zero monoid."
Conj 15.7 (p.186): "We conjecture that the conclusion of Theorem 15.4 remains true without the additional assumption (i),(ii) or (iii)."
Prop 14.4 proof (p.184): "If N = Z is a group, the last assertion follows from Corollary 8.1."
Prop 2.19 proof (pp.137-138): "So by [32, 0ET0] the scheme A(N')_R is the push-out, in the category of schemes, of the diagram".
Ex 15.10(ii) (p.186): "Let a be the action of D(Z^n) on itself by multiplication. Then Ω(a) = {0, Z^n}." (Ω stands in for the print's pure-magnet symbol.)
Rem 2.5 (p.131 by PDF offset, PDF p.9): "We like to use standard notation and see A(N)_B and D(M)_B as base change from Spec(Z) to B of A(N) and D(M)."

Fix: Keep four items and drop two.

KEEP:
- Rem 2.9: replace (4, 5) with (5, 6). The rest of the sentence stands.
- Fact 15.11: add n >= 1. This is an edge case only.
- Conj 15.7: delete "or (iii)", so it reads "(i) or (ii)".
- Prop 14.4 proof: replace "Corollary 8.1" with "Proposition 8.1". This is only the citation slip; the separate falsity of the last assertion is not assessed here.

DROP:
- Prop 2.19 / Tag 0ET0: the print is right. Remove this item from STATUS.md (Paper corrections line 299 and the Prop 2.19 row, line 43). Also remove it from REMARKS.md:14 ("Forced: map not integral") and from the docstring at AlgMag/GeneralBasePushout.lean:15. GeneralBaseMilnor can stay as a Lean proof of 0ET0, since Mathlib-side work still needs it, but it is not a correction to the paper.
- Ex 15.10(ii) / S empty: the print is right. STATUS.md:305 already withdraws it.

No files were edited.

Reason: Four items survive the refutation attempt and two do not.

RIGHT:
- Rem 2.9: N = {0,2,3,...}. The orbit of (2,3) is (2,3),(4,5),(5,6),... and the orbit of (3,4) is (3,4),(5,6),(6,7),.... (4,5) would need n = 1 applied to (3,4), and 1 is excluded. So (4,5) is not in the intersection, and the smallest common element is (5,6) = (2,3)+3 = (3,4)+2. The conclusion "not free" still holds. Confirmed on the page image.
- Fact 15.11: Z^0 = 0, and the print itself says the empty set generates the zero monoid, so mk = 0, not 1. The print states no n >= 1. The proof's contradiction ("linked") also fails for the empty family. This is true but trivial. Lean `monoidRank_int_pi` carries hn : 0 < n.
- Conj 15.7: Thm 15.4 lists only (i) and (ii), and its proof treats only those two cases. "(iii)" points at nothing. The Thm 15.4 list was read from am.txt; only the Conj 15.7 wording was read on the page image.
- Prop 14.4: Section 8 contains Prop 8.1, Rem 8.2, Thm 8.3, Rem 8.4 and Prop 8.5, and the list of numbered Corollaries in am.txt has no 8.x. Prop 8.1 is the closed-subspace result meant here.

WRONG:
- Prop 2.19 / Tag 0ET0: I fetched the live tag (Stacks Lemma 37.14.1). Its hypotheses are: "Let A' -> A be a surjection of rings and let B -> A be a ring map. Let B' = B x_A A' ... is a pushout of schemes." It has no integrality or finiteness hypothesis on B -> A. The print applies it with A' = R[L'], A = R[L], B = R[N], B' = R[N']. A' -> A is surjective because L is a face of L', and the print establishes R[L'] x_{R[L]} R[N] = R[N']. So the hypotheses are met exactly. "A(L) -> A(N) is not integral" is true but irrelevant; it seems to confuse 0ET0 with an integral-type pushout lemma. The repo's own AlgMag/GeneralBaseMilnor.lean:11-14 says its no-finiteness statement "is what the proof of Proposition 2.19 needs from [Stacks, 0ET0]", which is the tag's own content.
- Ex 15.10(ii) / S empty: the print writes D(Z^n) with no subscript, and Rem 2.5 reads that as over Spec Z, which is nonempty. There, an equivariant map A(N)_T -> D(Z^n)_T forces e_m -> c_m e_m with c_m a unit, so every m lies in N when T is nonempty. So X^N is empty unless N = Z^n, and the pure magnets are exactly {0, Z^n}. The n = 0 case also holds. S empty is only a generalization the print never states. Sec 15 does open with a general S, but the literal print is proved by `ex1510_ii_Zn`, and STATUS.md:305 records the same withdrawal.

Limits: I did not compile the Lean; those names are cited from source and STATUS.md. The work was done directly, without sub-agents, because this step needed only reading and the live tag check.

## vote 35: partly

Quote: Rem 2.9 (p.135): "the orbits of (2, 3) and (3, 4) have non-trivial intersection (e.g. the intersection contains (4, 5))". Fact 15.11 (p.186): "We have mk(Z^n) = n + 1." Conj 15.7 (p.186): "remains true without the additional assumption (i),(ii) or (iii)." Thm 15.4 (p.185) lists only "(i) X is affine over S, (ii) M is a group and there exists an S-affine strongly-FPR atlas for X". Prop 14.4 proof (p.184): "If N = Z is a group, the last assertion follows from Corollary 8.1." Prop 2.19 proof (p.138): "So by [32, 0ET0] the scheme A(N')_R is the push-out, in the category of schemes". Ex 15.10 (p.186): "(ii) Let a be the action of D(Z^n) on itself by multiplication. Then Π(a) = {0, Z^n}." Stacks Lemma 37.14.1 (Tag 0ET0), read live: "Let A' \to A be a surjection of rings and let B \to A be a ring map. Let B' = B \times_A A' be the fibre product of rings. [...] is a pushout of schemes."

Fix: Four changes to the paper, all keeping the statements. (1) Rem 2.9: replace "(4, 5)" with "(5, 6)". (2) Fact 15.11: "We have mk(Z^n) = n + 1 for n >= 1." (3) Conj 15.7: "without the additional assumption (i) or (ii)." (4) Prop 14.4 proof: "Corollary 8.1" becomes "Proposition 8.1". This fixes only the pointer. Prop 8.1 needs a Z-FPR atlas, so the already agreed correction of the last assertion still stands. No change to the paper for two items. (5) Prop 2.19: the citation is correct. (6) Ex 15.10(ii): the print is correct. On the project side: remove the "Prop 2.19, citation" entry from "To review" in C:\Users\Arnaud\Desktop\algmag-stacks\STATUS.md. Change the STATUS.md row "Tag 0ET0 replaced by GeneralBaseMilnor" and the C:\Users\Arnaud\Desktop\algmag-stacks\REMARKS.md row "Forced: map not integral", and fix the docstring in C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\GeneralBasePushout.lean. They should say GeneralBaseMilnor reproves Tag 0ET0 in Lean, and that nothing in the print forced this.

Reason: The bundle mixes four right items with two wrong ones. I read every printed passage on the PDF page images (pp.135, 138, 184, 186, 187).

- **Rem 2.9: misprint, correction right.** The orbit of (2,3) is (2,3), (4,5), (5,6), ... and the orbit of (3,4) is (3,4), (5,6), (6,7), ... Reaching (4,5) from (3,4) needs n = 1, which is not in N \ {1}. The point (5,6) = 3·(2,3) = 2·(3,4) works. The remark's conclusion is unaffected, and the rest of its argument ("(3, 4) is not in the orbit of (2, 3)") is correct. Lean: `not_isFreeAction_natNeOne`.

- **Fact 15.11: real but degenerate boundary failure, correction right.** The print itself says "The emptyset generates the zero monoid", so mk(Z^0) = 0, not 1. The proof tacitly takes n >= 1, since at n = 0 the empty relation gives no contradiction. Lean: `monoidRank_int_pi`, with hypothesis 0 < n. The printed "p_1, ..., p_n > 0" in the proof is harmless, because such a choice exists and >= 0 already suffices.

- **Conj 15.7: misprint, correction right.** Thm 15.4 has only (i) and (ii), and I found no (iii) elsewhere. This looks like a leftover from an earlier list, though that origin is my inference. The content of the conjecture is unchanged.

- **Prop 14.4: misprint, correction right.** "Corollary 8.1" occurs exactly once in the text and no such item exists. §8 numbers Prop 8.1, Rem 8.2, Thm 8.3, Rem 8.4, Prop 8.5, and Prop 8.1 is the closed-immersion statement for X^Z. The print is also loose about labels elsewhere ("Lemma 2.19", "Proposition 8.3"). I could not check the PDF hyperlink target because the pymupdf import failed.

- **Prop 2.19: correction wrong, the print is fine.** Tag 0ET0 has no integrality or finiteness hypothesis: only A' -> A surjective and B -> A arbitrary. Here A' = R[L'], A = R[L] (surjective because L is a face of L'), B = R[N] and B' = R[N'], which is exactly the fibre product the printed proof computes. That A(L) -> A(N) is not integral (for example N = 0, L = ℕ) is true but irrelevant. The Lean docstring of `GeneralBaseMilnor` states this same no-finiteness result and calls it what the proof needs from 0ET0, so it reproves the tag. The "Forced" label is wrong. The other Tag 0ET0 uses, in the proof of Fact 11.8, have the same shape, though I checked them less closely.

- **Ex 15.10(ii): correction wrong, reading problem.** STATUS.md already lists this as withdrawn. Without a subscript, D(Z^n) is over Spec Z (Def 2.4, Rem 2.5), and item (ix) uses A(M)_S when a base is meant. By hand: a graded map Z[Z^n] -> R[N] sends X^m to r_m X^m with r_m a unit, so X^N is empty for N != Z^n once R != 0. Hence X^0 is empty, X^{Z^n} = X, and Π(a) = {0, Z^n}, which also holds at n = 0. Lean: `ex1510_ii_Zn`. `ex1510_ii_empty` concerns only the generalization to an empty S, which the paper never states.

Read-only: no files were changed and nothing was compiled. Rendered pages are in C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\chk.

## vote 36: partly

Quote: Rem 2.9 (p.135): "the orbits of (2, 3) and (3, 4) have non-trivial intersection (e.g. the intersection contains (4, 5)) but are different (e.g. (3, 4) is not in the orbit of (2, 3))."
Fact 15.11 (p.186): "We have mk(Z^n) = n + 1." Def 15.9 preamble: "The emptyset generates the zero monoid."
Conj 15.7 (p.186): "We conjecture that the conclusion of Theorem 15.4 remains true without the additional assumption (i),(ii) or (iii)."
Prop 14.4, proof (p.184): "If N = Z is a group, the last assertion follows from Corollary 8.1."
Prop 2.19, proof (pp.137-138): "We have R[L'] x_{R[L]} R[N] = {(x, y) in R[L'] x R[N] | f(x) = g(y)} = R[N'] ... So by [32, 0ET0] the scheme A(N')_R is the push-out, in the category of schemes, of the diagram".
Ex 15.10(ii) (p.186): "Let a be the action of D(Z^n) on itself by multiplication. Then U(a) = {0, Z^n}."
Stacks 0ET0 (Lemma 37.14.1, fetched live 2026-11-06): "Let A' -> A be a surjection of rings and let B -> A be a ring map. Let B' = B x_A A' be the fibre product of rings. ... is a pushout of schemes."

Fix: Keep these four corrections:
- Rem 2.9: replace "(4, 5)" by "(5, 6)".
- Fact 15.11: add "for n >= 1".
- Conj 15.7: replace "(i),(ii) or (iii)" by "(i) or (ii)".
- Prop 14.4, proof: replace "Corollary 8.1" by "Proposition 8.1". This still needs the Z-FPR hypothesis from the separate agreed correction to the last assertion.

Drop these two:
- Prop 2.19: the citation of Tag 0ET0 is correct, so no correction. Remove the entry at C:\Users\Arnaud\Desktop\algmag-stacks\STATUS.md line 299. Reword REMARKS.md line 14 ("Forced: map not integral") and the docstring in C:\Users\Arnaud\Desktop\algmag-stacks\AlgMag\GeneralBasePushout.lean lines 15-16. GeneralBaseMilnor is simply a Lean proof of the content of 0ET0, and the departure is not forced by the print being wrong. I did not check whether Mathlib has this lemma, so do not state a reason beyond that.
- Ex 15.10(ii): no correction, as STATUS.md line 305 already says.

No files were edited.

Reason: Four of the six items are correct. Two are wrong: the print is fine.

**Rem 2.9: correct.** N = {0,2,3,...}.
- The orbit of (2,3) is (2,3), (4,5), (5,6), ...
- The orbit of (3,4) is (3,4), (5,6), (6,7), ...
- (4,5) would need n = 1 in the second orbit, and 1 is not in N, so the printed witness is false.
- (5,6) = 3·(2,3) = 2·(3,4) lies in both orbits. The claim that the action is not free survives (Lean: not_isFreeAction_natNeOne).

**Fact 15.11: correct, but trivial.** No n >= 1 is stated, and n = 0 is not excluded. The sentence printed just before Def 15.9 gives mk(0) = 0, not 1. The printed proof also fails at n = 0, because the empty family is not "linked". For n >= 1 the statement holds (Lean: monoidRank_int_pi). The printed "p_i > 0" is stronger than generation directly gives (p_i >= 0), but it can be arranged and the argument only uses p_i + 1 > 0.

**Conj 15.7: correct.** Thm 15.4 lists only (i) and (ii), and its proof treats only those two. The (ii) line ends in a comma before "then". This check used the text layer for p.185 and the page image for p.186.

**Prop 14.4 proof: correct.** The paper has no Corollary 8.1. Section 8 numbers run Prop 8.1, Rem 8.2, Thm 8.3, and Prop 8.1 is the closed-immersion statement.

**Prop 2.19 citation: wrong.** The proposed correction assumes 0ET0 requires integrality. The live statement has no such hypothesis, only A' -> A surjective and B -> A arbitrary, with B' = B x_A A'. The print fits it exactly:
- A' = R[L'] and A = R[L], where the map is surjective because L is a face of L'.
- B = R[N], where B -> A is the inclusion, as printed.
- B' = R[N'], by the fibre product identity the proof establishes.

A(L) -> A(N) is indeed not integral in general (for example N = 0, L = N x 0, L' = N^2), but 0ET0 does not need that. The Lean file GeneralBaseMilnor.lean states this same result with "no finiteness hypothesis", and its own header says it is what the proof needs from 0ET0.

I checked the current Stacks text, not a version dated to the paper's reference [32]. The paper uses the same tag the same way in §13.

**Ex 15.10(ii), S empty: wrong.**
- The print writes D(Z^n) with no subscript. Rem 2.5 reads A(N)_B and D(M)_B as base changes from Spec(Z) of A(N) and D(M), so here S = Spec Z, which is nonempty.
- Direct check: for T nonempty, an equivariant map A(N)_T -> D(M)_T sends the unit X^m to a nonzero element of degree m, which forces N = M. So X^M = X and X^N is empty otherwise, giving {0, Z^n}. At n = 0 this is {0}, which is also consistent.
- The Lean result ex1510_ii_empty is true, but it concerns only a generalization to S empty that the print does not state. STATUS.md line 305 already withdraws it.
- The hypotheses of §15 hold here: D(Z^n) is separated over S, with M = Z^n.

Lean evidence was read, not rebuilt. Page images read: pp.135, 137, 138, 184, 186, 187, rendered to C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\ck.
