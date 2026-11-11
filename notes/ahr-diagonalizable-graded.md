# AHR Cor. 10.2 for D(M): direct graded route

Target. M f.g. abelian, S affine f.t. over Z, X separated algebraic space f.t. over S with D(M)-action,
x closed point. Want: U affine, (U,u)->(X,x) etale D(M)-equivariant, k(u)=k(x), G_u=G_x.

Sources actually read: arXiv:1912.06162 (Thm 1.1, 5.6, 5.8, proof of 5.6, Thm 10.1, Cor 10.2, intro on Sumihiro);
Mayeux AM Thm 6.8 / Conj 6.9; Drinfeld arXiv:1308.2604 sec. 0.4 only; Stacks 04D1.
Citations marked [mem] are from memory and were NOT read in this session.

Notation: T always a torus; A^ (graded completion) is the ring called "Spec of the completion" in AHR.

## 0. Status

| Case | Status |
|---|---|
| G finite diagonalizable, X any separated space (mu_p allowed) | PROVED, sec. 2. Elementary, no quotient needed. |
| Reduction D(M) -> torus | PROVED given existence of X/F (Keel-Mori [mem]), sec. 3 |
| The proposed reduction to G_x by induction G x^{G_x} W | FALSE in general, sec. 1 (F1) |
| Torus: equivariant etale nbhd preserving stabilizer, but neither affine nor separated | PROVED given rep. of pi_0 (LMB/Romagny [mem]), sec. 4 |
| Torus: non-reduced -> reduced -> normal | PROVED given Ferrand [mem], sec. 5 |
| Torus on a scheme over F_q | PROVED given Sumihiro (read only as quoted in AHR intro), sec. 5-6 |
| Torus on a scheme flat over Z | GAP G1: Sumihiro's condition (N) fails at bad primes |
| Torus on a normal algebraic space | GAP G2: the remaining core. NOT proved. |
| General D(M) on a scheme | inherits G2, since X/F can be a non-scheme (G3) |

THE FULL STATEMENT IS NOT PROVED. Solid: sec. 1-5. All remaining difficulty is one statement: normal + torus,
for spaces (G2), and for schemes in mixed characteristic (G1). The proofs of sec. 2-5 are mine and have had no independent check.

## 1. Preliminary reductions and failed reductions

R1 (forget S). D(M)_S x_S X = D(M)_Z x_Z X, so the action is a D(M)_Z-action; equivariance, etaleness,
k and stabilizers do not see S. Take S = Spec Z. As X is f.t. over Z, k(x) is a finite field; so
k(x) is perfect and all residue extensions below are separable.

R2 (rational point). If f in Z[t] lifts the minimal polynomial of a generator of k(x)/F_p, then Z[t]/f localized
is etale over Z at a point with residue field k(x); X' = X x Z' -> X is etale equivariant and x has a preimage with same k and
same stabilizer. Compose charts with X'->X.

F1. COUNTEREXAMPLE to the slice reduction. G = mu_p over k of char p, X = Spec k[t,1/t], t of weight 1, x: t=1.
G_x = 1, orbit = mu_p. A chart mu_p x W is non-reduced unless W is empty, while anything etale over X is reduced.
So no chart is induced from G_x. (X is affine: the theorem holds; the reduction fails.)
General form: for U = Spec A, M-graded, Y := degrees of homogeneous elements nonvanishing at u after inverting them;
U is induced from G_x near u iff 1 -> units(A_0) -> homogeneous units -> Y -> 1 splits. When Y has p-torsion, this asks for
p-th roots in A_0, not available etale-locally. When Y is free it splits. So after sec. 3 (M free) induction is valid,
but it applies to an existing chart and does not help build one.

F2. COUNTEREXAMPLE: normalization and reduction are not mu_p-stable. Char 2, A = k[s,u]/(u^2-1-s^3), Z/2-graded,
deg s = 0, deg u = 1. The normalization contains w = (u+1)/s (w^2 = s), with homogeneous components 1/s and u/s, not integral.
So the action does not lift. Likewise k[u]/(u^p-1), deg u = 1 in Z/p: the nilradical (u-1) is not homogeneous.
Devissage is legal only for smooth G. Sec. 3 removes the torsion first.

F3. COUNTEREXAMPLE: Weil restriction along a torus. X=A^1 with G_m, V={y^2=1+t, y != 0}. The sheaf
W(B)={lifts of the orbit map G_m,B -> X to V} is empty over the generic point: the orbit does not lift to the double cover.
So W is not etale over X near 0. Norm/Res stops at finite G.

F4. COUNTEREXAMPLE: averaging. T=G_m^2 on A^3, weights of a,b,c = (1,0),(0,1),(-1,-1). f = 1/(1-a-b-c) is regular at 0;
its degree-0 component is sum (3n)!/n!^3 (abc)^n, coefficients ~ C 27^n/n. Algebraic series cannot have exponent -1
(Flajolet 1987 [mem]), so it is transcendental. So homogeneous components of elements of O^h need not lie in O^h:
"take non-equivariant Artin approximation and project to graded pieces" fails.

## 2. Finite G: PROVED

Theorem A. F = D(N), N finite, acts on a separated noetherian algebraic space X, x a point with k=k(x) perfect
(automatic after R1). There is an affine W with etale F-equivariant (W,w)->(X,x), k(w)=k(x), F_w=F_x.

Proof. H := F_x in F_k, O' := F_k/H = D(Y)_k finite, o: O' -> X the orbit map. For each point y of the image of o choose
an affine etale (V_y,v_y)->(X,y), k(v_y)=k(y); V := disjoint union, affine. Each component of O' is local artinian,
so o lifts to phi_0: O'->V: on residue fields via v_y, then by unique infinitesimal lifting.
As V is affine and X separated, pi: V->X is affine.
Define W(B->X) = {phi: F_B -> V with pi phi = a_B}, a_B(g) = g.b. Then:
- W = Res_{F x X / X}(a^* V). F x X -> X is finite free and a^*V -> F x X affine f.p., so W exists, affine f.p. over X
  (locally, Res of a f.p. algebra along a finite free algebra is an explicit f.p. algebra).
- W->X is formally etale: for B0 in B square zero, F_B0 in F_B is square zero, and maps F_B->V over X lift uniquely. So etale.
- W is affine: W->X is affine and factors through ev_1: W->V; V->X separated, so ev_1 is affine; V is affine.
- Action: (h.phi)(g) = phi(gh); pi((h.phi)(g)) = gh.b = g.(hb), so it lies over h.b; W->X is equivariant.
- Point: w := phi_0 composed with F_k->O'. It is a k-point over x. It is H-invariant, so H is in F_w; F_w is in F_x by equivariance. QED.
No characteristic hypothesis; mu_p and non-normal play no role. X need not be a scheme.

## 3. Reduction to a torus

M = Z^r + M_tors, G = T x F, T = D(Z^r), F = D(M_tors). F x X -> X x X is finite, so X/F exists as a separated f.t. space
[Keel-Mori 1997 mem; Rydh mem], X -> X/F finite, compatible with flat base change, so T acts on X/F.

Prop B. A T-chart (U',u')->(X/F, xbar) yields the G-chart U = U' x_{X/F} X.
Proof. U is affine (U' affine, X->X/F affine), etale over X, G-equivariant. Over x the fibre contains
Spec(k(u') tensor_{k(xbar)} k(x)) = Spec k(x), as k(u')=k(xbar); this is u.
G_u = {g in G_x: gbar fixes u'} = G_x, because gbar lies in T_xbar = T_u'. QED.

So mu_p disappears, except as torsion of T_x inside T.

G3. X scheme does not imply X/F scheme. So "D(M) on a scheme" needs the space case, or the following variant which I have
NOT verified in detail: chart V for T on X, then W = Res_F(V), with T acting by (t,h)phi(g)=t phi(gh). The point must be a phi with
t phi(gh)=phi(g) for (t,h) in G_x; on K=pr_F(G_x) it is forced by the T-orbit of v; extension over F_k/K by twisted forms.

## 4. Torus: pi_0-equivariantization

Theorem C. T acts on X, x with k=k(x). There is an algebraic space U with T-action, etale (not nec. separated) over X,
T-equivariant, with u over x, k(u)=k, T_u=T_x, and an affine etale V->U through u, with T.V = U.

Construction. n := exponent of the torsion of the character group of T_x, F := T[n]. Then T_x = T_x^0 . (T_x cap F).
Take (V,v) from Theorem A for F: V affine, F-equivariant etale over X, F_v=F_x. Y := T x^F V, affine, with Y -> X, [g,w] -> g.w.
T x V -> X is smooth (etale, then a, which is pr up to an automorphism of T x X); so Y->X is smooth, by descent along the fppf T x V -> Y.
U := pi_0(Y/X), an etale algebraic space over X with Y->U smooth surjective with connected fibres [LMB 6.8 mem; Romagny 2011 mem].
pi_0 commutes with base change, and (t,y)->(t,ty) on T x Y covers (t,x)->(t,tx) on T x X, so T acts on U; axioms hold as Y->U is an epimorphism.
u := class of [1,v].
Stabilizer. U_x is etale over k. g -> class[g,v] is a morphism T_x -> U_x, constant on T_x^0 (connected, contains 1, even if non-reduced),
and [g0 f, v] = [g0, f v] = [g0, v] for f in F_x. So it is constant: T_x is in T_u. Reverse inclusion by equivariance.
k(u)=k: u is the image of a k-point in an etale fibre. QED.

Examples. X=A^1, V the double cover containing both y=+-1: U = A^1 with doubled origin. Nodal curve with Zariski V: U = X (no gain).
Nodal curve with V splitting the branches: U = two copies of A^1 (a true chart). So V must be fine enough.

Reformulation. If a true chart U_t exists (AHR) and V is open in it, U contains a T-stable affine nbhd of u. So:
Theorem for T <=> for V small enough, u has a T-stable affine nbhd in pi_0(T x^F V / X).
This removes the formal part of AHR (no completion, no effectivity) and replaces it with an affineness statement.

Criterion D (standard; not fully written). If u has a T-stable separated open nbhd U1 with a T-equivariant map to a T-representation,
unramified and quasi-finite at u, then equivariant ZMT plus deletion of a degree-0 hypersurface gives an affine T-stable nbhd.
So one only needs ENOUGH HOMOGENEOUS FUNCTIONS near u.

## 5. Torus: devissage (T smooth, so legal)

N (nilpotents). X_red in X is T-stable. Chart U0->X_red. Etale sites of X and X_red agree; U := the etale lift; U is affine
(thickening of an affine [Stacks, limits of spaces, mem]); T-action by uniqueness over T x X. Stabilizer and k unchanged.

Lemma G (graded completion). P=R[T_1..T_n], deg T_i = m_i in Z^r, m a homogeneous maximal ideal, R local noetherian, n=m cap P_0.
N_0 = {a in N^n: sum a_i m_i = 0} is f.g. (Gordan), each degree-set in N^n is a finite union of N_0-translates (Dickson). So m^k cap P_d is in n^{f(k)} P_d
with f(k) -> infinity, and A^(P) := + lim (P/m^k)_d = P tensor_{P_0} (P_0)^.
Passing to quotients: for x fixed, A^ := + lim (O_x/m^k)_d is noetherian, f.t. over its complete local A^_0.
Graded coherent completeness: a compatible system N_k has N_d=lim(N_k)_d finite over A^_0. Elementary.

Lemma L (Luna, diagonalizable). B->B' graded etale of f.t. Z^r-graded rings, y' over y, closed orbits, T_y'=T_y, k(y')/k(y) finite separable.
Then there is f in B'_0, f(y') != 0, with B_0 -> (B'_f)_0 etale and B tensor_{B_0} (B'_f)_0 = B'_f.
Proof. Degrees of units Y are free (M=Z^r), so after localizing in degree 0 B=Ind(C), B_0=C_0: reduce to y fixed. Etale extension of B_0 gives same k.
By Lemma G, degreewise completions of B_d are B_d tensor (B_0)^ and compute lim (B/m^k)_d. B/m^k = B'/m'^k (etale, same k), so (B_0)^ = (B'_0)^.
So B_0->B'_0 is etale at the point, and B tensor_{B_0} B'_0 -> B' is an isomorphism after degreewise completion, hence after localizing, by finite generation. QED.

P (pinching). X reduced, nu: X~ -> X normalization (finite; X excellent), T acts on X~ (T x X~ normal). C conductor, C~ = nu^-1 C, O_X = O_X~ x_{O_C~} O_C.
Noetherian induction on closed T-stable subspaces: chart (U_C,u) for x in C (if x not in C, X is normal at x),
plus T-stable affines W_i in X~ around each closed T-orbit in the fibre of x (the normal case).
E := U_C x_C C~, affine, graded, finite over U_C, etale over C~. Fibre over u: y_i. k(y_i)=k(x~_i); stabilizers preserved, as T_u=T_x contains T_x~_i.
(a) Splitting. O(E)_0 is finite over O(U_C)_0. Base-change U_C along an etale nbhd of ubar in Spec O(U_C)_0 (trivial residue extension; henselian finite algebra, finite level)
  so that E = + E_i according to the closed orbits y_i. Preserves k and stabilizers.
  This is needed: P^1 -> nodal curve has 0, infinity with no common T-stable affine.
(b) Delete a degree-0 function of U_C (image of a closed T-stable set avoiding u; separated by O(U_C)_0 as the orbit of u is closed; degree 0 is exact).
  Get E_i -> C~ cap W_i, and by Lemma L, strongly etale: D'=D tensor_{D_0} D'_0 where D=O(C~ cap W_i).
(c) Lift. B_i=O(W_i), D=B_i/I, D_0=(B_i)_0/I_0. Stacks 04D1 (read): an etale (B_i)_0 -> B'_0 with B'_0/I_0 = D'_0. Set B'_i = B_i tensor_{(B_i)_0} B'_0.
  U~ := + Spec B'_i: etale over X~, T-equivariant, U~ x C~ = E.
(d) Pushout. U := Spec(O(U~) x_{O(E)} O(U_C)), affine, Z^r-graded, f.t. (Artin-Tate). Etale over X: on an affine etale nbhd of X the conductor square is a Milnor square,
  Ferrand 2003 [mem] glues flat algebras, etaleness descends. U x_X X~=U~, U x_X C=U_C. k and stabilizer read on U_C. QED.

Therefore: theorem for T on all X <=> theorem for T on normal X. Same within schemes.

## 6. The normal case

Schemes over F_q. X~ normal f.t. over F_q, connected, over its constant field: geometrically integral and normal. AHR intro quotes [Sum75, Cor 3.11]: (N) gives a T-stable affine nbhd.
Conclusion: T on a separated f.t. scheme over F_q: PROVED modulo Sum75 itself (not read), Ferrand, and sec. 5.

G1, flat over Z. X~ normal, flat over O_K. (N) wants geometrically integral fibres in codim 1, which fails at reducible special fibres. Thomason 1987 [mem] may cover it; NOT checked.

G2, normal spaces. NOT proved. Established facts:
1. Equivalent form. The theorem at x (X normal) holds iff there is a finite extension E_0 of k(Q), Q the rational quotient, such that the normalization Y of X in E_0.k(X), which has a T-action, is a scheme near the fibre of x.
   (=>) True chart U: k(U)=E_1.k(X); with E_0 containing the Galois closure, Y x_X U -> Y is etale, birational on components, Y normal, so open immersion. (<=) Sumihiro on Y with T x Gamma, quotient by decomposition group. Sketch only, needs G1 in mixed char.
   Obstacle: k(V)/k(X) for arbitrary V is not of the form E_0.k(X) (e.g. sqrt(s+1)); V must be T-adapted.
2. Homogeneous functions. R := + (O_{U,u} cap k(U)_d), k(U)_d = s^d k(Q). As U is normal and poles of homogeneous elements are T-stable, an element is regular at u iff it has no pole on T-stable prime divisors through u. Needed: R -> m/m^2 surjective; then Criterion D finishes (U separated near u also needed).
   Not proved. Sumihiro's argument needs the complement of an affine V to avoid x; in the etale setting the complement of V in the normalization of X in k(V) maps onto a divisor through x. I have no replacement for the linearized ample bundle.
3. Effectivity route: A^ -> X (sec. 7). For the toy case A^ = k[t], psi(gt)=g.psi(t): fpqc descent along T x Spec k[[t]] -> A^1 fails because Spec(k[[t]] tensor k[[t']]) has points not specializing to the closed fibre. Rosenlicht invariants give constancy of psi^*q for invariant rational q, which handles this toy case only heuristically (I did not finish it; closure of the image need not be T-stable a priori).
4. Deformation to the normal cone gives a T x G_m space with affine central fibre, but the extended Rees ring has weight -1 on t: no contraction. No proof.
Drinfeld sec. 0.4 records that via Halpern-Leistner-Preygel Thm 2.1 attractor representability for affine diagonal uses cohomological properness of A^1/G_m, a coherent-completeness-type input. His original proof uses Artin's method (ibid.). I did not read the details.

## 7. Where AHR's machinery goes at D(M)

- Thm 1.6/1.10 (coherent completeness, effectivity at G fixed): Lemma G, elementary.
- Luna (AHR sec. 3): Lemma L, elementary.
- Equivariant Artin (Thm 5.8): AHR use fundamental Z->BGL_m and [AHR20 A.18] (not read). At D(M): C -> Hom_G(Spec(A^ tensor_{A^_0} C), X) on A^_0-algebras, classical Artin over A^_0. Plausible, not written; avoidable by sec. 4.
- Tannaka (Spec A^ -> X): the only step with no elementary replacement. Sec. 2-5 bypass it, except at G1,G2.
- Cotangent complexes (deforming W_0): not needed at D(M), W_0 = BG_x lifts by a graded polynomial presentation (Lemma G).

## 8. What is hard, precisely

- Non-normal: not hard for a torus (sec. 5). One trap, step (a), resolved.
- mu_p: not hard (sec. 2, 3), but it invalidates reductions F1, F2.
- Spaces vs schemes: THE difficulty (G2). Scheme case rests on Sumihiro's ample bundles.
- Mixed characteristic: G1, for lack of (N).

## 9. Lean feasibility (greps of .lake/packages, no build)

Present: IsEtale, StandardEtale, Zariski main theorem (Mathlib/RingTheory/ZariskisMainTheorem.lean, Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean), Henselian.lean, algebraic spaces (Stacks/StacksFrontier/AlgebraicGeometry/Spaces; 57 files mention them), GradedAlgebra, one file mentioning Gordan (not inspected), local AlgMag/GeneralBaseMilnor.lean (Milnor pushouts of schemes).
Absent (0 grep hits): Weil restriction, Ferrand; none found for henselization, Artin approximation, Sumihiro; relative pi_0 not found.
- Theorem A: FEASIBLE. Res along finite free algebra (new, moderate), etale by infinitesimal lifting + f.p., representability on a space (moderate), elementary etale nbhds on spaces (check Spaces/AffineAtlas).
- Lemmas G, L, F1-F3: feasible; pure graded commutative algebra.
- Keel-Mori, pi_0 representability, Sumihiro: out of reach soon. Full theorem by this route: not currently feasible, and in any case not proved on paper.
