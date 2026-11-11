# Theorem 6.8(ii) = Theorem A.2(ii): the chart family for quasi-separated X

Source: Mayeux, *Algebraic Magnetism*, with appendix by Romagny, Semigroup Forum 113 (2026), 126–201. Theorem 6.8 on p. 158, Theorem A.2 on p. 196, its proof on pp. 199–200 (text `am.txt` lines 1753–1762, 3915–3924, 4081–4122). Pure mathematics; no Lean was edited.

## 0. Verdict in five lines

1. The printed proof of case (ii) is correct as it stands, with one citation slip: "[3], Corollary 20.2" is **Corollary 10.2** of Alper–Hall–Rydh, *The étale local structure of algebraic stacks* (arXiv:1912.06162v4, §10.1). That corollary asks for `X` **quasi-separated** only, with `T` of multiplicative type over a quasi-separated base. No separatedness is needed anywhere in the print for (ii).
2. What must be constructed is exactly the Lean `EtaleChartFamily` (`AlgMag/ChartAtlas.lean:31`): for every point, an affine scheme `U` with `D(M)`-action and a `D(M)`-equivariant étale `U → X` through it. Nothing weaker suffices (Definition 6.1(iv) requires `D(M)_S`-stable `S`-affine pieces and `D(M)`-equivariance), and nothing stronger is needed: the `Z`-FPR property is free from Theorem A.1 because `D(M/Z)` has connected fibres. The family hypothesis of `thm68_ii_of_charts` is therefore **not stronger than true**; no counterexample exists, and no "weaker family" is called for. The torus `D(M/Z)` never acts in the construction; it enters only through Theorem A.1 at the end.
3. The gap is in the specialized route (`notes/ahr-specialized-proof.md`, formalized as `chartLemma`), which proves AHR Cor. 10.2 for `D(M)` only when `X` is separated. Separatedness is used there in five places, all of the form "the equalizer of two maps into `X` is closed" or "`V ×_X V` is affine", plus the Stacks replacement of Bhatt's theorem, which has a separated target.
4. Each use has a replacement that needs only quasi-separatedness: a local lemma on monomorphisms containing a formal neighbourhood (Lemma M below), its two corollaries (M′, U), Bhatt's Theorems 1.1 and 1.4(1) (both stated for qcqs algebraic spaces), closedness of field-valued stabilizers (a general fact about group schemes over fields), and a generic-flatness argument for the generic stabilizer. Sections 1, 2, 3, 5 and 6 of the specialized proof do not change.
5. The corrections to the printed statement remain the agreed ones: `S` separated for the `S`-affine clause (so that affine-over-an-open is affine over `S`), and the citation number. The hypothesis "`M/Z` torsion-free" can be weakened to "`D(M/Z)` has connected fibres" (the appendix's form, the Lean `IrreducibleFibres`), as the print already does in A.2(ii).

## 1. What the print proves and cites

**Theorem A.2** (p. 196). `X` a quasi-separated `S`-algebraic space locally of finite presentation with an action of `G = D(M)_S`, `M` f.g.; `H = D(M/Z)`. If (i) `X` is separated over `S`, or (ii) `H` has connected fibres, there is a `Z`-FPR atlas `U → X`, quasi-compact if `X → S` is.

**Printed proof, case (ii)** (pp. 199–200), step by step:

- (R) Reduce, "as in the beginning of the proof of Theorem A.1", to `S` affine and `S, X` of finite type over `ℤ`. Then closed points are dense and it is enough to find an affine `G`-equivariant étale neighbourhood `U(x) → X` of each closed point `x`; `U := ⊔_x U(x)`.
- (C) For a closed point `x` with image `s`, `κ(x)/κ(s)` is finite. "By [3], Corollary 20.2" there is an affine pointed scheme `(U_0 = Spec A, u_0)` and an étale `G`-equivariant `(U_0, u_0) → (X, x)` with `κ(x) = κ(u_0)` and `G_{u_0} = G_x`.
- (F) Write `H = T × F`. In case (ii) `F` is infinitesimal and Theorem A.1 gives `U_0^H = X^H ×_X U_0`, so `U(x) := U_0` is `Z`-FPR at `x`. (Case (i) then builds `U_1 = U_0/F ×_{X/F} X`; it is not needed for (ii).)
- (Q) The quasi-compact clause is "obvious".

**What [3] says.** arXiv:1912.06162v4, p. 51:

> Theorem 10.1. Let `S` be a quasi-separated algebraic space. Let `G` be an affine and flat group scheme over `S` of finite presentation. Let `X` be a quasi-separated algebraic space locally of finite presentation over `S` with an action of `G`. Let `x ∈ X` be a point with image `s ∈ S` such that `κ(x)/κ(s)` is finite. Assume that `x` has linearly reductive stabilizer. Then there exists a `G`-equivariant étale neighbourhood `(Spec A, w) → (X, x)` that induces an isomorphism of residue fields and stabilizer groups at `w`.
>
> Corollary 10.2. Let `S` be a quasi-separated algebraic space, `T → S` be a group scheme of multiplicative type over `S` (e.g., a torus), and `X` be a quasi-separated algebraic space locally of finite presentation over `S` with an action of `T`. [Same conclusion.] Proof: any subgroup of a fibre of `T → S` is linearly reductive.

Its proof applies Theorem 1.1 of AHR to `[X/G]`; Theorem 1.1 asks for `[X/G]` quasi-separated with affine stabilizers. For `X` quasi-separated, `[X/G]` is quasi-separated, and its stabilizers at field-valued points are closed subgroups of `D(M)_k` (§4.1 below), hence affine. The "separated diagonal" clause of Theorem 1.1 is only used by AHR to make `W → X` representable; Theorem 10.1 gets representability differently (`W := W ×_{BG} S` after shrinking with Proposition 5.3(1)), with no separatedness of `X`. I read Theorem 1.1, Theorem 10.1, Corollary 10.2 and their proofs in v4; I did not check the numbering in the ASENS version, and I have not verified AHR's proof of Theorem 1.1 beyond what the specialized note already did.

**Theorem A.1** (p. 196): `G` flat f.p. with connected fibres, `X, Y` locally f.p. with `G`-actions, and (i) `S` locally noetherian or (ii) `X, Y` quasi-separated. Then `X^G → X` is a closed immersion of finite presentation and every étale equivariant `X → Y` is fixed point reflecting. Applied with `G := H = D(M/Z)` (a split torus when `M/Z` is torsion-free; connected fibres in the `IrreducibleFibres` generality), `X := U_0` affine, `Y := X` quasi-separated. This is the only place where `M/Z` torsion-free is used.

So the print is complete for (ii) given AHR Cor. 10.2, and the Lean has everything except that corollary for quasi-separated `X` (`isZFPRAtlas_of_family_irreducible` is Theorem A.1 + gluing, `thm68_ii_qc` is the finite subfamily).

## 2. Exactly what must be constructed, and why

**Target (Chart Lemma, quasi-separated form).** `M` f.g. abelian, `G = D(M)`, `S` affine of finite type over `ℤ`, `X` a quasi-separated algebraic space of finite type over `S` with `G`-action, `x` a closed point. Then there is an affine scheme `U` with `G`-action and an étale `G`-equivariant `(U, u) → (X, x)`.

- The residue-field and stabilizer clauses of Cor. 10.2 are **not needed** for (ii) (they are needed in case (i) for the `U_0/F` construction). The specialized proof yields them anyway (§5–6 of the note), so nothing is lost by keeping the Lean `IsChartAt`.
- `D(M)`-equivariance is needed, not `D(M/Z)`-equivariance: Definition 6.1(iv) requires the pieces to be `D(M)_S`-stable and `f` to be `D(M)_S`-equivariant, and Proposition 8.1 / Theorem 8.3 use the `D(M)`-action on `U`. The print gets `D(M)`-equivariance directly from Cor. 10.2 with `T = D(M)_S`. There is no version of the theorem with charts equivariant only for a subgroup.
- "Passing to the torus `D(M/Z)`" is not an option for the construction: the quotient `D(M)/D(M/Z) = D(Z)` is the group that acts on `X^{D(M/Z)}`, not on `X`. `D(M/Z)` enters only through Theorem A.1.
- The `EtaleChartFamily` fields match Definition 6.1(iv) and (v): `act`, `equivariant`, `etale`, `isAffineHom` (= `S`-affine piece; with `S` affine, `U` affine), `covers` (= surjective). It is exactly what the print produces after reduction (R). It is not stronger than true.

**Globalization (unchanged from case (i)).** For general `S` and non-quasi-compact `X`: cover `S` by affine opens `S_i`; for each, the orbit `G·W` of a quasi-compact open `W ⊂ X_{S_i}` is a `G`-stable quasi-compact open (`G × W → X` is flat of finite presentation, hence open, and `G` is affine), and it is of finite presentation over `S_i` because `X` is quasi-separated; by Stacks 07SJ-type limit arguments (as in the proof of A.1) it descends with its action to `S_0` of finite type over `ℤ`. Charts for `X_0` pull back to charts of `G·W`, affine over `S_i`. The pieces are affine over `S` when `S_i → S` is affine, which holds when `S` is separated: the agreed correction. If `X → S` is quasi-compact, finitely many `S_i` and finitely many charts suffice (`thm68_ii_qc` does this from a family). Nothing here depends on (i) versus (ii), and the Lean `SpacesLimitThm68` already does it.

So the one thing to prove is the Chart Lemma for quasi-separated `X`.

## 3. Where the existing route uses separatedness

The specialized proof `notes/ahr-specialized-proof.md` proves the Chart Lemma for `X` separated. The uses of separatedness, with the Lean constants:

| # | Place in the note | Use | Lean |
|---|---|---|---|
| S1 | §1 Orbit | "The stabilizer `H ⊂ G_k` is closed (`X` separated)" | `ChartPoint*`, `exists_orbit_data` |
| S2 | §1 Lemma 1.1 | `o : O → X` quasi-compact (for the scheme-theoretic image) | `chart-point-state.md` A |
| S3 | §4 Thm 4.1 uniqueness | "the equalizer is closed, defined by a homogeneous ideal ⊂ ∩ mⁿ = 0" | `Chart.eq_of_agree_of_iInf`, `thm41_unique` |
| S4 | §4 Lemma 4.2 | `H_K` closed; and the Lean route's generic stabilizer `exists_generic_stabilizer` ("`X` separated") | `ChartStratumStab.lean` |
| S5 | §4 Lemma 4.3 | Lean instance adds "`X` separated over `S`" (`chart-deligne-state.md`) | `ChartDeligneInst` |
| S6 | §4 Glue | Stacks 0GHK-type algebraization: proper source, **separated** target | stub `existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType` |
| S7 | §4 Remark (fpqc gluing) | equalizer on `T̂ ×_T T̂` closed + Lemma 4.5 | `eq_on_kernelPair`, `existsUnique_pushout` |
| S8 | §4 "φ extends φₙ", "φ is equivariant" | closed equalizer + Lemma 4.5 | `Chart.eq_of_agree_basicOpen_of_agree_thickening`, `restrict_eq_of_strata`, `equivariant_of_agree` |

Sections 2, 3, 5, 6 of the note do not use separatedness: thickenings of an affine closed subspace are affine (Stacks 07VT, any algebraic space); §3 is graded algebra; §5 uses that `X` is locally of finite presentation (limit preservation of `Hom(-, X)` and of equalities, the latter because the diagonal of an l.f.p. space is l.f.p.) and the completion criterion for étaleness on an étale chart of `X`; §6 is graded algebra on `W`.

**Why a stabilizer need not be closed.** `Stab = (G × X) ×_{X ×_S X} X` is the pullback of the diagonal of `X`. For `X` quasi-separated, `Δ_X` is a quasi-compact monomorphism locally of finite type, representable by schemes, but not an immersion unless `X` is locally separated. So `Stab → G × X` is a quasi-compact monomorphism of schemes over `G × X`, not a closed immersion in general. What survives: for a point `x : Spec k → X`, `Stab_x → G_k` is a monomorphism of group schemes of finite type over a field, hence a closed immersion (SGA 3, Exp. VI_B, Cor. 1.4.2; see §7 for what I did not verify). The replacements below only ever use (a) field-valued stabilizers, (b) quasi-compactness of `Δ_X`, (c) local finiteness of `Δ_X`.

## 4. The replacements

### 4.1 Field-valued stabilizers are closed (replaces S1, half of S4)

Let `x ∈ X(k)`, `k` a field, `G = D(M)_k`. `Stab_x = G ×_{X} Spec k` (fibre of `g ↦ gx` over `x`) is a scheme (pullback of `Δ_X`, representable by schemes), a subgroup scheme of `G`, quasi-compact over `k` (`Δ_X` quasi-compact) and locally of finite type, so of finite type. A monomorphism of group schemes of finite type over a field is a closed immersion (SGA 3 VI_B 1.4.2). Closed subgroups of `D(M)_k` are `D(M/Z_0)` (SGA 3 VIII 3.2, as in the note). So S1 and the "`H_K` closed" in Lemma 4.2 hold verbatim for quasi-separated `X`. Everything else in §1 (Lemma 1.1: scheme-theoretic image, generic flatness, flat f.p. monomorphism = open immersion) only needs `o : O → X` quasi-compact, which holds since `O` is affine and `X` quasi-separated (S2).

### 4.2 Lemma M: a monomorphism containing a formal neighbourhood is an open immersion there

**Lemma M.** Let `R` be a locally noetherian scheme, `J ⊂ O_R` a coherent ideal, `j : E → R` a monomorphism locally of finite type such that for every `k ≥ 1` the closed immersion `V(J^k) → R` factors through `j`. Then there is an open `W ⊂ R` containing `V(J)` such that `E ×_R W → W` is an isomorphism.

*Proof.* Fix `p ∈ V(J)`, `A := O_{R,p}`, `m := m_A`, `J_p ⊂ m`. Since `Spec κ(p) → V(J) → R` factors through `j` and `j` is a monomorphism, there is a unique point `e ∈ E` over `p`, the fibre `E_p` is `Spec κ(p)`, hence `κ(e) = κ(p)` and, with `B := O_{E,e}`, `mB = m_B` (a monomorphism locally of finite type is unramified). For each `k`, the factorization `Spec(A/J^kA) → E` sends the closed point to `e` (the only point over `p`), so it factors through `Spec B`: there are local maps `r_k : B → A/J^kA` with `r_k ∘ (A → B) = ` the projection.

(a) `A → B` is injective: its kernel lies in `∩_k J^kA = 0` (Krull, `A` noetherian local, `J_p ⊂ m`).

(b) `Â → B̂` (`m`-adic completions) is surjective: `B/m_B^n` is a local ring of finite length with `B/m_B = κ(p)` the image of `A`, so `A/m^n → B/m_B^n` is onto by nilpotent Nakayama applied to the cokernel; pass to the limit.

(c) `Â → B̂` is injective: `r_k` is a retraction of `A/J^kA → B/J^kB`, `B`-linear for the `B`-module structure of `A/J^kA` through `r_k`; tensoring with `B̂` (flat, and `B̂ ⊗_B N = N̂` for finite `N`) gives a retraction of `Â/J^kÂ → B̂/J^kB̂`. So an element of the kernel of `Â → B̂` lies in `J^kÂ` for all `k`, hence is `0`.

(d) So `Â ≅ B̂`. Since `B → B̂` is faithfully flat and `Â` is flat over `A`, `B` is flat over `A`. Flat and unramified of finite presentation (`R` locally noetherian) is étale: `j` is étale at `e`. The étale locus `E° ⊂ E` is open and `j|_{E°}` is an étale monomorphism, hence an open immersion (Stacks 025G: flat monomorphism locally of finite presentation). `W := j(E°)` is open, contains every `p ∈ V(J)`, and `E ×_R W → W` is a monomorphism with the section `W ≅ E° ⊂ E ×_R W`, hence an isomorphism. ∎

**Corollary M′ (replaces Lemma 4.5 and `eq_of_agree_basicOpen_of_agree_thickening`; S8, and the thickening half of S7).** Let `R = Spec D` with `D` noetherian, `a ⊂ D` an ideal, `X` a quasi-separated algebraic space, `φ, ψ ∈ X(R)` two points which agree on `D(g)` for `g` in a generating set of `a` and on every `V(a^k)`. Then `φ = ψ`.

*Proof.* The equalizer `E := R ×_{X ×_S X} X → R` is the pullback of `Δ_X`: a monomorphism of schemes, quasi-compact (`X` quasi-separated) and locally of finite type (any algebraic space). It has sections over each `D(g)`, hence over `D(a)`, and over each `V(a^k)`. Lemma M with `J = a` gives an open `W ⊃ V(a)` over which `E → R` is an isomorphism. `W ∪ D(a) = R`. Sections of a monomorphism over the members of an open cover agree on overlaps and glue; so `E → R` has a section and is an isomorphism, i.e. `φ = ψ`. ∎

The flatness hypothesis of Lemma 4.5 disappears; what is needed instead is that `R` be noetherian. In S8 the rings are `C/mⁿ` and `ℤ[M] ⊗ C` (finite type over the noetherian `C`), so M′ applies. It also applies in the separated case, where it is a simplification.

**Lemma U (replaces S3, Theorem 4.1 uniqueness).** Let `(C, m)` be a complete pair (§3 of the note: `M`-graded noetherian, `C_d = lim (C/mⁿ)_d`, with `C_0/m_0 = k` a field, so that `C_0` is local with maximal ideal `m_0`, elements of `1 + m_0` being units by completeness). Let `X` be a quasi-separated algebraic space with `G`-action and `φ, φ′ : T = Spec C → X` two **equivariant** maps that agree on every `V(mⁿ)`. Then `φ = φ′`.

*Proof.* Let `j : E → T` be the equalizer (a quasi-compact monomorphism locally of finite type, as above), `W ⊂ T` the open of Lemma M (`J = m`): `W ⊃ V(m)` and `j` is an isomorphism over `W`; `W` is the set of `t ∈ T` at which `j` is étale at the point over `t`.

*`W` is `G`-stable.* `E` is a `G`-stable subfunctor of `T`, being the equalizer of two equivariant maps. For a field `K` and `g ∈ G(K)`, translation `τ_g` is an automorphism of `T_K` preserving `E_K = E ×_T T_K`, hence preserving the locus `W_K′` where `E_K → T_K` is an open immersion. It remains to see `W_K′ = W ×_T T_K`. "⊇" is base change. "⊆": let `t′ ∈ W_K′` over `t ∈ T`, `e, e′` the points of `E, E_K` over them, `A = O_{T,t}`, `A′ = O_{T_K,t′}` (flat local over `A`), `B = O_{E,e}`. Since `E_K → T_K` is a monomorphism, `Spec(B ⊗_A A′)` has a unique closed point, so `B ⊗_A A′ = O_{E_K,e′} ≅ A′`, which is flat over `A′`; flatness descends along the faithfully flat `A → A′`, so `B` is flat over `A`, and `j` is étale at `e`, i.e. `t ∈ W`. Hence `W_K′ = W ×_T T_K`, so `W(K)` is stable under `G(K)` for every `K`, and the two opens `α^{-1}(W), pr_2^{-1}(W) ⊂ G × T` have the same `K`-points for all `K`, so they coincide: `W` is `G`-stable.

*`W = T`.* `Y := T ∖ W` is a `G`-stable closed subset not meeting `V(m)`. As in the Shrinking Lemma (§6 of the note), there is a homogeneous ideal `I` with `V(I) = Y`. `V(I) ∩ V(m) = ∅` and `C` noetherian give `I + m = C`; taking degree-0 components (both ideals homogeneous), `1 = i_0 + m_0′` with `i_0 ∈ I_0`, `m_0′ ∈ m_0`, so `i_0` is a unit of the local ring `C_0`, `I = C`, `Y = ∅`. So `E → T` is an isomorphism and `φ = φ′`. ∎

(An alternative that avoids the `G`-stability argument: prove uniqueness inside the noetherian induction of Theorem 4.1 by the same stratification: two extensions agree on `T_U` because the Lemma 4.3 formula is canonical and `φ^*J = a` for both, agree on each `V(a^k)` by induction, then M′. Either form is fine; the one above is self-contained and is what `thm41_unique` should become.)

### 4.3 The gluing: Bhatt's Theorems 1.1 and 1.4(1) (replace S6, S7)

Bhatt, *Algebraization and Tannaka duality*, arXiv:1404.7483 (published: Camb. J. Math. 4 (2016); numbering checked only on the arXiv text in the scratchpad, `txt2/bhatt.txt` lines 19–20 and 66–78):

> Theorem 1.1. If `A` is a ring which is `I`-adically complete for some ideal `I`, and `X` is a qcqs algebraic space, then `X(A) ≃ lim X(A/Iⁿ)` via the natural map.
>
> Theorem 1.4. Let `π : Y → X` be a map of qcqs algebraic spaces. Assume there exists a finitely presented closed subspace `Z ⊂ X` satisfying `Z ×^L_X Y ≃ Z` [i.e. `Y → X` and `Z → X` are Tor-independent and `π^{-1}(Z) ≃ Z`]. Set `U = X ∖ Z` and `V = Y ∖ π^{-1}(Z)`. Then: (1) the fibre square `V → Y, U → X` is a pushout in qcqs algebraic spaces.

Both are for **quasi-compact quasi-separated** spaces, with no separatedness. After the reduction (R), `X` is of finite type over `S` affine, so qcqs. In §4 "Glue" of the note:

- `θ : T̂ = Spec Ĉ → X` comes from Theorem 1.1 applied to the `a`-adically complete `Ĉ` and the system `T^{(k)} = Spec C/a^k → Z^{(k)} ⊂ X` (`Ĉ/a^kĈ = C/a^k`). This replaces the Stacks stub `existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType` (0GHK form: proper source over `Spec A`, separated target), which cannot be used for non-separated `X`. Note that in the Lean, `NoetherianAlgebraization X` packages this input; its instance is the only thing to change.
- `φ : T → X` comes from Theorem 1.4(1) with `π : T̂ → T` (flat, so Tor-independent), `Z = V(a)` (finitely presented, `C` noetherian), `π^{-1}(Z) = V(aĈ) = Z`; the data are `τ : T_U → U ⊂ X` (Lemma 4.3) and `θ`, which agree on `V = T̂ ∖ V(aĈ)`. The compatibility on `V` is unchanged from the note: `θ^{-1}(U) = V` by Nakayama, and both restrictions are given by the Lemma 4.3 formula, which is an identity between maps into the **affine** `U`, so its equalizer is closed and the note's argument applies as written.
- The fpqc Remark of the note (`T_U ⊔ T̂ → T`, Gabber 0APL, equalizer on `T̂ ×_T T̂` closed) is explicitly separated-only and is **not** rescued by Lemma M: `Ĉ ⊗_C Ĉ` is not noetherian, and I found no proof of the kernel-pair identity there without Bhatt 1.4. So S7 is replaced by the black box 1.4(1), which was the note's original plan ("§4 Glue"), and `existsUnique_pushout` / `eq_on_kernelPair` are not needed.
- "φ extends φₙ" and "φ is equivariant": Corollary M′ with `R = Spec C/mⁿ` (resp. `Spec(ℤ[M] ⊗ C)`), `a` the image of `a` (resp. `a(ℤ[M] ⊗ C)`, with `D(a) = G × T_U` and `V(a^k) = G × V(a^k)`), exactly as in the note but with M′ in place of Lemma 4.5.

### 4.4 Lemma 4.2 (affine stratum) for quasi-separated `X` (replaces the rest of S4)

Two routes; the first is the paper proof, the second is the Lean's.

**Gerbe route (the note's §4.2, now valid).** `𝒳 = [X/G]` has quasi-compact inertia: `I_𝒳 = Stab → X` is the pullback of `Δ_X` (quasi-compact) composed with `G × X → X` (affine). Stacks 06RC needs only a reduced algebraic stack with quasi-compact inertia and gives a dense open gerbe `𝒰 ⊂ 𝒳_red` over an algebraic space `Q`. `𝒳` is quasi-separated (its diagonal `G × X → X ×_S X` is quasi-compact when `Δ_X` is: the preimage of `W_1 ×_S W_2` is `(G × W_1) ∩ act^{-1}(W_2)`, an intersection of two quasi-compact opens of the quasi-separated `G × X`), so `𝒰` is, and `Q` is quasi-separated by fppf descent of quasi-compactness of `Δ_Q` along `𝒰 × 𝒰 → Q × Q` (`𝒰 → 𝒰 ×_Q 𝒰` is fppf surjective for a gerbe). A quasi-separated algebraic space is decent and has a dense open subscheme (Stacks 086U), so `Q` has a nonempty affine open. The rest of the note's argument is unchanged: over the generic point, `H_K` is closed (§4.1), the orbit map `G_K → U′_K` is an `H_K`-torsor, `U′_K = D(Z′)` is affine, affineness descends (fpqc) and spreads out (07SQ), and 07VT returns to `X`.

**Lean route (04S6).** Steps 1 (reduce to `X[1/N]_red`, `D(M′)`), 3 (open orbit `Y`), 4 (free `D(Z)`-action), 5 (`Q = Y/D(Z)` by 04S6), 6 (`Q` quasi-separated: `R = D(Z) × Y → Y ×_A Y` is quasi-compact by the same intersection argument as above, which needs `X` quasi-separated only), 7 (affineness along the torsor), 8 (assemble) do not use separatedness. Step 2 (`exists_generic_stabilizer`: on an integral affine chart `V → X`, after shrinking to `V′ = D(s)`, `Stab_{V′} = D(M/Z) × V′`) does, and is replaced by:

*Claim.* `V` integral affine noetherian, `p ∈ X(V)`, `Stab_V := {(h, v) : h·p(v) = p(v)} ⊂ G × V`, `K = κ(η)`. There are a nonempty open `V′ ⊂ V` and `Z ⊂ M` with `Stab_{V′} = D(M/Z) × V′` as subfunctors of `G × V′`.

*Proof.* `Stab_V → V` is of finite type (pullback of `Δ_X`: quasi-compact, locally of finite type). By §4.1, `Stab_K = D(M/Z)_K` for some `Z`. By generic flatness (EGA IV 6.9.1) shrink `V` so that `Stab_V` is flat over `V`.
(⊆) The composite `Stab_V → G × V → D(Z) × V` and the unit section `e(V) ⊂ D(Z) × V`, a closed immersion (`D(Z)` is affine, hence separated): `Σ := Stab_V ×_{D(Z) × V} e(V)` is a closed subscheme of `Stab_V` containing the generic fibre. `Stab_V` is flat over the integral `V`, so `O_{Stab_V} → O_{Stab_K}` is injective and `Σ = Stab_V`. Hence `Stab_V ⊂ P := D(M/Z) × V`, the kernel of `G × V → D(Z) × V`.
(open) `Stab_V → P` is a monomorphism of finite type, hence quasi-finite and separated; by Zariski's Main Theorem it factors as an open immersion into a finite `P`-scheme `P̃`, which we replace by the scheme-theoretic closure of `Stab_V` in it. Over `K`, `Stab_K = P_K`, so `P̃_K = P_K` (the open `Stab_K ⊂ P̃_K` is also closed, being a section of the separated `P̃_K → P_K`, and dense). The kernel and cokernel of `O_P → O_{P̃}` are coherent with support not meeting `P_K`; the image of the support in `V` is constructible (Chevalley) and misses `η`, so it lies in a proper closed subset; shrinking `V`, `P̃ = P` and `Stab_V ⊂ P` is an **open** subgroup scheme containing the generic fibre.
(=) Write `D(M/Z) = T_0 × F_{p′} × F_p` with `T_0` a split torus, `F_{p′}` finite diagonalizable of order invertible on `V` and `F_p` the `p`-primary part, where either `char K = 0` (shrink `V` to invert the order of `F`, `F_p = 1`) or `char K = p` (then `p = 0` on the integral `V`). `Stab_V ∩ (F_{p′} × V)` is open in the finite étale `F_{p′} × V → V` and contains the generic fibre, so its complement has closed image in `V` missing `η`; shrink. `F_p × V` is infinitesimal over `V`, so it has the same points as the unit section and lies in the open `Stab_V`. For `v ∈ V`, `Stab_v ∩ T_{0,v}` is an open subgroup of the connected `T_{0,v}`, hence all of it; so the open subscheme `Stab_V ∩ (T_0 × V) ⊂ T_0 × V` contains every point and equals `T_0 × V`. `Stab_V` is a subgroup containing `T_0 × V`, `F_{p′} × V`, `F_p × V`, hence `P`. ∎

Everything downstream (`hmul_of_stabIdeal`, `OrbitLocal`, `descAction_free`) is stated through this "iff", so it is unchanged.

### 4.5 Lemma 4.3 (Deligne's formula) (S5)

The note's proof uses only that `X` is noetherian and quasi-separated: Deligne's formula on `X` (prove it from the scheme case by étale descent along an affine étale cover `V → X`: `V ×_X V` is a qcqs scheme because `Δ_X` is quasi-compact, and Deligne's formula holds on qcqs schemes, Stacks 01Y3), and "a coherent module supported on `V(J)` is killed by a power of `J`". The Lean instance (`chart-deligne-state.md`) lists "`X` separated over `S`" among its added hypotheses; the only mathematical use I can see is that `V ×_X V` is then affine (closed in `V ×_S V`), which makes `exists_cross` a statement about one ring. For quasi-separated `X`, replace `V ×_X V` by a finite affine cover of it (or by a second affine étale cover of it), and take the maximum of the torsion exponents. I did not open `ChartDeligneCore` to confirm that this is the only use.

### 4.6 Map of changes to `notes/ahr-specialized-proof.md`

| Section | Status for quasi-separated `X` |
|---|---|
| §1 rational point | unchanged |
| §1 orbit, `H` closed | replace "X separated" by §4.1 (SGA 3 VI_B 1.4.2) |
| §1 Lemma 1.1 | unchanged (`o` quasi-compact because `X` is quasi-separated) |
| §2 thickenings | unchanged |
| §3 graded completion | unchanged |
| §4 Thm 4.1 uniqueness | Lemma U |
| §4 Lemma 4.2 | gerbe route as written, with `Q` quasi-separated by descent; Lean route: §4.4 Claim |
| §4 Lemma 4.3 | unchanged on paper; Lean: §4.5 |
| §4 Lemma 4.4 | unchanged (uses uniqueness = Lemma U) |
| §4 Glue, `θ` | Bhatt 1.1 (qcqs), not 0GHK |
| §4 Glue, pushout | Bhatt 1.4(1) (qcqs); the fpqc Remark is dropped |
| §4 "φ extends φₙ", "φ equivariant" | Corollary M′ instead of Lemma 4.5 |
| §5 Artin approximation | unchanged |
| §6 shrink | unchanged |
| §7 inputs | I1 Bhatt 1.1 is now genuinely needed; add I1′ Bhatt 1.4(1); drop I4 (Gabber 0APL); add SGA 3 VI_B 1.4.2, generic flatness, ZMT |

## 5. The proof of Theorem 6.8(ii), assembled

Let `M` be f.g., `X` quasi-separated locally of finite presentation over `S` with `D(M)_S`-action, `Z ⊂ M` with `D(M/Z)` of connected fibres (e.g. `M/Z` torsion-free). Assume `S` separated for the `S`-affine clause.

1. **Reduction.** As in §2 (Globalization): it suffices to produce, for `S` affine of finite type over `ℤ` and `X` of finite type over `S`, a `D(M)`-equivariant étale affine chart through every closed point. Closed points are dense (`X` is Jacobson), étale maps are open, so the charts are jointly surjective, and a finite subfamily suffices when `X` is quasi-compact.
2. **Chart Lemma, quasi-separated form** (= AHR Cor. 10.2 for `D(M)`): §1–§6 of the specialized note with the replacements of §4 above. Inputs beyond the note's: Bhatt 1.1 and 1.4(1) for qcqs spaces, SGA 3 VI_B 1.4.2, generic flatness, ZMT. Output: affine `U` with `G`-action, étale equivariant `(U, u) → (X, x)` (with `κ(u) = κ(x)` and `G_u = G_x` as a bonus).
3. **Family.** `U := ⊔_x U(x) → X` is an equivariant atlas in the sense of Definition 6.1(iv) (`S`-affine pieces since `S` is affine; finitely many pieces if `X` is quasi-compact, so then the atlas is `S`-affine, Remark 6.2).
4. **`Z`-FPR.** Theorem A.1(ii) with the group `D(M/Z)` (flat f.p., connected fibres) and the quasi-separated spaces `U(x)`, `X`: each `U(x) → X` is `D(M/Z)`-fixed-point reflecting; so is the disjoint union (`isZFPRAtlas_of_family_irreducible`). Hence `U → X` is a `Z`-FPR atlas.
5. **Quasi-compact clause.** If `X → S` is quasi-compact, finitely many charts cover `X`; their disjoint union is `S`-affine (`thm68_ii_qc`); for general separated `S`, finitely many affine opens `S_i` cover the image of `X` and `S_i → S` is affine.

This is the printed proof with Corollary 10.2 unpacked, and with (ii)'s only use of `M/Z` being Theorem A.1.

## 6. Consequences for the Lean

- `thm68_ii_of_charts` and `thm68_ii_qc` are correct conditional statements; the hypothesis `L : EtaleChartFamily act A U` is exactly what must be proved, not more.
- `ChartLemmaStatement` with `Space.IsSeparatedOver` replaced by `Space.IsQuasiSeparated` (over `S`) is the target. The theorems to change are the eight rows of §3, with the replacements of §4: `eq_of_agree_basicOpen_of_agree_thickening` → Corollary M′ (drop flatness, keep noetherian); `eq_of_agree_of_iInf`/`thm41_unique` → Lemma U; `exists_generic_stabilizer` → §4.4 Claim; `ChartDeligneInst` → §4.5; the 0GHK stub and `existsUnique_pushout`/`eq_on_kernelPair` → Bhatt 1.1 and 1.4(1) as stubs (new stubs: Bhatt's theorems are not in Stacks; the separated-target algebraization in Stacks does not cover them).
- The separated case stays as is; M′ would also simplify it.

## 7. What I did not verify

- The ASENS numbering of AHR's Corollary 10.2 (the print's "20.2"); I read arXiv v4 only.
- Bhatt's published numbering; I read the arXiv text in the scratchpad.
- Exact Stacks tags: 025G (flat monomorphism l.f.p. is an open immersion), 07VT, 07SQ, 086U, 06RC, 01Y3, and "flatness descends along faithfully flat maps" are cited from memory of their content; the tag numbers are as in the specialized note where it cites them, and otherwise unchecked.
- SGA 3 VI_B Cor. 1.4.2 (monomorphism of group schemes of finite type over a field is a closed immersion): statement standard, number unchecked.
- Lemma M, Corollary M′, Lemma U and the §4.4 Claim are my own arguments, written here for the first time; no independent read. The riskiest points are step (c) of Lemma M (the retraction argument on completions) and the `G`-stability of `W` in Lemma U (flat descent of flatness at a point); both are elementary but should get one independent read before formalization.
- I did not open `ChartDeligneCore` or `ChartStratumStab` to confirm that the separatedness uses there are exactly the ones I name; §3 is from the state notes and the docstrings grepped in `ChartEffectiveMain.lean`.
- Theorem A.1's proof is taken as given (it is in the print and already formalized as `AppendixA`).
