# Dropping "S separated" (Props. 3.31 (ii), 3.32 (ii)) and the coproduct clause (Thm. 6.8 (ii))

[AM] = Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, read from `HDR/SemigroupForum-Proof.pdf` (text `am.txt`).
Pure mathematics only: nothing was compiled, and no existing file was changed.

## 0. What the print says (checked in am.txt)

- §3, p. 140, standing hypotheses: $S$ is a scheme, $X$ is an algebraic space over $S$, and $A(M)_S$ acts on $X$. Neither $S$ nor $X$ is assumed separated.
- Prop. 3.31 (ii): the only hypothesis is that $M$ and $Z$ are finitely generated groups. Prop. 3.32 (ii): the only hypothesis is that $M$ is a finitely generated abelian group. Neither assumes $X$ separated, $X$ locally of finite presentation, or $S$ separated.
- Prop. 3.2: $X^N$ is an fppf sheaf on $Sch/S$. Cor. 3.30: if $X$ is separated, $X^N\to X$ is a monomorphism.
- Def. 6.1 (iv): an equivariant atlas is étale and surjective, from a disjoint union of $D(M)_S$-stable $S$-affine schemes.
- Thm. 6.8 (p. 158): $M$ finitely generated, $X$ quasi-separated and locally of finite presentation, and either (i) $X$ separated or (ii) $M/Z$ torsion-free. Then a $Z$-FPR atlas exists. The statement has no clause about coproducts and no hypothesis that $S$ is separated.

Consequently, the three extra hypotheses of `prop331_separated` / `prop332_separated` (X separated, X lfp, `[S.IsSeparated]`) come from the separated route of the formalization, not from the print.

## 1. Task 1: dropping $S$ separated

### 1.1 Shortest route: the general case already has no hypothesis on $S$

`AlgMag/SDR4Final.lean` states

- `prop331_space_final (hX : IsAlgebraicSpace B S hS X) … : Function.Bijective (ptAlong aX …)`,
- `prop332_space_final (hX : IsAlgebraicSpace B S hS X) … : Function.Bijective (iterOfInf …)`,

for any scheme $S$ and any algebraic space $X$. This is Theorem 331B / 332B of `notes/prop331-332-two-statements.tex`, proved through Lemma D (§"The descent lemma" there). Its conclusion is the conclusion of `prop331_separated` / `prop332_separated`, for the same `ptAlong` and `iterOfInf`. So both separated statements follow without `[S.IsSeparated]`, `hsep`, `hfp`, `hZ` or `hM`:

```lean
theorem prop331_anyS … (hX : IsAlgebraicSpace B S hS X) … (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong act : AttractorPt act (Y.comap f) T → AttractorPt (actAlong f act) Y T) :=
  AlgMag.SD.prop331_space_final hX T
theorem prop332_anyS … := AlgMag.SD.prop332_space_final hX T
```

Not verified: that `SDR4Final.lean` builds and prints `[propext, Classical.choice, Quot.sound]`. I ran no build, because a build is running. `grep` finds no `sorry` or `axiom` in `AlgMag/`. `SDR4_00UD` (`SDR4Step2.lean:21`) is a theorem, so the 00UD hypothesis of `lemmaD-lean-round3.md` is discharged. `SDR4Final.lean` (Nov 7 00:37) is newer than `SepProp33.lean` (Nov 6 23:00). The implicit binders of `prop331_space_final` (`{f} {Y} {aX}`) have to be matched against `prop331_separated` (`act f Y` explicit). Variables: `SepProp33` has `[AddGroup.FG M] [AddGroup.FG Z]`, which matches.

### 1.2 Zariski localization of the separated route (independent of Lemma D)

**Claim.** Assume $X$ is separated and locally of finite presentation over an arbitrary scheme $S$. Then $\theta\colon X^{f^{-1}(Y)}_M\to X^Y_Z$ and $\alpha\colon X^{N\cap L}\to (X^N)^L$ are bijective at every $T\to S$.

*Step 1 (restriction to an open $V\subset S$).* Let $T$ be a $V$-scheme, seen as an $S$-scheme through $V\subset S$. Then:
- $D(M)_V\times_V T=D(M)_T$ and $A(N)_V\times_V T=A(N)_T$, since both are $\mathrm{Spec}\,\mathbb Z[\,\cdot\,]\times T$;
- $(X\times_S V)\times_V T= X\times_S T=X_T$, by pasting of cartesian squares (a formal fact about fibre products);
- the actions coincide, being base changes of the same action map.

So $(X_V)^N(T)=\mathrm{Hom}^{D(M)_T}_T(A(N)_T,X_T)=X^N(T)$. Likewise $(X_V)^Y_Z(T)=X^Y_Z(T)$, and $((X_V)^N)^L(T)=(X^N)^L(T)$ via the description of [AM, Prop. 3.9] used in the proof of 332B. Under these identifications $\theta$ and $\alpha$ are the same maps, because both are defined by precomposition ($\varphi\mapsto\varphi\circ A(f)$, $h\mapsto h\circ\mathrm{mult}$), and precomposition does not see the base.
- $X_V\to V$ is separated by Stacks 03KL (separation axioms are stable under base change), and locally of finite presentation by Stacks 03XR.
- An fppf covering of a $V$-scheme in $Sch/V$ is one in $Sch/S$, and conversely for $S$-schemes lying over $V$. So the sheaf property of Prop. 3.2 restricts.

*Step 2 (affine case of $S$).* If $V$ is affine, it is separated (Stacks 01KN). The existing theorems `prop331_separated` / `prop332_separated` apply to $X_V\to V$ and give bijectivity at every $V$-scheme.

*Step 3 (gluing).* Let $\{S_i\}$ be an affine open covering of $S$, let $T\to S$, and put $T_i=T\times_S S_i$. These form a Zariski covering of $T$, hence an fppf covering (Stacks 021N). $T_{ij}:=T_i\times_T T_j$ lies over $S_i$, so the bijectivity of Step 2 for $S_i$ applies at $T_{ij}$. Neither $S_i\cap S_j$ nor $T_{ij}$ needs to be affine, so no separatedness of $S$ enters.
- Injectivity: if $\theta(\varphi)=\theta(\varphi')$, then $\varphi|_{T_i}=\varphi'|_{T_i}$ for all $i$, so $\varphi=\varphi'$ because $X^N$ is separated as a presheaf (Prop. 3.2).
- Surjectivity: given $\psi\in X^Y(T)$, there is a unique $\varphi_i\in X^N(T_i)$ with $\theta(\varphi_i)=\psi|_{T_i}$. On $T_{ij}$, $\theta(\varphi_i|_{T_{ij}})=\psi|_{T_{ij}}=\theta(\varphi_j|_{T_{ij}})$, and injectivity at $T_{ij}$ gives $\varphi_i=\varphi_j$ there. By Prop. 3.2 the $\varphi_i$ glue to $\varphi\in X^N(T)$. Then $\theta(\varphi)|_{T_i}=\psi|_{T_i}$ for all $i$, so $\theta(\varphi)=\psi$ ($X^Y$ is a sheaf).
- For $\alpha$ the argument is the same word for word, with $(X^N)^L$ a sheaf: it is $X^{N\times L}_{M\times M}$, proof of 332A.

*Gluing for algebraic spaces.* Points of $X^N(T)$ are morphisms $A(N)_T\to X_T$. Gluing them along the open covering $\{A(N)_{T_i}\}$ of $A(N)_T$ uses only that $X$ is an fppf sheaf, which is part of the definition of an algebraic space (Stacks 025Y). Equivariance of the glued map is checked locally, and this is exactly the content of Prop. 3.2. Uniqueness of the descended maps is used only through injectivity of $\theta$ at the $T_{ij}$. In the separated route that injectivity is Cor. 3.30 (via $\mathrm{ev}$); in the Lemma D route it is Step 1 of Lemma D.

**No obstruction** exists at the level of attractors: every construction is compatible with restriction to opens of $S$. The only obstruction is the atlas. Def. 6.1 (iv) asks for $S$-affine pieces, and this is not local on $S$; `prop331-332-two-statements.tex`, Remark "Reduction to $S$ affine", gives the doubled-origin example. That is why the localization has to happen **before** Thm. 6.8 is invoked. It is also why one cannot instead replace $X$ by its open $X_V$ while keeping the base $S$ (`StronglyFPRNoteThm.overOpen`): an affine chart of $X_V$ is affine over $V$, but not over $S$ when $V\to S$ is not affine.

**Checked:** Steps 1–3 line by line on paper. Stacks 03KL, 03XR, 01KN, 021N and 025Y were read on stacks.math.columbia.edu today; their statements are as used. Also 01SG (affine to separated is affine: the reason `isAffineHom_structMap` needs `S.IsSeparated`), 0BCU (used in the doubled-origin remark) and 03H4 (points of fibre products surject).

### 1.3 Lean plan for 1.2 (only needed if 1.1 is not accepted)

Missing in `AlgMag/`: a change of base site to an open $V\subset S$. I searched for `restrictBase`, `overOpen`, `BigFppfOver B V`; only `overOpen` exists, a subfunctor over the same $S$, which is not enough (see above). `chart-stubs.md` mentions a Stacks module `ChangeOfBigSite.lean`. I did not open it, since `.lake` is off limits. To write:
1. A functor `ιV : BigFppfOver B V hV ⥤ BigFppfOver B S hS`, composition with $V\to S$, with `B.Contains V` from `B.Contains S`. Also: it is fully faithful onto objects over $V$, and preserves and reflects fppf covers.
2. `X_V := ιV.op ⋙ X`: `IsAlgebraicSpace` (sheaf; diagonal; atlas $W\times_S V$), `Space.IsSeparatedOver`, `Space.IsLocallyOfFinitePresentation`, plus the restricted `AAction`.
3. `AttractorPt act_V N T ≃ AttractorPt act N (ιV T)`, commuting with `ptAlong`, `iterOfInf` and `AttractorPt.baseChange`.
4. The gluing: copy the pattern of `ptAlong_injective` / `ptAlong_surjective` (`Sec3Final.lean` ~958–1004), which already proves bijectivity from local bijectivity plus `isSheaf_attractor`. Use the cover $T\times_S S_i$ (pull back `S.affineCover`) in place of `exists_affine_cover T`.
5. Apply `prop331_separated` / `prop332_separated` on each affine $S_i$ (instance `IsSeparated` from `IsAffine`).

Items 1–3 are the cost, and they are generic infrastructure. Route 1.1 costs one line, so I recommend 1.1.

## 2. Task 2: the clause "for each coproduct in the site" of `thm68_ii_proved`

**On paper the clause is vacuous.** $Sch$ has all disjoint unions, and the print (Thm. 6.8, proof of A.2: "consider $U:=\bigsqcup_x U(x)$") uses one. The clause exists only because `BigFppfSite` has a size cutoff. For an arbitrary index type `A`, the coproduct of the `U a` need not be an object of `B`, and then the conclusion of `thm68_ii_proved` says nothing.

**It is not automatic for the family that `thm68_ii_proved` returns**: that index set is $\Sigma_{u\in|U_0|} I_u$, with no size bound. **It is provable from the printed hypotheses** by choosing one chart per point of an atlas. This is the argument of `FinalNonQCAtlas.exists_small_charts` for Thm. 6.8 (i), and it uses no separatedness of $X$:
1. Let $U_0\to X$ be an atlas (`hX.exists_atlas`). For each point $u\in U_0$, `exists_charts_at_qs` gives affine equivariant étale charts, one of which hits the image of $u$. Choose one: $c(u)$. Index set $A:=|U_0|$, and $\#A\le 2^{\mathrm{size}\,U_0}$ (`mk_scheme_le`).
2. Joint surjectivity: every point of $X$ comes from $U_0$ (`Space.isSurjective_of_presheafSurjective`). So `hit` holds, and `covers_of_hit` gives the `covers` field. `isAffineHom_structMap` gives `isAffineHom` under `[S.IsSeparated]`, which `thm68_ii_proved` already assumes. This yields an `EtaleChartFamily` on $A$.
3. Each chart is affine, hence quasi-compact. It is étale over $X$, and $X$ is locally of finite presentation over $S$, so the chart is locally of finite type over $S$ (`chartsOfFiniteType_of_lfp`, `SpacesLimitA1.lean:391`, which takes exactly `hlfp : … (toT1 X)`). So its size is at most `S.size` (`Scheme.size_le_of_locallyOfFiniteType`).
4. With $\mu=\max(2^{\mathrm{size}\,U_0},\mathrm{size}\,S)<$ `B.cutoff` (`B.cutoff_isStrongPrelimit U_0.left.property`, `hS`), `exists_cofan_of_size` gives $V$ and an `IsColimit`.
5. `thm68_ii_of_charts hX L hV hMZ hirr` (or `isZFPRAtlas_of_family_irreducible`) gives the $Z$-FPR atlas $v\colon V\to X$.

New statement (same hypotheses as `thm68_ii_proved`, still `[S.IsSeparated]`):
`∃ (V) (actV) (v : yoneda.obj V ⟶ X), IsZFPRAtlas actV act v Z`, which is the printed form of Thm. 6.8 (ii) via `ExistsZFPRAtlas`.

New code: a variant `exists_small_family_qs` of `ChartQSTop.exists_family_qs` (`ChartQSTop.lean:251`). It should `choose` a single `i` from `hhit` instead of keeping all `I u`, and then follow `exists_small_charts` lines 79–102 and `thm68_atlas` lines 113–118. All the lemmas named above exist (I read their statements). The new code was not compiled.

`[S.IsSeparated]` itself **cannot** be dropped from the $S$-affine form of Thm. 6.8. Doubled-origin plane, $X=A_1$, $M=0$: no étale chart over the origin is $S$-affine (Stacks 0BCU). This is the author decision of 2026-11-06 in `partial-state.md`, and the same obstruction as in §1.2.
