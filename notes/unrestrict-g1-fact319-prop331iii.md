# Unrestricting Fact 3.19, Prop 3.31 (iii), Prop 3.32 (iii) (group g1-fact319-prop331iii)

Source: Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, read from
`HDR/SemigroupForum-Proof.pdf` (page images pp. 147–149 for 3.31/3.32, text `am.txt` ll. 1025–1030
for 3.19 and ll. 769–796 for the standing hypotheses of §3). Pure mathematics; nothing compiled, no
existing file changed. Lean statements quoted from the files named below, read today.

Standing hypotheses of §3 (p. 140, am.txt 769–796): "Let us fix a base scheme S. In this paper, an
S-space is an algebraic space over S. Let us fix an S-space X. Let us fix a commutative monoid M ...
We assume that A(M)_S acts on X ... a magnet N is by definition a submonoid N ⊂ M." No finiteness on
M, no separatedness, no size bound.

Stacks tags, read live today: **049J** (Def. 70.3.1: a functor is limit preserving / locally of
finite presentation if F(T) = colim F(T_i) for affine T = lim T_i directed; a transformation a : F → G
is limit preserving if every fibre functor F_y is), **04AK** (Prop. 70.3.10: for algebraic spaces,
f locally of finite presentation ⇔ f limit preserving as a transformation of functors).

---

## 1. Fact 3.19

### 1.1 Print (am.txt 1025–1030)

"Fact 3.19 Let N ⊂ M be a magnet. Assume f : X → Y is an A(M)_S-equivariant morphism of S-spaces.
If f is locally of finite presentation, then f^N : X^N → Y^N is locally of finite presentation.
Proof This follows from the definitions and [32, Tag 04AK]."

Here X^N, Y^N are functors (Def. 3.1); "locally of finite presentation" for f^N can only mean
Tag 049J (transformation of functors), and the proof cites 04AK to turn the hypothesis on f into
limit preservation. So the printed statement is: **f^N : X^N → Y^N is a limit preserving
transformation of functors**, for any commutative monoid M, any magnet N, any algebraic spaces X, Y.

### 1.2 Lean and what it adds

- `locallyOfFinitePresentation_repMap` (Sec11SchemesLimit.lean:312): X, Y, Zx, Zy schemes over S,
  `rx : RepresentsAttractor aX N (yoneda.obj Zx)`, `ry`, `z : Zx ⟶ Zy` compatible, M any
  commutative group (`[AddCommGroup M]` in that file's header).
- `isLocallyOfFinitePresentation_repMap_spaces` (Sec11SpacesFact.lean:239): X, Y, Zx, Zy
  algebraic spaces, `rx`, `ry`, `[AddCommGroup M] [SM B M]`.

Added beyond the print: (a) **representability of X^N and Y^N** (the printed statement is about the
functors); (b) **M a group** (print: commutative monoid); (c) `[SM B M]`, i.e. `#M < B.cutoff`
(Sec11SpacesBase.lean:31), a site-size cutoff.

None of (a), (b) is agreed anywhere in STATUS.md / the notes (checked: STATUS row "Fact 3.19" says
PARTIAL, "Monoid, non-representable form absent").

### 1.3 Proof of the printed statement without (a) and (b)

Fix an affine S-scheme T = lim_i T_i, a cofiltered limit of affine S-schemes (all in the site), with
rings R = colim R_i. Write A(N)_T = Spec R[N], and A(N)_T ×_T A(M)_T = Spec R[N][M] = Spec R[N × M]
(M a monoid; nothing uses inverses).

**Step 0 (points of X^N).** By Prop. 3.2 / the universal point, X^N(T) is the set of
x ∈ X(A(N)_T) such that the two maps A(N)_T ×_T A(M)_T → X_T ("act then x" and "x then act")
coincide, i.e. an equation E(x) in X(A(N)_T ×_T A(M)_T). In Lean this is
`attractorPtEquivOfUniversal (specU N T _ rfl)` (Representation.lean:67, Sec11SpacesLift.lean:57),
and the two sides of E are `pb X (rrS N T) ·` and `ss aX (eTS N T) (pb X (ccS N T) ·)`
(`vvS_equiv`, Sec11SpacesLift.lean). This step holds for any presheaf X and any monoid M.

**Step 1 (the two limits).** R[N] = colim R_i[N] and R[N × M] = colim R_i[N × M], because the monoid
algebra commutes with filtered colimits of rings. Hence A(N)_T = lim A(N)_{T_i} and
A(N)_T ×_T A(M)_T = lim (A(N)_{T_i} ×_{T_i} A(M)_{T_i}) as affine schemes. Lean: `isLimit_cN`,
`isLimit_cM` (Sec11SpacesFact.lean:214, 223).

**Step 2 (f is limit preserving).** By Tag 04AK, f : X → Y locally of finite presentation gives, for
every cofiltered limit of affines W = lim W_k, the two halves of the pullback property: (S) for
x ∈ X(W), k_0, y ∈ Y(W_{k_0}) with f(x) = y|_W there are k → k_0 and x_k ∈ X(W_k) with x_k|_W = x and
f(x_k) = y|_{W_k}; (I) if a, b ∈ X(W_k) have f(a) = f(b) and a|_W = b|_W then a|_{W_{k'}} = b|_{W_{k'}}
for some k' → k. Lean: `relativelyLimitPreserving_of_isLocallyOfFinitePresentation` and
`limit_square` (Sec11SpacesLimit.lean:36), used in Sec11SpacesFact.lean:246–261 exactly on the two
limits of Step 1.

**Step 3 (surjectivity half for f^N).** Let x ∈ X^N(T), i_0, y ∈ Y^N(T_{i_0}) with f^N(x) = y|_T. By
(S) on A(N)_T = lim A(N)_{T_i} there are j → i_0 and x_j ∈ X(A(N)_{T_j}) with x_j|_T = x and
f(x_j) = y|_{T_j} (as points of Y(A(N)_{T_j})). x_j need not be equivariant. The two sides of E(x_j)
lie in X(A(N)_{T_j} × A(M)); they agree after pullback to T (because E(x) holds) and after f (because
E(y|_{T_j}) holds and f is equivariant). By (I) on A(N)_T × A(M)_T = lim_k (A(N)_{T_k} × A(M)) there
is k → j with E(x_j|_{T_k}) true. So x_k := x_j|_{T_k} ∈ X^N(T_k), x_k|_T = x, f^N(x_k) = y|_{T_k}.

**Step 4 (injectivity half for f^N).** If x, x' ∈ X^N(T_i) with f^N(x) = f^N(x') and x|_T = x'|_T,
then x, x' ∈ X(A(N)_{T_i}) satisfy the hypotheses of (I) on A(N)_T = lim A(N)_{T_i}, so they agree on
some T_k. Hence colim X^N(T_i) → X^N(T) ×_{Y^N(T)} colim Y^N(T_i) is bijective: f^N is limit preserving
(Tag 049J, transformation form). ∎

Where the Lean proof uses representability: only to transport points of Zx, Zy to attractor points
(`rx.equiv`, `ry.equiv`, lines 262–263, 305–326) and to state the conclusion through Tag 0CM6
(`Space.isLocallyOfFinitePresentation_of_affineLimit_surjective`). Steps 3–4 are lines 251–304 of
Sec11SpacesFact.lean verbatim with `rx.equiv = id`. Where it uses M a group: nowhere in the argument;
the header `[AddCommGroup M]` (Sec11SpacesLift.lean:24) is inherited from the §11 smoothness files
(D(M) a torus). Monoid algebras `AddMonoidAlgebra R M` and `sp_inv` are fine for a monoid.

**Size.** The proof needs Spec R_T[N × M] in the site, i.e. `#M < B.cutoff`, since
R_T has size < cutoff and the cutoff is a strong limit (`contains_alg`, Prop337General.lean:49). The
site is a parameter containing S: for a given M one takes any site with cutoff > #M. So `[SM B M]`
is a universe/size cutoff with no mathematical content: **grade 1, harmless**.

**Verified:** Steps 0–4 by hand on paper against the print and the Lean proof text (lines 239–326
read in full); Tags 049J and 04AK read live; limit of monoid algebras is a one-line check
(colimits of rings are computed on underlying sets, and R[N] = ⊕_N R).

### 1.4 Lean plan (new file, nothing existing edited)

```
theorem relativelyLimitPreserving_attractorMap [AddCommMonoid M] [SM B M]
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : EquivariantHom aX aY)
    (hf : Space.IsLocallyOfFinitePresentation B S hS f.hom) (N : AddSubmonoid M) :
    RelativelyLimitPreserving B S hS (attractorMap f N)
```
Proof: `(relativelyLimitPreserving_iff_affineLimit_isPullback B S hS _).mpr`, then on `I D c hc hA hp`
build the two halves of `Types.isPullback_iff` from the body of
`isLocallyOfFinitePresentation_repMap_spaces` lines 251–304 with `rx.equiv`, `ry.equiv` replaced by
the identity on `AttractorPt` (`(attractor aX N).obj (op T) = AttractorPt aX N T` by definition,
Sec3Functorial.lean:200). Injectivity half: `limit_square … .2` on `lN` plus `vv_inj`. Cost: the
Sec11SpacesLift infrastructure (`PO2`, `eTS`, `rrS`, `ccS`, `muS`, `equiv_pullS`, `vvS_equiv`,
`attPtOfS`) is declared under `[AddCommGroup M]`; a copy of that section with `[AddCommMonoid M]` is
needed for the monoid form (no proof changes expected; `sp_inv` and `AddMonoidAlgebra` do not use
inverses). Then both existing theorems become corollaries (representable case) via Tag 0CM6 as now.

**Verdict: UNRESTRICTED proof.** Only `SM B M` remains, a harmless size cutoff.

---

## 2. Proposition 3.31 (iii)

### 2.1 Print (p. 147, page image)

"Proposition 3.31 Let Z be a monoid and let f : M → Z be a morphism of monoids. Let Y be a magnet of
Z and let N be f^{-1}(Y). Then N is a magnet of M. Assume that one of the following conditions holds
(i) X is affine over S, (ii) M and Z are finitely generated groups, (iii) M is cancellative,
Z = M^gp, N = Y and X is separated, then in each case we have an identification of functors
X^N = X^Y, where on the left-hand-side X is seen as an A(M)_S-space and on the right-hand-side as an
A(Z)_S-space (via A(Z)_S → A(M)_S dual to f : M → Z). In other words, with the notation of
Remark 3.4, we have X^{N⊂M} = X^{Y⊂Z}."

Proof of (iii) (pp. 148–149): "We have to show that for any T/S, Hom^{D(M^gp)_T}_T(A(N)_T, X_T) =
Hom^{A(M)_T}_T(A(N)_T, X_T). The inclusion ⊃ is clear. Reciprocally let φ : A(N)_T → X_T be
D(M^gp)_T-equivariant. We use that X is separated and that the schematic image of
A(N)_T ×_T D(M^gp)_T → A(N)_T ×_T A(M)_T is A(N)_T ×_T A(M)_T to prove that φ is A(M)_T-equivariant
(cf. the proof of Proposition 3.29 for similar arguments)."

Printed hypotheses of (iii): M cancellative (⇔ M → M^gp injective), Z = M^gp, "N = Y" (i.e. Y ⊂ M
inside M^gp, so f^{-1}(Y) = Y), X separated. **No finite generation of M or of Z.**

### 2.2 Lean (`prop331_iii`, Sec3Remaining.lean:1345, section header l. 1103)

```
variable {M Z : Type u} [AddCommMonoid M] [AddCommGroup Z] [AddMonoid.FG Z]
variable (hf : Function.Injective f) (hY : ∀ y ∈ Y, ∃ m, f m = y)
noncomputable def prop331_iii (hF : Presieve.IsSheaf … F) (hd : HasDensePullback F) (T) :
    AttractorPt act (Y.comap f) T ≃ AttractorPt (actAlong f act) Y T
```
Comparison with the print:
- `hf` = M cancellative (f : M → Z injective; print's f is M → M^gp). Same.
- `hY` = "N = Y" (Y ⊆ f(M)). Same.
- Z any abelian group, not only M^gp: more general.
- X: any sheaf with `HasDensePullback` (Sec5Etale.lean:1681); a separated algebraic space has it
  (`hasDensePullback_of_separated`, l. 1688). Weaker than printed, so fine.
- **`[AddMonoid.FG Z]`: the only added hypothesis.** Not on the Agreed list (STATUS.md row 82 says
  "(iii) Z f.g., Y <= f(M)", no agreement recorded).

### 2.3 Where FG Z is used, and the proof without it

I traced every use of the instance in section `Prop331` (ll. 1101–1363):
- `contains_of_inj` (l. 1150): `contains_M (contains_RT T)` for the monoid Z × Z, which is
  Sec5Etale.lean:759 `contains_M`, whose only job is `B.Contains (Spec R_T[Z × Z])`, proved from
  `AddMonoidAlgebra.finiteType_of_fg`. Then `Scheme.size_Spec_lt_of_mk_le_max` for subobjects.
- Nothing else: `actAlong`, `linMagnetHom`, `magnetIso`, `ptAlong`, `eInv`, `along_equivariant`
  (the printed argument: inject R_T[M × N] → R_T[Z × N], schematic density, `HasDensePullback`),
  `ptOfAlong` (`exists_affine_cover`, sheaf separation) and the two inverse laws use no finiteness.

Mathematical proof of the print without FG (it is the printed proof, spelled out): let
φ : A(N)_T → X_T be A(Z)_T-equivariant, T affine with ring R (the general T follows because X^N is
an fppf sheaf, Prop. 3.2, and equivariance is local: `ptOfAlong`, ll. 1318–1339). Equivariance for
A(M)_T is the equality of two maps A(N)_T × A(M)_T → X_T, i.e. of two points of X(Spec R[N × M]).
The ring map R[N × M] → R[N × Z] induced by id × f is injective (f injective, `mapDomain_injective`),
and it is the inclusion of a direct summand of free R-modules, so Spec R[N × Z] → Spec R[N × M] is
schematically dominant and stays so after any base change. The two points agree on Spec R[N × Z]
because φ is A(Z)-equivariant and Y ⊆ f(M) identifies N with Y. Since X is separated, the equaliser
of the two maps is a closed subscheme (Tag 01KM form used in Prop. 3.29's printed proof) containing a
schematically dense subscheme, hence everything. This is `along_equivariant` (l. 1164), whose only
site input is that Spec R_T[M × N], Spec R_T[Z × N] and Spec R_T[Z × Z] are objects of the site.

**Size.** These three affine schemes are in the site as soon as `#Z < B.cutoff` (`contains_alg`,
Prop337General.lean:49: `#P < cutoff` and `Spec R` in the site give `Spec R[P]` in the site; for
Z × Z use `#(Z × Z) ≤ max(#Z, ℵ_0) < cutoff`, `B.aleph0_lt_cutoff`). For the printed Z = M^gp,
`#M^gp ≤ max(#M, ℵ_0)`, so `#M < cutoff` suffices, and the site is a parameter. Hence FG Z can be
replaced by `[SM B Z]` (or `Fact (#Z < B.cutoff)`), a universe cutoff with no mathematical content.

**Verified:** page image p. 147–149 for the wording; each use of `AddMonoid.FG Z` in ll. 1101–1363
(the only one is l. 1152 via `contains_M`); the printed density argument by hand (free-module
splitting ⇒ universal injectivity ⇒ schematic dominance after base change; separated ⇒ closed
equaliser).

### 2.4 Lean plan (new file)

1. `contains_of_inj'` : same statement as `contains_of_inj` with `[Fact (#Z < B.cutoff)]` instead
   of FG, proof `P337.contains_alg (by simpa using Cardinal.mul_lt_of_lt …) (contains_RT T)` for
   Z × Z, then the existing `Scheme.size_Spec_lt_of_mk_le_max` line.
2. Re-state `along_equivariant`, `ptOfAlong`, `prop331_iii` with `[Fact (#Z < B.cutoff)]`; the
   proof bodies are unchanged (only `contains_of_inj` is swapped). Since the files cannot be
   edited now, this is a copy of ll. 1148–1363 in a new file with the one instance changed; after
   the build, the original section can simply have its `[AddMonoid.FG Z]` replaced, which is a
   one-token change.
3. For the printed form, instantiate `Z := Algebra.GrothendieckAddGroup M`, `f := .of`,
   `hf := of_injective` (as `prop332_iii_gp` does, Sec3Final.lean:1267), with
   `Fact (#(GrothendieckAddGroup M) < cutoff)` from `#M < cutoff` (`mk_le_of_surjective` from
   M × M → M^gp, `Cardinal.mul_lt_of_lt`).

**Verdict: UNRESTRICTED proof.** FG Z is only the site-size cutoff; `#Z < cutoff` is harmless
(grade 1).

---

## 3. Proposition 3.32 (iii)

### 3.1 Print (p. 149, page image)

"Proposition 3.32 Let L and N be arbitrary submonoids of M. Assume that one of the following
conditions holds (i) X is affine over S, (ii) M is a finitely generated abelian group, (iii) M is
cancellative, M^gp is finitely generated as abelian group, and X and X^N are separated algebraic
spaces, then we have canonical identifications (X^N)^L = X^{N∩L}, cf. 3.11 for the actions of A(M)_S
on X^N and X^L that we used implicitely on the left-hand sides."

Proof of (iii) (p. 150): "Using three times Proposition 3.31 and one time (ii), we have
(X^{N⊂M})^{L⊂M} = (X^{N⊂M^gp})^{L⊂M^gp} = X^{(L∩N)⊂M^gp} = X^{(N∩L)⊂M}."

Printed hypotheses of (iii): M cancellative, **M^gp finitely generated** (printed, so FG Z is not an
addition here), X a separated algebraic space, X^N a separated algebraic space.

### 3.2 Lean (Sec3Final.lean)

- `prop332_iii_of` (l. 1090): X any algebraic space, `hsep : IsSeparatedOver F`, f : M → Z injective
  into a f.g. group, and a hypothesis `hZ` = Prop 3.32 (ii) for the Z-action in the form
  "every point of X^{f(N) × f(L)}_{Z×Z} has the image in X(T) of a point of X^{f(N) ∩ f(L)}_Z".
  Conclusion: bijectivity of `χ ↦ (iterEquivBi T).symm (χ.toBi …)`, which is `iterOfInf`
  (Sec3Intersections.lean:455) unfolded.
- `prop332_iii_scheme` (l. 1197): X a separated **scheme**; `hZ` from `exists_toBi`
  (Sec3SchemeQuotient.lean:1636, Prop 3.32 (ii) for schemes).
- `prop332_iii_gp` (l. 1263): the printed instance Z = M^gp for schemes.
- `prop332_iii_atlas` (l. 1228): X separated algebraic space **plus** `hat : IsStronglyFPRAtlas`
  for the Z-action **plus** `hb : (f(N).FG ∧ f(L).FG) ∨ IsLimitPreserving X`.

Added beyond the print: for schemes nothing (and "X^N separated" is dropped, so the Lean statement
is stronger there). For algebraic spaces: the atlas `hat` and `hb`. Both come only from the old
proof of Prop 3.32 (ii) for spaces (`exists_inf_of_bi`, via `prop332` with an atlas).

### 3.3 Proof for algebraic spaces without `hat`, `hb`

The decision already taken (task text; `AlgMag/SDR4Final.lean`) is that Lemma D proves
Prop 3.32 (ii) for every algebraic space:
```
theorem prop332_space_final (hX : IsAlgebraicSpace B S hS X) {M} [AddCommGroup M] [AddGroup.FG M]
    {aX : AAction (fppfO B S hS) M X} {N L : AddSubmonoid M} (T) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T)
```
(SDR4Final.lean:33; no separatedness, no atlas, no `hb`). Apply it to the Z-action
`actAlong f aX` on X (Z = M^gp is a f.g. group: `AddGroup.fg_iff_addMonoid_fg.mpr`) and to the magnets
f(N), f(L) of Z. Given φ : AttractorPt (biAct (actAlong f aX)) (f(N).prod f(L)) T, put
Ψ := (iterEquivBi T).symm φ : IterPt. Surjectivity gives χ : AttractorPt (actAlong f aX) (f(N) ⊓ f(L)) T
with iterOfInf χ = Ψ, i.e. (iterEquivBi T).symm (χ.toBi _) = (iterEquivBi T).symm φ, hence
χ.toBi _ = φ and χ.toPoint = φ.toPoint by `AttractorPt.toPoint_toBi` (as in l. 1203). This is
exactly the hypothesis `hZ` of `prop332_iii_of`. Therefore

`prop332_iii_space (hX) (hsep : IsSeparatedOver X) (N L) (T) : Function.Bijective (fun χ => (iterEquivBi T).symm (χ.toBi …))`

holds for every separated algebraic space X over any S, M cancellative with M^gp f.g., N, L arbitrary.
This is the printed (iii) minus the printed hypothesis "X^N separated" (the Lean route runs the
chain on X^{N × L}_{M × M} instead of on X^N, as the docstring at l. 1086 explains, so nothing about
X^N is needed). The remaining inputs of `prop332_iii_of` are: `toPoint_injective_of_embed`
(Cor. 3.30 for M embedded in a f.g. group, needs X separated: printed), `ptAlong` / `ptOfAlong`
(Prop 3.31 (iii), §2 above, with Z = M^gp f.g. as printed), `hasDensePullback_of_separated`.

**Verified:** the statement of `prop332_space_final` and that `iterOfInf` is definitionally the map in
`prop332_iii_of` (Sec3Intersections.lean:455–458 vs Sec3Final.lean:1096–1097, same term); the
derivation of `hZ` from surjectivity by hand; the printed hypotheses on the page image.

### 3.4 Lean plan (new file importing `AlgMag.Sec3Final` and `AlgMag.SDR4Final`)

```
theorem prop332_iii_space (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (N L : AddSubmonoid M) (T : BigFppfOver B S hS) :
    Function.Bijective fun χ : AttractorPt aX (N ⊓ L) T =>
      (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L) (hKinf' N L)) :=
  prop332_iii_of hf hX hsep (fun φ => by
    haveI : AddGroup.FG Z := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
    obtain ⟨χ, hχ⟩ := (prop332_space_final hX (aX := actAlong f aX) (N := N.map f) (L := L.map f) T).2
      ((iterEquivBi T).symm φ)
    refine ⟨χ, ?_⟩
    have : χ.toBi _ = φ := (iterEquivBi T).symm.injective hχ   -- unfold iterOfInf
    rw [← this]; exact (AttractorPt.toPoint_toBi _ χ).symm) T
```
plus `prop332_iii_space_gp` with `Z := GrothendieckAddGroup M`, `f := .of`, as in `prop332_iii_gp`.
Check: `prop332_space_final` is stated for `[AddCommGroup M] [AddGroup.FG M]` and `aX` implicit; the
instance for `Z` comes from the section's `[AddMonoid.FG Z]`. Imports: SDR4Final does not import
Sec3Final (or vice versa) as far as the headers show; the new file imports both.

**Verdict: UNRESTRICTED proof** (algebraic spaces, no atlas, no `hb`; the printed "X^N separated" is
not needed). FG of M^gp is printed, not added.

---

## Summary

| Statement | Added hypothesis | Verdict |
|---|---|---|
| Fact 3.19 | representability of X^N, Y^N; M a group; `SM B M` | UNRESTRICTED: limit-preserving transformation `attractorMap f N` for any monoid M; `SM B M` is a harmless size cutoff |
| Prop 3.31 (iii) | `AddMonoid.FG Z` | UNRESTRICTED: only used for site membership; `#Z < cutoff` suffices (grade 1) |
| Prop 3.32 (iii) | spaces: atlas + f.g./limit-preserving | UNRESTRICTED: `prop332_iii_of` + `prop332_space_final` (Lemma D) |
