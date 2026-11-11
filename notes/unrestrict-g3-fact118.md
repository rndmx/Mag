# Unrestrict, group g3-fact118: Fact 11.8

Source: Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), pp. 174-175 (publisher PDF pages 49-50 of `~/Desktop/HDR/SemigroupForum-Proof.pdf`, read as page images). Lean read: `AlgMag/Sec11Formal.lean` (478-722), `AlgMag/Sec11SchemesFace.lean` (82-227, 327-413), `AlgMag/Sec11SpacesBase.lean` (26-158), `AlgMag/Sec11SpacesFace.lean` (131-219), `AlgMag/Sec10LiftsCore.lean` (79-92), `AlgMag/GeneralBaseMilnor.lean` (37-41), the 07SY stub `scratchpad/sl/src/.../Pushouts/ThickeningAffineSections.lean`. Nothing was compiled.

## 1. Printed statement (verbatim, p. 174)

> **Fact 11.8** The push-out of the diagram A(F)_T ← A(F)_T̄ → A(N)_T̄, in the category of algebraic spaces over T, exists and is denoted A(F)_T ⊔_{A(F)_T̄} A(N)_T̄. Moreover A(F)_T ⊔_{A(F)_T̄} A(N)_T̄ is an affine scheme over T and is in fact a push-out of A(F)_T ← A(F)_T̄ → A(N)_T̄ in the category whose objects are algebraic spaces over T and whose morphisms are D(M)_T-equivariant morphisms of algebraic spaces over T.

Context fixed by the print (proof of Prop 11.7, p. 174): "Let ι_T : T̄ → T be a first order thickening of affine schemes, over S. Let R and I ⊂ R such that T = Spec(R) and T̄ = Spec(R/I)." So in the print **T is affine and T̄ → T is a first order thickening**; F is a face of N, M a group (§2 conventions).

The statement has four clauses:
- (A) existence of the push-out in algebraic spaces over T;
- (B) it is an affine scheme over T;
- (C) D(M)_T acts on it and ν₁, ν₂ are equivariant (this is in the printed proof, p. 175, and is what Prop 11.7 uses: "By Fact 11.8, i and ν are D(M)_T-equivariant");
- (D) push-out in the category of algebraic spaces over T with equivariant morphisms.

## 2. What the Lean has, and what it adds

| Clause | Lean | Hypotheses beyond the print |
|---|---|---|
| (B) ring | `pushoutRing hF φ` (Sec11Formal:553): the subring R[F] ×_{(R/I)[F]} (R/I)[N] of the product, = ⊕_{n∈F} R.Xⁿ ⊕ ⊕_{n∈N∖F} (R/I).Xⁿ as in the print; `pushoutMap_surjective` (:580) | none; `φ` is any surjective ring map, weaker than a square-zero quotient |
| (A) in schemes | `milnorPushout` (Sec11SchemesFace:116): ∃! k : Spec Pu → Y for any scheme Y, from `milnor_pushout` (:97) + `milnor_desc` (Sec10LiftsCore:79) | `hι : Function.Surjective ι` only (print: first order thickening, stronger). `Scheme.{u}`, rings in `Type u`: universe bookkeeping. Target is a **scheme**, not an algebraic space |
| (A) in spaces | `glue` (Sec11SpacesBase:132): for any `IsAlgebraicSpace` P and compatible sections f ∈ P(Spec A), g ∈ P(Spec C), ∃! k ∈ P(Spec R') restricting to f, g; instantiated on the Milnor data `H := milnor_pushout` in Sec11SpacesFace:143 | `[SR B _]` on the four rings (site cutoff), `hqs`, `hker`, `hiq` (all true for this square, see §3). Stated for sections, i.e. S-morphisms Spec R' → P, not T-morphisms (see §3.A) |
| (C) | `coactP` (Sec11SchemesFace:200) the coaction on Pu; `coactP_fst`, `coactP_snd` (:212, :219): ν₁, ν₂ are M-graded, i.e. equivariant | `hι` surjective. **Not packaged** as "an action of D(M)_T on Spec Pu with ν₁, ν₂ equivariant" |
| (D) | not stated. Proved inline, for the one X at hand, as `ha` in Sec11SchemesFace:386-413 (schemes) and Sec11SpacesFace:179-219 (spaces) | — |
| graded lift | `homogeneous_pushout_lift` (Sec11Formal:696) | none; it is the affine, graded form of (D) used by `attractor_face_formallySmooth_affine` |

Conclusion of the audit: **no clause of Fact 11.8 is restricted in the Lean by a hypothesis absent from the print**. "T affine" is printed. `hι` surjective is weaker than printed. `[SR B]`/`[SM B M]` are the site size cutoffs, harmless (§3.E). What is missing is *statement*: (A) for spaces is only used, not named; (C) is only at ring level; (D) is not stated at all. The row's grade-3 reason ("the universal property for spaces and the equivariant clause are not stated") is about packaging, not about an added restriction.

## 3. Proofs of the printed clauses, from what the repo has

Notation: R = Γ(T), R̄ = R/I with I² = 0 (print), ι : R → R̄; A := R[F], C := R̄[N], B := R̄[F], Pu := pushoutRing = A ×_B C; p := pFst : Pu → A, q := pSnd : Pu → C, i := mapRingHom F ι : A → B, j := faceRingHom : C → B. `milnor_pushout` (Sec11SchemesFace:97) checks `MilnorData p q i j`: i ∘ p = j ∘ q, i surjective (`mapRingHom_surjective`), (p,q) jointly injective, and every compatible pair (x,y) lifts. Verified by reading: the four fields are the definition of the fibre product subring.

### 3.A Clause (A): push-out in algebraic spaces over T

*Step 1, schemes.* Stacks **0ET0** (Lemma 37.14.1, live statement checked 2026-11-06 in `notes/corrections-verified.md:1134`): A' → A surjective, B → A any ring map, B' = B ×_A A'; then Spec is a push-out of schemes. Here A' = R[F] → A = R̄[F] is surjective (ι surjective), B = R̄[N] → A = R̄[F] is `faceRingHom`. So Spec Pu is the push-out of schemes, as the print says. In the repo this is reproved without 0ET0: `isPushout_of_milnor H hqs hker` (Sec11SpacesBase:118) gives `IsPushout (sp i) (sp j) (sp p) (sp q)` in `Scheme`, from `milnor_desc`. The two side hypotheses hold: `hqs` = `pSnd_surjective N hF ι hι` (:104), `hker` = `pFst_ker N hF ι` (:108). No hypothesis on N, F, M beyond `IsFace F N` and M a group.

*Step 2, spaces.* Stacks **07SY** (Lemma 81.6.1, fetched live 2026-11-07): "Let S be a scheme. Let X → X' be a thickening of schemes over S and let X → Y be an affine morphism of schemes over S. Let Y' = Y ⊔_X X' be the pushout in the category of schemes. Then Y' is also a pushout in the category of algebraic spaces over S." Apply with X = A(F)_T̄ = Spec B, X' = A(F)_T = Spec A (thickening: i surjective with ker² = 0, `thick_of_ring` Sec11SchemesFace:28 / `magnetAlgebra_mul_eq_zero ι hi.sq_zero`), Y = A(N)_T̄ = Spec C (X → Y is a morphism of affine schemes, hence affine), Y' = Spec Pu. All four are S-schemes through T. 07SY gives: for every algebraic space Z over S, Hom_S(Spec Pu, Z) = Hom_S(Spec A, Z) ×_{Hom_S(Spec B, Z)} Hom_S(Spec C, Z). This is exactly `glue` (Sec11SpacesBase:132), whose proof is `existsUnique_section_of_isThickening_of_isAffineHom` (07SY in section form, currently a **stub with sorry**, `notes/REQUIRES_FULL_STACKS.md:14`) applied to `isPushout_of_milnor`.

*Over T rather than over S.* The print wants the push-out in spaces over T. Let Z → T be an algebraic space over T and f₁ : Spec A → Z, f₂ : Spec C → Z be T-morphisms agreeing on Spec B. They are in particular S-morphisms, so Step 2 gives a unique S-morphism k : Spec Pu → Z with k∘ν₁ = f₁, k∘ν₂ = f₂. The composite Spec Pu → Z → T and the structure map Spec Pu → T are two S-morphisms Spec Pu → T (T is an algebraic space over S) that agree after ν₁ and ν₂ (f₁, f₂ are over T); by the uniqueness part of Step 2 applied to Z := T they coincide, so k is a T-morphism. Uniqueness among T-morphisms is a fortiori. Hence Spec Pu is the push-out in algebraic spaces over T, with no extra hypothesis. (In Lean, "over S" is the site `BigFppfOver B S hS`, T-morphisms are sections of the fibre; this reduction is the standard one and needs no new lemma: `glue` with `P := yoneda.obj T`, or `isAlgebraicSpace_yoneda B S hS T`.)

Verified: statement of 0ET0 (from the checked note), statement of 07SY (live), the hypotheses of both on this square, the Lean statements of `glue`, `isPushout_of_milnor`, `milnor_desc`. Not verified: the body of the 07SY stub (it is `sorry`); its real Stacks module is not in the sparse build.

### 3.B Clause (B)

Spec Pu with structure map `sp π₁ ≫ t` (π₁ = `pushoutMap`, t : Spec R[N] → S through T). It is affine over T by construction. Nothing to prove.

### 3.C Clause (C): the action and equivariance of ν₁, ν₂

Print: "Since D(M)_T-equivariant morphisms of affine schemes correspond to M-graded morphisms, we obtain that A(F)_T ⊔ A(N)_T̄ is endowed with an action of D(M)_T and that ν₁, ν₂ are D(M)_T-equivariant." Concretely: Pu = ⊕_{n∈F} R.Xⁿ ⊕ ⊕_{n∈N∖F} R̄.Xⁿ is an M-graded ring (graded subring of the M-graded ring A × C), the coaction is Xⁿ ↦ Xⁿ ⊗ Xⁿ, and p, q are graded. In Lean: `coactP N hF ι hι : Pu →+* Pu[M]` (Sec11SchemesFace:200) is the coaction induced from `coactN N D` on R[N] through the surjection π₁ (`coactP_π`, :206); `coactP_fst` (:212) says mapRingHom p ∘ coactP = coactN F ∘ p and `coactP_snd` (:219) says mapRingHom q ∘ coactP = coactN N R̄ ∘ q. These are precisely "ν₁ and ν₂ are equivariant" in coaction form. Coassociativity and counit of `coactP` follow from those of `coactN` (`coactN_coassoc N _` is used at Sec11SpacesFace:232) by surjectivity of π₁ (`pushoutMap_surjective`); the proof of Prop 11.7 does not need them packaged, which is why they are not. No hypothesis beyond `hι` surjective.

Verified: the statements of `coactP`, `coactP_π`, `coactP_fst`, `coactP_snd`, `coact_face`, `coact_ker`, and that `coactP` is well defined only through `coact_ker` (the coaction kills ker π₁).

### 3.D Clause (D): the desc of equivariant maps is equivariant

Let Z be an algebraic space over T with a D(M)_T-action and f₁ : Spec A → Z, f₂ : Spec C → Z equivariant T-morphisms agreeing on Spec B; let k = f₁ ⊔ f₂ from 3.A. Claim: k is equivariant, i.e. m_Z ∘ (id × k) = k ∘ m_Pu as maps D(M)_T ×_T Spec Pu → Z.

Proof (the printed one, p. 175-176, made precise with repo lemmas). D(M)_T ×_T Spec Pu = Spec Pu[M], and Pu[M] = A[M] ×_{B[M]} C[M] with p[M], q[M], i[M], j[M] again Milnor data: `milnor_map H` (Sec11SchemesFace:126) proves `MilnorData (mapRingHom M p) (mapRingHom M q) (mapRingHom M i) (mapRingHom M j)`; i[M] is still square-zero surjective (`map_sq_zero _ hιq`, used at Sec11SpacesFace:191), q[M] surjective (`mapRingHom_surjective _ (pSnd_surjective ...)`), and the kernel condition transfers (`HM.ex y 0`, same lines). So by 3.A applied to HM, two T-morphisms Spec Pu[M] → Z are equal as soon as they agree after id × ν₁ and id × ν₂ (uniqueness in `glue HM`). Both sides agree after id × ν₁: m_Z ∘ (id × k) ∘ (id × ν₁) = m_Z ∘ (id × f₁) = f₁ ∘ m_A (f₁ equivariant) = k ∘ ν₁ ∘ m_A = k ∘ m_Pu ∘ (id × ν₁) (ν₁ equivariant, 3.C). Same with ν₂. Done. In the print these are items (i), (ii) on p. 176.

This is exactly what Lean already does, for Z := X and f₁ := yF, f₂ := x₀U, in `ha` (Sec11SpacesFace:179-219): `glue HM ... .unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩`, and the two goals are closed by `pb_sq` (functoriality squares for `cst` and for the coactions, from `coactP_fst`/`coactP_snd` through `sp_sq`), `pb_ss` (the action is natural), `res_eS`/`eS_congr` (restriction of the universal point), and the equivariance of yF, x₀U (`equiv_of_attPtS`). Replacing the last ingredient by a hypothesis gives the general clause (D). Nothing else in that proof depends on X being the given X. No hypothesis beyond those of 3.A.

Verified: read the whole `ha` block and the signatures of every lemma it calls; the only two uses of the specific sections are the two `equiv_of_attPtS` calls (lines 206, 219) and the identifications `hpFa'`, `hpSa'` (lines 204, 217), which become the hypotheses `hpFa`, `hpSa` of `glue`.

### 3.E Size hypotheses

`[SR B A]`, `[SR B C]`, `[SR B Pu]`, `[SR B R']`: discharged by `sr_sections T` (Sec11SpacesFace:82), `srMonoidAlgebra` (Sec11SpacesBase:63, needs `[SM B M]`), `sr_subring`/`srPushout` (Sec11SpacesFace:66). `[SM B M]`: #M below the site cutoff. The site cutoff is a strongly inaccessible-type bound chosen above everything in sight (`sr_iff`, Sec11SpacesBase:36); any T, M of the universe satisfy it after choosing B. Harmless, grade 1 as for Props 11.1-11.7 (fidelity rows 69-75 record "only SM").

## 4. Verdict

Fact 11.8: **UNRESTRICTED**. Every printed clause follows for the printed hypotheses (T affine, T̄ → T first order thickening; even ι merely surjective for (A) in schemes, (B), (C)) from `milnor_pushout`, `isPushout_of_milnor`, `glue`, `milnor_map`, `coactP_fst`, `coactP_snd`, `pb_sq`, `pb_ss`, `res_eS`; the "over T" refinement is the uniqueness part of `glue` applied to `yoneda.obj T`. No counterexample, no paper error. The only wall is not mathematical: `glue` rests on the 07SY stub (sorry), the same stub that already carries Props 11.1-11.7 and Cor 10.3 for spaces.

## 5. Lean plan (new file, e.g. `AlgMag/Sec11Fact118.lean`, importing `AlgMag.Sec11SpacesFace`)

1. `fact118_pushout_spaces`: specialise `glue` to `H := milnor_pushout N hF ι hι`, `hqs := pSnd_surjective`, `hker := pFst_ker`, `hiq := magnetAlgebra_mul_eq_zero ι hsq` with `hsq : ∀ x y, ι x = 0 → ι y = 0 → x*y = 0` (first order thickening; print), structure maps `hpFs`, `hpSs`, `rfl`, `hface₀` copied from Sec11SpacesFace:133-144. Statement: for every `IsAlgebraicSpace` P and compatible f ∈ P(Sv sF), g ∈ P(Sv s₀), ∃! k ∈ P(Sv (sp π₁ ≫ t)). This is clause (A) for spaces over S; add `fact118_overT`: the T-structure of k, by `(fact118_pushout_spaces (P := yoneda.obj T) ...).unique`.
2. `fact118_affine`: `IsAffine (Spec (CommRingCat.of Pu))`, instance, clause (B).
3. `fact118_action`: package `coactP` with `coactP_fst`, `coactP_snd`, plus `coactP_coassoc`/`coactP_counit` by `pushoutMap_surjective` and `coactN_coassoc` (one `obtain ⟨w, rfl⟩` each) — clause (C) as the print states it.
4. `fact118_equivariant_desc`: hypotheses `hX`, `aX`, f, g as in 1 with
   `hf : pb X (svHom B hS (coactN F Γ(T)) hF₁ρ) f = ss aX (eS B hS sF₁ (eU _ M)) (pb X (svHom B hS (cst _ M) hF₁c) f)` and the same `hg` for g over N, R̄; conclusion `pb X (svHom B hS (coactP ..) h₀ρ) k = ss aX (eS B hS s₁ (eU Pu M)) (pb X (svHom B hS (cst Pu M) h₀c) k)` for the k of 1. Proof: lines 179-219 of Sec11SpacesFace verbatim with `equiv_of_attPtS` replaced by `hf`, `hg`. Then Sec11SpacesFace's `ha` becomes `fact118_equivariant_desc ... (equiv_of_attPtS ...) (equiv_of_attPtS ...)` (edit of an existing file: after the build).
5. Scheme twins in `AlgMag.SmoothSchemes`: `milnorPushout` is already (A) for schemes; (D) for schemes is Sec11SchemesFace:386-413 with the same replacement, giving `fact118_equivariant_desc_scheme`.
6. Axioms: 1 and 4 inherit `sorryAx` from the 07SY stub until the real `Spaces.Pushouts.ThickeningAffineSections` is built; 2, 3, 5 are clean.
