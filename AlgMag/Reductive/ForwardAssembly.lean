/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TorusConjFinal
import AlgMag.Reductive.Equivalence
import AlgMag.Reductive.RegularSlice
import AlgMag.Reductive.ParabolicGenStep
import AlgMag.Reductive.AttractorSmooth
import AlgMag.Reductive.PushCocharacter
import AlgMag.Sec3Affine
import AlgMag.Sec15PureMagnets
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import AlgMag.Reductive.RankOneReflectionAlt
import AlgMag.Reductive.TangentRoots
import AlgMag.Reductive.AttractorSubgroup
import AlgMag.Weyl.Normalizer
import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Character

/-!
# Forward assembly: `r1_of_reductive'` and `dimCount_of_reductive'`

The two geometric inputs of (⇒) in `Equivalence.lean`, proved here with the same conclusions
from **explicitly named** geometric hypotheses (no `sorry`, no axiom).

* (R1), T4 steps 2–4 of `equivalence-reductive/T-steps.md`: the geometry (the closed orbit
  `X = Z·x₀ ≅ Z/B⁺` (G1), the second fixed point `x₁ = g x₀` of `B⁻`, `x₁ ≠ x₀`) is packaged in
  `R1Datum`; the algebra is proved: T1-dyn (`exists_unipotent_conjugate_eq_of_isMaximalTorus'`)
  in `B⁺`, transport to `H` (`conjugate_comapOfSurjective`), the normaliser bridge (D6), and
  `σ ≠ 1` from `σ = 1 ⇒ n ∈ C(k)`.
* (DC): from (i) at Lie level and T4 ray by ray (`dim Lie U_{Z_α}(λ) ≤ 1`), via
  `finrank_lie_eq_sum_rootSpace`, `sum_rootSpace_eq_posDim` and a fibrewise count of rays.
-/

set_option linter.style.haveILetI false

suppress_compilation

open Magnetism TauCeti TauCeti.HopfIdeal TauCeti.Cocharacter WithConv AlgMag.Weyl
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]

section D6

variable (π : H →ₐc[k] MonoidAlgebra k X)

omit [DecidableEq X] in
/-- **(D6) Normaliser bridge.** A `k`-point stabilising `ker π` normalises `T` with some `σ`. -/
theorem exists_isNormalizingWith_of_conjugate_eq (hπ : Function.Surjective π)
    {y : WithConv (H →ₐ[k] k)}
    (h : (HopfIdeal.kerOfSurjective π hπ).conjugate y = HopfIdeal.kerOfSurjective π hπ) :
    ∃ σ : X ≃* X, Weyl.IsNormalizingWith π k y σ := by
  have hmem : y ∈ BialgHom.normalizerPoints π hπ := (BialgHom.mem_normalizerPoints _ _ _).2 h
  set w := BialgHom.normalizerCharacterEquiv π hπ ⟨y, hmem⟩
  have hc : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom y⁻¹) =
      (MonoidAlgebra.domCongr k k w).toAlgHom.comp π.toAlgHom := by
    ext x
    have h1 := BialgHom.normalizerCoordinateMap_apply π hπ ⟨y, hmem⟩ x
    have h2 := AlgHom.congr_fun (BialgHom.normalizerCoordinateMap_eq_domCongr π hπ ⟨y, hmem⟩)
      (π x)
    simp only [BialgHom.coe_toAlgHom, AlgEquiv.coe_toAlgHom] at h2
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, AlgEquiv.coe_toAlgHom]
    rw [← h2, h1]
  have hc' := HopfAlgebra.comp_pointConjugationAlgHom_eq_symm_comp π.toAlgHom y _ hc
  refine ⟨w.symm, ?_⟩
  unfold Weyl.IsNormalizingWith
  have hinc : (Algebra.TensorProduct.includeLeft : k →ₐ[k] k ⊗[k] MonoidAlgebra k X) =
      Algebra.ofId k _ := Subsingleton.elim _ _
  rw [MulAut.conj_apply, hinc, ← HopfAlgebra.comp_pointConjugationAlgHom, Weyl.twistPoint,
    AlgMag.Reductive.torusPoint, ofConv_toConv, AlgHom.comp_assoc, hc']
  congr 2

end D6

variable [IsAlgClosed k]

omit [DecidableEq X] in
lemma weylMagnet_one_le_bot' : Weyl.weylMagnet (1 : X ≃* X) ≤ ⊥ :=
  AddSubmonoid.closure_le.2 (by rintro _ ⟨χ, rfl⟩; simp)

/-- **Geometric data for (R1) at a root `α`** (T4 steps 1–2 of T-steps.md). `Q = k[B⁺]` with
`B⁺ = P_Z(λ)` the parabolic of `Z = G^{ℤα}`, given as a quotient `f : H ↠ Q`.

* `le_Z`: `B⁺ ⊆ Z` on `k`-points;
* `l`, `hP`: the cocharacter `λ` of `B⁺` with `P_{B⁺}(λ) = B⁺` (via `parCochar`,
  `parabolic_parCochar_eq_bot`);
* `TQ`, `hTQ`, `hT`: `T ⊆ B⁺`, maximal there; `hlT`: `λ` factors through `T`;
  `hcent`: (D5) `T` is central in `Z_{B⁺}(λ)`;
* `g`, `SQ`, `hS`, `hSQ` (**(G1) + step 2**): the second fixed point `x₁ = g x₀` of `B⁻` on
  the closed orbit `Z/B⁺`, with `g ∈ Z(k)`, so `g⁻¹Tg ⊆ Stab(x₀) = B⁺`, a maximal torus there;
* `notC` (**`x₁ ≠ x₀`** with `C ⊆ B⁺`): no `b g` with `b ∈ B⁺(k)` lies in `C(k) = G^0(k)`. -/
structure R1Datum (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (α : Additive X) where
  Q : Type u
  [ring : CommRing Q]
  [hopf : HopfAlgebra k Q]
  [dec : DecidableEq Q]
  [ft : Algebra.FiniteType k Q]
  [sm : Algebra.Smooth k Q]
  f : H →ₐc[k] Q
  surj : Function.Surjective f
  le_Z : ∀ b : WithConv (Q →ₐ[k] k),
    BialgHom.mapDomain f b ∈ attractorSubgroup π (lineMagnet α) k
  l : Q →ₐc[k] LaurentPolynomial k
  hP : parabolicDefiningHopfIdeal l = ⊥
  TQ : HopfIdeal k Q
  hTQ : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k Q) TQ
  hlT : TQ.toIdeal ≤ RingHom.ker (l : Q →ₐ[k] LaurentPolynomial k)
  hcent : ∀ (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv (Q →ₐ[k] A)),
    (leviDefiningHopfIdeal l).toIdeal ≤ RingHom.ker (ofConv g) →
    TQ.toIdeal ≤ RingHom.ker (ofConv t) → g * t = t * g
  hT : TQ.comapOfSurjective f surj = HopfIdeal.kerOfSurjective π hπ
  g : WithConv (H →ₐ[k] k)
  g_mem : g ∈ attractorSubgroup π (lineMagnet α) k
  SQ : HopfIdeal k Q
  hSQ : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k Q) SQ
  hS : SQ.comapOfSurjective f surj = (HopfIdeal.kerOfSurjective π hπ).conjugate g
  notC : ∀ b : WithConv (Q →ₐ[k] k), BialgHom.mapDomain f b * g ∉ attractorSubgroup π ⊥ k

attribute [instance] R1Datum.ring R1Datum.hopf R1Datum.dec R1Datum.ft R1Datum.sm

/-- **(R1) at `α` from `R1Datum`** (T4 step 2): `n := u g` with `u ∈ U⁺(k)` from T1-dyn. -/
theorem r1_of_r1Datum (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    {α : Additive X} (D : R1Datum π hπ α) :
    ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
      n ∈ attractorSubgroup π (lineMagnet α) k ∧ σ ≠ 1 := by
  obtain ⟨u, -, hu⟩ := exists_unipotent_conjugate_eq_of_isMaximalTorus' D.l D.hP D.TQ D.hTQ
    D.hlT D.hcent D.SQ D.hSQ
  set u' : WithConv (H →ₐ[k] k) := BialgHom.mapDomain D.f u
  have hconj : (HopfIdeal.kerOfSurjective π hπ).conjugate (u' * D.g) =
      HopfIdeal.kerOfSurjective π hπ := by
    rw [HopfIdeal.conjugate_mul, ← D.hS, ← D.hT, ← hu, show u' = _ from BialgHom.mapDomain_apply D.f u,
      HopfIdeal.conjugate_comapOfSurjective]
  obtain ⟨σ, hσ⟩ := exists_isNormalizingWith_of_conjugate_eq π hπ hconj
  refine ⟨u' * D.g, σ, hσ, Subgroup.mul_mem _ (D.le_Z u) D.g_mem, ?_⟩
  rintro rfl
  exact D.notC u ((mem_attractorSubgroup_iff_weylMagnet_le π hπ hσ ⊥).2 weylMagnet_one_le_bot')

/-! ### The built part of `R1Datum`: `B⁺ = P_Z(λ)` inside `Z = G^{ℤα}` -/

section Built

/-- **`T ⊆ P(λ)`** (port of ParabolicGenRay `parabolic_le_ker_torus`, whose file is in
progress): the torus lies in the dynamic parabolic of its own cocharacter. -/
theorem parabolic_le_ker_torus' {H' : Type u} [CommRing H'] [HopfAlgebra k H'] [DecidableEq H']
    [Algebra.FiniteType k H'] [Algebra.Smooth k H'] (π' : H' →ₐc[k] MonoidAlgebra k X) (ψ : X →* Multiplicative ℤ) :
    (parabolicDefiningHopfIdeal (π'.cocharacter ψ)).toIdeal ≤
      RingHom.ker (π' : H' →ₐ[k] MonoidAlgebra k X) := by
  classical
  let lT : MonoidAlgebra k X →ₐc[k] LaurentPolynomial k :=
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm.toBialgHom.comp
      (MonoidAlgebra.mapDomainBialgHom k ψ)
  have hl : lT.comp π' = π'.cocharacter ψ := rfl
  set e : WithConv (MonoidAlgebra k X →ₐ[k] MonoidAlgebra k X) := toConv (AlgHom.id k _)
  have hconst : constPoint (MonoidAlgebra k X) (BialgHom.mapDomain π' e) =
      BialgHom.mapDomain π' (constPoint (MonoidAlgebra k X) e) := by
    apply WithConv.ofConv_injective
    rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
    rfl
  have he : e ∈ levi (MonoidAlgebra k X) lT := by
    rw [levi_eq_top]; exact Subgroup.mem_top _
  have hlevi : BialgHom.mapDomain π' e ∈ levi (MonoidAlgebra k X) (π'.cocharacter ψ) := by
    rw [mem_levi_iff, conjugate_mapDomain (π'.cocharacter ψ) π' lT hl, mem_levi_iff.1 he, hconst]
  have hle := (TauCeti.Cocharacter.negativeCoefficientIdeal_le_ker_iff _ _).2
    (levi_le_parabolic hlevi)
  intro x hx
  rw [parabolicDefiningHopfIdeal, HopfIdeal.ofIdealOfPointsSubgroup_toIdeal] at hx
  have h := hle hx
  rw [RingHom.mem_ker, BialgHom.mapDomain_apply, WithConv.ofConv_toConv] at h
  exact h

open CategoryTheory in
/-- **Maximal tori descend along a surjection**: if `I.comap p` is a maximal torus of `H'`,
then `I` is a maximal torus of `Q` (`H' ⧸ I.comap p ≅ Q ⧸ I`). -/
theorem isMaximalTorus_of_comapOfSurjective {H' Q : Type u} [CommRing H'] [HopfAlgebra k H']
    [CommRing Q] [HopfAlgebra k Q] [Algebra.FiniteType k H'] [Algebra.FiniteType k Q]
    (p : H' →ₐc[k] Q) (hp : Function.Surjective p) (I : HopfIdeal k Q)
    (h : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H') (I.comapOfSurjective p hp)) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k Q) I := by
  have iso : ∀ J : HopfIdeal k Q,
      FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k H', (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          (J.comapOfSurjective p hp) ≅
        FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k Q, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ J := by
    intro J
    let q : _root_.CommHopfAlgCat.of k H' ⟶ CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k Q) J :=
      _root_.CommHopfAlgCat.ofHom p ≫ CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k Q) J
    have hq : ∀ x, q.hom x = (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k Q) J).hom (p x) :=
      fun x => by
        simp only [q, _root_.CommHopfAlgCat.hom_comp, _root_.CommHopfAlgCat.hom_ofHom,
          BialgHom.comp_apply]
    have hqs : Function.Surjective q.hom := by
      intro y
      obtain ⟨z, hz⟩ := CommHopfAlgCat.mkQuotient_surjective (_root_.CommHopfAlgCat.of k Q) J y
      obtain ⟨x, rfl⟩ := hp z
      exact ⟨x, (hq x).trans hz⟩
    have hk : HopfIdeal.kerOfSurjective q.hom hqs = J.comapOfSurjective p hp := by
      ext x
      rw [HopfIdeal.mem_kerOfSurjective, hq, HopfIdeal.mem_comapOfSurjective]
      exact CommHopfAlgCat.mkQuotient_eq_zero_iff (_root_.CommHopfAlgCat.of k Q) J (p x)
    exact ObjectProperty.isoMk _
      (_root_.CommHopfAlgCat.Hom.quotientIsoOfKerOfSurjectiveEq q hqs hk)
  have key : ∀ J : HopfIdeal k Q, torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k H', (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          (J.comapOfSurjective p hp)) ↔ torusCommHopfAlgProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k Q, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ J) :=
    fun J => ⟨fun t => (torusCommHopfAlgProperty k).prop_of_iso (iso J) t,
      fun t => (torusCommHopfAlgProperty k).prop_of_iso (iso J).symm t⟩
  rw [HopfIdeal.isMaximalTorus_iff] at h ⊢
  refine ⟨(key I).1 h.1, fun J hJ hJI => ?_⟩
  have := h.2 (J.comapOfSurjective p hp) ((key J).2 hJ)
    ((HopfIdeal.comapOfSurjective_le_comapOfSurjective_iff p hp).2 hJI)
  exact (HopfIdeal.comapOfSurjective_le_comapOfSurjective_iff p hp).1 this

/-- **Points of `C = G^0` commute with points of `T`.** -/
theorem commute_torusPt_of_mem_bot (π : H →ₐc[k] MonoidAlgebra k X) {A : Type u} [CommRing A]
    [Algebra k A] (τ : MonoidAlgebra k X →ₐ[k] A) (g : WithConv (H →ₐ[k] A))
    (hg : magnetIdeal (torusGrading π) ⊥ ≤ RingHom.ker g.ofConv) :
    Commute (toConv (τ.comp π.toAlgHom)) g := by
  have hconj : toConv (τ.comp π.toAlgHom) * g * (toConv (τ.comp π.toAlgHom))⁻¹ = g := by
    apply WithConv.ofConv_injective
    apply AlgHom.toLinearMap_injective
    apply LinearMap.ext
    intro a
    induction a using DirectSum.Decomposition.inductionOn (torusGrading π) with
    | zero => simp
    | @homogeneous χ m =>
      obtain ⟨a, ha⟩ := m
      change (toConv (τ.comp π.toAlgHom) * g * (toConv (τ.comp π.toAlgHom))⁻¹).ofConv a =
        g.ofConv a
      rw [conj_torusPt_apply π τ g ha]
      by_cases hχ : χ = 0
      · subst hχ
        rw [toMul_zero, ← MonoidAlgebra.one_def, map_one, one_mul]
      · have h0 : g.ofConv a = 0 := hg (mem_magnetIdeal_of_notMem (by simpa using hχ) ha)
        rw [h0, mul_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
  exact mul_inv_eq_iff_eq_mul.1 hconj

variable (π : H →ₐc[k] MonoidAlgebra k X) (α : Additive X) (ψ : X →* Multiplicative ℤ)

/-- `k[Z]`, `Z = G^{ℤα}`. -/
abbrev ZAlg : Type u := H ⧸ (magnetHopfIdeal π (lineMagnet α)).toIdeal

/-- `O(G) ↠ O(Z)`. -/
abbrev zMk : H →ₐc[k] ZAlg π α :=
  Bialgebra.Quotient.mkBialgHom (magnetHopfIdeal π (lineMagnet α)).toIdeal

lemma zMk_eq_zero {x : H} (hx : x ∈ magnetIdeal (torusGrading π) (lineMagnet α)) :
    zMk π α x = 0 := by
  rw [← magnetHopfIdeal_toIdeal] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.2 hx

lemma ker_zMk_le_ker_torus :
    RingHom.ker (zMk π α : H →ₐ[k] ZAlg π α) ≤ RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X) := by
  intro x hx
  have hx' : x ∈ (magnetHopfIdeal π (lineMagnet α)).toIdeal := by
    simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
  rw [magnetHopfIdeal_toIdeal] at hx'
  exact magnetIdeal_le_ker_torus π _ hx'

/-- The torus `T ⊆ Z`. -/
noncomputable def piZ : ZAlg π α →ₐc[k] MonoidAlgebra k X :=
  descBialgHom (zMk π α) Ideal.Quotient.mk_surjective π (ker_zMk_le_ker_torus π α)

lemma piZ_apply (x : H) : piZ π α (zMk π α x) = π x :=
  congrArg (fun f : H →ₐc[k] MonoidAlgebra k X => f x)
    (descBialgHom_comp (zMk π α) Ideal.Quotient.mk_surjective π (ker_zMk_le_ker_torus π α))

/-- The cocharacter `λ = ψ ∘ π` of `Z`. -/
noncomputable def zCochar : ZAlg π α →ₐc[k] LaurentPolynomial k := (piZ π α).cocharacter ψ

lemma zCochar_apply (x : H) : zCochar π α ψ (zMk π α x) = π.cocharacter ψ x := by
  simp only [zCochar, BialgHom.cocharacter, BialgHom.comp_apply, piZ_apply]

variable [Algebra.FiniteType k H] [Algebra.Smooth k H]

local instance zDec : DecidableEq (ZAlg π α) := Classical.decEq _
local instance zSmooth : Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _

/-- `k[B⁺]`, `B⁺ = P_Z(λ)`. -/
abbrev BAlg : Type u := ZAlg π α ⧸ (parabolicDefiningHopfIdeal (zCochar π α ψ)).toIdeal

/-- `O(G) ↠ O(B⁺)`. -/
noncomputable def bMk : H →ₐc[k] BAlg π α ψ :=
  (Bialgebra.Quotient.mkBialgHom (parabolicDefiningHopfIdeal (zCochar π α ψ)).toIdeal).comp
    (zMk π α)

lemma bMk_apply (x : H) : bMk π α ψ x = Ideal.Quotient.mk _ (zMk π α x) := rfl

lemma bMk_surjective : Function.Surjective (bMk π α ψ) := fun y => by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨x, rfl⟩

/-- `B⁺ ⊆ Z` on points. -/
lemma mapDomain_bMk_le {A : Type u} [CommRing A] [Algebra k A]
    (b : WithConv (BAlg π α ψ →ₐ[k] A)) :
    magnetIdeal (torusGrading π) (lineMagnet α) ≤
      RingHom.ker (BialgHom.mapDomain (bMk π α ψ) b).ofConv := by
  intro x hx
  rw [RingHom.mem_ker, BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
  change b.ofConv (bMk π α ψ x) = 0
  rw [bMk_apply, zMk_eq_zero π α hx, map_zero, map_zero]

lemma bMk_mem_attractor (b : WithConv (BAlg π α ψ →ₐ[k] k)) :
    BialgHom.mapDomain (bMk π α ψ) b ∈ attractorSubgroup π (lineMagnet α) k :=
  (mem_attractorSubgroup π).2 (mapDomain_bMk_le π α ψ b)

lemma ker_bMk_le_ker_torus :
    RingHom.ker (bMk π α ψ : H →ₐ[k] BAlg π α ψ) ≤
      RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X) := by
  intro x hx
  have h1 : zMk π α x ∈ (parabolicDefiningHopfIdeal (zCochar π α ψ)).toIdeal := by
    rw [RingHom.mem_ker] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.1 hx
  have h2 := parabolic_le_ker_torus' (piZ π α) ψ h1
  rw [RingHom.mem_ker] at h2 ⊢
  have := piZ_apply π α x
  simp only [BialgHom.coe_toAlgHom] at h2 ⊢
  rw [← this]; exact h2

/-- The torus `T ⊆ B⁺`. -/
local instance bDec : DecidableEq (BAlg π α ψ) := Classical.decEq _

noncomputable def piQ : BAlg π α ψ →ₐc[k] MonoidAlgebra k X :=
  descBialgHom (bMk π α ψ) (bMk_surjective π α ψ) π (ker_bMk_le_ker_torus π α ψ)

lemma piQ_apply (x : H) : piQ π α ψ (bMk π α ψ x) = π x :=
  congrArg (fun f : H →ₐc[k] MonoidAlgebra k X => f x)
    (descBialgHom_comp (bMk π α ψ) (bMk_surjective π α ψ) π (ker_bMk_le_ker_torus π α ψ))

lemma piQ_surjective (hπ : Function.Surjective π) : Function.Surjective (piQ π α ψ) := fun y => by
  obtain ⟨x, rfl⟩ := hπ y
  exact ⟨_, piQ_apply π α ψ x⟩

/-- `T` as a Hopf ideal of `B⁺`. -/
noncomputable def TQ (hπ : Function.Surjective π) : HopfIdeal k (BAlg π α ψ) :=
  HopfIdeal.kerOfSurjective (piQ π α ψ) (piQ_surjective π α ψ hπ)

lemma TQ_comap (hπ : Function.Surjective π) :
    (TQ π α ψ hπ).comapOfSurjective (bMk π α ψ) (bMk_surjective π α ψ) =
      HopfIdeal.kerOfSurjective π hπ := by
  ext x
  rw [HopfIdeal.mem_comapOfSurjective, TQ, HopfIdeal.mem_kerOfSurjective,
    HopfIdeal.mem_kerOfSurjective, piQ_apply]

lemma TQ_isMaximalTorus (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ)) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k (BAlg π α ψ)) (TQ π α ψ hπ) :=
  isMaximalTorus_of_comapOfSurjective (bMk π α ψ) (bMk_surjective π α ψ) _
    (by rw [TQ_comap]; exact hT)


lemma parCochar_bMk : (parCochar (zCochar π α ψ)).comp (bMk π α ψ) = π.cocharacter ψ := by
  ext x
  have h := congrArg (fun f : ZAlg π α →ₐc[k] LaurentPolynomial k => f (zMk π α x))
    (parCochar_comp (zCochar π α ψ))
  simp only [BialgHom.comp_apply] at h ⊢
  rw [← zCochar_apply, ← h]
  rfl

lemma TQ_le_ker_parCochar (hπ : Function.Surjective π) :
    (TQ π α ψ hπ).toIdeal ≤
      RingHom.ker (parCochar (zCochar π α ψ) : BAlg π α ψ →ₐ[k] LaurentPolynomial k) := by
  intro y hy
  obtain ⟨x, rfl⟩ := bMk_surjective π α ψ y
  rw [HopfIdeal.mem_toIdeal, TQ, HopfIdeal.mem_kerOfSurjective, piQ_apply] at hy
  rw [RingHom.mem_ker]
  have h := congrArg (fun f : H →ₐc[k] LaurentPolynomial k => f x) (parCochar_bMk π α ψ)
  simp only [BialgHom.comp_apply] at h
  simp only [BialgHom.coe_toAlgHom]
  rw [h]
  simp [BialgHom.cocharacter, hy]

/-- **(D5)**: the Levi of `B⁺` centralizes `T`, when `⟨α, ψ⟩ ≠ 0`. -/
lemma TQ_central (hπ : Function.Surjective π) (hψ : pairingHom ψ α ≠ 0)
    (A : Type u) [CommRing A] [Algebra k A] (g t : WithConv (BAlg π α ψ →ₐ[k] A))
    (hg : (leviDefiningHopfIdeal (parCochar (zCochar π α ψ))).toIdeal ≤ RingHom.ker (ofConv g))
    (ht : (TQ π α ψ hπ).toIdeal ≤ RingHom.ker (ofConv t)) : g * t = t * g := by
  classical
  set f := bMk π α ψ
  have hinj : Function.Injective (BialgHom.mapDomain f (A := A)) := by
    intro a b hab
    apply WithConv.ofConv_injective
    ext y
    obtain ⟨x, rfl⟩ := bMk_surjective π α ψ y
    have := congrArg (fun z => z.ofConv x) hab
    simpa [BialgHom.mapDomain_apply] using this
  have hker : RingHom.ker π.toAlgHom ≤ RingHom.ker (BialgHom.mapDomain f t).ofConv := by
    intro x hx
    rw [RingHom.mem_ker, BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
    apply ht
    rw [HopfIdeal.mem_toIdeal, TQ, HopfIdeal.mem_kerOfSurjective]
    change piQ π α ψ (f x) = 0
    rw [piQ_apply]; exact hx
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := π.toAlgHom) hπ
  let τ : MonoidAlgebra k X →ₐ[k] A := (Ideal.Quotient.liftₐ (RingHom.ker π.toAlgHom)
    (BialgHom.mapDomain f t).ofConv fun a ha => hker ha).comp e.symm.toAlgHom
  have hτ : toConv (τ.comp π.toAlgHom) = BialgHom.mapDomain f t := by
    apply WithConv.ofConv_injective
    ext x
    rw [ofConv_toConv]
    show (Ideal.Quotient.liftₐ (RingHom.ker π.toAlgHom) (BialgHom.mapDomain f t).ofConv
      fun a ha => hker ha) (e.symm (π.toAlgHom x)) = _
    rw [show e.symm (π.toAlgHom x) = Ideal.Quotient.mk _ x from e.symm_apply_eq.2 rfl]
    rfl
  have hlevi : BialgHom.mapDomain f g ∈ levi A (π.cocharacter ψ) := by
    have hgL : g ∈ levi A (parCochar (zCochar π α ψ)) := by
      rw [← quotientPointsSubgroup_leviDefiningHopfIdeal _ (CommAlgCat.of k A)]
      exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).2
        fun y hy => hg (HopfIdeal.mem_toIdeal.2 hy)
    have hconst : constPoint A (BialgHom.mapDomain f g) =
        BialgHom.mapDomain f (constPoint A g) := by
      apply WithConv.ofConv_injective
      rw [BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
      rfl
    rw [mem_levi_iff, conjugate_mapDomain (π.cocharacter ψ) f _ (parCochar_bMk π α ψ),
      mem_levi_iff.1 hgL, hconst]
  have h1 := (magnetIdeal_torusGrading_comap_bot_le_ker_iff (π := π) (ψ := ψ) _).2 hlevi
  have h2 := mapDomain_bMk_le π α ψ g
  have hbot : magnetIdeal (torusGrading π) ⊥ ≤ RingHom.ker (BialgHom.mapDomain f g).ofConv := by
    refine le_trans (magnetIdeal_anti_pure (torusGrading π)
      (N := (⊥ : Magnet ℤ).comap (pairingHom ψ) ⊓ lineMagnet α) ?_) ?_
    · intro χ hχ
      obtain ⟨h0, n, rfl⟩ := hχ
      have : n * pairingHom ψ α = 0 := by
        simpa [AddSubmonoid.mem_comap, AddSubmonoid.mem_bot, map_zsmul] using h0
      rcases mul_eq_zero.1 this with hn | hn
      · simp [hn]
      · exact absurd hn hψ
    · rw [magnetIdeal_inf]; exact sup_le h1 h2
  have hc := commute_torusPt_of_mem_bot π τ _ hbot
  rw [hτ] at hc
  apply hinj
  rw [map_mul, map_mul]
  exact hc.symm.eq

/-- **Geometric data for (R1)** at `α`, for a cocharacter `ψ`: only (G1) and the second fixed
point. Everything else in `R1Datum` is built (`Q = k[B⁺]`, `f`, `λ̄`, `P_{B⁺}(λ̄) = B⁺`,
`B⁺ ⊆ Z`, `T ⊆ B⁺` maximal, (D5)). -/
structure R1Geom (hπ : Function.Surjective π) where
  g : WithConv (H →ₐ[k] k)
  g_mem : g ∈ attractorSubgroup π (lineMagnet α) k
  SQ : HopfIdeal k (BAlg π α ψ)
  hSQ : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k (BAlg π α ψ)) SQ
  hS : SQ.comapOfSurjective (bMk π α ψ) (bMk_surjective π α ψ) =
    (HopfIdeal.kerOfSurjective π hπ).conjugate g
  notC : ∀ b : WithConv (BAlg π α ψ →ₐ[k] k), BialgHom.mapDomain (bMk π α ψ) b * g ∉
    attractorSubgroup π ⊥ k

/-- `R1Geom` gives `R1Datum`. -/
noncomputable def R1Geom.toR1Datum {hπ : Function.Surjective π}
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (hψ : pairingHom ψ α ≠ 0) (G : R1Geom π α ψ hπ) : R1Datum π hπ α where
  Q := BAlg π α ψ
  sm := smooth_parQuot (zCochar π α ψ)
  f := bMk π α ψ
  surj := bMk_surjective π α ψ
  le_Z := bMk_mem_attractor π α ψ
  l := parCochar (zCochar π α ψ)
  hP := parabolic_parCochar_eq_bot (zCochar π α ψ)
  TQ := TQ π α ψ hπ
  hTQ := TQ_isMaximalTorus π α ψ hπ hT
  hlT := TQ_le_ker_parCochar π α ψ hπ
  hcent := TQ_central π α ψ hπ hψ
  hT := TQ_comap π α ψ hπ
  g := G.g
  g_mem := G.g_mem
  SQ := G.SQ
  hSQ := G.hSQ
  hS := G.hS
  notC := G.notC

end Built

variable [Algebra.FiniteType k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **(⇒), (R1)**, same statement as `r1_of_reductive`, from one `R1Geom` per root (for some
cocharacter `ψ`). -/
theorem r1_of_reductive' (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hG : letI : Algebra.Smooth k H := hred.smooth
      ∀ α ∈ roots π, ∃ ψ : X →* Multiplicative ℤ, pairingHom ψ α ≠ 0 ∧
        Nonempty (R1Geom π α ψ hπ)) :
    ∀ α ∈ roots π, ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
      n ∈ attractorSubgroup π (lineMagnet α) k ∧ σ ≠ 1 := by
  letI : Algebra.Smooth k H := hred.smooth
  intro α hα
  obtain ⟨ψ, hψ, ⟨G⟩⟩ := hG α hα
  exact r1_of_r1Datum π hπ (G.toR1Datum π α ψ hT hψ)

/-! ### (DC) -/

open scoped Classical in
/-- **Ray count from T4**: if each ray carries total root-space dimension `≤ 1`, then
`dim U(λ_f) ≤ #rays`. -/
theorem posDim_le_posRays (π : H →ₐc[k] MonoidAlgebra k X) (f : Additive X →+ ℤ)
    (hray : ∀ α ∈ posRoots π f,
      ∑ β ∈ (posRoots π f).filter (fun β => SameRayRel β α),
        Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul β)) ≤ 1) :
    posDim π f ≤ posRays π f := by
  classical
  unfold posDim posRays
  set s := posRoots π f
  set q : Additive X → Quotient (raySetoid (X := X)) := Quotient.mk _
  rw [← Finset.sum_fiberwise_of_maps_to (g := q) (t := s.image q)
    (fun x hx => Finset.mem_image_of_mem q hx), Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun y hy => ?_
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hy
  refine le_of_eq_of_le ?_ (hray α hα)
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext β
  simp only [Finset.mem_filter, q]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, Quotient.exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, Quotient.sound h2⟩

omit [DecidableEq X] in
/-- **`X` is torsion-free when `T = D(X)` is a (maximal) torus**: `k[X] ≅ k[T]` is reduced with
connected spectrum (`isMulTorsionFree_of_isReduced_monoidAlgebra_of_connectedSpace`). -/
theorem isTorsionFree_of_isMaximalTorus
    (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ)) :
    Module.IsTorsionFree ℤ (Additive X) := by
  have ht := ((HopfIdeal.isMaximalTorus_iff _ _ _).1 hT).1
  set A := H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal
  haveI : ConnectedSpace (PrimeSpectrum A) :=
    connectedSpace_of_geometricallyConnected k A (ht.geometricallyConnected)
  haveI : Algebra.Smooth k A := ht.smooth
  haveI : IsReduced A := isReduced_of_smooth k _
  have hkerI : (HopfIdeal.kerOfSurjective π hπ).toIdeal = RingHom.ker π.toAlgHom := by
    ext x; rw [HopfIdeal.mem_toIdeal, HopfIdeal.mem_kerOfSurjective, RingHom.mem_ker]; rfl
  let e : A ≃ₐ[k] MonoidAlgebra k X :=
    (Ideal.quotientEquivAlgOfEq k hkerI).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := π.toAlgHom) hπ)
  haveI : IsReduced (MonoidAlgebra k X) := isReduced_of_injective e.symm.toRingHom e.symm.injective
  haveI hc : ConnectedSpace (PrimeSpectrum (MonoidAlgebra k X)) := by
    let h := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
    exact h.surjective.connectedSpace h.continuous
  haveI := isMulTorsionFree_of_isReduced_monoidAlgebra_of_connectedSpace k X
  rw [Module.isTorsionFree_int_iff_isAddTorsionFree]
  exact ⟨fun n hn => IsMulTorsionFree.pow_left_injective (M := X) hn⟩

open scoped Classical in
/-- **(⇒), (DC)**, same statement as `dimCount_of_reductive`, from
* `hLie0` (**(i) at Lie level**): `dim 𝔤₀ ≤ dim Lie T`;
* `hT4` (**T4**, `dim Lie U_{Z_α}(λ) = 1`): for every `f` and every `f`-positive root `α`,
  the `f`-positive roots on the ray of `α` carry total root-space dimension `≤ 1`. -/
theorem dimCount_of_reductive' (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (_hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hLie0 : Module.finrank k (rootSpace π 0) ≤
      Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)))
    (hT4 : ∀ (f : Additive X →+ ℤ), ∀ α ∈ posRoots π f,
      ∑ β ∈ (posRoots π f).filter (fun β => SameRayRel β α),
        Module.finrank k (Derivation.adjointWeightSpace π (Additive.toMul β)) ≤ 1) :
    ∃ ψ : X →* Multiplicative ℤ, (∀ α ∈ roots π, pairingHom ψ α ≠ 0) ∧
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) ≤
        Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) +
          posRays π (pairingHom ψ) + posRays π (-pairingHom ψ) := by
  haveI := isTorsionFree_of_isMaximalTorus π hπ hT
  have : Algebra.FiniteType k (MonoidAlgebra k X) :=
    Algebra.FiniteType.of_surjective π.toAlgHom hπ
  haveI : Monoid.FG X := MonoidAlgebra.fg_of_finiteType (R := k)
  haveI : Module.Finite ℤ (Additive X) :=
    Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2
      (Monoid.fg_iff_add_fg.1 inferInstance))
  haveI : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  obtain ⟨ψ, hψ⟩ := exists_generic_cocharacter (roots π) (roots_finite π)
    (fun α hα => ne_zero_of_mem_roots hα)
  refine ⟨ψ, hψ, ?_⟩
  have hsum := finrank_lie_eq_sum_rootSpace π
  rw [sum_rootSpace_eq_posDim π (pairingHom ψ) hψ] at hsum
  have h1 := posDim_le_posRays π (pairingHom ψ) (hT4 _)
  have h2 := posDim_le_posRays π (-pairingHom ψ) (hT4 _)
  omega

end AlgMag.Reductive


