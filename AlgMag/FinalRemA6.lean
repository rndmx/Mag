/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Finsupp.Weight

/-!
# Remark A.6 of *Algebraic Magnetism*

"If `G → S` is smooth, the `n`-th order thickenings of the unit section are finite locally free."
The paper gives no proof. Local form: `A` a smooth `R`-algebra with an augmentation `e : A → R` of kernel `I`; then
`A/I^{n+1}` is finite projective over `R`.

Proof: `P = I/I²` is finite projective; `A/I^{n+1}` is `R`-linearly isomorphic to the truncation
`T_n(P) = Sym(P)/Sym(P)₊^{n+1} = ⨁_{k ≤ n} Sym^k P` (a section of `I → P` gives `T_n(P) → A/I^{n+1}`, formal smoothness gives a
map back, both composites are the identity plus a nilpotent operator); `T_n(P)` is a direct summand of
`T_n(R^d) = R[x₁,…,x_d]/(x)^{n+1}`, free on the monomials of degree `≤ n`. The truncation carries all the `Sym^k` at once.
-/

noncomputable section

namespace AlgMag.Final.RemA6

universe u

open Ideal

section Unipotent

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]

/-- An `R`-algebra endomorphism of `C = R + J`, `J` nilpotent, that is the identity modulo `J²` on generators of `J`, is bijective. -/
theorem bijective_of_unipotent (J : Ideal C) (G : Set C) (hG : J = span G) (m : ℕ) (hm : J ^ m = ⊥)
    (hC : ∀ c : C, ∃ r : R, c - algebraMap R C r ∈ J) (θ : C →ₐ[R] C)
    (hθ : ∀ g ∈ G, θ g - g ∈ J ^ 2) : Function.Bijective θ := by
  have hGJ : ∀ g ∈ G, g ∈ J := fun g hg => hG ▸ Ideal.subset_span hg
  have hθ1 : ∀ g ∈ G, θ g - g ∈ J := fun g hg => Ideal.pow_le_self two_ne_zero (hθ g hg)
  have hstab : ∀ j ∈ J, θ j ∈ J := by
    intro j hj
    rw [hG] at hj
    induction hj using Submodule.span_induction with
    | mem g hg => simpa using J.add_mem (hθ1 g hg) (hGJ g hg)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, map_mul]; exact J.mul_mem_left _ hx
  have hν0 : ∀ c, θ c - c ∈ J := by
    intro c
    obtain ⟨r, hr⟩ := hC c
    have e : θ c - c = θ (c - algebraMap R C r) - (c - algebraMap R C r) := by
      simp
    rw [e]
    exact J.sub_mem (hstab _ hr) hr
  have hν1 : ∀ j ∈ J, θ j - j ∈ J ^ 2 := by
    intro j hj
    have hj' := hj
    rw [hG] at hj'
    induction hj' using Submodule.span_induction with
    | mem g hg => exact hθ g hg
    | zero => simp
    | add x y hx' hy' hx hy =>
      rw [map_add, add_sub_add_comm]
      exact (J ^ 2).add_mem (hx (hG ▸ hx')) (hy (hG ▸ hy'))
    | smul a x hx' hx =>
      have hxJ : x ∈ J := hG ▸ hx'
      rw [smul_eq_mul, map_mul, show θ a * θ x - a * x = (θ a - a) * θ x + a * (θ x - x) by ring]
      refine (J ^ 2).add_mem ?_ ((J ^ 2).mul_mem_left _ (hx hxJ))
      rw [pow_two]
      exact Ideal.mul_mem_mul (hν0 a) (hstab x hxJ)
  have hνk : ∀ k, ∀ j ∈ J ^ (k + 1), θ j - j ∈ J ^ (k + 2) := by
    intro k
    induction k with
    | zero => intro j hj; simpa using hν1 j (by simpa using hj)
    | succ k ih =>
      intro j hj
      rw [pow_succ] at hj
      induction hj using Submodule.mul_induction_on' with
      | mem_mul_mem x hx y hy =>
        rw [map_mul, show θ x * θ y - x * y = (θ x - x) * θ y + x * (θ y - y) by ring]
        refine Ideal.add_mem _ ?_ ?_
        · rw [show k + 1 + 2 = (k + 2) + 1 by ring, pow_succ]
          exact Ideal.mul_mem_mul (ih x hx) (hstab y hy)
        · rw [show k + 1 + 2 = (k + 1) + 2 by ring, pow_add]
          exact Ideal.mul_mem_mul hx (hν1 y hy)
      | add x _ y _ hx hy =>
        rw [map_add, add_sub_add_comm]
        exact Ideal.add_mem _ hx hy
  let ν : Module.End R C := θ.toLinearMap - LinearMap.id
  have hνa : ∀ c, ν c = θ c - c := fun c => rfl
  have hpow : ∀ k c, (ν ^ (k + 1)) c ∈ J ^ (k + 1) := by
    intro k
    induction k with
    | zero => intro c; simpa [hνa] using hν0 c
    | succ k ih =>
      intro c
      have h1 : (ν ^ (k + 1 + 1)) c = ν ((ν ^ (k + 1)) c) := by rw [pow_succ']; rfl
      rw [h1, hνa]
      exact hνk k _ (ih c)
  have hnil : IsNilpotent ν := by
    refine ⟨m + 1, LinearMap.ext fun c => ?_⟩
    have h := hpow m c
    have h' := Ideal.pow_le_pow_right (Nat.le_succ m) h
    rw [hm] at h'
    simpa using Ideal.mem_bot.mp h'
  have hunit : IsUnit (1 + ν) := hnil.isUnit_one_add
  have hb := (Module.End.isUnit_iff _).mp hunit
  have hf : (θ : C → C) = ⇑(1 + ν) := by
    funext c
    change θ c = c + (θ c - c)
    ring
  rw [hf]
  exact hb

end Unipotent

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (e : A →ₐ[R] R)

/-- The kernel of the augmentation. -/
abbrev aI : Ideal A := RingHom.ker e

lemma sub_mem_aI (a : A) : a - algebraMap R A (e a) ∈ aI e := by
  simp [aI, RingHom.mem_ker]

/-- The `R`-linear projection `I → I/I²`. -/
abbrev cot : aI e →ₗ[R] (aI e).Cotangent := (aI e).toCotangent.restrictScalars R

/-- `a ↦ [a - e(a)]`. -/
def delta : A →ₗ[R] (aI e).Cotangent :=
  cot e ∘ₗ LinearMap.codRestrict ((aI e).restrictScalars R)
    (LinearMap.id - (Algebra.linearMap R A) ∘ₗ e.toLinearMap) (fun a => sub_mem_aI e a)

lemma delta_apply (a : A) : delta e a = (aI e).toCotangent ⟨a - algebraMap R A (e a), sub_mem_aI e a⟩ := rfl

lemma delta_of_mem (x : aI e) : delta e x = (aI e).toCotangent x := by
  rw [delta_apply]
  congr 1
  ext
  have : e (x : A) = 0 := x.2
  simp [this]

lemma delta_mul (a b : A) : delta e (a * b) = e a • delta e b + e b • delta e a := by
  have hs : ∀ (r : R) (x : aI e), r • (aI e).toCotangent x = (aI e).toCotangent (r • x) :=
    fun r x => ((cot e).map_smul r x).symm
  rw [delta_apply, delta_apply, delta_apply, hs, hs, ← map_add, Ideal.toCotangent_eq]
  have hx := sub_mem_aI e a
  have hy := sub_mem_aI e b
  have : (a * b - algebraMap R A (e (a * b))) -
      (e a • (b - algebraMap R A (e b)) + e b • (a - algebraMap R A (e a))) =
      (a - algebraMap R A (e a)) * (b - algebraMap R A (e b)) := by
    simp only [map_mul, Algebra.smul_def]
    ring
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower]
  rw [this, pow_two]
  exact Ideal.mul_mem_mul hx hy

/-- A map `A → Q` from a linear map `l : I/I² → Q` with `l x * l y = 0`. -/
def toSqZero {Q : Type u} [CommRing Q] [Algebra R Q] (l : (aI e).Cotangent →ₗ[R] Q)
    (hl : ∀ x y, l x * l y = 0) : A →ₐ[R] Q :=
  AlgHom.ofLinearMap ((Algebra.linearMap R Q) ∘ₗ e.toLinearMap + l ∘ₗ delta e)
    (by
      have : delta e 1 = 0 := by
        rw [delta_apply]
        have h0 : (⟨1 - algebraMap R A (e 1), sub_mem_aI e 1⟩ : aI e) = 0 := by ext; simp
        rw [h0, map_zero]
      simp [this])
    (fun a b => by
      simp only [LinearMap.add_apply, LinearMap.comp_apply, delta_mul, map_add, map_smul,
        Algebra.linearMap_apply, AlgHom.toLinearMap_apply, map_mul, Algebra.smul_def]
      linear_combination -(hl (delta e a) (delta e b)))

lemma toSqZero_apply {Q : Type u} [CommRing Q] [Algebra R Q] (l : (aI e).Cotangent →ₗ[R] Q)
    (hl : ∀ x y, l x * l y = 0) (a : A) :
    toSqZero e l hl a = algebraMap R Q (e a) + l (delta e a) := rfl

/-- Descent along a surjection. -/
lemma exists_descend {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module R X]
    [Module R Y] [Module R Z] (π : X →ₗ[R] Y) (hπ : Function.Surjective π) (h : X →ₗ[R] Z)
    (hk : LinearMap.ker π ≤ LinearMap.ker h) : ∃ h' : Y →ₗ[R] Z, ∀ x, h' (π x) = h x :=
  ⟨(LinearMap.ker π).liftQ h hk ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, fun x => by
    have : (π.quotKerEquivOfSurjective hπ).symm (π x) = Submodule.Quotient.mk x :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp [this]⟩

variable [Algebra.FormallySmooth R A]

/-- A map from `I/I²` lifts along a surjection, for `A` formally smooth (the square-zero lifting). -/
theorem exists_lift_cot {M N : Type u} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (l : (aI e).Cotangent →ₗ[R] N) :
    ∃ s : (aI e).Cotangent →ₗ[R] M, f.comp s = l := by
  open TrivSqZeroExt in
  let L : TrivSqZeroExt R M →ₗ[R] TrivSqZeroExt R N :=
    { toFun := fun x => inl x.fst + inr (f x.snd)
      map_add' := fun x y => by
        ext <;> simp
      map_smul' := fun r x => by
        ext <;> simp [smul_eq_mul] }
  have hL : ∀ x, L x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr (f x.snd) := fun _ => rfl
  let g : TrivSqZeroExt R M →ₐ[R] TrivSqZeroExt R N :=
    AlgHom.ofLinearMap L (by ext <;> simp [hL]) (fun x y => by
      ext
      · simp [hL]
      · simp [hL, TrivSqZeroExt.snd_mul, add_comm])
  have hgk : ∀ x, g x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr (f x.snd) := fun _ => rfl
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨m, hm⟩ := hf y.snd
    refine ⟨TrivSqZeroExt.inl y.fst + TrivSqZeroExt.inr m, ?_⟩
    ext <;> simp [hgk, hm]
  have hnil : IsNilpotent (RingHom.ker (g : TrivSqZeroExt R M →+* TrivSqZeroExt R N)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hfst : ∀ z ∈ RingHom.ker (g : TrivSqZeroExt R M →+* TrivSqZeroExt R N), z.fst = 0 := by
      intro z hz
      have : g z = 0 := hz
      simpa [hgk] using congrArg TrivSqZeroExt.fst this
    rw [Ideal.mem_bot]
    ext
    · simp [hfst x hx]
    · simp [TrivSqZeroExt.snd_mul, hfst x hx, hfst y hy]
  let F0 : A →ₐ[R] TrivSqZeroExt R N :=
    toSqZero e ((TrivSqZeroExt.inrHom R N) ∘ₗ l) (fun x y => by simp)
  let F := Algebra.FormallySmooth.liftOfSurjective F0 g hgs hnil
  have hF : ∀ a, g (F a) = F0 a := Algebra.FormallySmooth.liftOfSurjective_apply F0 g hgs hnil
  have hFfst : ∀ a, (F a).fst = e a := by
    intro a
    have := congrArg TrivSqZeroExt.fst (hF a)
    simpa [hgk, F0, toSqZero_apply, TrivSqZeroExt.algebraMap_eq_inl] using this
  have hFin : ∀ x : aI e, F x = TrivSqZeroExt.inr (F x).snd := by
    intro x
    ext
    · have : e (x : A) = 0 := x.2
      simp [hFfst, this]
    · simp
  let h0 : aI e →ₗ[R] M :=
    (TrivSqZeroExt.sndHom R M).restrictScalars R ∘ₗ F.toLinearMap ∘ₗ ((aI e).restrictScalars R).subtype
  have hk : LinearMap.ker (cot e) ≤ LinearMap.ker h0 := by
    intro x hx
    have hx2 : (x : A) ∈ aI e ^ 2 := (Ideal.mem_toCotangent_ker (aI e)).1 hx
    rw [pow_two] at hx2
    have key : ∀ z ∈ aI e * aI e, (F z).snd = 0 := by
      intro z hz
      induction hz using Submodule.mul_induction_on' with
      | mem_mul_mem u hu v hv =>
        rw [map_mul, hFin ⟨u, hu⟩, hFin ⟨v, hv⟩]
        simp
      | add u _ v _ hu hv => simp [hu, hv]
    exact key _ hx2
  obtain ⟨s, hs⟩ := exists_descend (R := R) (cot e) (Ideal.toCotangent_surjective _) h0 hk
  refine ⟨s, LinearMap.ext fun p => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ p
  have h1 : f (s ((aI e).toCotangent x)) = f (F x).snd := congrArg f (hs x)
  have h2 := congrArg TrivSqZeroExt.snd (hF x)
  have h3 : (g (F x)).snd = f (F x).snd := by simp [hgk]
  have h4 : (F0 (x : A)).snd = l (delta e x) := by
    simp [F0, toSqZero_apply, TrivSqZeroExt.algebraMap_eq_inl]
  rw [LinearMap.comp_apply, h1, ← h3, h2, h4, delta_of_mem]

/-- A surjection onto `I/I²` splits. -/
theorem exists_section {M : Type u} [AddCommGroup M] [Module R M] (f : M →ₗ[R] (aI e).Cotangent)
    (hf : Function.Surjective f) : ∃ s : (aI e).Cotangent →ₗ[R] M, f.comp s = .id := by
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id R).fromOpposite mul_comm)
  letI : Module Rᵐᵒᵖ (aI e).Cotangent :=
    Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  haveI : IsCentralScalar R (aI e).Cotangent := ⟨fun _ _ => rfl⟩
  exact exists_lift_cot e f hf LinearMap.id

/-- The cotangent module `I/I²` of the augmentation ideal is projective. -/
theorem projective_cotangent : Module.Projective R (aI e).Cotangent :=
  Module.Projective.of_lifting_property'' fun f hf => exists_section e f hf

/-- `I/I²` is finite over `R`, for `A` of finite presentation. -/
theorem finite_cotangent [Algebra.FinitePresentation R A] : Module.Finite R (aI e).Cotangent := by
  have hsurj : Function.Surjective e := fun r => ⟨algebraMap R A r, by simp⟩
  have hfg : (aI e).FG := Algebra.FinitePresentation.ker_fG_of_surjective e hsurj
  haveI : Module.Finite A (aI e) := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite A (aI e).Cotangent :=
    Module.Finite.of_surjective (aI e).toCotangent (Ideal.toCotangent_surjective _)
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A (aI e).Cotangent).FG)
  refine ⟨⟨S, ?_⟩⟩
  let N : Submodule A (aI e).Cotangent :=
    { (Submodule.span R (S : Set (aI e).Cotangent)) with
      smul_mem' := by
        intro a x hx
        have hsm : a • x = e a • x := by
          obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ x
          have hs : e a • (aI e).toCotangent y = (aI e).toCotangent (e a • y) :=
            ((cot e).map_smul _ y).symm
          rw [hs, ← map_smul, Ideal.toCotangent_eq]
          have : (a • y : aI e).1 - (e a • y : aI e).1 = (a - algebraMap R A (e a)) * y := by
            simp [Algebra.smul_def, sub_mul]
          rw [this, pow_two]
          exact Ideal.mul_mem_mul (sub_mem_aI e a) y.2
        rw [hsm]
        exact (Submodule.span R (S : Set (aI e).Cotangent)).smul_mem _ hx }
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← hS, Submodule.span_le]
    exact Submodule.subset_span
  rw [eq_top_iff]
  intro x _
  have : x ∈ N := hN ▸ Submodule.mem_top
  exact this

section Trunc

variable (R) (P : Type u) [AddCommGroup P] [Module R P]

/-- The augmentation ideal of `Sym(P)`. -/
def aug : Ideal (SymmetricAlgebra R P) := span (Set.range (SymmetricAlgebra.ι R P))

/-- The truncation `T_n(P) = Sym(P)/Sym(P)₊^{n+1}`, i.e. `⨁_{k ≤ n} Sym^k P`. -/
abbrev T (n : ℕ) := SymmetricAlgebra R P ⧸ aug R P ^ (n + 1)

lemma aug_compl (c : SymmetricAlgebra R P) : ∃ r : R, c - algebraMap R _ r ∈ aug R P := by
  induction c using SymmetricAlgebra.induction with
  | algebraMap r => exact ⟨r, by simp⟩
  | ι x =>
    have h : SymmetricAlgebra.ι R P x ∈ aug R P := Ideal.subset_span ⟨x, rfl⟩
    exact ⟨0, by simpa using h⟩
  | mul a b ha hb =>
    obtain ⟨r, hr⟩ := ha
    obtain ⟨t, ht⟩ := hb
    refine ⟨r * t, ?_⟩
    have : a * b - algebraMap R _ (r * t) =
        (a - algebraMap R _ r) * b + algebraMap R _ r * (b - algebraMap R _ t) := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hr) (Ideal.mul_mem_left _ _ ht)
  | add a b ha hb =>
    obtain ⟨r, hr⟩ := ha
    obtain ⟨t, ht⟩ := hb
    refine ⟨r + t, ?_⟩
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hr ht

end Trunc

section MvTrunc

open MvPolynomial

/-- `R[x₁,…,x_d]/(x)^k` is finite free. -/
theorem mvTrunc (σ : Type*) [Finite σ] (k : ℕ) :
    Module.Finite R (MvPolynomial σ R ⧸ idealOfVars σ R ^ k) ∧
      Module.Projective R (MvPolynomial σ R ⧸ idealOfVars σ R ^ k) := by
  let s : Set (σ →₀ ℕ) := Finsupp.degree ⁻¹' Set.Ici k
  have hsf : Finite (sᶜ : Set (σ →₀ ℕ)) := by
    refine Set.Finite.subset (Finsupp.finite_of_degree_le (σ := σ) k) ?_
    intro d hd
    have : ¬ k ≤ Finsupp.degree d := hd
    exact (not_le.mp this).le
  have hc : IsCompl (restrictSupport R s) (restrictSupport R sᶜ) :=
    ⟨Submodule.disjoint_def.2 fun x h1 h2 => by
        rw [mem_restrictSupport_iff] at h1 h2
        refine MvPolynomial.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem fun m hm => ?_)
        exact h2 hm (h1 hm),
      codisjoint_iff.2 (eq_top_iff.2 fun x _ => by
        induction x using MvPolynomial.induction_on' with
        | monomial u a =>
          by_cases hu : u ∈ s
          · refine Submodule.mem_sup_left ((mem_restrictSupport_iff R).2 ?_)
            exact (Finset.coe_subset.2 (support_monomial_subset)).trans (by simpa using hu)
          · refine Submodule.mem_sup_right ((mem_restrictSupport_iff R).2 ?_)
            exact (Finset.coe_subset.2 (support_monomial_subset)).trans (by simpa using hu)
        | add a b ha hb => exact Submodule.add_mem _ (ha trivial) (hb trivial))⟩
  have hI : (idealOfVars σ R ^ k).restrictScalars R = restrictSupport R s := by
    rw [pow_idealOfVars]; rfl
  let e₁ := (Submodule.Quotient.restrictScalarsEquiv R (idealOfVars σ R ^ k)).symm
  let e₂ : (MvPolynomial σ R ⧸ (idealOfVars σ R ^ k).restrictScalars R) ≃ₗ[R] restrictSupport R sᶜ :=
    (Submodule.quotEquivOfEq _ _ hI).trans (Submodule.quotientEquivOfIsCompl _ _ hc)
  let e := e₁.trans e₂
  haveI : Module.Free R (restrictSupport R sᶜ) := Module.Free.of_basis (basisRestrictSupport R _)
  haveI : Module.Finite R (restrictSupport R sᶜ) := Module.Finite.of_basis (basisRestrictSupport R _)
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

end MvTrunc

lemma hi_sum {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P] {d : ℕ} (p : (Fin d → R) →ₗ[R] P)
    (v : Fin d → R) : p v = ∑ j, v j • p (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum]

section Retract

variable (R) (P : Type u) [AddCommGroup P] [Module R P]

open MvPolynomial in
/-- `T_n(P)` is finite projective for `P` finite projective: it is a direct summand of `T_n(R^d)`. -/
theorem trunc_finite_projective [Module.Finite R P] [Module.Projective R P] (n : ℕ) :
    Module.Finite R (T R P n) ∧ Module.Projective R (T R P n) := by
  obtain ⟨d, p, hp⟩ := Module.Finite.exists_fin' R P
  obtain ⟨i, hi⟩ := Module.projective_lifting_property p LinearMap.id hp
  let V := MvPolynomial (Fin d) R
  let l : (Fin d → R) →ₗ[R] V := ∑ j, (LinearMap.proj j).smulRight (X j : V)
  have hl : ∀ v, l v = ∑ j, v j • (X j : V) := fun v => by simp [l, LinearMap.sum_apply]
  let a : SymmetricAlgebra R P →ₐ[R] V := SymmetricAlgebra.lift (l ∘ₗ i)
  let b : V →ₐ[R] SymmetricAlgebra R P :=
    aeval fun j => SymmetricAlgebra.ι R P (p (Pi.single j 1))
  have hba : b.comp a = AlgHom.id R _ := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    have hv : ∑ j, i x j • p (Pi.single j 1) = x := by
      rw [← hi_sum p (i x)]; exact LinearMap.congr_fun hi x
    have h1 : a (SymmetricAlgebra.ι R P x) = ∑ j, i x j • (X j : V) := by
      simp only [a, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, hl]
    have : b (a (SymmetricAlgebra.ι R P x)) = SymmetricAlgebra.ι R P (∑ j, i x j • p (Pi.single j 1)) := by
      rw [h1]
      simp only [map_sum, map_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      exact aeval_X _ _
    simpa [hv] using this
  have ha : aug R P ≤ (idealOfVars (Fin d) R).comap a := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    change a _ ∈ idealOfVars (Fin d) R
    simp only [a, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, hl]
    exact Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hb : idealOfVars (Fin d) R ≤ (aug R P).comap b := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    change b _ ∈ aug R P
    have h : b (X j) = SymmetricAlgebra.ι R P (p (Pi.single j 1)) := aeval_X _ _
    rw [h]
    exact Ideal.subset_span ⟨_, rfl⟩
  have ha' : aug R P ^ (n + 1) ≤ (idealOfVars (Fin d) R ^ (n + 1)).comap a :=
    (Ideal.pow_right_mono ha _).trans (Ideal.le_comap_pow _ _)
  have hb' : idealOfVars (Fin d) R ^ (n + 1) ≤ (aug R P ^ (n + 1)).comap b :=
    (Ideal.pow_right_mono hb _).trans (Ideal.le_comap_pow _ _)
  let ab : T R P n →ₐ[R] V ⧸ idealOfVars (Fin d) R ^ (n + 1) :=
    Ideal.quotientMapₐ _ a ha'
  let bb : V ⧸ idealOfVars (Fin d) R ^ (n + 1) →ₐ[R] T R P n :=
    Ideal.quotientMapₐ _ b hb'
  have hsplit : bb.toLinearMap ∘ₗ ab.toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have := AlgHom.congr_fun hba y
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at this
    simp [ab, bb, this]
  have hsj : Function.Surjective bb := fun x =>
    ⟨ab x, LinearMap.congr_fun hsplit x⟩
  obtain ⟨hF, hPr⟩ := mvTrunc (R := R) (Fin d) (n + 1)
  exact ⟨Module.Finite.of_surjective bb.toLinearMap hsj,
    Module.Projective.of_split ab.toLinearMap bb.toLinearMap hsplit⟩

end Retract

/-- The `R`-linear isomorphism `A/I^{n+1} ≃ T_n(I/I²)`. -/
theorem exists_equiv_trunc [Module.Projective R (aI e).Cotangent] (n : ℕ) :
    Nonempty ((A ⧸ aI e ^ (n + 1)) ≃ₗ[R] T R (aI e).Cotangent n) := by
  let P := (aI e).Cotangent
  let Tn := T R P n
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (cot e) LinearMap.id (Ideal.toCotangent_surjective _)
  have hs' : ∀ x : P, (aI e).toCotangent (s x) = x := fun x => LinearMap.congr_fun hs x
  let sA : P →ₗ[R] A := ((aI e).restrictScalars R).subtype ∘ₗ s
  let J : Ideal Tn := (aug R P).map (Ideal.Quotient.mk _)
  have hJn : J ^ (n + 1) = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have hJ2n : IsNilpotent (J ^ 2) := ⟨n + 1, by
    rw [← pow_mul, mul_comm, pow_mul, hJn, Ideal.zero_eq_bot]
    exact Ideal.bot_pow two_ne_zero⟩
  let lT : P →ₗ[R] Tn ⧸ J ^ 2 :=
    (Ideal.Quotient.mkₐ R (J ^ 2)).toLinearMap ∘ₗ
      (Ideal.Quotient.mkₐ R (aug R P ^ (n + 1))).toLinearMap ∘ₗ SymmetricAlgebra.ι R P
  have hιJ : ∀ x : P, Ideal.Quotient.mk (aug R P ^ (n + 1)) (SymmetricAlgebra.ι R P x) ∈ J := fun x =>
    Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨x, rfl⟩)
  have hlT : ∀ x y, lT x * lT y = 0 := by
    intro x y
    change Ideal.Quotient.mk (J ^ 2) _ * Ideal.Quotient.mk (J ^ 2) _ = 0
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul (hιJ x) (hιJ y)
  let ψ : A →ₐ[R] Tn := Algebra.FormallySmooth.lift (J ^ 2) hJ2n (toSqZero e lT hlT)
  have hψ : ∀ x : aI e, ψ x - Ideal.Quotient.mk _ (SymmetricAlgebra.ι R P ((aI e).toCotangent x)) ∈ J ^ 2 := by
    intro x
    rw [← Ideal.Quotient.eq]
    have h := Algebra.FormallySmooth.mk_lift (J ^ 2) hJ2n (toSqZero e lT hlT) (x : A)
    have hx : e (x : A) = 0 := x.2
    rw [toSqZero_apply, hx, map_zero, zero_add, delta_of_mem] at h
    exact h
  have hψJ : aI e ≤ J.comap (ψ : A →+* Tn) := by
    intro x hx
    have := J.add_mem (Ideal.pow_le_self two_ne_zero (hψ ⟨x, hx⟩)) (hιJ ((aI e).toCotangent ⟨x, hx⟩))
    simpa using this
  have hψk : aI e ^ (n + 1) ≤ (⊥ : Ideal Tn).comap (ψ : A →+* Tn) := by
    rw [← hJn]
    exact (Ideal.pow_right_mono hψJ _).trans (Ideal.le_comap_pow _ _)
  let ψb : (A ⧸ aI e ^ (n + 1)) →ₐ[R] Tn :=
    Ideal.Quotient.liftₐ _ ψ (fun a ha => by simpa using hψk ha)
  let Φ : SymmetricAlgebra R P →ₐ[R] A := SymmetricAlgebra.lift sA
  have hΦ : aug R P ≤ (aI e).comap Φ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    change Φ _ ∈ aI e
    simp only [Φ, SymmetricAlgebra.lift_ι_apply]
    exact (s x).2
  have hΦk : aug R P ^ (n + 1) ≤ (aI e ^ (n + 1)).comap Φ :=
    (Ideal.pow_right_mono hΦ _).trans (Ideal.le_comap_pow _ _)
  let φ : Tn →ₐ[R] (A ⧸ aI e ^ (n + 1)) := Ideal.quotientMapₐ _ Φ hΦk
  have hφι : ∀ x : P, φ (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R P x)) = Ideal.Quotient.mk _ (s x : A) := by
    intro x
    change Ideal.Quotient.mk _ (Φ (SymmetricAlgebra.ι R P x)) = _
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl
  let J' : Ideal (A ⧸ aI e ^ (n + 1)) := (aI e).map (Ideal.Quotient.mk _)
  have hφJ : J ≤ J'.comap (φ : Tn →+* _) := by
    refine Ideal.map_le_iff_le_comap.2 ?_
    intro c hc
    have : Φ c ∈ aI e := hΦ hc
    change Ideal.Quotient.mk _ (Φ c) ∈ J'
    exact Ideal.mem_map_of_mem _ this
  have hφJ2 : J ^ 2 ≤ (J' ^ 2).comap (φ : Tn →+* _) :=
    (Ideal.pow_right_mono hφJ _).trans (Ideal.le_comap_pow _ _)
  have hb1 : Function.Bijective (ψb.comp φ) := by
    refine bijective_of_unipotent J
      ((Ideal.Quotient.mk _) '' Set.range (SymmetricAlgebra.ι R P)) ?_ (n + 1) hJn ?_ _ ?_
    · exact Ideal.map_span _ _
    · intro c
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨r, hr⟩ := aug_compl R P c
      exact ⟨r, by simpa using Ideal.mem_map_of_mem (Ideal.Quotient.mk (aug R P ^ (n + 1))) hr⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      have h := hψ (s x)
      rw [hs'] at h
      change ψb (φ (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R P x))) - _ ∈ _
      rw [hφι]
      exact h
  have hb2 : Function.Bijective (φ.comp ψb) := by
    refine bijective_of_unipotent J' ((Ideal.Quotient.mk _) '' (aI e : Set A)) ?_ (n + 1) ?_ ?_ _ ?_
    · rfl
    · rw [← Ideal.map_pow, Ideal.map_quotient_self]
    · intro c
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨e c, by simpa using Ideal.mem_map_of_mem (Ideal.Quotient.mk (aI e ^ (n + 1))) (sub_mem_aI e c)⟩
    · rintro _ ⟨x, hx, rfl⟩
      let x' : aI e := ⟨x, hx⟩
      have h1 := hφJ2 (hψ x')
      have h2 : (s ((aI e).toCotangent x') : A) - x ∈ aI e ^ 2 :=
        (Ideal.toCotangent_eq (aI e)).1 (hs' _)
      have h3 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (aI e ^ (n + 1))) h2
      rw [Ideal.map_pow] at h3
      have h5 : φ (ψ x) - Ideal.Quotient.mk _ (s ((aI e).toCotangent x') : A) ∈ J' ^ 2 := by
        have h1' : φ (ψ x - Ideal.Quotient.mk _ (SymmetricAlgebra.ι R P ((aI e).toCotangent x'))) ∈ J' ^ 2 := h1
        rwa [map_sub, hφι] at h1'
      have h4 := Ideal.add_mem _ h5 h3
      rw [map_sub] at h4
      change φ (ψ x) - Ideal.Quotient.mk _ x ∈ J' ^ 2
      convert h4 using 1
      ring
  have hbφ : Function.Bijective φ :=
    ⟨fun u v h => hb1.1 (by simp [h]), fun y => by
      obtain ⟨z, hz⟩ := hb2.2 y
      exact ⟨ψb z, hz⟩⟩
  exact ⟨(LinearEquiv.ofBijective φ.toLinearMap hbφ).symm⟩

/-- **Remark A.6**, local form. `A` smooth over `R`, `e : A → R` a section of `Spec A → Spec R` (for `G`, the unit section), `I = ker e`:
the `n`-th order thickening `A/I^{n+1}` is finite projective over `R`, i.e. finite locally free. -/
theorem remA6 [Algebra.FinitePresentation R A] (n : ℕ) :
    Module.Finite R (A ⧸ aI e ^ (n + 1)) ∧ Module.Projective R (A ⧸ aI e ^ (n + 1)) := by
  haveI := finite_cotangent e
  haveI := projective_cotangent e
  obtain ⟨E⟩ := exists_equiv_trunc e n
  obtain ⟨h1, h2⟩ := trunc_finite_projective R (aI e).Cotangent n
  exact ⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv E.symm⟩

end AlgMag.Final.RemA6

#print axioms AlgMag.Final.RemA6.remA6
