/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12SymRing
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Theorem 12.4: the ring computation, along the printed proof

Mayeux, *Algebraic Magnetism*, proof of Theorem 12.4. `B` is graded by a monoid `Y`, with a morphism
of monoids `w : Y → ℕ` (on the support of the grading) such that `w⁻¹(0) = 0` (Ogus, Prop. 2.2.1, for `Y` fine and sharp). `A₀ → B` is
the degree zero part, `π : B → A₀` the projection, `I = ker π`, `P = I / I²`.

The printed steps, in order: `I` is graded, `P` is graded (`delta`), each `P_y` is a direct summand
of `P`, so projective, `A_y → P_y` has a section, `s = ⨁ s_y`; `φ : Sym(P) → B` is surjective by
induction on `w`; `φ` is injective by the filtration argument.

The printed proof cites Tags 067U, 063M, 062Z for "`P` is finite projective" and "`Sym(P) → gr_I` is
an isomorphism". Those two citations are here replaced by the same statements obtained from formal
smoothness of `A₀ → B`: `projective_cotangent`, `finite_cotangent`, `gamma_injective`.
-/

open AlgMag.SymRing

universe u

namespace AlgMag.Sec12Printed

section Cited

variable {A₀ B : Type u} [CommRing A₀] [CommRing B] [Algebra A₀ B] (π : B →ₐ[A₀] A₀)

/-- The ideal `I = ker π`. -/
abbrev augI : Ideal B := RingHom.ker π.toRingHom

/-- The conormal module `I/I²`, an `A₀`-module. -/
abbrev Conormal : Type u := (augI π).Cotangent

/-- `b ↦ [b - π b]`. -/
noncomputable def tMap : B →ₗ[A₀] Conormal π where
  toFun b := (augI π).toCotangent ⟨b - algebraMap A₀ B (π b), by
    change π (b - algebraMap A₀ B (π b)) = 0
    simp⟩
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' r a := by
    rw [RingHom.id_apply]
    have : (⟨r • a - algebraMap A₀ B (π (r • a)), by
        change π (r • a - algebraMap A₀ B (π (r • a))) = 0
        simp⟩ : augI π) = (algebraMap A₀ B r) • ⟨a - algebraMap A₀ B (π a), by
        change π (a - algebraMap A₀ B (π a)) = 0
        simp⟩ := by
      ext
      simp [Algebra.smul_def, mul_sub]
    rw [this, map_smul]
    exact (algebraMap_smul B r _)

lemma tMap_of_mem {a : B} (ha : a ∈ augI π) : tMap π a = (augI π).toCotangent ⟨a, ha⟩ := by
  have : π a = 0 := ha
  simp only [tMap, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  ext
  simp [this]

lemma tMap_mul (a b : B) : tMap π (a * b) = π a • tMap π b + π b • tMap π a := by
  have ha : a - algebraMap A₀ B (π a) ∈ augI π := by
    change π (a - algebraMap A₀ B (π a)) = 0
    simp
  have hb : b - algebraMap A₀ B (π b) ∈ augI π := by
    change π (b - algebraMap A₀ B (π b)) = 0
    simp
  have e : (⟨a * b - algebraMap A₀ B (π (a * b)), by
      change π (a * b - algebraMap A₀ B (π (a * b))) = 0
      simp⟩ : augI π) =
      ⟨(a - algebraMap A₀ B (π a)) * (b - algebraMap A₀ B (π b)), Ideal.mul_mem_left _ _ hb⟩ +
      (algebraMap A₀ B (π a)) • ⟨b - algebraMap A₀ B (π b), hb⟩ +
      (algebraMap A₀ B (π b)) • ⟨a - algebraMap A₀ B (π a), ha⟩ := by
    ext
    simp only [map_mul, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
    ring
  simp only [tMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [e, map_add, map_add, map_smul, map_smul]
  have h0 : (augI π).toCotangent
      ⟨(a - algebraMap A₀ B (π a)) * (b - algebraMap A₀ B (π b)), Ideal.mul_mem_left _ _ hb⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [h0, zero_add, algebraMap_smul, algebraMap_smul]

lemma tMap_surjective : Function.Surjective (tMap π) := fun p => by
  obtain ⟨⟨a, ha⟩, rfl⟩ := (augI π).toCotangent_surjective p
  exact ⟨a, tMap_of_mem π ha⟩

lemma tMap_algebraMap (r : A₀) : tMap π (algebraMap A₀ B r) = 0 := by
  have : (algebraMap A₀ B r) - algebraMap A₀ B (π (algebraMap A₀ B r)) = 0 := by simp
  simp only [tMap, LinearMap.coe_mk, AddHom.coe_mk, this]
  exact map_zero (augI π).toCotangent

/-- Cited in the printed proof (Tags 067U, 063M): `I/I²` is of finite type. -/
theorem finite_cotangent [Algebra.FiniteType A₀ B] : Module.Finite A₀ (Conormal π) := by
  classical
  obtain ⟨g, hg⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A₀ B).FG)
  refine ⟨⟨g.image (tMap π), ?_⟩⟩
  rw [eq_top_iff]
  intro p _
  obtain ⟨b, rfl⟩ := tMap_surjective π p
  have hb : b ∈ Algebra.adjoin A₀ (g : Set B) := hg ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
  | algebraMap r => rw [tMap_algebraMap]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | mul x y _ _ hx hy =>
    rw [tMap_mul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hy trivial)) (Submodule.smul_mem _ _ (hx trivial))

/-- The universal property of `I/I²`: a linear map out of `B` that kills `A₀` and `I²` factors
through `b ↦ [b - π b]`. -/
theorem exists_factor {Q : Type*} [AddCommGroup Q] [Module A₀ Q] (g : B →ₗ[A₀] Q)
    (h₀ : ∀ r, g (algebraMap A₀ B r) = 0) (h₂ : ∀ a ∈ augI π, ∀ b ∈ augI π, g (a * b) = 0) :
    ∃ gb : Conormal π →ₗ[A₀] Q, ∀ b, gb (tMap π b) = g b := by
  have hker : LinearMap.ker (tMap π) ≤ LinearMap.ker g := by
    intro b hb
    have hm : b - algebraMap A₀ B (π b) ∈ augI π := by
      change π (b - algebraMap A₀ B (π b)) = 0
      simp
    have hz : (augI π).toCotangent ⟨_, hm⟩ = 0 := hb
    rw [Ideal.toCotangent_eq_zero, pow_two] at hz
    have key : ∀ x ∈ augI π * augI π, g x = 0 := by
      intro x hx
      refine Submodule.mul_induction_on hx (fun a ha c hc => h₂ a ha c hc) ?_
      intro x y hx hy
      rw [map_add, hx, hy, add_zero]
    have := key _ hz
    rw [map_sub, h₀, sub_zero] at this
    exact this
  let e := (tMap π).quotKerEquivOfSurjective (tMap_surjective π)
  refine ⟨((LinearMap.ker (tMap π)).liftQ g hker).comp e.symm.toLinearMap, fun b => ?_⟩
  have : e.symm (tMap π b) = Submodule.Quotient.mk b := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  change (LinearMap.ker (tMap π)).liftQ g hker (e.symm (tMap π b)) = _
  rw [this]
  rfl

/-- Lifting along surjections of `A₀`-modules, from formal smoothness of `A₀ → B`, through the
trivial square zero extension. -/
theorem exists_lift_conormal [Algebra.FormallySmooth A₀ B] {Q E : Type u} [AddCommGroup Q]
    [AddCommGroup E] [Module A₀ Q] [Module A₀ E] (f : E →ₗ[A₀] Q) (hf : Function.Surjective f)
    (g : Conormal π →ₗ[A₀] Q) : ∃ h : Conormal π →ₗ[A₀] E, f.comp h = g := by
  let _ : Module A₀ᵐᵒᵖ Q := Module.compHom Q ((RingHom.id A₀).fromOpposite fun _ _ => mul_comm _ _)
  let _ : Module A₀ᵐᵒᵖ E := Module.compHom E ((RingHom.id A₀).fromOpposite fun _ _ => mul_comm _ _)
  have : IsCentralScalar A₀ Q := ⟨fun _ _ => rfl⟩
  have : IsCentralScalar A₀ E := ⟨fun _ _ => rfl⟩
  let ψ : B →ₐ[A₀] TrivSqZeroExt A₀ Q :=
    { toFun := fun b => TrivSqZeroExt.inl (π b) + TrivSqZeroExt.inr (g (tMap π b))
      map_one' := by
        have : tMap π 1 = 0 := by simpa using tMap_algebraMap π 1
        simp [this]
      map_zero' := by simp
      map_add' := fun a b => by
        ext <;> simp [add_comm, add_left_comm, add_assoc]
      map_mul' := fun a b => by
        ext
        · simp
        · simp [tMap_mul, op_smul_eq_smul]
      commutes' := fun r => by
        rw [tMap_algebraMap, map_zero, TrivSqZeroExt.inr_zero, add_zero]
        rw [AlgHom.commutes]
        exact (congrFun (TrivSqZeroExt.algebraMap_eq_inl A₀ Q) r).symm }
  let F := TrivSqZeroExt.map (R' := A₀) f
  have hF : Function.Surjective F := fun x => by
    obtain ⟨e, he⟩ := hf x.snd
    refine ⟨TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr e, ?_⟩
    ext <;> simp [F, he]
  have hnil : IsNilpotent (RingHom.ker (F : TrivSqZeroExt A₀ E →+* TrivSqZeroExt A₀ Q)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have h1 : x.fst = 0 := by
      have := congrArg TrivSqZeroExt.fst (show F x = 0 from hx)
      simpa [F] using this
    have h2 : y.fst = 0 := by
      have := congrArg TrivSqZeroExt.fst (show F y = 0 from hy)
      simpa [F] using this
    rw [Ideal.mem_bot]
    ext <;> simp [h1, h2]
  let L := Algebra.FormallySmooth.liftOfSurjective ψ F hF hnil
  have hL : ∀ b, F (L b) = ψ b := Algebra.FormallySmooth.liftOfSurjective_apply ψ F hF hnil
  have hfst : ∀ b, (L b).fst = π b := fun b => by
    have := congrArg TrivSqZeroExt.fst (hL b)
    simpa [F, ψ] using this
  have hsnd : ∀ b, f (L b).snd = g (tMap π b) := fun b => by
    have := congrArg TrivSqZeroExt.snd (hL b)
    simpa [F, ψ] using this
  let u : B →ₗ[A₀] E := (TrivSqZeroExt.sndHom A₀ E).comp L.toLinearMap
  obtain ⟨h, hh⟩ := exists_factor π u
    (fun r => by
      change (L (algebraMap A₀ B r)).snd = 0
      rw [AlgHom.commutes, congrFun (TrivSqZeroExt.algebraMap_eq_inl A₀ E) r]
      exact TrivSqZeroExt.snd_inl _ _)
    (fun a ha b hb => by
      have ha' : π a = 0 := ha
      have hb' : π b = 0 := hb
      change (L (a * b)).snd = 0
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, ha', hb']
      simp)
  refine ⟨h, LinearMap.ext fun p => ?_⟩
  obtain ⟨b, rfl⟩ := tMap_surjective π p
  change f (h (tMap π b)) = _
  rw [hh]
  exact hsnd b

/-- Cited in the printed proof (Tags 067U, 063M): `I/I²` is projective. -/
theorem projective_cotangent [Algebra.FormallySmooth A₀ B] : Module.Projective A₀ (Conormal π) :=
  Module.Projective.of_lifting_property'' fun f hf => exists_lift_conormal π f hf .id

end Cited


section Graded

variable {A₀ B Y : Type u} [CommRing A₀] [CommRing B] [Algebra A₀ B] [AddCommMonoid Y] [DecidableEq Y]
  (𝒜 : Y → Submodule A₀ B) [GradedAlgebra 𝒜] (π : B →ₐ[A₀] A₀) (w : Y → ℕ)

/-- The data of the printed proof: `B` is graded by `Y`, `w⁻¹(0) = 0`, `π` is the projection to the
degree zero part `A₀`. -/
structure IsAug : Prop where
  hw : ∀ y, ∀ b ∈ 𝒜 y, b ≠ 0 → w y = 0 → y = 0
  hadd : ∀ u, ∀ b ∈ 𝒜 u, b ≠ 0 → ∀ v, ∀ d ∈ 𝒜 v, d ≠ 0 → w (u + v) = w u + w v
  hπ : ∀ y, y ≠ 0 → ∀ b ∈ 𝒜 y, π b = 0
  h0 : ∀ b ∈ 𝒜 0, algebraMap A₀ B (π b) = b

variable {𝒜 π w} (H : IsAug 𝒜 π w)

include H

lemma tMap_of_zero {b : B} (hb : b ∈ 𝒜 0) : tMap π b = 0 := by
  rw [← H.h0 b hb, tMap_algebraMap]

lemma π_eq_comp_zero (a : B) : π a = π (DirectSum.decompose 𝒜 a 0 : B) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  rw [map_sum]
  by_cases h0 : (0 : Y) ∈ (DirectSum.decompose 𝒜 a).support
  · refine (Finset.sum_eq_single_of_mem 0 h0 fun y _ hy => H.hπ y hy _ (SetLike.coe_mem _))
  · have : (DirectSum.decompose 𝒜 a 0 : B) = 0 := by
      have := DFinsupp.notMem_support_iff.1 h0
      rw [this]
      rfl
    rw [this, map_zero]
    exact Finset.sum_eq_zero fun y hy => H.hπ y (fun e => h0 (e ▸ hy)) _ (SetLike.coe_mem _)

/-- `I = ⨁_{n ≠ 0} A_n`: the degree zero component of an element of `I` vanishes. -/
lemma comp_zero_of_mem {a : B} (ha : a ∈ augI π) : (DirectSum.decompose 𝒜 a 0 : B) = 0 := by
  have h : π a = 0 := ha
  rw [← H.h0 _ (SetLike.coe_mem (DirectSum.decompose 𝒜 a 0)), ← π_eq_comp_zero H, h, map_zero]

/-- "The ideal `I` is graded by definition." -/
lemma comp_mem {a : B} (ha : a ∈ augI π) (y : Y) : (DirectSum.decompose 𝒜 a y : B) ∈ augI π := by
  by_cases hy : y = 0
  · subst hy
    rw [comp_zero_of_mem H ha]
    exact Ideal.zero_mem _
  · exact H.hπ y hy _ (SetLike.coe_mem _)

omit H in
/-- `A_y → (I/I²)_y`. -/
noncomputable def qMap (π : B →ₐ[A₀] A₀) (𝒜 : Y → Submodule A₀ B) (y : Y) : 𝒜 y →ₗ[A₀] Conormal π :=
  (tMap π).comp (𝒜 y).subtype

omit H in
/-- `(I/I²)_y`, the image of `A_y`. -/
noncomputable abbrev Py (π : B →ₐ[A₀] A₀) (𝒜 : Y → Submodule A₀ B) (y : Y) : Submodule A₀ (Conormal π) :=
  LinearMap.range (qMap π 𝒜 y)

omit H in
lemma of_Py_zero {y : Y} {p : Conormal π} (h : p ∈ Py π 𝒜 y) (hp : p = 0) :
    DirectSum.of (fun y => Py π 𝒜 y) y ⟨p, h⟩ = 0 := by
  subst hp
  exact map_zero (DirectSum.of (fun y => Py π 𝒜 y) y)

omit H in
/-- `B → ⨁ (I/I²)_y`. -/
noncomputable def dQ (π : B →ₐ[A₀] A₀) (𝒜 : Y → Submodule A₀ B) [GradedAlgebra 𝒜] :
    B →ₗ[A₀] DirectSum Y fun y => Py π 𝒜 y :=
  (DFinsupp.mapRange.linearMap fun y => (qMap π 𝒜 y).rangeRestrict).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

omit H in
lemma dQ_of_mem {y : Y} {b : B} (hb : b ∈ 𝒜 y) :
    dQ π 𝒜 b = DirectSum.of (fun y => Py π 𝒜 y) y ⟨tMap π b, ⟨⟨b, hb⟩, rfl⟩⟩ := by
  have e : DirectSum.decompose 𝒜 b = DirectSum.of (fun y => 𝒜 y) y ⟨b, hb⟩ :=
    DirectSum.decompose_of_mem 𝒜 hb
  change DFinsupp.mapRange.linearMap (fun y => (qMap π 𝒜 y).rangeRestrict)
    (DirectSum.decompose 𝒜 b) = _
  rw [e]
  exact DFinsupp.mapRange_single (hf := fun _ => map_zero _)

lemma dQ_mul {a b : B} (ha : a ∈ augI π) (hb : b ∈ augI π) : dQ π 𝒜 (a * b) = 0 := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 a, ← DirectSum.sum_support_decompose 𝒜 b,
    Finset.sum_mul_sum, map_sum]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun v _ => ?_
  have hm := SetLike.mul_mem_graded (SetLike.coe_mem (DirectSum.decompose 𝒜 a u))
    (SetLike.coe_mem (DirectSum.decompose 𝒜 b v))
  rw [dQ_of_mem hm]
  have hz : tMap π ((DirectSum.decompose 𝒜 a u : B) * (DirectSum.decompose 𝒜 b v : B)) = 0 := by
    have h₁ : π (DirectSum.decompose 𝒜 a u : B) = 0 := comp_mem H ha u
    have h₂ : π (DirectSum.decompose 𝒜 b v : B) = 0 := comp_mem H hb v
    rw [tMap_mul, h₁, h₂, zero_smul, zero_smul, add_zero]
  exact of_Py_zero _ hz

lemma dQ_algebraMap (r : A₀) : dQ π 𝒜 (algebraMap A₀ B r) = 0 := by
  have hm : algebraMap A₀ B r ∈ 𝒜 0 := SetLike.algebraMap_mem_graded 𝒜 r
  rw [dQ_of_mem hm]
  exact of_Py_zero _ (tMap_algebraMap π r)

/-- The grading of `I/I²`: "`I²` is graded, so `I → I/I²` is a homomorphism of graded modules." -/
theorem exists_delta : ∃ δ : Conormal π →ₗ[A₀] DirectSum Y fun y => Py π 𝒜 y,
    ∀ b, δ (tMap π b) = dQ π 𝒜 b :=
  exists_factor π (dQ π 𝒜) (dQ_algebraMap H) fun _ ha _ hb => dQ_mul H ha hb


/-- "The `A₀`-module `(I/I²)_n` is projective because it is a direct summand of `I/I²`, and so the
surjection `A_n → (I/I²)_n` admits a section `s_n`. Let `s` be the direct sum." -/
theorem exists_section [Module.Projective A₀ (Conormal π)] :
    ∃ s : Conormal π →ₗ[A₀] B, (∀ p, tMap π (s p) = p) ∧ (∀ p, π (s p) = 0) ∧
      ∀ (y : Y) (b : B), b ∈ 𝒜 y → s (tMap π b) ∈ 𝒜 y := by
  classical
  obtain ⟨δ, hδ⟩ := exists_delta H
  have hsec : ∀ y, ∃ σ : Py π 𝒜 y →ₗ[A₀] 𝒜 y, ∀ x, (qMap π 𝒜 y).rangeRestrict (σ x) = x := by
    intro y
    have hpr : Module.Projective A₀ (Py π 𝒜 y) := by
      refine Module.Projective.of_split (Py π 𝒜 y).subtype
        ((DirectSum.component A₀ Y (fun y => Py π 𝒜 y) y).comp δ) (LinearMap.ext ?_)
      rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩⟩
      change DirectSum.component A₀ Y (fun y => Py π 𝒜 y) y (δ (tMap π b)) = _
      rw [hδ, dQ_of_mem hb]
      exact DirectSum.component.lof_self _ _ _
    obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (qMap π 𝒜 y).rangeRestrict LinearMap.id
      (LinearMap.surjective_rangeRestrict _)
    exact ⟨σ, fun x => LinearMap.congr_fun hσ x⟩
  choose σ hσ using hsec
  let σ' : DirectSum Y (fun y => Py π 𝒜 y) →ₗ[A₀] B :=
    DirectSum.toModule A₀ Y B fun y => (𝒜 y).subtype.comp (σ y)
  let s : Conormal π →ₗ[A₀] B := σ'.comp δ
  have hs_of : ∀ (y : Y) (b : B) (hb : b ∈ 𝒜 y), s (tMap π b) = (σ y ⟨tMap π b, ⟨⟨b, hb⟩, rfl⟩⟩ : B) := by
    intro y b hb
    change σ' (δ (tMap π b)) = _
    rw [hδ, dQ_of_mem hb]
    exact DirectSum.toModule_lof A₀ _ _
  have ht_of : ∀ (y : Y) (b : B) (hb : b ∈ 𝒜 y), tMap π (s (tMap π b)) = tMap π b := by
    intro y b hb
    rw [hs_of y b hb]
    exact congrArg Subtype.val (hσ y ⟨tMap π b, ⟨⟨b, hb⟩, rfl⟩⟩)
  have hπ_of : ∀ (y : Y) (b : B) (hb : b ∈ 𝒜 y), π (s (tMap π b)) = 0 := by
    intro y b hb
    by_cases hy : y = 0
    · subst hy
      rw [tMap_of_zero H hb, map_zero, map_zero]
    · rw [hs_of y b hb]
      exact H.hπ y hy _ (SetLike.coe_mem _)
  refine ⟨s, fun p => ?_, fun p => ?_, fun y b hb => ?_⟩
  · obtain ⟨b, rfl⟩ := tMap_surjective π p
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous m => exact ht_of _ _ (SetLike.coe_mem m)
    | add a b ha hb => simp only [map_add, ha, hb]
  · obtain ⟨b, rfl⟩ := tMap_surjective π p
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous m => exact hπ_of _ _ (SetLike.coe_mem m)
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  · rw [hs_of y b hb]
    exact SetLike.coe_mem _

variable {s : Conormal π →ₗ[A₀] B}

/-- "We first prove that `φ` is surjective": induction on `h(c)`, `c` the degree. -/
theorem phi_surjective (hts : ∀ p, tMap π (s p) = p) (hπs : ∀ p, π (s p) = 0)
    (hg : ∀ (y : Y) (b : B), b ∈ 𝒜 y → s (tMap π b) ∈ 𝒜 y) :
    Function.Surjective (SymmetricAlgebra.lift s : SymmetricAlgebra A₀ (Conormal π) →ₐ[A₀] B) := by
  classical
  let C : Subalgebra A₀ B := (SymmetricAlgebra.lift s : SymmetricAlgebra A₀ (Conormal π) →ₐ[A₀] B).range
  have hsC : ∀ p, s p ∈ C := fun p => ⟨SymmetricAlgebra.ι A₀ _ p, SymmetricAlgebra.lift_ι_apply _ _⟩
  have main : ∀ (k : ℕ) (c : Y), w c = k → ∀ a ∈ 𝒜 c, a ∈ C := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro c hc a ha
      by_cases hc0 : c = 0
      · subst hc0
        rw [← H.h0 a ha]
        exact C.algebraMap_mem _
      -- the element `a - s [a]` lies in `I²`, in degree `c`
      have ha' : a ∈ augI π := H.hπ c hc0 a ha
      have hsa := hg c a ha
      let x := a - s (tMap π a)
      have hxI : x ∈ augI π := by
        change π (a - s (tMap π a)) = 0
        rw [map_sub, hπs, sub_zero]
        exact ha'
      have hx2 : x ∈ augI π * augI π := by
        have h1 : tMap π x = 0 := by
          change tMap π (a - s (tMap π a)) = 0
          rw [map_sub, hts, tMap_of_mem π ha', sub_eq_zero]
        rw [tMap_of_mem π hxI, Ideal.toCotangent_eq_zero, pow_two] at h1
        exact h1
      have hxc : x ∈ 𝒜 c := Submodule.sub_mem _ ha hsa
      -- "write `a = ∑ bᵢ dᵢ`; omit the terms of degree `≠ c`"
      have key : ∀ z ∈ augI π * augI π, (DirectSum.decompose 𝒜 z c : B) ∈ C := by
        intro z hz
        refine Submodule.mul_induction_on hz ?_ ?_
        · intro b hb d hd
          rw [← DirectSum.sum_support_decompose 𝒜 b, ← DirectSum.sum_support_decompose 𝒜 d,
            Finset.sum_mul_sum]
          rw [← GradedRing.proj_apply 𝒜 c, map_sum]
          refine C.sum_mem fun u _ => ?_
          rw [map_sum]
          refine C.sum_mem fun v _ => ?_
          rw [GradedRing.proj_apply]
          have hm := SetLike.mul_mem_graded (SetLike.coe_mem (DirectSum.decompose 𝒜 b u))
            (SetLike.coe_mem (DirectSum.decompose 𝒜 d v))
          by_cases huv : u + v = c
          · subst huv
            rw [DirectSum.decompose_of_mem_same 𝒜 hm]
            by_cases hu : (DirectSum.decompose 𝒜 b u : B) = 0
            · rw [hu, zero_mul]
              exact C.zero_mem
            by_cases hv : (DirectSum.decompose 𝒜 d v : B) = 0
            · rw [hv, mul_zero]
              exact C.zero_mem
            have hu0 : u ≠ 0 := fun e => hu (by subst e; exact comp_zero_of_mem H hb)
            have hv0 : v ≠ 0 := fun e => hv (by subst e; exact comp_zero_of_mem H hd)
            have wu : w u ≠ 0 := fun e => hu0 (H.hw u _ (SetLike.coe_mem _) hu e)
            have wv : w v ≠ 0 := fun e => hv0 (H.hw v _ (SetLike.coe_mem _) hv e)
            rw [H.hadd u _ (SetLike.coe_mem _) hu v _ (SetLike.coe_mem _) hv] at hc
            exact C.mul_mem (ih (w u) (by omega) u rfl _ (SetLike.coe_mem _))
              (ih (w v) (by omega) v rfl _ (SetLike.coe_mem _))
          · rw [DirectSum.decompose_of_mem_ne 𝒜 hm huv]
            exact C.zero_mem
        · intro y z hy hz
          rw [DirectSum.decompose_add]
          simpa using C.add_mem hy hz
      have hxC : x ∈ C := by
        have := key x hx2
        rwa [DirectSum.decompose_of_mem_same 𝒜 hxc] at this
      have : a = x + s (tMap π a) := by
        change a = a - s (tMap π a) + s (tMap π a)
        ring
      rw [this]
      exact C.add_mem hxC (hsC _)
  intro b
  have hb : b ∈ C := by
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => exact C.zero_mem
    | homogeneous m => exact main _ _ rfl _ (SetLike.coe_mem m)
    | add a b ha hb => exact C.add_mem ha hb
  exact hb

end Graded

section Injective

variable {A₀ B : Type u} [CommRing A₀] [CommRing B] [Algebra A₀ B] (π : B →ₐ[A₀] A₀)
  {s : Conormal π →ₗ[A₀] B}

local notation "Sy" => SymmetricAlgebra A₀ (Conormal π)
local notation "JJ" => augIdeal A₀ (Conormal π)
local notation "ιS" => SymmetricAlgebra.ι A₀ (Conormal π)

/-- The map `I = φ(J)`. -/
theorem map_J_eq (hπs : ∀ p, π (s p) = 0)
    (hsurj : Function.Surjective (SymmetricAlgebra.lift s : Sy →ₐ[A₀] B)) :
    Ideal.map (SymmetricAlgebra.lift s : Sy →ₐ[A₀] B) JJ = augI π := by
  have hle : JJ ≤ (augI π).comap (SymmetricAlgebra.lift s : Sy →ₐ[A₀] B) := by
    rw [augIdeal, Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    change π (SymmetricAlgebra.lift s (ιS p)) = 0
    rw [SymmetricAlgebra.lift_ι_apply, hπs]
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.2 hle
  · intro a ha
    obtain ⟨u, rfl⟩ := hsurj a
    have dec : ∀ u : Sy, ∃ r : A₀, ∃ j ∈ JJ, u = algebraMap A₀ Sy r + j := by
      intro u
      induction u using SymmetricAlgebra.induction with
      | algebraMap r => exact ⟨r, 0, Ideal.zero_mem _, by simp⟩
      | ι p => exact ⟨0, _, ι_mem p, by simp⟩
      | mul a b ha hb =>
        obtain ⟨r, j, hj, rfl⟩ := ha
        obtain ⟨r', j', hj', rfl⟩ := hb
        refine ⟨r * r', algebraMap A₀ Sy r * j' + j * (algebraMap A₀ Sy r' + j'), ?_, ?_⟩
        · exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hj') (Ideal.mul_mem_right _ _ hj)
        · rw [map_mul]
          ring
      | add a b ha hb =>
        obtain ⟨r, j, hj, rfl⟩ := ha
        obtain ⟨r', j', hj', rfl⟩ := hb
        exact ⟨r + r', j + j', Ideal.add_mem _ hj hj', by rw [map_add]; ring⟩
    obtain ⟨r, j, hj, rfl⟩ := dec u
    have hzero : π (SymmetricAlgebra.lift s j) = 0 := hle hj
    have h0 : r = 0 := by
      have e : π (SymmetricAlgebra.lift s (algebraMap A₀ Sy r + j)) = 0 := ha
      rw [map_add, map_add, hzero, AlgHom.commutes, AlgHom.commutes, add_zero] at e
      exact e
    subst h0
    rw [map_zero, zero_add]
    exact Ideal.mem_map_of_mem _ hj

/-- The "`e`-computation": for a map `e : Sym → Sym/J^(m+2)` with `e (ι p) ≡ ι p mod J²`, one has
`e y ≡ y mod J^(n+1)` on `J^n`. -/
lemma e_congr (m : ℕ) (e : Sy →ₐ[A₀] Sy ⧸ JJ ^ (m + 2))
    (heι : ∀ p, ∃ y ∈ JJ ^ 2, e (ιS p) = mk _ (ιS p + y)) (n : ℕ) (y : Sy) (hy : y ∈ JJ ^ n) :
    ∃ z ∈ JJ ^ (n + 1), e y = mk _ (y + z) := by
  have D0 : ∀ y : Sy, ∃ z ∈ JJ, e y = mk _ (y + z) := by
    intro y
    induction y using SymmetricAlgebra.induction with
    | algebraMap r => exact ⟨0, Ideal.zero_mem _, by rw [add_zero, AlgHom.commutes, AlgHom.commutes]⟩
    | ι p =>
      obtain ⟨z, hz, h⟩ := heι p
      exact ⟨z, mem_of_le (n := 1) (by omega) hz |> (by simpa using ·), h⟩
    | mul a b ha hb =>
      obtain ⟨z, hz, h⟩ := ha
      obtain ⟨z', hz', h'⟩ := hb
      refine ⟨a * z' + z * b + z * z', ?_, ?_⟩
      · exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hz') (Ideal.mul_mem_right _ _ hz))
          (Ideal.mul_mem_right _ _ hz)
      · rw [map_mul, h, h', ← map_mul]
        congr 1
        ring
    | add a b ha hb =>
      obtain ⟨z, hz, h⟩ := ha
      obtain ⟨z', hz', h'⟩ := hb
      refine ⟨z + z', Ideal.add_mem _ hz hz', ?_⟩
      rw [map_add, h, h', ← map_add]
      congr 1
      ring
  have D1 : ∀ y ∈ JJ, ∃ z ∈ JJ ^ 2, e y = mk _ (y + z) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨p, rfl⟩
      exact heι p
    · exact ⟨0, Ideal.zero_mem _, by simp⟩
    · rintro a b _ _ ⟨z, hz, h⟩ ⟨z', hz', h'⟩
      refine ⟨z + z', Ideal.add_mem _ hz hz', ?_⟩
      rw [map_add, h, h', ← map_add]
      congr 1
      ring
    · rintro c a ha ⟨z, hz, h⟩
      obtain ⟨z₀, hz₀, h₀⟩ := D0 c
      refine ⟨c * z + z₀ * a + z₀ * z, ?_, ?_⟩
      · refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hz) ?_) ?_
        · rw [pow_two]
          exact Ideal.mul_mem_mul hz₀ ha
        · exact Ideal.mul_mem_left _ _ hz
      · rw [smul_eq_mul, map_mul, h₀, h, ← map_mul]
        congr 1
        ring
  cases n with
  | zero => simpa using D0 y
  | succ n =>
    induction n generalizing y with
    | zero => exact D1 y (by simpa using hy)
    | succ n ihn =>
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha b hb
        obtain ⟨z, hz, h⟩ := ihn a ha
        obtain ⟨z', hz', h'⟩ := D1 b hb
        refine ⟨a * z' + z * b + z * z', ?_, ?_⟩
        · have hb₁ : b ∈ JJ ^ 1 := by simpa using hb
          refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
          · exact mem_of_le (by omega) (pow_mul_mem ha hz')
          · exact mem_of_le (by omega) (pow_mul_mem hz hb₁)
          · exact mem_of_le (by omega) (pow_mul_mem hz hz')
        · rw [map_mul, h, h', ← map_mul]
          congr 1
          ring
      · rintro a b ⟨z, hz, h⟩ ⟨z', hz', h'⟩
        refine ⟨z + z', Ideal.add_mem _ hz hz', ?_⟩
        rw [map_add, h, h', ← map_add]
        congr 1
        ring

variable [Algebra.FormallySmooth A₀ B]

/-- The content of the citation "`Sym(I/I²) → gr_I` is an isomorphism" (Tags 062Z, 063M), in the
form used by the printed proof: if `x ∈ J^k`, `x' ∈ J^(k+1)` and `φ x = φ x'`, then `x ∈ J^(k+1)`.
The printed proof gets it from regularity of `X⁰ → X^N`; here from formal smoothness of `A₀ → B`. -/
theorem gamma_injective (hπs : ∀ p, π (s p) = 0) (hts : ∀ p, tMap π (s p) = p) (k : ℕ) {x x' : Sy}
    (hx : x ∈ JJ ^ k) (hx' : x' ∈ JJ ^ (k + 1))
    (h : SymmetricAlgebra.lift s x = SymmetricAlgebra.lift s x') : x ∈ JJ ^ (k + 1) := by
  obtain ⟨ψ, hψ⟩ := exists_psi π (tMap π) (tMap_mul π) s hπs hts k
  let e : Sy →ₐ[A₀] Sy ⧸ JJ ^ (k + 2) := ψ.comp (SymmetricAlgebra.lift s)
  have heι : ∀ p, ∃ y ∈ JJ ^ 2, e (ιS p) = mk _ (ιS p + y) := fun p => by
    obtain ⟨y, hy, h⟩ := hψ p
    refine ⟨y, hy, ?_⟩
    change ψ (SymmetricAlgebra.lift s (ιS p)) = _
    rw [SymmetricAlgebra.lift_ι_apply, h]
  obtain ⟨z, hz, ez⟩ := e_congr π k e heι k x hx
  obtain ⟨z', hz', ez'⟩ := e_congr π k e heι (k + 1) x' hx'
  have hee : e x = e x' := congrArg ψ h
  rw [ez, ez', mk_eq_iff] at hee
  have h1 : x + z - (x' + z') ∈ JJ ^ (k + 1) := mem_of_le (by omega) hee
  have h2 : z' ∈ JJ ^ (k + 1) := mem_of_le (by omega) hz'
  have : x = (x + z - (x' + z')) + x' + z' - z := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.add_mem _ h1 hx') h2) hz

/-- "We then prove that `φ` is injective": `0 = φ(X) mod I^(j+1)` kills the components of `X` one
at a time. By `map_J_eq`, an element of `I^(j+1)` is `φ` of an element of `J^(j+1)`. -/
theorem phi_injective (hπs : ∀ p, π (s p) = 0) (hts : ∀ p, tMap π (s p) = p) :
    Function.Injective (SymmetricAlgebra.lift s : Sy →ₐ[A₀] B) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => eq_zero_of_mem_pow x fun j => ?_
  induction j with
  | zero => simp
  | succ j ih =>
    exact gamma_injective π hπs hts j ih (Ideal.zero_mem _) (hx.trans (map_zero _).symm)

end Injective

section Main

variable {A₀ B Y : Type u} [CommRing A₀] [CommRing B] [Algebra A₀ B] [AddCommMonoid Y] [DecidableEq Y]
  {𝒜 : Y → Submodule A₀ B} [GradedAlgebra 𝒜] {π : B →ₐ[A₀] A₀} {w : Y → ℕ}

/-- **Theorem 12.4**, the ring statement of the printed proof: `I/I²` is finite projective and
`φ : Sym_{A₀}(I/I²) → B` is an isomorphism. -/
theorem printed_ring [Algebra.FormallySmooth A₀ B] [Algebra.FiniteType A₀ B] (H : IsAug 𝒜 π w) :
    Module.Finite A₀ (Conormal π) ∧ Module.Projective A₀ (Conormal π) ∧
      Nonempty (SymmetricAlgebra A₀ (Conormal π) ≃ₐ[A₀] B) := by
  have := projective_cotangent π
  refine ⟨finite_cotangent π, this, ?_⟩
  obtain ⟨s, hts, hπs, hg⟩ := exists_section H
  have hsurj := phi_surjective H hts hπs hg
  exact ⟨AlgEquiv.ofBijective _ ⟨phi_injective π hπs hts, hsurj⟩⟩

end Main

#print axioms printed_ring

end AlgMag.Sec12Printed
