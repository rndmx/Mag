/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSEqGens

/-!
# Uniqueness along an ideal in the Jacobson radical, any algebraic space

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.
Uniqueness part of equivariant effectivity. The separated variant `Chart.eq_of_agree_of_iInf`
allows any family of ideals with zero intersection; that form fails without separatedness.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQS

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- Krull: an ideal inside all `a^k` of a noetherian ring is killed by an element of `1 + a`. -/
theorem exists_one_sub_mul_eq_zero {R : Type*} [CommRing R] [IsNoetherianRing R] (a I : Ideal R)
    (hI : ∀ i ∈ I, ∀ k : ℕ, i ∈ a ^ k) : ∃ r ∈ a, ∀ i ∈ I, (1 - r) * i = 0 := by
  have hx : ∀ x ∈ I, ∃ r ∈ a, (1 - r) * x = 0 := by
    intro x hx
    have hm : x ∈ (⨅ i : ℕ, a ^ i • ⊤ : Submodule R R) := by
      refine (Submodule.mem_iInf _).2 fun k => ?_
      simpa using hI x hx k
    obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff a x).1 hm
    refine ⟨r.1, r.2, ?_⟩
    have : (r : R) * x = x := hr
    rw [sub_mul, one_mul, this, sub_self]
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian I : I.FG)
  classical
  induction t using Finset.induction_on generalizing I with
  | empty =>
    refine ⟨0, a.zero_mem, fun i hi => ?_⟩
    rw [← ht] at hi
    simpa using hi
  | insert z t' hz ih =>
    have hzI : z ∈ I := ht ▸ Submodule.subset_span (by simp)
    obtain ⟨r₁, hr₁, h₁⟩ := hx z hzI
    have hle : Ideal.span (t' : Set R) ≤ I := by
      rw [← ht]
      exact Submodule.span_mono (by simp)
    obtain ⟨r₂, hr₂, h₂⟩ := ih (Ideal.span (t' : Set R)) (fun i hi => hI i (hle hi))
      (fun x hx' => hx x (hle hx')) rfl
    refine ⟨r₁ + r₂ - r₁ * r₂, a.sub_mem (a.add_mem hr₁ hr₂) (a.mul_mem_right _ hr₁), fun i hi => ?_⟩
    rw [← ht, Finset.coe_insert, Ideal.submodule_span_eq, Ideal.span_insert] at hi
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hi
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    have e : 1 - (r₁ + r₂ - r₁ * r₂) = (1 - r₁) * (1 - r₂) := by ring
    rw [e]
    have h3 := h₂ w hw
    calc (1 - r₁) * (1 - r₂) * (c * z + w)
        = (1 - r₂) * c * ((1 - r₁) * z) + (1 - r₁) * ((1 - r₂) * w) := by ring
      _ = 0 := by rw [h₁, h3]; ring

set_option maxHeartbeats 2000000 in
/-- **Equivariant effectivity, uniqueness, any algebraic space.** `W` affine noetherian, `a` in the Jacobson
radical of `Γ(W)`. Two points of `X` over `W` agreeing on all `V(a^k)` are equal. -/
theorem eq_of_agree_pow (hX : IsAlgebraicSpace B S hS X) (W : BigFppfOver B S hS)
    [IsAffine ((SCH).obj W)] [IsNoetherianRing Γ((SCH).obj W, ⊤)] (a : Ideal Γ((SCH).obj W, ⊤))
    (ha : a ≤ Ideal.jacobson ⊥) (p q : X.obj (op W))
    (h : ∀ k : ℕ, X.map (Chart.immι W (Chart.closedι ((SCH).obj W) (a ^ k))).op p =
      X.map (Chart.immι W (Chart.closedι ((SCH).obj W) (a ^ k))).op q) : p = q := by
  let p' : yoneda.obj W ⟶ X := yonedaEquiv.symm p
  let q' : yoneda.obj W ⟶ X := yonedaEquiv.symm q
  have hVk : ∀ k : ℕ, yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) (a ^ k))) ≫ p' =
      yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) (a ^ k))) ≫ q' := by
    intro k
    apply yonedaEquiv.injective
    simpa [p', q', yonedaEquiv_apply] using h k
  have hch : ∀ y : (SCH).obj W, (∀ r ∈ a, y ∉ ((SCH).obj W).basicOpen r) →
      ∃ (P : BigFppfOver B S hS) (e : P ⟶ W), Etale ((SCH).map e) ∧ y ∈ Set.range ((SCH).map e) ∧
        X.map e.op p = X.map e.op q := by
    intro y hy
    obtain ⟨P, V, hPa, e, v, hv, s, t, hVa, heE, ⟨y₁, hy₁⟩, hs, ht, hst⟩ :=
      exists_chart_agree hX a p' q' hVk y hy
    let f := ((SCH).map e).appTop.hom
    have hft : f.FiniteType :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
    letI : Algebra Γ((SCH).obj W, ⊤) Γ((SCH).obj P, ⊤) := f.toAlgebra
    haveI : Algebra.FiniteType Γ((SCH).obj W, ⊤) Γ((SCH).obj P, ⊤) := hft
    haveI hNP : IsNoetherianRing Γ((SCH).obj P, ⊤) :=
      Algebra.FiniteType.isNoetherianRing Γ((SCH).obj W, ⊤) _
    let σ : Γ((SCH).obj V, ⊤) →+* Γ((SCH).obj P, ⊤) := ((SCH).map s).appTop.hom
    let τ : Γ((SCH).obj V, ⊤) →+* Γ((SCH).obj P, ⊤) := ((SCH).map t).appTop.hom
    let I : Ideal Γ((SCH).obj P, ⊤) := Ideal.span (Set.range fun b => σ b - τ b)
    let aP : Ideal Γ((SCH).obj P, ⊤) := a.map f
    have hIk : ∀ i ∈ I, ∀ k : ℕ, i ∈ aP ^ k := by
      intro i hi k
      refine (Ideal.span_le.2 ?_ : I ≤ _) hi
      rintro _ ⟨b, rfl⟩
      have hk : aP ^ k = (a ^ k).map f := (Ideal.map_pow _ _ _).symm
      rw [hk]
      refine Chart.closedι_appTop_eq_zero _ _ ?_
      have h' := congrArg (fun φ => ((SCH).map φ).appTop.hom b) (hst k)
      simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at h'
      change (Chart.closedι ((SCH).obj P) _).appTop.hom (σ b - τ b) = 0
      rw [map_sub, sub_eq_zero]
      exact h'
    obtain ⟨r, hr, hri⟩ := exists_one_sub_mul_eq_zero aP I hIk
    let D := ((SCH).obj P).basicOpen (1 - r)
    haveI hDa : IsAffine D.toScheme := (isAffineOpen_top _).basicOpen _
    let jD := Chart.immι P D.ι
    have hzz : ∀ b, D.ι.appTop.hom (σ b - τ b) = 0 := fun b =>
      ι_appTop_eq_zero_of_mul _ _ (hri _ (Ideal.subset_span ⟨b, rfl⟩))
    have hstD : jD ≫ s = jD ≫ t := by
      haveI : IsAffine ((SCH).obj V) := hVa
      refine ChartMain.siteExt (ChartMain.toAffine_ext (RingHom.ext fun b => ?_))
      have h0 := hzz b
      rw [map_sub, sub_eq_zero] at h0
      simp only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h0
    have hyD : y₁ ∈ D := by
      refine (mem_basicOpen_iff y₁ _).2 fun hm => ?_
      have hrp : r ∈ (((SCH).obj P).isoSpec.hom y₁).asIdeal := by
        refine (Ideal.map_le_iff_le_comap.2 fun x hx => ?_ : aP ≤ _) hr
        by_contra hc
        have hb := (mem_basicOpen_iff y₁ (f x)).2 hc
        have e' : ((SCH).obj P).basicOpen (f x) = (SCH).map e ⁻¹ᵁ ((SCH).obj W).basicOpen x :=
          (Scheme.preimage_basicOpen _ x).symm
        rw [e'] at hb
        refine hy x hx ?_
        rw [← hy₁]
        exact hb
      have := Ideal.add_mem _ hm hrp
      rw [sub_add_cancel] at this
      exact (((SCH).obj P).isoSpec.hom y₁).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
    refine ⟨Chart.immObj P D.ι, jD ≫ e, ?_, ⟨(⟨y₁, hyD⟩ : D), hy₁⟩, ?_⟩
    · change Etale (D.ι ≫ (SCH).map e)
      infer_instance
    · have hps : yoneda.map (jD ≫ s) ≫ v = yoneda.map (jD ≫ e) ≫ p' := by
        simp only [yoneda.map_comp, Category.assoc, hs]
      have hpt : yoneda.map (jD ≫ t) ≫ v = yoneda.map (jD ≫ e) ≫ q' := by
        simp only [yoneda.map_comp, Category.assoc, ht]
      rw [hstD] at hps
      have := congrArg yonedaEquiv (hps.symm.trans hpt)
      simpa [p', q', yonedaEquiv_apply] using this
  let Y₀ : Type u := {y : (SCH).obj W // ∀ r ∈ a, y ∉ ((SCH).obj W).basicOpen r}
  have hch' : ∀ y : Y₀, ∃ (P : BigFppfOver B S hS) (e : P ⟶ W), Etale ((SCH).map e) ∧
      y.1 ∈ Set.range ((SCH).map e) ∧ X.map e.op p = X.map e.op q := fun y => hch y.1 y.2
  choose Pf ef hEt hrg heq using hch'
  refine eq_of_family hX Pf ef (fun y => ?_) (fun y => ?_) (fun z => ?_) p q heq
  · have := hEt y
    infer_instance
  · have := hEt y
    exact ((SCH).map (ef y)).isOpenMap
  · -- `z` generizes a closed point, which lies in `V(a)`
    let Y := (SCH).obj W
    let P₀ := (Y.isoSpec.hom z).asIdeal
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal P₀ (Y.isoSpec.hom z).isPrime.ne_top
    let mp : Spec Γ(Y, ⊤) := ⟨m, hm.isPrime⟩
    let y₀ : Y := Y.isoSpec.inv mp
    have hhj : ∀ w : Spec Γ(Y, ⊤), Y.isoSpec.hom (Y.isoSpec.inv w) = w := fun w => by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    have hhi : Y.isoSpec.inv (Y.isoSpec.hom z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    have hy₀ : ∀ r ∈ a, y₀ ∉ Y.basicOpen r := by
      intro r hr hb
      have hb' := (mem_basicOpen_iff y₀ r).1 hb
      rw [show y₀ = Y.isoSpec.inv mp from rfl, hhj] at hb'
      exact hb' ((Ideal.mem_sInf.1 (ha hr)) ⟨bot_le, hm⟩)
    have hsp : (Y.isoSpec.hom z) ⤳ mp := (PrimeSpectrum.le_iff_specializes _ _).1 hle
    have hsp' : z ⤳ y₀ := by
      have := hsp.map Y.isoSpec.inv.continuous
      rwa [hhi] at this
    have ho : IsOpen (Set.range ((SCH).map (ef ⟨y₀, hy₀⟩))) := by
      have := hEt ⟨y₀, hy₀⟩
      exact ((SCH).map (ef ⟨y₀, hy₀⟩)).isOpenMap.isOpen_range
    exact ⟨⟨y₀, hy₀⟩, hsp'.mem_open ho (hrg ⟨y₀, hy₀⟩)⟩

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.exists_one_sub_mul_eq_zero
#print axioms AlgMag.ChartQS.eq_of_agree_pow
