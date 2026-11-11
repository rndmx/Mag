/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.OpenCellGen
import AlgMag.Reductive.ForwardAssembly
import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation

/-!
# `hcent`: points of `C_u` commute with the ray pieces `U_(α)`

For `c ∈ C_u(k) ⊆ C(k) = Z_G(T)(k)` let `Ad c` be the coordinate map of `g ↦ c g c⁻¹`.
* `Ad c` preserves every weight space `H_χ` (`c` commutes with `T`), and the counit, hence
  preserves the ideal of `U_(α)`;
* with `O(U_(α)) = k[ȳ]`, `y ∈ H_α` (T4, named), the torus forces `Ad c ȳ = μ ȳ`
  (`T`-equivariant endomorphisms of the weight-`α` line are scalars);
* `Ad c` is locally unipotent (named: `C_u(k)` unipotent), so `μ = 1`;
* hence `c r c⁻¹ = r` for every `r ∈ U_(α)(k)`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct
open Polynomial (aeval aeval_C aeval_X comp_C_mul_X_coeff coeff_C_mul coeff_C_mul_X X_ne_zero)

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

local notation "Ad" => HopfAlgebra.pointConjugationAlgHom

omit [DecidableEq X] in
/-- Conjugation of `k`-points through `Ad`. -/
lemma conj_eq_toConv_comp_Ad (c r : WithConv (H →ₐ[k] k)) :
    c * r * c⁻¹ = toConv (r.ofConv.comp (Ad c)) := by
  have h := HopfAlgebra.comp_pointConjugationAlgHom c r
  rw [Algebra.ofId_self, AlgHom.mapValue_id, MonoidHom.id_apply] at h
  exact h.symm

/-- `Ad c` preserves weight spaces for `c ∈ C(k)`. -/
lemma Ad_mem_torusGrading [IsAlgClosed k] (c : WithConv (H →ₐ[k] k))
    (hc : magnetIdeal (torusGrading π) ⊥ ≤ RingHom.ker c.ofConv)
    {χ : Additive X} {h : H} (hh : h ∈ torusGrading π χ) :
    Ad c h ∈ torusGrading π χ := by
  set O := orbitHom π H
  set cH : WithConv (H →ₐ[k] H) := AlgHom.mapValue (Algebra.ofId k H) c
  set e : WithConv (H →ₐ[k] H ⊗[k] MonoidAlgebra k X) := O (toConv (AlgHom.id k H))
  have h1 : toConv (Ad c) = cH * toConv (AlgHom.id k H) * cH⁻¹ := by
    have := HopfAlgebra.comp_pointConjugationAlgHom c (toConv (AlgHom.id k H))
    rwa [ofConv_toConv, AlgHom.id_comp] at this
  have hcA : AlgHom.mapValue (Algebra.TensorProduct.includeLeft (S := k) (B := MonoidAlgebra k X))
      cH = AlgHom.mapValue (Algebra.ofId k (H ⊗[k] MonoidAlgebra k X)) c := by
    apply WithConv.ofConv_injective
    ext x
    simp [cH, AlgHom.mapValue_apply, Algebra.TensorProduct.algebraMap_apply]
  have hOc : O cH = AlgHom.mapValue (Algebra.ofId k (H ⊗[k] MonoidAlgebra k X)) c := by
    have hcomm := commute_torusPt_of_mem_bot π (A := H ⊗[k] MonoidAlgebra k X) Algebra.TensorProduct.includeRight
      (AlgHom.mapValue (Algebra.ofId k (H ⊗[k] MonoidAlgebra k X)) c) (by
        intro x hx
        rw [RingHom.mem_ker, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
          RingHom.mem_ker.1 (hc hx), map_zero])
    rw [show O cH = torusPoint π H * AlgHom.mapValue
      (Algebra.TensorProduct.includeLeft (S := k) (B := MonoidAlgebra k X)) cH *
        (torusPoint π H)⁻¹ from rfl, hcA]
    unfold torusPoint
    rw [hcomm.eq]
    exact mul_inv_cancel_right (G := WithConv (H →ₐ[k] H ⊗[k] MonoidAlgebra k X)) _ _
  have h2 : O (toConv (Ad c)) = toConv (e.ofConv.comp (Ad c)) := by
    rw [h1, map_mul, map_mul, map_inv, hOc]
    exact (HopfAlgebra.comp_pointConjugationAlgHom c e).symm
  have h3 := orbitHom_apply_of_mem (π := π) (toConv (Ad c)) hh
  rw [h2, ofConv_toConv, ofConv_toConv, AlgHom.comp_apply] at h3
  rw [mem_torusGrading]
  have h4 : torusCoact π (Ad c h) = e.ofConv (Ad c h) := by
    show _ = (orbitHom π H (toConv (AlgHom.id k H))).ofConv _
    rw [orbitHom_apply]
    simp [torusCoact, Algebra.TensorProduct.map_id]
    rfl
  rw [h4, h3]

/-- `Ad t` for a point `t` of `T` scales `H_χ` by `χ(t)`. -/
lemma Ad_torus_apply (τ : MonoidAlgebra k X →ₐ[k] k) {χ : Additive X} {h : H}
    (hh : h ∈ torusGrading π χ) :
    Ad (toConv (τ.comp π.toAlgHom)) h = τ (MonoidAlgebra.single (Additive.toMul χ) 1) • h := by
  have h1 := HopfAlgebra.comp_pointConjugationAlgHom (toConv (τ.comp π.toAlgHom))
    (toConv (AlgHom.id k H))
  rw [ofConv_toConv, AlgHom.id_comp] at h1
  have h2 : AlgHom.mapValue (Algebra.ofId k H) (toConv (τ.comp π.toAlgHom)) =
      toConv (((Algebra.ofId k H).comp τ).comp π.toAlgHom) := by
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_assoc]
  rw [h2] at h1
  have h3 := conj_torusPt_apply π (A := H) ((Algebra.ofId k H).comp τ) (toConv (AlgHom.id k H)) hh
  rw [← h1, ofConv_toConv, ofConv_toConv] at h3
  rw [h3, Algebra.smul_def]
  rfl

/-- An algebra endomorphism preserving weight spaces and the counit preserves `U_α`. -/
lemma map_mem_rootGroupIdeal (f : H →ₐ[k] H)
    (hf : ∀ χ : Additive X, ∀ h ∈ torusGrading π χ, f h ∈ torusGrading π χ)
    (hε : ∀ h, Coalgebra.counit (R := k) (f h) = Coalgebra.counit (R := k) h)
    (α : Additive X) (hα : ∀ n : ℕ, n • α = 0 → n = 0) {z : H}
    (hz : z ∈ (rootGroupIdeal π α hα).toIdeal) : f z ∈ (rootGroupIdeal π α hα).toIdeal := by
  have hspan : (rootGroupIdeal π α hα).toIdeal = Ideal.span
      ((⋃ (m : Additive X) (_ : m ∉ rayMagnet α), (torusGrading π m : Set H)) ∪
        {y | ∃ x ∈ torusGrading π 0, x - algebraMap k H (Coalgebra.counit (R := k) x) = y}) := by
    rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal, prescribedUnitIdeal, magnetIdeal,
      Ideal.span_union]
  have hle : (rootGroupIdeal π α hα).toIdeal ≤ (rootGroupIdeal π α hα).toIdeal.comap f := by
    conv_lhs => rw [hspan]
    rw [Ideal.span_le]
    rintro x (hx | ⟨x, hx, rfl⟩)
    · obtain ⟨m, hm, hx⟩ := Set.mem_iUnion₂.1 hx
      rw [SetLike.mem_coe, Ideal.mem_comap, hspan]
      exact Ideal.subset_span (Or.inl (Set.mem_iUnion₂.2 ⟨m, hm, hf m x hx⟩))
    · rw [SetLike.mem_coe, Ideal.mem_comap, hspan, map_sub, AlgHom.commutes, ← hε x]
      exact Ideal.subset_span (Or.inr ⟨f x, hf 0 x hx, rfl⟩)
  exact hle hz

omit [DecidableEq X] in
/-- Units of an infinite field avoiding a given nonzero `zpow` equation. -/
lemma exists_zpow_ne_one [Infinite k] {d : ℤ} (hd : d ≠ 0) : ∃ x : k, x ≠ 0 ∧ x ^ d ≠ 1 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    ((Polynomial.nthRoots d.natAbs (1 : k)).toFinset ∪ {0})
  simp only [Finset.mem_union, Multiset.mem_toFinset, Finset.mem_singleton, not_or] at hx
  obtain ⟨hx1, hx0⟩ := hx
  have hpos : 0 < d.natAbs := Int.natAbs_pos.2 hd
  rw [Polynomial.mem_nthRoots hpos] at hx1
  refine ⟨x, hx0, fun h => hx1 ?_⟩
  rcases Int.natAbs_eq d with e | e
  · rw [e, zpow_natCast] at h; exact h
  · rw [e, zpow_neg, zpow_natCast, inv_eq_one] at h; exact h

section Main

variable {ψ : X →* Multiplicative ℤ}

/-- The torus point `χ ↦ x^{⟨χ,ψ⟩}`. -/
def torusEval (ψ : X →* Multiplicative ℤ) (x : k) (hx : x ≠ 0) : MonoidAlgebra k X →ₐ[k] k :=
  MonoidAlgebra.lift (R := k) (A := k) (M := X)
    { toFun := fun χ => x ^ (ψ χ).toAdd
      map_one' := by simp
      map_mul' := fun a b => by simp [zpow_add₀ hx] }

omit [DecidableEq X] in
lemma torusEval_single (x : k) (hx : x ≠ 0) (χ : Additive X) :
    torusEval ψ x hx (MonoidAlgebra.single (Additive.toMul χ) 1) = x ^ pairingHom ψ χ := by
  simp [torusEval, MonoidAlgebra.lift_single]

variable [IsAlgClosed k]

/-- **The weight-`α` line of `O(U_α) = k[ȳ]` is `k ȳ`** (`T`-equivariance forces linearity). -/
lemma mk_eq_smul_of_mem (α : Additive X) (hα : ∀ n : ℕ, n • α = 0 → n = 0) {γ : Additive X}
    (hpair : pairingHom ψ γ ≠ 0) {y : H} (hy : y ∈ torusGrading π γ)
    (hbij : Function.Bijective (Polynomial.aeval (R := k)
      (Ideal.Quotient.mk (rootGroupIdeal π α hα).toIdeal y)))
    {h : H} (hh : h ∈ torusGrading π γ) :
    ∃ μ : k, Ideal.Quotient.mk (rootGroupIdeal π α hα).toIdeal h =
      μ • Ideal.Quotient.mk (rootGroupIdeal π α hα).toIdeal y := by
  set I := (rootGroupIdeal π α hα).toIdeal
  set q := Ideal.Quotient.mkₐ k I
  obtain ⟨P, hP⟩ := hbij.2 (Ideal.Quotient.mk I h)
  -- every torus scaling `s = x^m` gives `P(s X) = s P`
  have key : ∀ x : k, (hx : x ≠ 0) →
      P.comp (Polynomial.C (x ^ pairingHom ψ γ) * Polynomial.X) = Polynomial.C (x ^ pairingHom ψ γ) * P := by
    intro x hx
    set τ := torusEval ψ x hx
    set t : WithConv (H →ₐ[k] k) := toConv (τ.comp π.toAlgHom)
    set s := x ^ pairingHom ψ γ
    have hAd : ∀ χ : Additive X, ∀ g ∈ torusGrading π χ, Ad t g ∈ torusGrading π χ :=
      fun χ g hg => by
        rw [Ad_torus_apply π τ hg]; exact Submodule.smul_mem _ _ hg
    have hε : ∀ g, Coalgebra.counit (R := k) (Ad t g) = Coalgebra.counit (R := k) g := fun g =>
      AlgHom.congr_fun (HopfAlgebra.counit_comp_pointConjugationAlgHom t) g
    have hs : ∀ g ∈ torusGrading π γ, Ad t g = s • g := fun g hg => by
      rw [Ad_torus_apply π τ hg, torusEval_single]
    -- `h - P(y) ∈ I`
    have hd : h - Polynomial.aeval y P ∈ I := by
      rw [← Ideal.Quotient.eq, ← hP]
      have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I) y P
      rw [Ideal.Quotient.mkₐ_eq_mk] at this
      exact this
    have hd' := map_mem_rootGroupIdeal π (Ad t) hAd hε α hα hd
    rw [map_sub, ← Ideal.Quotient.eq, hs h hh, ← Polynomial.aeval_algHom_apply (Ad t),
      hs y hy] at hd'
    apply hbij.1
    rw [Polynomial.aeval_comp, map_mul, aeval_C, aeval_X, map_mul, aeval_C, hP]
    have e1 : (Ideal.Quotient.mk I) (s • h) = algebraMap k _ s * Ideal.Quotient.mk I h :=
      (map_smul (Ideal.Quotient.mkₐ k I) s h).trans (Algebra.smul_def _ _)
    have e2 : (Ideal.Quotient.mk I) (Polynomial.aeval (s • y) P) =
        Polynomial.aeval (algebraMap k _ s * Ideal.Quotient.mk I y) P := by
      have := (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I) (s • y) P).symm
      rw [map_smul (Ideal.Quotient.mkₐ k I) s y,
        Algebra.smul_def s (Ideal.Quotient.mkₐ k I y)] at this
      exact this
    rw [← e1, hd', e2]
  refine ⟨P.coeff 1, ?_⟩
  have hPX : P = Polynomial.C (P.coeff 1) * Polynomial.X := by
    ext n
    rw [coeff_C_mul_X]
    split_ifs with hn
    · subst hn; rfl
    · have hd : pairingHom ψ γ * ((n : ℤ) - 1) ≠ 0 :=
        mul_ne_zero hpair (sub_ne_zero.2 (by exact_mod_cast hn))
      obtain ⟨x, hx0, hx1⟩ := exists_zpow_ne_one (k := k) hd
      have := congrArg (fun Q => Q.coeff n) (key x hx0)
      simp only [comp_C_mul_X_coeff, coeff_C_mul] at this
      have hne : (x ^ pairingHom ψ γ) ^ n ≠ x ^ pairingHom ψ γ := by
        intro e
        apply hx1
        rw [mul_sub, mul_one, zpow_sub₀ hx0, zpow_mul, zpow_natCast, e, div_self]
        exact zpow_ne_zero _ hx0
      have : P.coeff n * ((x ^ pairingHom ψ γ) ^ n - x ^ pairingHom ψ γ) = 0 := by
        linear_combination this
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  rw [← hP]
  conv_lhs => rw [hPX]
  rw [map_mul, aeval_C, aeval_X, Algebra.smul_def]

variable [Algebra.FiniteType k H]

omit [IsAlgClosed k] in
lemma kills_bot_of_kills_Cu (c : WithConv (H →ₐ[k] k))
    (hc : ∀ y ∈ CuIdeal π, c.ofConv y = 0) :
    magnetIdeal (torusGrading π) ⊥ ≤ RingHom.ker c.ofConv := by
  intro y hy
  rw [RingHom.mem_ker]
  apply hc
  rw [mem_CuIdeal]
  have : Ideal.Quotient.mk (magnetHopfIdeal π ⊥).toIdeal y = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, magnetHopfIdeal_toIdeal]; exact hy
  rw [this]
  exact (RuC π).toIdeal.zero_mem

/-- **`hcent` for `C_u`.** Named inputs: `hGa` (T4: `O(U_(α)) = k[ȳ]`, `y` of weight `α`) and
`hunip` (`Ad c` locally unipotent for `c ∈ C_u(k)`). -/
theorem hcent_CuIdeal
    (hGa : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      (∀ r ∈ rayPoints π φ α, r = 1) ∨ ∃ γ : Additive X, pairingHom φ γ ≠ 0 ∧
      ∃ y ∈ torusGrading π γ, Function.Bijective (Polynomial.aeval (R := k)
        (Ideal.Quotient.mk (rootGroupIdeal π α.1 (PosRay.torsionFree φ α)).toIdeal y)))
    (hunip : ∀ c : WithConv (H →ₐ[k] k), (∀ y ∈ CuIdeal π, c.ofConv y = 0) →
      ∀ h : H, ∃ n : ℕ, (((Ad c).toLinearMap - 1) ^ n) h = 0) :
    ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      ∀ r ∈ rayPoints π φ α, ∀ c : WithConv (H →ₐ[k] k), (∀ y ∈ CuIdeal π, c.ofConv y = 0) →
        c * r = r * c := by
  intro φ hφ α r hr c hc
  set hα := PosRay.torsionFree φ α
  set I := (rootGroupIdeal π α.1 hα).toIdeal
  rcases hGa φ hφ α with htriv | ⟨γ, hγ, y, hy, hbij⟩
  · rw [htriv r hr, one_mul, mul_one]
  have hcb := kills_bot_of_kills_Cu π c hc
  have hAd : ∀ χ : Additive X, ∀ g ∈ torusGrading π χ, Ad c g ∈ torusGrading π χ :=
    fun χ g hg => Ad_mem_torusGrading π c hcb hg
  have hε : ∀ g, Coalgebra.counit (R := k) (Ad c g) = Coalgebra.counit (R := k) g := fun g =>
    AlgHom.congr_fun (HopfAlgebra.counit_comp_pointConjugationAlgHom c) g
  have hI : ∀ z ∈ I, Ad c z ∈ I := fun z hz => map_mem_rootGroupIdeal π (Ad c) hAd hε α.1 hα hz
  obtain ⟨μ, hμ⟩ := mk_eq_smul_of_mem π (ψ := φ) α.1 hα hγ hy hbij (hAd γ y hy)
  -- `mk z = ν ȳ ⇒ mk (Ad c z) = (ν μ) ȳ`
  have hstep : ∀ z : H, ∀ ν : k, Ideal.Quotient.mk I z = ν • Ideal.Quotient.mk I y →
      Ideal.Quotient.mk I (Ad c z) = (ν * μ) • Ideal.Quotient.mk I y := by
    intro z ν hz
    have h1 : z - ν • y ∈ I := by
      rw [← Ideal.Quotient.eq, hz]; exact (map_smul (Ideal.Quotient.mkₐ k I) ν y).symm
    have h2 := hI _ h1
    rw [map_sub, map_smul, ← Ideal.Quotient.eq] at h2
    rw [h2]
    change Ideal.Quotient.mkₐ k I (ν • Ad c y) = _
    rw [map_smul]
    change ν • Ideal.Quotient.mk I (Ad c y) = _
    rw [hμ, smul_smul]
  -- unipotency: `μ = 1`
  have hμ1 : μ = 1 := by
    obtain ⟨n, hn⟩ := hunip c hc y
    have hpow : ∀ j : ℕ, Ideal.Quotient.mk I ((((Ad c).toLinearMap - 1) ^ j) y) =
        (μ - 1) ^ j • Ideal.Quotient.mk I y := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
          map_sub, AlgHom.toLinearMap_apply, hstep _ _ ih, ih, ← sub_smul (R := k)]
        congr 1; ring
    have h0 := hpow n
    rw [hn, map_zero] at h0
    have hy0 : Ideal.Quotient.mk I y ≠ 0 := by
      intro e
      have : Polynomial.aeval (R := k) (Ideal.Quotient.mk I y) Polynomial.X =
          Polynomial.aeval (R := k) (Ideal.Quotient.mk I y) 0 := by rw [aeval_X, e, map_zero]
      exact X_ne_zero (hbij.1 this)
    have := (smul_eq_zero.1 h0.symm).resolve_right hy0
    exact sub_eq_zero.1 (eq_zero_of_pow_eq_zero this)
  -- `Ad c y ≡ y` modulo `I`
  have hy1 : Ad c y - y ∈ I := by
    rw [← Ideal.Quotient.eq, hμ, hμ1, one_smul]
  -- `r ∘ Ad c = r`
  have hr' : ∀ z ∈ I, r.ofConv z = 0 := fun z hz => hr hz
  have hcomp : r.ofConv.comp (Ad c) = r.ofConv := by
    ext z
    obtain ⟨P, hP⟩ := hbij.2 (Ideal.Quotient.mk I z)
    have hd : z - Polynomial.aeval y P ∈ I := by
      rw [← Ideal.Quotient.eq, ← hP]
      have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I) y P
      rw [Ideal.Quotient.mkₐ_eq_mk] at this
      exact this
    have e1 : r.ofConv z = r.ofConv (Polynomial.aeval y P) := by
      rw [← sub_eq_zero, ← map_sub]; exact hr' _ hd
    have e2 : r.ofConv (Ad c z) = r.ofConv (Ad c (Polynomial.aeval y P)) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub]; exact hr' _ (hI _ hd)
    have e3 : r.ofConv (Ad c y) = r.ofConv y := by
      rw [← sub_eq_zero, ← map_sub]; exact hr' _ hy1
    rw [AlgHom.comp_apply, e2, e1, ← Polynomial.aeval_algHom_apply (Ad c),
      ← Polynomial.aeval_algHom_apply r.ofConv, ← Polynomial.aeval_algHom_apply r.ofConv, e3]
  have hconj := conj_eq_toConv_comp_Ad c r
  rw [hcomp, toConv_ofConv] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

end Main

end AlgMag.Reductive
