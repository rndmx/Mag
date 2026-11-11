/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSStabGenField

/-!
# The generic stabilizer for quasi-separated `X`: the translate argument

For a nonzerodivisor `F` of `k[N]` and a character `g` of `N` in a field `L₀`, there is a point `y` of
`D(N)` in a field with `F(y) ≠ 0` and `F(g y) ≠ 0`: both `F` and its translate by `g` are
nonzerodivisors on `L₀ ⊗ k[N]`.
-/

open TensorProduct

universe u

namespace AlgMag.ChartQSStabGen

section Translate

variable {k : Type u} [Field k] {N : Type u} [AddCommGroup N] {L₀ : Type u} [Field L₀] [Algebra k L₀]

/-- `L₀ ⊗ k[N]`. -/
local notation "Ω" => L₀ ⊗[k] AddMonoidAlgebra k N

variable (k) in
/-- `n ↦ g(n) ⊗ [n]`. -/
noncomputable def tauChar (g : Multiplicative N →* L₀) : Multiplicative N →* Ω where
  toFun n := g n ⊗ₜ[k] AddMonoidAlgebra.of k N n
  map_one' := by rw [map_one, map_one]; rfl
  map_mul' a b := by
    rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul]

variable (k) in
/-- The translation by `g` on `L₀ ⊗ k[N]`. -/
noncomputable def tau (g : Multiplicative N →* L₀) : Ω →ₐ[L₀] Ω :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId L₀ Ω)
    (AddMonoidAlgebra.lift k Ω N (tauChar k g))

lemma tau_tmul_of (g : Multiplicative N →* L₀) (l : L₀) (n : Multiplicative N) :
    tau k g (l ⊗ₜ[k] AddMonoidAlgebra.of k N n) = (l * g n) ⊗ₜ[k] AddMonoidAlgebra.of k N n := by
  have e : AddMonoidAlgebra.lift k Ω N (tauChar k g) (AddMonoidAlgebra.of k N n) = tauChar k g n := by
    simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.lift_single]
  change algebraMap L₀ Ω l * AddMonoidAlgebra.lift k Ω N (tauChar k g) (AddMonoidAlgebra.of k N n) = _
  rw [e]
  change algebraMap L₀ Ω l * (g n ⊗ₜ[k] AddMonoidAlgebra.of k N n) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

lemma single_eq_smul_of (m : N) (r : k) :
    AddMonoidAlgebra.single m r = r • AddMonoidAlgebra.of k N (Multiplicative.ofAdd m) := by
  simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.smul_single]

lemma tau_tau (g g' : Multiplicative N →* L₀) (h : ∀ n, g n * g' n = 1) (w : Ω) :
    tau k g (tau k g' w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul l x =>
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | single m r =>
      rw [single_eq_smul_of, ← TensorProduct.smul_tmul, tau_tmul_of, tau_tmul_of, mul_assoc,
        mul_comm (g' _), h, mul_one]

/-- `Ω` is nontrivial. -/
lemma omega_nontrivial : Nontrivial Ω := by
  let e : Ω →ₐ[L₀] L₀ := Algebra.TensorProduct.productLeftAlgHom (AlgHom.id L₀ L₀)
    (AddMonoidAlgebra.lift k L₀ N 1)
  exact e.toRingHom.domain_nontrivial

/-- Left multiplication by `1 ⊗ F` is injective on `Ω` when `F` is a nonzerodivisor. -/
lemma one_tmul_mem (F : AddMonoidAlgebra k N) (hF : F ∈ nonZeroDivisors (AddMonoidAlgebra k N))
    (w : Ω) (h : ((1 : L₀) ⊗ₜ[k] F) * w = 0) : w = 0 := by
  let μ : AddMonoidAlgebra k N →ₗ[k] AddMonoidAlgebra k N := LinearMap.mulLeft k F
  have hμ : Function.Injective μ := by
    refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
    have e : F * a = 0 := ha
    exact (mem_nonZeroDivisors_iff.1 hF).1 a e
  have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := L₀) μ hμ
  refine (injective_iff_map_eq_zero _).mp hl w ?_
  have e : ∀ w : Ω, LinearMap.lTensor L₀ μ w = ((1 : L₀) ⊗ₜ[k] F) * w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | tmul l x =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rfl
  rw [e, h]

/-- **The translate argument.** -/
theorem exists_translate (g : Multiplicative N →* L₀) (F : AddMonoidAlgebra k N)
    (hF : F ∈ nonZeroDivisors (AddMonoidAlgebra k N)) :
    ∃ (L' : Type u) (_ : Field L') (ι : L₀ →+* L') (y : Multiplicative N →* L'),
      ev (ι.comp (algebraMap k L₀)) y F ≠ 0 ∧
        ev (ι.comp (algebraMap k L₀)) ((rm ι).comp g * y) F ≠ 0 := by
  classical
  haveI : Nontrivial Ω := omega_nontrivial
  let a : Ω := (1 : L₀) ⊗ₜ[k] F
  let g' : Multiplicative N →* L₀ := g.comp (invMonoidHom)
  have hgg : ∀ n, g n * g' n = 1 := fun n => by
    change g n * g n⁻¹ = 1
    rw [← map_mul, mul_inv_cancel, map_one]
  have hgg' : ∀ n, g' n * g n = 1 := fun n => by rw [mul_comm, hgg]
  have ha : ∀ w, a * w = 0 → w = 0 := one_tmul_mem F hF
  have hb : ∀ w, tau k g a * w = 0 → w = 0 := by
    intro w hw
    have e := congrArg (tau k g') hw
    rw [map_mul, tau_tau g' g hgg', map_zero] at e
    have := ha _ e
    have e2 := congrArg (tau k g) this
    rwa [tau_tau g g' hgg, map_zero] at e2
  have hab : ∀ n : ℕ, (a * tau k g a) ^ n ≠ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro h0
      rw [pow_succ, mul_comm, mul_assoc] at h0
      exact ih (hb _ (ha _ h0))
  have hnil : a * tau k g a ∉ nilradical Ω := fun h => by
    obtain ⟨n, hn⟩ := h
    exact hab n hn
  rw [nilradical_eq_sInf, Ideal.mem_sInf] at hnil
  push Not at hnil
  obtain ⟨q, hq, hqa⟩ := hnil
  haveI : q.IsPrime := hq
  let L' := FractionRing (Ω ⧸ q)
  let π : Ω →+* L' := (algebraMap (Ω ⧸ q) L').comp (Ideal.Quotient.mk q)
  have hπ : π (a * tau k g a) ≠ 0 := fun h => by
    refine hqa (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    exact (IsFractionRing.injective (Ω ⧸ q) L') (h.trans (map_zero _).symm)
  let ι : L₀ →+* L' := π.comp (algebraMap L₀ Ω)
  let y : Multiplicative N →* L' := (rm π).comp
    ((rm (Algebra.TensorProduct.includeRight (R := k) (A := L₀) (B := AddMonoidAlgebra k N)).toRingHom).comp
      (AddMonoidAlgebra.of k N))
  have e1 : (ev (ι.comp (algebraMap k L₀)) y) =
      π.comp (Algebra.TensorProduct.includeRight (R := k) (A := L₀) (B := AddMonoidAlgebra k N)).toRingHom := by
    refine ringHom_ext' fun m r => ?_
    rw [ev_single, single_eq_smul_of]
    change π (algebraMap L₀ Ω (algebraMap k L₀ r)) * π ((1 : L₀) ⊗ₜ[k] _) = π ((1 : L₀) ⊗ₜ[k] (r • _))
    rw [← map_mul]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    rw [algebraMap_smul]
  have e2 : (ev (ι.comp (algebraMap k L₀)) ((rm ι).comp g * y)) =
      π.comp ((tau k g).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := k) (A := L₀) (B := AddMonoidAlgebra k N)).toRingHom) := by
    refine ringHom_ext' fun m r => ?_
    rw [ev_single, single_eq_smul_of]
    have e3 : tau k g ((1 : L₀) ⊗ₜ[k] (r • AddMonoidAlgebra.of k N (Multiplicative.ofAdd m))) =
        (algebraMap k L₀ r * g (Multiplicative.ofAdd m)) ⊗ₜ[k]
          AddMonoidAlgebra.of k N (Multiplicative.ofAdd m) := by
      rw [← TensorProduct.smul_tmul, tau_tmul_of, Algebra.algebraMap_eq_smul_one]
    change π (algebraMap L₀ Ω (algebraMap k L₀ r)) * (π (algebraMap L₀ Ω (g (Multiplicative.ofAdd m))) *
      π ((1 : L₀) ⊗ₜ[k] _)) = π (tau k g ((1 : L₀) ⊗ₜ[k] (r • AddMonoidAlgebra.of k N (Multiplicative.ofAdd m))))
    rw [e3, ← map_mul, ← map_mul]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp
  refine ⟨L', inferInstance, ι, y, ?_, ?_⟩
  · rw [e1]
    intro h
    refine hπ ?_
    rw [map_mul]
    exact mul_eq_zero_of_left h _
  · rw [e2]
    intro h
    refine hπ ?_
    rw [map_mul]
    exact mul_eq_zero_of_right _ h

end Translate

end AlgMag.ChartQSStabGen
