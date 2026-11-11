/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.

Compiled; no sorry.
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Free
import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent

/-!
# Invariant differentials: `Ω[H⁄k] ≅ H ⊗[k] ω_G`

For a commutative Hopf algebra `H` over a field `k`, with `I = ker ε` and `ω = I/I²`
(`TauCeti.Bialgebra.CotangentSpace k H`), the `H`-modules `Ω[H⁄k]` and `H ⊗[k] ω` are isomorphic.
Hence `Ω[H⁄k]` is free, of rank `dim ω`.

* `Ψ : Ω → H ⊗ ω` is induced by the derivation `d x = ∑ x₁ ⊗ [x₂ - ε(x₂)]`
  (Leibniz from `cot (ab) = ε(a) cot b + ε(b) cot a` and multiplicativity of `Δ`).
* `Φ : H ⊗ ω → Ω` is `a ⊗ [y] ↦ a · θ(y)`, `θ(y) = ∑ S(y₁) dy₂`; `θ(xy) = ε(x)θ(y) + ε(y)θ(x)`
  (from `∑ S(x₁)x₂ = ε(x)`), so `θ` kills `I²` and descends to `ω`.
* `Φ Ψ (dx) = ∑ x₁ S(x₂) dx₃ = dx` and `Ψ Φ (1 ⊗ [y]) = ∑ S(y₁) y₂ ⊗ [y₃] = 1 ⊗ [y]`
  (coassociativity and the two antipode axioms).
-/

namespace AlgMag.OpenCellNotes

open scoped TensorProduct
open TensorProduct

universe u

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]

local notation "ω" => TauCeti.Bialgebra.CotangentSpace k H
local notation "cot" => TauCeti.Bialgebra.cotangentMap k H
local notation "S" => HopfAlgebra.antipode k (A := H)
local notation "Δ" => Coalgebra.comul (R := k) (A := H)
local notation "ε" => Coalgebra.counit (R := k) (A := H)
local notation "dd" => KaehlerDifferential.D k H

/-! ### Linear-map forms of the Hopf axioms used below. -/

/-- `E = rid ∘ (id ⊗ ε)`, a left inverse of `Δ`. -/
noncomputable def counitRight : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H ε

lemma counitRight_tmul (a b : H) : counitRight k H (a ⊗ₜ b) = ε b • a := by
  simp [counitRight]

lemma counitRight_comul (x : H) : counitRight k H (Δ x) = x := by
  simp [counitRight, Coalgebra.lTensor_counit_comul]

/-- `M = mul' ∘ (S ⊗ id)`; `M (Δ x) = ε(x) • 1`. -/
noncomputable def antipodeMul : H ⊗[k] H →ₗ[k] H :=
  LinearMap.mul' k H ∘ₗ LinearMap.rTensor H S

lemma antipodeMul_tmul (a b : H) : antipodeMul k H (a ⊗ₜ b) = S a * b := by
  simp [antipodeMul]

lemma antipodeMul_comul (x : H) : antipodeMul k H (Δ x) = algebraMap k H (ε x) := by
  -- Mathlib: `HopfAlgebra.mul_antipode_rTensor_comul_apply`.
  simp [antipodeMul, HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) x]

/-! ### The derivation `d : H → H ⊗ ω` and `Ψ`. -/

lemma lTensor_cot_mul (u v : H ⊗[k] H) :
    (cot).lTensor H (u * v) =
      counitRight k H u • (cot).lTensor H v + counitRight k H v • (cot).lTensor H u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
    simp only [add_mul, map_add, h₁, h₂, add_smul, smul_add]
    abel
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v₁ v₂ h₁ h₂ =>
      simp only [mul_add, map_add, h₁, h₂, smul_add, add_smul]
      abel
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul,
        TauCeti.Bialgebra.cotangentMap_mul, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul, counitRight_tmul, counitRight_tmul, LinearMap.lTensor_tmul,
        LinearMap.lTensor_tmul]
      simp only [TensorProduct.smul_tmul', smul_eq_mul]
      rw [smul_mul_assoc, smul_mul_assoc, mul_comm c a]

/-- The invariant-differential derivation `d x = ∑ x₁ ⊗ cot x₂`. -/
noncomputable def invDer : Derivation k H (H ⊗[k] ω) :=
  Derivation.mk' ((cot).lTensor H ∘ₗ Δ) fun a b => by
    simp only [LinearMap.comp_apply]
    have hm : Δ (a * b) = Δ a * Δ b := map_mul (Bialgebra.comulAlgHom k H) a b
    rw [hm, lTensor_cot_mul, counitRight_comul, counitRight_comul]

/-- `Ψ : Ω[H⁄k] → H ⊗ ω`. -/
noncomputable def kaehlerToInv : Ω[H⁄k] →ₗ[H] H ⊗[k] ω :=
  (invDer k H).liftKaehlerDifferential

lemma kaehlerToInv_D (x : H) : kaehlerToInv k H (dd x) = (cot).lTensor H (Δ x) := by
  simp [kaehlerToInv, invDer]

/-! ### `θ(y) = ∑ S(y₁) dy₂` and `Φ`. -/

/-- `B (a ⊗ b) = a • db`. -/
noncomputable def smulD : H ⊗[k] H →ₗ[k] Ω[H⁄k] :=
  TensorProduct.lift (LinearMap.mk₂ k (fun a b => a • dd b)
    (fun a₁ a₂ b => add_smul a₁ a₂ _)
    (fun c a b => smul_assoc c a _)
    (fun a b₁ b₂ => by rw [map_add, smul_add])
    (fun c a b => by rw [(KaehlerDifferential.D k H).map_smul, smul_comm]))

lemma smulD_tmul (a b : H) : smulD k H (a ⊗ₜ b) = a • dd b := rfl

/-- `B' = B ∘ (S ⊗ id)`. -/
noncomputable def antipodeSmulD : H ⊗[k] H →ₗ[k] Ω[H⁄k] := smulD k H ∘ₗ LinearMap.rTensor H S

lemma antipodeSmulD_tmul (a b : H) : antipodeSmulD k H (a ⊗ₜ b) = S a • dd b := by
  simp [antipodeSmulD, smulD_tmul]

lemma antipodeSmulD_mul (u v : H ⊗[k] H) :
    antipodeSmulD k H (u * v) =
      antipodeMul k H u • antipodeSmulD k H v + antipodeMul k H v • antipodeSmulD k H u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
    simp only [add_mul, map_add, h₁, h₂, add_smul, smul_add]
    abel
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v₁ v₂ h₁ h₂ =>
      simp only [mul_add, map_add, h₁, h₂, smul_add, add_smul]
      abel
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, antipodeSmulD_tmul, antipodeSmulD_tmul,
        antipodeSmulD_tmul, antipodeMul_tmul, antipodeMul_tmul, Derivation.leibniz]
      -- (`HopfAlgebra.antipode_mul` / `antipode_mul_comm`), then `module`.
      rw [HopfAlgebra.antipode_mul_antidistrib (R := k)]
      simp only [smul_add, smul_smul]
      congr 1 <;> ring_nf

/-- `θ = B' ∘ Δ`. -/
noncomputable def theta : H →ₗ[k] Ω[H⁄k] := antipodeSmulD k H ∘ₗ Δ

lemma theta_mul (x y : H) : theta k H (x * y) = ε x • theta k H y + ε y • theta k H x := by
  simp only [theta, LinearMap.comp_apply]
  rw [show Δ (x * y) = Δ x * Δ y from map_mul (Bialgebra.comulAlgHom k H) x y]
  rw [antipodeSmulD_mul, antipodeMul_comul, antipodeMul_comul, algebraMap_smul, algebraMap_smul]

lemma theta_one : theta k H 1 = 0 := by
  rw [theta, LinearMap.comp_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    antipodeSmulD_tmul, Derivation.map_one_eq_zero, smul_zero]

lemma theta_algebraMap (c : k) : theta k H (algebraMap k H c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, theta_one, smul_zero]

local notation "I" => TauCeti.Bialgebra.AugmentationIdeal k H

lemma theta_eq_zero_of_mem_sq {y : H} (hy : y ∈ I ^ 2) : theta k H y = 0 := by
  rw [pow_two] at hy
  refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · have ha' : ε a = 0 := ha
    have hb' : ε b = 0 := hb
    rw [theta_mul, ha', hb', zero_smul, zero_smul, add_zero]
  · rw [map_add, hx, hy, add_zero]

/-- `θ` descends to `ω = I / I²`. -/
noncomputable def cotToKaehler : ω →ₗ[k] Ω[H⁄k] := by
  let P : Submodule H I := I • ⊤
  refine ((P.restrictScalars k).liftQ (theta k H ∘ₗ ((Submodule.subtype I).restrictScalars k)) ?_) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k P).symm.toLinearMap
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  apply theta_eq_zero_of_mem_sq
  -- `x ∈ I • ⊤` iff `toCotangent x = 0` iff `x ∈ I ^ 2`.
  have : Ideal.toCotangent I x = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hx
  exact (Ideal.toCotangent_eq_zero I x).mp this

lemma cotToKaehler_toCotangent (x : I) :
    cotToKaehler k H (Ideal.toCotangent I x) = theta k H x := by
  rfl

lemma cotToKaehler_cot (y : H) : cotToKaehler k H (cot y) = theta k H y := by
  rw [TauCeti.Bialgebra.cotangentMap_apply, cotToKaehler_toCotangent]
  simp only
  rw [map_sub, theta_algebraMap, sub_zero]

/-- `Φ : H ⊗ ω → Ω[H⁄k]`. -/
noncomputable def invToKaehler : H ⊗[k] ω →ₗ[H] Ω[H⁄k] :=
  (cotToKaehler k H).liftBaseChange H

lemma invToKaehler_tmul (a : H) (c : ω) : invToKaehler k H (a ⊗ₜ c) = a • cotToKaehler k H c :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-! ### The two composites. -/

/-- `Φ ∘ (id ⊗ cot) = (a ⊗ b ↦ a • θ b)`; with coassociativity, `Φ (d x) = dx`. -/
lemma invToKaehler_invDer (x : H) : invToKaehler k H (invDer k H x) = dd x := by
  -- Write `Φ (∑ x₁ ⊗ cot x₂) = ∑ x₁ • θ x₂ = ∑ x₁ S(x₂) • d x₃`.
  have h1 : ∀ u : H ⊗[k] H, invToKaehler k H ((cot).lTensor H u) =
      smulD k H (((LinearMap.mul' k H ∘ₗ LinearMap.lTensor H S).rTensor H)
        ((TensorProduct.assoc k H H H).symm ((Δ).lTensor H u))) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, invToKaehler_tmul, cotToKaehler_cot, LinearMap.lTensor_tmul]
      simp only [theta, antipodeSmulD, LinearMap.comp_apply]
      induction Δ b using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add, tmul_add, smul_add, hz, hw]
      | tmul y z =>
        simp [smulD_tmul, smul_smul]
  rw [show invDer k H x = (cot).lTensor H (Δ x) from rfl, h1]
  -- Coassociativity: `assoc⁻¹ ∘ (id ⊗ Δ) ∘ Δ = (Δ ⊗ id) ∘ Δ`.
  rw [Coalgebra.coassoc_symm_apply]
  rw [← LinearMap.rTensor_comp_apply]
  -- `mul' ∘ (id ⊗ S) ∘ Δ = algebraMap ∘ ε` (`HopfAlgebra.mul_antipode_lTensor_comul`).
  rw [LinearMap.comp_assoc, HopfAlgebra.mul_antipode_lTensor_comul]
  rw [LinearMap.rTensor_comp_apply, Coalgebra.rTensor_counit_comul]
  simp [smulD_tmul]

lemma kaehlerToInv_antipodeSmulD (u : H ⊗[k] H) :
    kaehlerToInv k H (antipodeSmulD k H u) =
      TensorProduct.map (antipodeMul k H) (cot)
        ((TensorProduct.assoc k H H H).symm (LinearMap.lTensor H Δ u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul a b =>
    rw [antipodeSmulD_tmul, map_smul, kaehlerToInv_D, LinearMap.lTensor_tmul]
    induction Δ b using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, tmul_add, smul_add, hz, hw]
    | tmul y z => simp [TensorProduct.smul_tmul', antipodeMul_tmul]

lemma kaehlerToInv_theta (y : H) : kaehlerToInv k H (theta k H y) = 1 ⊗ₜ cot y := by
  have hM : antipodeMul k H ∘ₗ Δ = Algebra.linearMap k H ∘ₗ ε :=
    LinearMap.ext (antipodeMul_comul k H)
  rw [theta, LinearMap.comp_apply, kaehlerToInv_antipodeSmulD, Coalgebra.coassoc_symm_apply,
    ← LinearMap.comp_apply (TensorProduct.map _ _), LinearMap.map_comp_rTensor, hM,
    ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, LinearMap.rTensor_comp_apply,
    Coalgebra.rTensor_counit_comul]
  simp

/-- **`Ω[H⁄k] ≃ H ⊗[k] ω` (invariant differentials).** -/
noncomputable def kaehlerEquivInv : Ω[H⁄k] ≃ₗ[H] H ⊗[k] ω :=
  LinearEquiv.ofLinearMap (kaehlerToInv k H) (invToKaehler k H)
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro a c
      obtain ⟨y, rfl⟩ := TauCeti.Bialgebra.cotangentMap_surjective k H c
      rw [LinearMap.comp_apply, invToKaehler_tmul, map_smul, cotToKaehler_cot,
        kaehlerToInv_theta, LinearMap.id_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one])
    (by
      -- `Ω` is generated by `d H`.
      apply Derivation.liftKaehlerDifferential_unique
      ext x
      change invToKaehler k H (kaehlerToInv k H (dd x)) = dd x
      rw [kaehlerToInv_D]
      exact invToKaehler_invDer k H x)

instance [Module.Finite k ω] : Module.Free H Ω[H⁄k] :=
  Module.Free.of_equiv (kaehlerEquivInv k H).symm

instance [Module.Finite k ω] : Module.Finite H Ω[H⁄k] :=
  Module.Finite.equiv (kaehlerEquivInv k H).symm

theorem finrank_kaehler [Module.Finite k ω] [Nontrivial H] :
    Module.finrank H Ω[H⁄k] = Module.finrank k ω := by
  rw [(kaehlerEquivInv k H).finrank_eq, Module.finrank_baseChange]

end AlgMag.OpenCellNotes
