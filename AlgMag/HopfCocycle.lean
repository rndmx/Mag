/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Hochschild 1-cocycles of a comodule, algebraically

For a bialgebra `H` over `R` (in particular a Hopf algebra, `G = Spec H`) and a left comodule
`ρ : V → H ⊗ V`, the low degrees of the cobar complex are
`d⁰ v = ρ v - 1 ⊗ v` and `d¹ c = (id ⊗ ρ) c - (Δ ⊗ id) c + 1 ⊗ c` (in `H ⊗ (H ⊗ V)`).
We define `Z¹`, `B¹`, `H¹ = Z¹ / B¹`, prove `d¹ ∘ d⁰ = 0`, and the formal part of
Proposition 10.1: for a morphism of comodules `i : F → E` and `α ∈ E` with
`ρ α - 1 ⊗ α = (H ⊗ i) c₀`, the element `c₀` is a cocycle (if `H ⊗ H ⊗ i` is injective, e.g. `H`
flat and `i` injective), and if `H¹(F) = 0` then `α - i v` is invariant for some `v`.
No antipode is needed.
-/

open TensorProduct

namespace AlgMag.HopfCocycle

variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]

/-- A left `H`-comodule: an `R`-linear coassociative coaction `ρ : V → H ⊗ V`. -/
structure Comod (R H : Type*) [CommRing R] [Ring H] [Bialgebra R H] (V : Type*) [AddCommGroup V]
    [Module R V] where
  ρ : V →ₗ[R] H ⊗[R] V
  coassoc : (LinearMap.lTensor H ρ) ∘ₗ ρ =
    (TensorProduct.assoc R H H V).toLinearMap ∘ₗ (LinearMap.rTensor V (Coalgebra.comul (R := R))) ∘ₗ ρ

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- `v ↦ 1 ⊗ v`. -/
def one (R H M : Type*) [CommRing R] [Ring H] [Algebra R H] [AddCommGroup M] [Module R M] :
    M →ₗ[R] H ⊗[R] M := TensorProduct.mk R H M 1

lemma comul_one_tmul (v : V) :
    (TensorProduct.assoc R H H V) (LinearMap.rTensor V (Coalgebra.comul (R := R)) ((1 : H) ⊗ₜ v)) =
      (1 : H) ⊗ₜ ((1 : H) ⊗ₜ v) := by
  simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def]

namespace Comod

variable (C : Comod R H V)

/-- `d⁰ v = ρ v - 1 ⊗ v`. -/
def d0 : V →ₗ[R] H ⊗[R] V := C.ρ - one R H V

/-- `d¹ c = (id ⊗ ρ) c - (Δ ⊗ id) c + 1 ⊗ c`. -/
def d1 : H ⊗[R] V →ₗ[R] H ⊗[R] (H ⊗[R] V) :=
  LinearMap.lTensor H C.ρ -
    (TensorProduct.assoc R H H V).toLinearMap ∘ₗ LinearMap.rTensor V (Coalgebra.comul (R := R)) +
    one R H (H ⊗[R] V)

/-- `d¹ ∘ d⁰ = 0`. -/
theorem d1_d0 (v : V) : C.d1 (C.d0 v) = 0 := by
  have h := congrArg (fun f => f v) C.coassoc
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  simp only [d1, d0, one, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_sub, TensorProduct.mk_apply, LinearMap.lTensor_tmul, comul_one_tmul, h]
  abel

/-- 1-cocycles. -/
def Z1 : Submodule R (H ⊗[R] V) := LinearMap.ker C.d1

/-- 1-coboundaries. -/
def B1 : Submodule R (H ⊗[R] V) := LinearMap.range C.d0

lemma B1_le_Z1 : C.B1 ≤ C.Z1 := by
  rintro _ ⟨v, rfl⟩; exact C.d1_d0 v

/-- `B¹` inside `Z¹`. -/
def B1Z : Submodule R C.Z1 := Submodule.comap C.Z1.subtype C.B1

instance : AddCommGroup C.Z1 := C.Z1.addCommGroup

/-- `H¹ = Z¹ / B¹`. -/
abbrev H1 : Type _ := C.Z1 ⧸ C.B1Z

/-- Invariant elements: `ρ v = 1 ⊗ v`. -/
def Inv (v : V) : Prop := C.ρ v = (1 : H) ⊗ₜ v

lemma inv_iff_d0 (v : V) : C.Inv v ↔ C.d0 v = 0 := by
  simp [Inv, d0, one, sub_eq_zero]

/-- If `H¹ = 0`, every cocycle is a coboundary. -/
theorem mem_B1_of_subsingleton (h : Subsingleton C.H1) {c : H ⊗[R] V} (hc : c ∈ C.Z1) :
    ∃ v, C.d0 v = c := by
  have e := h.elim (Submodule.Quotient.mk ⟨c, hc⟩) 0
  rw [Submodule.Quotient.mk_eq_zero] at e
  exact e

end Comod

/-! ## Morphisms of comodules: the formal part of Proposition 10.1 -/

variable {F E : Type*} [AddCommGroup F] [Module R F] [AddCommGroup E] [Module R E]

/-- A morphism of comodules `i : F → E` (the lifts sit in `E`, their differences in `F`). -/
structure ComodHom (CF : Comod R H F) (CE : Comod R H E) where
  i : F →ₗ[R] E
  comm : CE.ρ ∘ₗ i = LinearMap.lTensor H i ∘ₗ CF.ρ

omit [Bialgebra R H] in
lemma assoc_nat [Algebra R H] (j : F →ₗ[R] E) (x : (H ⊗[R] H) ⊗[R] F) :
    TensorProduct.assoc R H H E (LinearMap.lTensor (H ⊗[R] H) j x) =
      LinearMap.lTensor H (LinearMap.lTensor H j) (TensorProduct.assoc R H H F x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul p q => simp

namespace ComodHom

variable {CF : Comod R H F} {CE : Comod R H E} (φ : ComodHom CF CE)

lemma d0_comm (v : F) : CE.d0 (φ.i v) = LinearMap.lTensor H φ.i (CF.d0 v) := by
  have := congrArg (fun f => f v) φ.comm
  simp only [LinearMap.comp_apply] at this
  simp [Comod.d0, one, this]

lemma d1_comm (c : H ⊗[R] F) :
    CE.d1 (LinearMap.lTensor H φ.i c) =
      LinearMap.lTensor H (LinearMap.lTensor H φ.i) (CF.d1 c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul h v =>
    have hc := congrArg (fun f => f v) φ.comm
    simp only [LinearMap.comp_apply] at hc
    simp only [Comod.d1, one, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, map_sub, map_add, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
      TensorProduct.mk_apply, hc]
    rw [show Coalgebra.comul (R := R) h ⊗ₜ[R] φ.i v =
      LinearMap.lTensor (H ⊗[R] H) φ.i (Coalgebra.comul (R := R) h ⊗ₜ[R] v) from rfl, assoc_nat]

/-- `c₀` is the universal cocycle of `α ∈ E`, valued in `F`: `(H ⊗ i) c₀ = ρ α - 1 ⊗ α`. -/
def IsC0 (α : E) (c₀ : H ⊗[R] F) : Prop := LinearMap.lTensor H φ.i c₀ = CE.d0 α

/-- **(a)** `c₀` is a 1-cocycle, provided `H ⊗ H ⊗ i` is injective (e.g. `H` flat, `i` injective). -/
theorem c0_mem_Z1 (hinj : Function.Injective (LinearMap.lTensor H (LinearMap.lTensor H φ.i)))
    {α : E} {c₀ : H ⊗[R] F} (h : φ.IsC0 α c₀) : c₀ ∈ CF.Z1 := by
  apply hinj
  show _ = LinearMap.lTensor H (LinearMap.lTensor H φ.i) 0
  rw [map_zero, ← φ.d1_comm, h, CE.d1_d0]

/-- If `c₀ = d⁰ v`, then `α - i v` is invariant. -/
theorem invariant_of_coboundary {α : E} {c₀ : H ⊗[R] F} (h : φ.IsC0 α c₀) {v : F}
    (hv : CF.d0 v = c₀) : CE.Inv (α - φ.i v) := by
  rw [Comod.inv_iff_d0, map_sub, φ.d0_comm, hv, ← h, sub_self]

/-- **(b)** If `H¹(F) = 0` (and `H ⊗ H ⊗ i` is injective), some `α - i v` is invariant. -/
theorem exists_invariant (hinj : Function.Injective (LinearMap.lTensor H (LinearMap.lTensor H φ.i)))
    (h1 : Subsingleton CF.H1) {α : E} {c₀ : H ⊗[R] F} (h : φ.IsC0 α c₀) :
    ∃ v : F, CE.Inv (α - φ.i v) := by
  obtain ⟨v, hv⟩ := CF.mem_B1_of_subsingleton h1 (φ.c0_mem_Z1 hinj h)
  exact ⟨v, φ.invariant_of_coboundary h hv⟩

end ComodHom

end AlgMag.HopfCocycle
