/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.FlagLocus
import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Power
import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
import TauCeti.Algebra.Coalgebra.Comodule.Trivial
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic

/-!
# The flag tensor space as a comodule (part C1 of `exists_flagLocus`)

For a comodule `W`, the flag tensor space `FT n = ((k ⊗ ⋀¹W) ⊗ ⋯) ⊗ ⋀ⁿW` is a comodule
(`ftComodule`), and a rational point `g` acts on it by `actT (⋀ ρ_W(g))` (`bpr_ft`).
A comodule whose matrix coefficients generate `H` is faithful on rational points
(`basePointsRepresentation_injective`).
-/

open TensorProduct Module TauCeti TauCeti.Comodule

namespace AlgMag.Reductive.FlagLocus

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

section Tensor

variable {V U : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
  [AddCommGroup U] [Module k U] [Comodule k H U]

theorem lid_distribBaseChange_symm (X : k ⊗[k] V) (Y : k ⊗[k] U) :
    TensorProduct.lid k (V ⊗[k] U)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange k k V U).symm (X ⊗ₜ[k] Y)) =
      TensorProduct.lid k V X ⊗ₜ[k] TensorProduct.lid k U Y := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul a v =>
    induction Y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul b w =>
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
      simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, mul_smul, smul_comm a b]

theorem bpr_tensor (g : WithConv (H →ₐ[k] k)) :
    letI := Comodule.tensor k H V U
    basePointsRepresentation (H := H) (V ⊗[k] U) g =
      TensorProduct.map (basePointsRepresentation (H := H) V g)
        (basePointsRepresentation (H := H) U g) := by
  letI := Comodule.tensor k H V U
  refine TensorProduct.ext' fun v w ↦ ?_
  rw [basePointsRepresentation_apply, TensorProduct.map_tmul, basePointsRepresentation_apply,
    basePointsRepresentation_apply, ← lid_distribBaseChange_symm,
    endOfPoint_tensor_tmul g.ofConv 1 1 v w, one_mul]

end Tensor

section Exterior

variable {W : Type u} [AddCommGroup W] [Module k W] [Comodule k H W]

theorem lid_baseChange_apply {A B : Type u} [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) (x : k ⊗[k] A) :
    TensorProduct.lid k B (f.baseChange k x) = f (TensorProduct.lid k A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem algLid_apply (x : k ⊗[k] ExteriorAlgebra k W) :
    Algebra.TensorProduct.lid k (ExteriorAlgebra k W) x =
      TensorProduct.lid k (ExteriorAlgebra k W) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bpr_exteriorPower (r : ℕ) (g : WithConv (H →ₐ[k] k)) :
    letI := Comodule.exteriorPower k H W r
    basePointsRepresentation (H := H) (⋀[k]^r W) g =
      exteriorPower.map r (basePointsRepresentation (H := H) W g) := by
  letI := Comodule.exteriorPower k H W r
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti]
  have h := baseChange_subtype_endOfPoint_ιMulti (R := k) (H := H) (M := W) r g.ofConv 1 v
  have h2 := congrArg (TensorProduct.lid k (ExteriorAlgebra k W)) h
  rw [lid_baseChange_apply, one_smul, ← algLid_apply, map_list_prod] at h2
  rw [basePointsRepresentation_apply]
  change (⋀[k]^r W).subtype _ = _
  rw [h2, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
  refine congrArg (fun l ↦ List.prod (List.ofFn l)) (funext fun i ↦ ?_)
  simp only [Function.comp_apply, algLid_apply, lid_baseChange_apply,
    basePointsRepresentation_apply]

end Exterior

section FT

theorem bpr_trivial {M : Type u} [AddCommGroup M] [Module k M] (g : WithConv (H →ₐ[k] k)) :
    letI := Comodule.trivial (R := k) (C := H) (M := M)
    basePointsRepresentation (H := H) M g = LinearMap.id := by
  letI := Comodule.trivial (R := k) (C := H) (M := M)
  refine LinearMap.ext fun x ↦ ?_
  rw [basePointsRepresentation_apply, endOfPoint_trivial]
  simp

variable {W : Type u} [AddCommGroup W] [Module k W] [Comodule k H W]

variable (k H W) in
/-- The comodule structure on the flag tensor space. -/
@[implicit_reducible]
noncomputable def ftComodule : (n : ℕ) → Comodule k H (FT k W n)
  | 0 => Comodule.trivial (R := k) (C := H) (M := k)
  | j + 1 =>
    letI := ftComodule j
    letI := Comodule.exteriorPower k H W (j + 1)
    Comodule.tensor k H (FT k W j) (⋀[k]^(j + 1) W)

/-- The rational points act on the flag tensor space by the recursive tensor action. -/
theorem bpr_ft (n : ℕ) (g : WithConv (H →ₐ[k] k)) (u : (W →ₗ[k] W)ˣ)
    (hu : (u : W →ₗ[k] W) = basePointsRepresentation (H := H) W g) :
    letI := ftComodule k H W n
    basePointsRepresentation (H := H) (FT k W n) g = actT (wedgeAct u) n := by
  induction n with
  | zero =>
    exact bpr_trivial (M := k) g
  | succ j ih =>
    letI := ftComodule k H W j
    letI := Comodule.exteriorPower k H W (j + 1)
    letI := Comodule.tensor k H (FT k W j) (⋀[k]^(j + 1) W)
    rw [actT_succ]
    have := bpr_tensor (H := H) (V := FT k W j) (U := ⋀[k]^(j + 1) W) g
    rw [bpr_exteriorPower, ← hu, ih] at this
    refine LinearMap.ext fun t ↦ ?_
    change basePointsRepresentation (H := H) (FT k W j ⊗[k] ⋀[k]^(j + 1) W) g t = _
    rw [this]
    rfl

instance ft_finite [FiniteDimensional k W] : ∀ n : ℕ, Module.Finite k (FT k W n)
  | 0 => inferInstanceAs (Module.Finite k k)
  | j + 1 => by
    haveI := ft_finite j
    exact inferInstanceAs (Module.Finite k (FT k W j ⊗[k] ⋀[k]^(j + 1) W))

end FT

section Faithful

variable {W : Type u} [AddCommGroup W] [Module k W] [Comodule k H W]

/-- A comodule whose matrix coefficients generate `H` is faithful on rational points. -/
theorem basePointsRepresentation_injective
    (htop : matrixCoefficientSubalgebra (R := k) (C := H) (M := W) = ⊤) :
    Function.Injective (basePointsRepresentation (R := k) (H := H) W) := by
  intro g g' h
  apply WithConv.ofConv_injective
  apply AlgHom.ext_of_adjoin_eq_top (s := matrixCoefficientSet (R := k) (C := H) (M := W)) htop
  rintro _ ⟨⟨φ, m⟩, rfl⟩
  change g.ofConv (matrixCoefficient φ m) = g'.ofConv (matrixCoefficient φ m)
  rw [apply_matrixCoefficient (M := W), apply_matrixCoefficient (M := W), h]

end Faithful

end AlgMag.Reductive.FlagLocus
