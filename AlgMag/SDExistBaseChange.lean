/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3SchemeQuotient

/-!
# Lemma D, Steps 3-4: base change of a grading along `A₀ → A₀'`

In the proof of Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`: the grading of
`A` induces one on `A₀' ⊗ A`, with invariants `A₀'` ("`(A ⊗_{A₀} A₀')₀ = A₀'`", setup of Part B).
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

variable {R A Γ : Type u} [CommRing R] [CommRing A] [AddCommGroup Γ] [Algebra R A] (R' : Type u) [CommRing R']
  [Algebra R R'] (c : Coact A Γ)

/-- The `R`-algebra structure on `R' ⊗ A [Γ]` through degree zero. -/
noncomputable abbrev SDExist_toZero : (R' ⊗[R] A) →+* AddMonoidAlgebra (R' ⊗[R] A) Γ := cC (R' ⊗[R] A) Γ

variable (hc : ∀ r : R, c.σ (algebraMap R A r) = AddMonoidAlgebra.single 0 (algebraMap R A r))

include hc in
/-- The coaction on `R' ⊗ A`, as a ring map. -/
noncomputable def SDExist_bcσ : (R' ⊗[R] A) →+* AddMonoidAlgebra (R' ⊗[R] A) Γ :=
  letI : Algebra R (AddMonoidAlgebra (R' ⊗[R] A) Γ) := AddMonoidAlgebra.algebra
  (Algebra.TensorProduct.lift (A := R') (B := A) (S := R) (C := AddMonoidAlgebra (R' ⊗[R] A) Γ)
    { (cC (R' ⊗[R] A) Γ).comp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] A) with
      commutes' := fun r => rfl }
    { (AddMonoidAlgebra.mapRingHom Γ
        (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom).comp c.σ with
      commutes' := fun r => by
        change AddMonoidAlgebra.mapRingHom Γ _ (c.σ (algebraMap R A r)) = _
        rw [hc, AddMonoidAlgebra.mapRingHom_single]
        change AddMonoidAlgebra.single 0 ((Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A) _) = _
        rw [AlgHom.commutes]
        rfl }
    (fun _ _ => Commute.all _ _)).toRingHom

lemma SDExist_bcσ_tmul (r : R') (a : A) :
    SDExist_bcσ R' c hc (r ⊗ₜ a) = AddMonoidAlgebra.single 0 (r ⊗ₜ[R] (1 : A)) *
      AddMonoidAlgebra.mapRingHom Γ (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom (c.σ a) := by
  letI : Algebra R (AddMonoidAlgebra (R' ⊗[R] A) Γ) := AddMonoidAlgebra.algebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ r a

lemma SDExist_bc_coeff (r : R') (a : A) (d : Γ) :
    (SDExist_bcσ R' c hc (r ⊗ₜ a)).coeff d = r ⊗ₜ[R] (c.comp d a) := by
  rw [SDExist_bcσ_tmul]
  have := AddMonoidAlgebra.coeff_single_mul_apply
    (AddMonoidAlgebra.mapRingHom Γ (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom (c.σ a))
    (r ⊗ₜ[R] (1 : A)) (0 : Γ) d
  rw [neg_zero, zero_add] at this
  rw [this, AddMonoidAlgebra.coeff_mapRingHom]
  change (r ⊗ₜ[R] (1 : A)) * ((1 : R') ⊗ₜ[R] (c.comp d a)) = _
  simp

lemma SDExist_bc_sum (y : R' ⊗[R] A) :
    ((SDExist_bcσ R' c hc y).coeff.sum fun _ a => a) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hy, hz]
  | tmul r a =>
    classical
    have key : ∀ s : Finset Γ, (c.σ a).coeff.support ⊆ s →
        ((SDExist_bcσ R' c hc (r ⊗ₜ a)).coeff.sum fun _ a => a) = r ⊗ₜ[R] (∑ d ∈ s, c.comp d a) := by
      intro s hs
      rw [Finsupp.sum_of_support_subset (s := s) _ (fun d hd => hs ?_) _ (fun _ _ => rfl), TensorProduct.tmul_sum]
      · exact Finset.sum_congr rfl fun d _ => SDExist_bc_coeff R' c hc r a d
      · rw [Finsupp.mem_support_iff] at hd ⊢
        intro h0
        apply hd
        rw [SDExist_bc_coeff]
        change r ⊗ₜ[R] (c.σ a).coeff d = 0
        rw [h0, TensorProduct.tmul_zero]
    rw [key _ subset_rfl]
    congr 1
    exact c.sum_eq a

/-- The grading of `R' ⊗ A`. -/
noncomputable def SDExist_bc : Coact (R' ⊗[R] A) Γ where
  σ := SDExist_bcσ R' c hc
  sum_eq := SDExist_bc_sum R' c hc
  hom := fun y d => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz =>
      rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, hy, hz, AddMonoidAlgebra.single_add]
    | tmul r a =>
      rw [SDExist_bc_coeff, SDExist_bcσ_tmul]
      have h := c.hom a d
      change c.σ (c.comp d a) = AddMonoidAlgebra.single d (c.comp d a) at h
      rw [h, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.single_mul_single, zero_add]
      congr 1
      change _ * ((1 : R') ⊗ₜ[R] (c.comp d a)) = _
      simp

@[simp] lemma SDExist_bc_comp (r : R') (a : A) (d : Γ) :
    (SDExist_bc R' c hc).comp d (r ⊗ₜ a) = r ⊗ₜ[R] c.comp d a := SDExist_bc_coeff R' c hc r a d

/-- `(R' ⊗ A)₀ = R'`: the invariants of the base change. -/
theorem SDExist_bc_isInv (hι : c.IsInv (algebraMap R A)) :
    (SDExist_bc R' c hc).IsInv (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] A) := by
  -- the retraction
  let rl : A →ₗ[R] R :=
    { toFun := hι.r
      map_add' := hι.r_add
      map_smul' := fun r a => by
        rw [Algebra.smul_def]
        exact hι.r_mul r a }
  let ρ : R' ⊗[R] A →ₗ[R] R' := TensorProduct.lift
    { toFun := fun x => { toFun := fun a => rl a • x, map_add' := fun a b => by simp [add_smul],
                          map_smul' := fun r a => by simp [mul_smul] }
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext a; exact smul_comm _ _ _ }
  have hρ : ∀ x : R', ρ (x ⊗ₜ (1 : A)) = x := fun x => by
    change rl 1 • x = x
    have : rl 1 = 1 := hι.r_one
    rw [this, one_smul]
  have hι' : ∀ y : R' ⊗[R] A, (SDExist_bc R' c hc).comp 0 y = (ρ y) ⊗ₜ[R] (1 : A) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp [Coact.comp]
    | add y z hy hz => rw [Coact.comp_add, hy, hz, map_add, TensorProduct.add_tmul]
    | tmul r a =>
      rw [SDExist_bc_comp, ← hι.ι_r a]
      change r ⊗ₜ[R] (algebraMap R A (hι.r a)) = (hι.r a • r) ⊗ₜ[R] (1 : A)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  refine ⟨fun x y h => ?_, fun y => ⟨fun h => ?_, ?_⟩⟩
  · have := congrArg ρ h
    change ρ (x ⊗ₜ 1) = ρ (y ⊗ₜ 1) at this
    rwa [hρ, hρ] at this
  · refine ⟨ρ y, ?_⟩
    have h1 := (SDExist_bc R' c hc).comp_self_of_isHom h
    rw [hι'] at h1
    exact h1
  · rintro ⟨x, rfl⟩
    change SDExist_bcσ R' c hc (x ⊗ₜ 1) = _
    rw [SDExist_bcσ_tmul]
    have h1 : c.σ (1 : A) = AddMonoidAlgebra.single 0 1 := map_one c.σ
    rw [h1, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.single_mul_single, zero_add]
    congr 1
    change _ * ((1 : R') ⊗ₜ[R] (1 : A)) = _
    simp

end AlgMag.SD

#print axioms AlgMag.SD.SDExist_bc_isInv
