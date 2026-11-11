/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import TauCeti.Algebra.Coalgebra.Comodule.Corestrict

/-!
# A unipotent point is `1` on group-like elements of a quotient

Let `q : C → D` be a surjective morphism of commutative Hopf algebras over a field `K` (a closed
subgroup `W = Spec D ⊆ U = Spec C`), `b ∈ D` group-like, and `g : D → L` a point of `W` such that
`g ∘ q` is a unipotent point of `U`. Then `g b = 1`.

The group-like `b` need not lift to a group-like of `C` (`W ⊆ T` while `U ⊄ T`), so one cannot use
the line `K b` as a `C`-comodule. Instead: a lift `c` lies in a finite subcomodule `N` of the regular
comodule `C`; the composite `N → C → D` intertwines the action of `g ∘ q` on `N` with the action
of `g` on the regular comodule `D`, where `b` is an eigenvector with eigenvalue `g b`.
-/

suppress_compilation

open TensorProduct TauCeti TauCeti.Comodule

namespace AlgMag.Reductive

universe u

variable {K : Type u} [Field K] {C D : Type u} [CommRing C] [HopfAlgebra K C]
  [CommRing D] [HopfAlgebra K D] {L : Type u} [Field L] [Algebra K L]

/-- The bialgebra morphism `q` as a morphism of right `D`-comodules from `C` corestricted to `D`. -/
noncomputable def corestrictHom (q : C →ₐc[K] D) :
    letI : Comodule K D C := Corestrict q.toCoalgHom
    Comodule.Hom K D C D :=
  letI : Comodule K D C := Corestrict q.toCoalgHom
  { toLinearMap := (q : C →ₐ[K] D).toLinearMap
    map_coact := by
      ext c
      simp only [LinearMap.coe_comp, Function.comp_apply, corestrict_coact_apply,
        instSelf_coact]
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
      exact CoalgHomClass.map_comp_comul_apply q c }

/-- **Unipotent points are trivial on group-like elements of a quotient.** -/
theorem eq_one_of_groupLike (q : C →ₐc[K] D) (hq : Function.Surjective q) {b : D}
    (hb : Coalgebra.comul (R := K) b = b ⊗ₜ b) (hb1 : Coalgebra.counit (R := K) b = 1)
    (g : D →ₐ[K] L)
    (hu : HopfAlgebra.IsUnipotentPoint (WithConv.toConv (g.comp (q : C →ₐ[K] D)))) :
    g b = 1 := by
  obtain ⟨c, rfl⟩ := hq b
  obtain ⟨N, hNf, hcN⟩ := Subcomodule.exists_finite_subcomodule_mem (R := K) (C := C) c
  have : Module.Finite K N := hNf
  have hnil := (HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one _).1 hu
    (FGComoduleCat.of (R := K) (C := C) N)
  obtain ⟨n, hn⟩ := hnil
  -- the intertwining maps
  let h : C →ₐ[K] L := g.comp (q : C →ₐ[K] D)
  let EN : L ⊗[K] N →ₗ[L] L ⊗[K] N := endOfPoint N h
  let EC : L ⊗[K] C →ₗ[L] L ⊗[K] C := endOfPoint C h
  let ED : L ⊗[K] D →ₗ[L] L ⊗[K] D := endOfPoint D g
  let ι : L ⊗[K] N →ₗ[L] L ⊗[K] C := (SMulMemClass.subtype N).baseChange L
  let Q : L ⊗[K] C →ₗ[L] L ⊗[K] D := (q : C →ₐ[K] D).toLinearMap.baseChange L
  have h1 : ι ∘ₗ EN = EC ∘ₗ ι := baseChange_comp_endOfPoint (Subcomodule.subtype N) h
  have h2 : Q ∘ₗ EC = ED ∘ₗ Q := by
    let : Comodule K D C := Corestrict q.toCoalgHom
    have := baseChange_comp_endOfPoint (corestrictHom q) g
    have hc := endOfPoint_corestrict (V := C) q g
    rw [hc] at this
    exact this
  let Φ := Q ∘ₗ ι
  have hcomm : Φ ∘ₗ EN = ED ∘ₗ Φ := by
    change Q ∘ₗ ι ∘ₗ EN = ED ∘ₗ Q ∘ₗ ι
    rw [h1, ← LinearMap.comp_assoc, h2, LinearMap.comp_assoc]
  have hΦ : Φ ∘ₗ (EN - 1) = (ED - 1) ∘ₗ Φ := by
    rw [LinearMap.comp_sub, LinearMap.sub_comp, hcomm, Module.End.one_eq_id,
      Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  have hpow : ∀ m : ℕ, Φ ∘ₗ ((EN - 1) ^ m) = ((ED - 1) ^ m) ∘ₗ Φ := by
    intro m
    induction m with
    | zero => simp [Module.End.one_eq_id]
    | succ m ih =>
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, hΦ, ← LinearMap.comp_assoc]
  have hEN : (EN - 1) ^ n = 0 := hn
  have hz := congrArg (fun F => F ((1 : L) ⊗ₜ[K] (⟨c, hcN⟩ : N))) (hpow n)
  simp only [hEN, LinearMap.comp_zero, LinearMap.zero_apply] at hz
  -- `(ED - 1) (1 ⊗ b) = (g b - 1) • (1 ⊗ b)`
  have hΦc : Φ ((1 : L) ⊗ₜ[K] (⟨c, hcN⟩ : N)) = (1 : L) ⊗ₜ[K] q c := rfl
  have hED : ∀ m : ℕ, ((ED - 1) ^ m) ((1 : L) ⊗ₜ[K] q c) = (g (q c) - 1) ^ m • ((1 : L) ⊗ₜ[K] q c) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Module.End.mul_apply]
      have hstep : (ED - 1) ((1 : L) ⊗ₜ[K] q c) = (g (q c) - 1) • ((1 : L) ⊗ₜ[K] q c) := by
        rw [LinearMap.sub_apply, Module.End.one_apply]
        simp only [ED, endOfPoint_tmul, instSelf_coact, hb, LinearMap.lTensor_tmul,
          AlgHom.toLinearMap_apply, TensorProduct.comm_tmul, one_smul]
        rw [sub_smul, one_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hstep, map_smul, ih, smul_smul, ← pow_succ']
  rw [LinearMap.comp_apply, hΦc, hED] at hz
  -- apply `id ⊗ ε`
  have hε := congrArg ((TensorProduct.AlgebraTensorModule.rid K L L).toLinearMap ∘ₗ
      (Coalgebra.counit (R := K) (A := D)).baseChange L) hz
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_smul, map_zero,
    LinearMap.baseChange_tmul, hb1, TensorProduct.AlgebraTensorModule.rid_tmul, one_smul,
    smul_eq_mul, mul_one] at hε
  exact sub_eq_zero.1 (pow_eq_zero_iff'.1 hε.symm).1

end AlgMag.Reductive
