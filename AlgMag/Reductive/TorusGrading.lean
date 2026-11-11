/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.CocharacterGrading
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Corestrict

/-!
# The torus action on `O(G)` as an `M`-grading

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Proposition 2.22 and §16.5.

Let `G = Spec H` be an affine group over `R` and `π : H →ₐc[R] R[X]` a group morphism
`D(X) → G` from a diagonalizable group (Tau Ceti's presentation of a split torus `T`; for a
`SplitMaximalTorus` take `π = T.coordinateMap.hom`). The action of `D(X)` on `G` by conjugation
makes `H` a comodule over `R[X]` (`torusComodule π`), hence (Proposition 2.22) an `M`-graded
algebra, `M = Additive X`, the degree `m` part being the weight space of weight `m`:

* `AlgMag.Reductive.torusGrading π : Additive X → Submodule R H` and its `GradedAlgebra` instance;
* `AlgMag.Reductive.magnetIdeal_torusGrading_bot` : the attractor of the magnet `0`
  (fixed points, Proposition 3.35) is Tau Ceti's centralizer `Z_G(D(X))`.

So for every magnet `N ⊆ M`, Theorem 3.20 (`Magnetism.attractorEquiv`) gives the attractor
`G^N = Spec (H / magnetIdeal (torusGrading π) N)`.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u v w

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X)

/-- The left coaction `H → R[X] ⊗ H` of the conjugation action of `D(X)` on `G`. -/
def torusCoactLeft : H →ₐ[R] MonoidAlgebra R X ⊗[R] H :=
  (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R H)).comp
    (HopfAlgebra.conjugationAlgHom (R := R) (H := H))

/-- The right coaction `H → H ⊗ R[X]` of the conjugation action of `D(X)` on `G`. -/
def torusCoact : H →ₗ[R] H ⊗[R] MonoidAlgebra R X :=
  (TensorProduct.comm R (MonoidAlgebra R X) H).toLinearMap ∘ₗ (torusCoactLeft π).toLinearMap

omit [CommGroup X] in
lemma comul_comm_monoidAlgebra {X : Type w} [CommMonoid X] (c : MonoidAlgebra R X) :
    TensorProduct.comm R _ _ (Coalgebra.comul (R := R) c) = Coalgebra.comul (R := R) c := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single x r =>
    rw [MonoidAlgebra.comul_single]
    have hr := LinearMap.congr_fun (Coalgebra.comm_comp_comul (R := R) (A := R)) r
    conv_rhs => rw [← hr]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    generalize CoalgebraStruct.comul (R := R) r = s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp

/-- Coassociativity of the left coaction (Tau Ceti `conjugationAlgHom_coassoc` pushed along `π`). -/
lemma torusCoactLeft_coassoc (h : H) :
    TensorProduct.assoc R _ _ _
        (TensorProduct.map (Coalgebra.comul (R := R)) LinearMap.id (torusCoactLeft π h)) =
      TensorProduct.map LinearMap.id (torusCoactLeft π).toLinearMap (torusCoactLeft π h) := by
  have hc := congrArg (fun f => f h) (HopfAlgebra.conjugationAlgHom_coassoc (R := R) (H := H))
  simp only [AlgHom.comp_apply] at hc
  set t := HopfAlgebra.conjugationAlgHom (R := R) (H := H) h with ht
  -- push the identity `hc` along `π ⊗ π ⊗ id`
  have key := congrArg (TensorProduct.map π.toLinearMap
    (TensorProduct.map π.toLinearMap (LinearMap.id : H →ₗ[R] H))) hc
  rw [torusCoactLeft, AlgHom.comp_apply, ← ht]
  convert key using 1
  · clear key hc ht
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_tmul, LinearMap.id_coe]
      rw [show CoalgebraStruct.comul ((π : H →ₐ[R] MonoidAlgebra R X) a) =
        TensorProduct.map π.toLinearMap π.toLinearMap (CoalgebraStruct.comul (R := R) a) from
        (CoalgHomClass.map_comp_comul_apply π a).symm]
      have hs : ∀ s : H ⊗[R] H,
          TensorProduct.assoc R _ _ _ (TensorProduct.map π.toLinearMap π.toLinearMap s ⊗ₜ[R] b) =
            TensorProduct.map π.toLinearMap (TensorProduct.map π.toLinearMap LinearMap.id)
              (Algebra.TensorProduct.assoc R R R H H H (s ⊗ₜ[R] b)) := by
        intro s
        induction s using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
        | tmul x y => simp
      exact hs _
  · clear key hc ht
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_tmul, LinearMap.id_coe,
        AlgHom.toLinearMap_apply, AlgHom.coe_comp, Function.comp_apply]
      rfl

/-- The counit law for the left coaction (Tau Ceti `conjugationAlgHom_counit_left`). -/
lemma torusCoactLeft_counit (h : H) :
    TensorProduct.map (Coalgebra.counit (R := R)) LinearMap.id (torusCoactLeft π h) =
      (1 : R) ⊗ₜ[R] h := by
  have hc := congrArg (fun f => f h) (HopfAlgebra.conjugationAlgHom_counit_left (R := R) (H := H))
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at hc
  rw [torusCoactLeft, AlgHom.comp_apply]
  conv_rhs => rw [← hc]
  generalize HopfAlgebra.conjugationAlgHom (R := R) (H := H) h = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, tmul_add]
  | tmul a b =>
    have hπ : CoalgebraStruct.counit ((π : H →ₐ[R] MonoidAlgebra R X) a) =
        CoalgebraStruct.counit (R := R) a := CoalgHomClass.counit_comp_apply π a
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_tmul, LinearMap.id_coe,
      AlgHom.toLinearMap_apply, Bialgebra.counitAlgHom_apply, hπ]
    erw [Algebra.TensorProduct.lid_tmul]
    rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one]

/-- **The conjugation action of `D(X)` makes `O(G)` an `R[X]`-comodule.** -/
@[instance_reducible] def torusComodule : Comodule R (MonoidAlgebra R X) H where
  coact := torusCoact π
  coassoc := by
    ext h
    simp only [LinearMap.coe_comp, Function.comp_apply, torusCoact, LinearEquiv.coe_coe]
    have key := torusCoactLeft_coassoc π h
    -- reverse the three factors
    let τ : MonoidAlgebra R X ⊗[R] (MonoidAlgebra R X ⊗[R] H) →ₗ[R]
        H ⊗[R] (MonoidAlgebra R X ⊗[R] MonoidAlgebra R X) :=
      LinearMap.lTensor H (TensorProduct.comm R (MonoidAlgebra R X) (MonoidAlgebra R X)).toLinearMap
        ∘ₗ (TensorProduct.assoc R H (MonoidAlgebra R X) (MonoidAlgebra R X)).toLinearMap
        ∘ₗ LinearMap.rTensor (MonoidAlgebra R X)
            (TensorProduct.comm R (MonoidAlgebra R X) H).toLinearMap
        ∘ₗ (TensorProduct.assoc R (MonoidAlgebra R X) H (MonoidAlgebra R X)).symm.toLinearMap
        ∘ₗ LinearMap.lTensor (MonoidAlgebra R X)
            (TensorProduct.comm R (MonoidAlgebra R X) H).toLinearMap
    have h1 : ∀ t : MonoidAlgebra R X ⊗[R] H,
        TensorProduct.assoc R _ _ _ (LinearMap.rTensor _ (torusCoact π)
          (TensorProduct.comm R _ _ t)) =
          τ (TensorProduct.map LinearMap.id (torusCoactLeft π).toLinearMap t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul c x =>
        simp only [TensorProduct.comm_tmul, LinearMap.rTensor_tmul, map_tmul, LinearMap.id_coe,
          id_eq, AlgHom.toLinearMap_apply, torusCoact, LinearMap.coe_comp, Function.comp_apply,
          LinearEquiv.coe_coe]
        generalize torusCoactLeft π x = y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add, add_tmul, tmul_add, ha, hb]
        | tmul d z => simp [τ]
    have h2 : ∀ t : MonoidAlgebra R X ⊗[R] H,
        LinearMap.lTensor H (Coalgebra.comul (R := R)) (TensorProduct.comm R _ _ t) =
          τ (TensorProduct.assoc R _ _ _
            (TensorProduct.map (Coalgebra.comul (R := R)) LinearMap.id t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul c x =>
        simp only [TensorProduct.comm_tmul, LinearMap.lTensor_tmul, map_tmul, LinearMap.id_coe,
          id_eq]
        conv_lhs => rw [← comul_comm_monoidAlgebra c]
        generalize Coalgebra.comul (R := R) c = y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add, add_tmul, tmul_add, ha, hb]
        | tmul d e => simp [τ]
    exact (h1 (torusCoactLeft π h)).trans ((congrArg τ key).symm.trans (h2 _).symm)
  lTensor_counit_comp_coact := by
    ext h
    simp only [LinearMap.coe_comp, Function.comp_apply, torusCoact, LinearEquiv.coe_coe,
      LinearMap.flip_apply, TensorProduct.mk_apply]
    have key := torusCoactLeft_counit π h
    have : ∀ t : MonoidAlgebra R X ⊗[R] H,
        LinearMap.lTensor H (Coalgebra.counit (R := R)) (TensorProduct.comm R _ _ t) =
          TensorProduct.comm R _ _ (TensorProduct.map (Coalgebra.counit (R := R))
            LinearMap.id t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul c x => simp
    exact (this (torusCoactLeft π h)).trans ((congrArg (TensorProduct.comm R R H) key).trans rfl)

/-- **The `M`-grading of `O(G)` given by the conjugation action of `D(X)` (Proposition 2.22 of
Algebraic Magnetism).** The degree `m` part is the weight space of the character `m`. -/
def torusGrading (m : Additive X) : Submodule R H :=
  letI := torusComodule π
  TauCeti.Comodule.weightSpace R X H (Additive.toMul m)

variable {π}

lemma mem_torusGrading {m : Additive X} {h : H} :
    h ∈ torusGrading π m ↔
      torusCoact π h = h ⊗ₜ[R] MonoidAlgebra.single (Additive.toMul m) 1 := by
  letI := torusComodule π
  exact TauCeti.Comodule.mem_weightSpace

variable (π)

/-- The weight spaces of the conjugation action form an internal direct sum
(Tau Ceti `Comodule.isInternal_weightSpace`, reindexed along `Additive X ≃ X`). -/
lemma torus_weightSpace_indep_top :
    letI := torusComodule π
    iSupIndep (TauCeti.Comodule.weightSpace R X H) ∧
      iSup (TauCeti.Comodule.weightSpace R X H) = ⊤ := by
  letI := torusComodule π
  classical
  have h0 := TauCeti.Comodule.isInternal_weightSpace R X H
  rwa [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h0

theorem isInternal_torusGrading [DecidableEq X] :
    DirectSum.IsInternal (torusGrading π) := by
  letI := torusComodule π
  have h := torus_weightSpace_indep_top π
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨h.1.comp Additive.toMul.injective, ?_⟩
  rw [← h.2]
  exact Additive.toMul.iSup_comp (g := fun x => TauCeti.Comodule.weightSpace R X H x)

lemma torusCoact_mul (a b : H) : torusCoact π (a * b) = torusCoact π a * torusCoact π b := by
  simp only [torusCoact, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    AlgHom.toLinearMap_apply, map_mul]
  exact (Algebra.TensorProduct.comm R _ _).map_mul _ _

/-- **Proposition 2.22 for `D(X)` acting on `G` by conjugation**: `O(G)` is an
`Additive X`-graded algebra. -/
instance torusGradedAlgebra [DecidableEq X] : GradedAlgebra (torusGrading π) where
  one_mem := by
    change (1 : H) ∈ torusGrading π 0
    rw [mem_torusGrading]
    simp only [torusCoact, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      AlgHom.toLinearMap_apply, map_one]
    rfl
  mul_mem i j a b ha hb := by
    change a * b ∈ torusGrading π (i + j)
    rw [mem_torusGrading] at *
    rw [torusCoact_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul,
      MonoidAlgebra.single_mul_single, mul_one, toMul_add]
  toDecomposition := (isInternal_torusGrading π).chooseDecomposition

end AlgMag.Reductive
