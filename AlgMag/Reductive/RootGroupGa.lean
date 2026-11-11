/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootGroups
import AlgMag.Reductive.AttractorSmooth
import AlgMag.Faces.Affine
import AlgMag.Faces.AffineSpaceFibration

/-!
# `U_α ≅ 𝔾_a` by magnets: the base change step

`G = Spec H` smooth over the field `k`, `N = [α⟩`, `F = 0`. By the Białynicki-Birula theorem for
faces (`Faces.face_sym_ring`), `B_N = H/J_N ≅ Sym_{B_0}(C)`, `B_0 = H/J_0`. The fibre of
`G^N → G^0` over `e` is `U_α`: `H/J_U ≅ B_N ⊗_{B_0} Q`, `Q = B_0/(x - ε x)_{x ∈ H_0} ≅ k`
(`prescribedUnit_equiv_tensor`). Hence `O(U_α) ≅ Sym_Q(Q ⊗ C)` is a polynomial ring over a field,
in particular reduced (`isReduced_quotient_rootGroupIdeal`).
-/

suppress_compilation

open Magnetism TauCeti WithConv AlgMag.Faces
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

section Classical
open scoped Classical
variable {k : Type u} {H : Type u} {X : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommGroup X] (π : H →ₐc[k] MonoidAlgebra k X)

/-- The grading of `O(G)`, with the classical decidable equality used in `AlgMag.Faces`. -/
noncomputable instance torusGradedAlgebraC :
    @GradedAlgebra (Additive X) k H (fun a b => Classical.propDecidable (a = b)) _ _ _ _
      (torusGrading π) := by
  convert torusGradedAlgebra π <;> rfl

end Classical

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}

/-- The generators `x - ε(x)`, `x ∈ H_0`. -/
def unitGens (π : H →ₐc[k] MonoidAlgebra k X) : Set H :=
  {y | ∃ x ∈ torusGrading π 0, x - algebraMap k H (Coalgebra.counit (R := k) x) = y}

lemma prescribedUnitIdeal_eq (N : Magnet (Additive X)) :
    prescribedUnitIdeal π N = magnetIdeal (torusGrading π) N ⊔ Ideal.span (unitGens π) := rfl

/-- `h - ε(h) ∈ J_0 + (x - ε x)`. -/
lemma sub_counit_mem (h : H) :
    h - algebraMap k H (Coalgebra.counit (R := k) h) ∈
      magnetIdeal (torusGrading π) ⊥ ⊔ Ideal.span (unitGens π) := by
  induction h using induction_torusGrading (π := π) with
  | h0 => simp
  | hadd x y hx hy =>
    have := Ideal.add_mem _ hx hy
    rwa [map_add, map_add, add_sub_add_comm]
  | hmem χ x hx =>
    by_cases hχ : χ = 0
    · subst hχ
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨x, hx, rfl⟩)
    · rw [counit_eq_zero_of_mem hχ hx, map_zero, sub_zero]
      exact Ideal.mem_sup_left (mem_magnetIdeal_of_notMem (by rwa [AddSubmonoid.mem_bot]) hx)

variable {α : Additive X} (hα : ∀ n : ℕ, n • α = 0 → n = 0)

include hα in
lemma isFace_bot_rayMagnet : IsFace (⊥ : AddSubmonoid (Additive X)) (rayMagnet α) where
  le := bot_le
  mem_of_add_mem {x y} hx hy hxy := by
    rw [AddSubmonoid.mem_bot] at hxy ⊢
    have h1 := rayMagnet_pointed hα x hx y hy hxy
    refine ⟨h1, ?_⟩
    rw [h1, zero_add] at hxy
    rw [AddSubmonoid.mem_bot]; exact hxy

lemma mem_Fgp_bot_iff {m : Additive X} {N : AddSubmonoid (Additive X)} :
    m ∈ Fgp ((⊥ : AddSubmonoid (Additive X)) ⊓ N) ↔ m = 0 := by
  rw [bot_inf_eq, Fgp, AddSubmonoid.coe_bot, AddSubgroup.closure_singleton_zero,
    AddSubgroup.mem_bot]

variable (π) in
include hα in
/-- The face data for `F = 0 ⊆ N = [α⟩`. -/
lemma faceData_ray :
    FaceData (torusGrading π) (rayMagnet α) ⊥ (Fgp (⊥ ⊓ rayMagnet α)) :=
  faceData_of_Nc (torusGrading π) (rayMagnet α) ⊥ (isFace_bot_rayMagnet hα) le_rfl
    (fun _ hm _ ha => mem_magnetIdeal_of_notMem hm ha)

/-- `Q = B_0 / (x - ε x)`. -/
abbrev unitQuotIdeal (π : H →ₐc[k] MonoidAlgebra k X) :
    Ideal (H ⧸ magnetIdeal (torusGrading π) ⊥) :=
  (Ideal.span (unitGens π)).map (Ideal.Quotient.mk _)

/-- `ρ(Q-ideal) = (x - ε x) B_N`. -/
lemma map_rhoF_unitQuotIdeal :
    (unitQuotIdeal π).map (rhoF (faceData_ray π hα)) =
      (Ideal.span (unitGens π)).map (Ideal.Quotient.mk (magnetIdeal (torusGrading π) (rayMagnet α))) := by
  rw [unitQuotIdeal, Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_image]
  congr 1
  refine Set.image_congr fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := hy
  have hy0 : x - algebraMap k H (Coalgebra.counit (R := k) x) ∈ torusGrading π 0 := by
    refine Submodule.sub_mem _ hx ?_
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  change rhoF (faceData_ray π hα) (Ideal.Quotient.mk _ _) = _
  rw [rhoF_mk, pr0_hom (torusGrading π) _ hy0, if_pos (mem_Fgp_bot_iff.2 rfl)]

/-- `H/J_U ≅ B_N/(x - ε x)B_N`. -/
def prescribedUnitEquivQuot :
    (H ⧸ prescribedUnitIdeal π (rayMagnet α)) ≃+*
      (H ⧸ magnetIdeal (torusGrading π) (rayMagnet α)) ⧸
        (unitQuotIdeal π).map (rhoF (faceData_ray π hα)) :=
  (Ideal.quotEquivOfEq (prescribedUnitIdeal_eq _)).trans
    ((DoubleQuot.quotQuotEquivQuotSup _ _).symm.trans
      (Ideal.quotEquivOfEq (map_rhoF_unitQuotIdeal hα).symm))

variable (π) in
/-- The unit point `e : B_0 → k` (the counit). -/
def unitPt : (H ⧸ magnetIdeal (torusGrading π) ⊥) →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom k H) (by
    intro x hx
    rw [magnetIdeal] at hx
    refine (Ideal.span_le (I := RingHom.ker (Bialgebra.counitAlgHom k H))).2 ?_ hx
    simp only [Set.iUnion_subset_iff]
    intro χ hχ y hy
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact counit_eq_zero_of_mem (by rwa [AddSubmonoid.mem_bot] at hχ) hy)

lemma unitPt_mk (h : H) : unitPt π (Ideal.Quotient.mk _ h) = Coalgebra.counit (R := k) h := rfl

lemma unitPt_surjective : Function.Surjective (unitPt π) :=
  fun r => ⟨algebraMap k _ r, by rw [AlgHom.commutes]; rfl⟩

lemma ker_unitPt : RingHom.ker (unitPt π) = unitQuotIdeal π := by
  apply le_antisymm
  · intro b hb
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [RingHom.mem_ker] at hb
    change unitPt π (Ideal.Quotient.mk _ h) = 0 at hb
    rw [unitPt_mk] at hb
    have h1 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (magnetIdeal (torusGrading π) ⊥))
      (sub_counit_mem (π := π) h)
    rw [hb, map_zero, sub_zero, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq] at h1
    exact h1
  · rw [unitQuotIdeal, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨x, -, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker]
    change unitPt π (Ideal.Quotient.mk _ _) = 0
    rw [unitPt_mk, map_sub, Bialgebra.counit_algebraMap, sub_self]

variable [Algebra.Smooth k H]

include hα in
/-- **BB for the face `0` of `[α⟩`**: `B_N ≅ Sym_{B_0}(C)`. -/
lemma exists_sym_ray :
    letI := (rhoF (faceData_ray π hα)).toRingHom.toAlgebra
    Nonempty (SymmetricAlgebra (H ⧸ magnetIdeal (torusGrading π) ⊥)
        (Sec12Printed.Conormal (piBF (faceData_ray π hα))) ≃ₐ[H ⧸ magnetIdeal (torusGrading π) ⊥]
      (H ⧸ magnetIdeal (torusGrading π) (rayMagnet α))) :=
  (face_sym_ring (torusGrading π) (rayMagnet α) ⊥ (isFace_bot_rayMagnet hα) le_rfl
    ⟨{α}, by rw [Finset.coe_singleton]; rfl⟩ (fun _ hm _ ha => mem_magnetIdeal_of_notMem hm ha)
    (smooth_quotient_magnetIdeal (torusGrading π) _)
    (smooth_quotient_magnetIdeal (torusGrading π) _)).2.2

include hα in
/-- **`O(U_α) ≅ Sym_k(k ⊗_{B_0} C)`** (base change of BB along `e`), as rings. -/
theorem nonempty_prescribedUnit_equiv_sym :
    letI := (rhoF (faceData_ray π hα)).toRingHom.toAlgebra
    letI := (unitPt π).toRingHom.toAlgebra
    Nonempty ((H ⧸ prescribedUnitIdeal π (rayMagnet α)) ≃+*
      SymmetricAlgebra k (k ⊗[H ⧸ magnetIdeal (torusGrading π) ⊥]
        Sec12Printed.Conormal (piBF (faceData_ray π hα)))) := by
  let _ := (rhoF (faceData_ray π hα)).toRingHom.toAlgebra
  let _ := (unitPt π).toRingHom.toAlgebra
  obtain ⟨φ⟩ := exists_sym_ray (π := π) hα
  set B0 := H ⧸ magnetIdeal (torusGrading π) ⊥
  set K : Ideal B0 := RingHom.ker (Algebra.ofId B0 k)
  have hK : K = unitQuotIdeal π := ker_unitPt
  have hker : (unitQuotIdeal π).map (rhoF (faceData_ray π hα)) =
      K.map (algebraMap B0 (H ⧸ magnetIdeal (torusGrading π) (rayMagnet α))) := by
    rw [hK]; rfl
  have hs : Function.Surjective (Algebra.ofId B0 k) := unitPt_surjective
  exact ⟨(prescribedUnitEquivQuot hα).trans ((Ideal.quotEquivOfEq hker).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := B0)
      (H ⧸ magnetIdeal (torusGrading π) (rayMagnet α)) K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := B0)
        (A₁ := H ⧸ magnetIdeal (torusGrading π) (rayMagnet α)))
      (Ideal.quotientKerAlgEquivOfSurjective hs)).toRingEquiv.trans
    ((Algebra.TensorProduct.comm B0
      (H ⧸ magnetIdeal (torusGrading π) (rayMagnet α)) k).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := B0) (A₁ := k)) φ.symm).toRingEquiv.trans
    (symBaseChange B0 k _).toRingEquiv)))))⟩

include hα in
/-- **`U_α` is reduced**: `O(U_α)` is a polynomial ring over `k`. -/
theorem isReduced_quotient_prescribedUnit :
    IsReduced (H ⧸ prescribedUnitIdeal π (rayMagnet α)) := by
  let _ := (rhoF (faceData_ray π hα)).toRingHom.toAlgebra
  let _ := (unitPt π).toRingHom.toAlgebra
  obtain ⟨e⟩ := nonempty_prescribedUnit_equiv_sym (π := π) hα
  set V := k ⊗[H ⧸ magnetIdeal (torusGrading π) ⊥] Sec12Printed.Conormal (piBF (faceData_ray π hα))
  let b := Module.Free.chooseBasis k V
  let f := (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv
  exact isReduced_of_injective ((f.toRingHom).comp e.toRingHom)
    (f.injective.comp e.injective)

end AlgMag.Reductive
