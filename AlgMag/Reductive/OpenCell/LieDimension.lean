/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.

Compiled; no sorry.
-/
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Weights
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# `dim 𝔤 = dim 𝔲(-λ) + dim 𝔷(λ) + dim 𝔲(λ)`

`𝔤 = ⊕ₙ 𝔤ₙ` (weights of `λ` on the tangent space, `isInternal_adjointWeightSpace`). Tau Ceti:
`Lie P(λ) = ⊕_{n ≥ 0} 𝔤ₙ`, `Lie U(λ) = ⊕_{n > 0} 𝔤ₙ`. For the opposite cocharacter the weights
are negated (`adjointWeightSpace_opposite`), so `Lie P(-λ) = ⊕_{n ≤ 0}`, `Lie U(-λ) = ⊕_{n < 0}`.
`Z(λ)` is cut out by `I_P ⊔ I_{P⁻}`, so `Lie Z(λ) = Lie P(λ) ⊓ Lie P(-λ)`.

Linear algebra: `𝔲⁻ ⊕ 𝔭 = 𝔤`, `𝔲 ⊕ 𝔭⁻ = 𝔤`, `𝔭 + 𝔭⁻ = 𝔤`, hence
`dim 𝔤 + dim (𝔭 ⊓ 𝔭⁻) = dim 𝔭 + dim 𝔭⁻ = 2 dim 𝔤 - dim 𝔲⁻ - dim 𝔲`.
Finally `dim Lie(H/I) = dim (lieSubalgebra I)` (the differential of `H → H/I` is injective).
-/

namespace AlgMag.OpenCellNotes

open TauCeti TauCeti.Cocharacter
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Derivation k H (Bialgebra.CounitAlgebra k H k)

/-! ### Linear algebra of a `ℤ`-graded space -/

section Graded

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (W : Multiplicative ℤ → Submodule k V)

/-- `⨆_{n ∈ s} Wₙ`. -/
noncomputable def gradedSum (s : Set ℤ) : Submodule k V :=
  ⨆ n : ℤ, ⨆ (_ : n ∈ s), W (Multiplicative.ofAdd n)

variable {W}

/-- Complementary index sets give complementary sums. -/
lemma isCompl_gradedSum (hW : DirectSum.IsInternal W) (s : Set ℤ) :
    IsCompl (gradedSum W s) (gradedSum W sᶜ) := by
  have hind : iSupIndep (fun n : ℤ => W (Multiplicative.ofAdd n)) :=
    hW.submodule_iSupIndep.comp Multiplicative.ofAdd.injective
  refine ⟨hind.disjoint_biSup_biSup disjoint_compl_right, ?_⟩
  rw [codisjoint_iff_le_sup, ← hW.submodule_iSup_eq_top]
  refine iSup_le fun m => ?_
  by_cases hm : m.toAdd ∈ s
  · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun n (_ : n ∈ s) => W (Multiplicative.ofAdd n))
      m.toAdd hm le_rfl)
  · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun n (_ : n ∈ sᶜ) => W (Multiplicative.ofAdd n))
      m.toAdd hm le_rfl)

/-- The three-term dimension formula. -/
theorem finrank_eq_three (hW : DirectSum.IsInternal W) :
    Module.finrank k V =
      Module.finrank k (gradedSum W (Set.Iio 0)) +
        Module.finrank k ↥(gradedSum W (Set.Ici 0) ⊓ gradedSum W (Set.Iic 0)) +
        Module.finrank k (gradedSum W (Set.Ioi 0)) := by
  have c₁ := isCompl_gradedSum hW (Set.Iio 0)
  have c₂ := isCompl_gradedSum hW (Set.Ioi 0)
  rw [Set.compl_Iio] at c₁
  rw [Set.compl_Ioi] at c₂
  have d₁ := Submodule.finrank_add_eq_of_isCompl c₁
  have d₂ := Submodule.finrank_add_eq_of_isCompl c₂
  -- `𝔭 ⊔ 𝔭⁻ = ⊤` since `𝔲⁻ ≤ 𝔭⁻`.
  have hsup : gradedSum W (Set.Ici 0) ⊔ gradedSum W (Set.Iic 0) = ⊤ := by
    have hle : gradedSum W (Set.Iio 0) ≤ gradedSum W (Set.Iic 0) :=
      iSup_mono fun n => iSup_mono' fun hn =>
        ⟨Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp hn)), le_rfl⟩
    rw [eq_top_iff, ← c₁.sup_eq_top]
    exact sup_le (hle.trans le_sup_right) le_sup_left
  have d₃ := Submodule.finrank_sup_add_finrank_inf_eq (gradedSum W (Set.Ici 0))
    (gradedSum W (Set.Iic 0))
  rw [hsup, finrank_top] at d₃
  omega

end Graded

/-! ### Weights of the opposite cocharacter -/

/-- The `ℤ`-graded comodule of a cocharacter. -/
noncomputable abbrev weightsOf (l : H →ₐc[k] LaurentPolynomial k) :
    Multiplicative ℤ → Submodule k (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
  Derivation.adjointWeightSpace
    ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)

/-- **Weights of `-λ` are the negatives of those of `λ`.** `oppositeCocharacter l` is `l`
followed by `T ↦ T⁻¹` (`domCongrBialgEquiv (AddEquiv.neg ℤ)`), so the composed coaction is the
original one followed by `α ↦ α⁻¹` on `k[ℤ]`. -/
theorem adjointWeightSpace_opposite (l : H →ₐc[k] LaurentPolynomial k) (n : ℤ) :
    weightsOf l.oppositeCocharacter (Multiplicative.ofAdd n) =
      weightsOf l (Multiplicative.ofAdd (-n)) := by
  -- The coaction along `-λ` is the coaction along `λ` pushed by `α ↦ α⁻¹`.
  have hcomp : (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp
      l.oppositeCocharacter =
      (MonoidAlgebra.mapDomainBialgHom k (invMonoidHom : Multiplicative ℤ →* Multiplicative ℤ)).comp
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l) := by
    rw [BialgHom.oppositeCocharacter, ← BialgHom.comp_assoc, ← BialgHom.comp_assoc]
    congr 1
    apply BialgHom.coe_toAlgHom_injective
    apply AddMonoidAlgebra.algHom_ext
    · intro n
      simp only [BialgHom.coe_comp, BialgHom.coe_toAlgHom, Function.comp_apply,
        BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom,
        AddMonoidAlgebra.toMultiplicativeBialgEquiv_single, MonoidAlgebra.mapDomainBialgHom_single]
      rw [show (AddMonoidAlgebra.domCongrBialgEquiv k k (AddEquiv.neg ℤ)) (AddMonoidAlgebra.single n (1 : k))
          = AddMonoidAlgebra.single (-n) (1 : k) from AddMonoidAlgebra.domCongr_single (R := k) _ _ _,
        AddMonoidAlgebra.toMultiplicativeBialgEquiv_single]
      rfl
    · exact Subsingleton.elim _ _
  rw [weightsOf, hcomp, Derivation.adjointWeightSpace_mapDomainBialgHom_comp]
  have hpre : (invMonoidHom : Multiplicative ℤ →* Multiplicative ℤ) ⁻¹'
      {Multiplicative.ofAdd n} = {Multiplicative.ofAdd (-n)} := by
    ext m
    simp only [Set.mem_preimage, Set.mem_singleton_iff, invMonoidHom_apply]
    constructor
    · intro h; rw [← inv_inv m, h]; rfl
    · rintro rfl; rw [← ofAdd_neg, neg_neg]
  rw [hpre, iSup_singleton]

/-! ### Lie algebras of the open-cell factors -/

/-- `Lie (I ⊔ J) = Lie I ⊓ Lie J`. -/
theorem lieSubalgebra_sup (I J : HopfIdeal k H) :
    ((I ⊔ J).lieSubalgebra (B := k)).toSubmodule =
      (I.lieSubalgebra (B := k)).toSubmodule ⊓ (J.lieSubalgebra (B := k)).toSubmodule := by
  ext d
  simp only [LieSubalgebra.mem_toSubmodule, Submodule.mem_inf, HopfIdeal.mem_lieSubalgebra_iff]
  rw [HopfIdeal.sup_toIdeal]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Ideal.mem_sup_left hx), fun x hx => h x (Ideal.mem_sup_right hx)⟩
  · rintro ⟨hI, hJ⟩ x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hI y hy, hJ z hz, add_zero]

/-- `dim Lie(H/I) = dim (lieSubalgebra I)`. -/
theorem finrank_quotient_eq_lieSubalgebra (I : HopfIdeal k H) :
    Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ I.toIdeal)) =
      Module.finrank k (I.lieSubalgebra (B := k)).toSubmodule := by
  rw [← Derivation.finrank_eq_finrank_cotangentSpace]
  let e₂ : (I.lieSubalgebra (B := k)) ≃ₗ[k] (I.lieSubalgebra (B := k)).toSubmodule :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ((HopfIdeal.quotientLieEquiv (B := k) I).toLinearEquiv.trans e₂).finrank_eq

/-- **`dim 𝔲(-λ) + dim 𝔷(λ) + dim 𝔲(λ) = dim 𝔤`.** -/
theorem finrank_openCell_cotangent (l : H →ₐc[k] LaurentPolynomial k) :
    Module.finrank k
        (Bialgebra.CotangentSpace k (H ⧸ l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal)) +
      Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ (leviDefiningHopfIdeal l).toIdeal)) +
      Module.finrank k (Bialgebra.CotangentSpace k (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal)) =
    Module.finrank k (Bialgebra.CotangentSpace k H) := by
  classical
  let e := Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)
  let W := weightsOf l
  have hW : DirectSum.IsInternal W := by
    convert Derivation.isInternal_adjointWeightSpace
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)
  -- Lie algebras as images of graded pieces.
  have hU : (l.unipotentDefiningHopfIdeal.lieSubalgebra (B := k)).toSubmodule =
      (gradedSum W (Set.Ioi 0)).map e.toLinearMap :=
    BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule l
  have hP : ((parabolicDefiningHopfIdeal l).lieSubalgebra (B := k)).toSubmodule =
      (gradedSum W (Set.Ici 0)).map e.toLinearMap :=
    BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule l
  have hU' : (l.oppositeCocharacter.unipotentDefiningHopfIdeal.lieSubalgebra (B := k)).toSubmodule =
      (gradedSum W (Set.Iio 0)).map e.toLinearMap := by
    rw [BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule]
    congr 1
    -- `⨆_{n>0} W^{opp}_n = ⨆_{n<0} W_n`, reindex `n ↦ -n`.
    simp only [gradedSum, adjointWeightSpace_opposite]
    exact (Equiv.neg ℤ).iSup_congr fun n => by simp [W]
  have hP' : ((parabolicDefiningHopfIdeal l.oppositeCocharacter).lieSubalgebra
      (B := k)).toSubmodule = (gradedSum W (Set.Iic 0)).map e.toLinearMap := by
    rw [BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule]
    congr 1
    simp only [gradedSum, adjointWeightSpace_opposite]
    exact (Equiv.neg ℤ).iSup_congr fun n => by simp [W]
  have hZ : ((leviDefiningHopfIdeal l).lieSubalgebra (B := k)).toSubmodule =
      (gradedSum W (Set.Ici 0) ⊓ gradedSum W (Set.Iic 0)).map e.toLinearMap := by
    rw [leviDefiningHopfIdeal_def, lieSubalgebra_sup, hP, hP',
      Submodule.map_inf _ e.injective]
  rw [finrank_quotient_eq_lieSubalgebra, finrank_quotient_eq_lieSubalgebra,
    finrank_quotient_eq_lieSubalgebra, hU', hZ, hU, LinearEquiv.finrank_map_eq,
    LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
  -- `finrank ω = finrank (Dual ω)`.
  rw [← Subspace.dual_finrank_eq (K := k) (V := Bialgebra.CotangentSpace k H)]
  exact (finrank_eq_three hW).symm

end AlgMag.OpenCellNotes
