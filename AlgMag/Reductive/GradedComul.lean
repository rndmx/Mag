/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.CocharacterGrading
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# (G) The comultiplication respects the `λ`-grading

For `h` of `λ`-degree `n`, `Δ h ∈ ⨆_{p+q=n} H_p ⊗ H_q` (`comul_mem_tensorGradingComul`).

Proof: `Δ` is the convolution product of the two universal points `includeLeft`,
`includeRight` of `H ⊗ H` (Tau Ceti `comulPoint_eq_include_mul`), conjugation by the generic point
is multiplicative, and the coefficients of conjugation are computed by `coeff_conjugate`.
-/

suppress_compilation

open TensorProduct TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- The induced grading on `H ⊗ H`: `(H ⊗ H)_n = ⨆_{p+q=n} H_p ⊗ H_q`. -/
def tensorGradingComul (n : ℤ) : Submodule k (H ⊗[k] H) :=
  ⨆ (p : ℤ) (q : ℤ) (_ : p + q = n),
    LinearMap.range (TensorProduct.map (lineGrading l p).subtype (lineGrading l q).subtype)

variable {l}

lemma tmul_mem_tensorGradingComul {p q n : ℤ} (hpq : p + q = n) {a b : H}
    (ha : a ∈ lineGrading l p) (hb : b ∈ lineGrading l q) : a ⊗ₜ[k] b ∈ tensorGradingComul l n := by
  refine Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem hpq ?_))
  exact ⟨⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩, rfl⟩

/-- Coefficients of `lift (conj x) (conj y)` on any tensor lie in the tensor grading. -/
lemma coeff_lift_conjugate_mem (t : H ⊗[k] H) (n : ℤ) :
    ((Algebra.TensorProduct.lift
        (conjugate (H ⊗[k] H) l (toConv Algebra.TensorProduct.includeLeft)).ofConv
        (conjugate (H ⊗[k] H) l (toConv Algebra.TensorProduct.includeRight)).ofConv
        (fun _ _ ↦ .all _ _)) t).coeff n ∈ tensorGradingComul l n := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, AddMonoidAlgebra.coeff_add]; exact add_mem ha hb
  | tmul a b =>
    rw [Algebra.TensorProduct.lift_tmul, AddMonoidAlgebra.coeff_mul]
    refine Submodule.sum_mem _ fun p _ ↦ ?_
    refine Submodule.sum_mem _ fun q _ ↦ ?_
    dsimp only
    split_ifs with hpq
    · rw [coeff_conjugate, coeff_conjugate]
      change ((conjugationAlgHom l a).coeff p ⊗ₜ[k] (1 : H)) *
        ((1 : H) ⊗ₜ[k] (conjugationAlgHom l b).coeff q) ∈ _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      exact tmul_mem_tensorGradingComul hpq (coeff_mem_lineGrading a p) (coeff_mem_lineGrading b q)
    · exact zero_mem _

/-- **(G).** The comultiplication maps `H_n` into `(H ⊗ H)_n`. -/
theorem comul_mem_tensorGradingComul {n : ℤ} {h : H} (hh : h ∈ lineGrading l n) :
    Coalgebra.comul (R := k) h ∈ tensorGradingComul l n := by
  classical
  have hxy : toConv (Bialgebra.comulAlgHom k H) =
      toConv (Algebra.TensorProduct.includeLeft (R := k) (A := H) (B := H)) *
        toConv (Algebra.TensorProduct.includeRight (R := k) (A := H) (B := H)) :=
    Bialgebra.comulPoint_eq_include_mul
  have e1 : ((conjugate (H ⊗[k] H) l (toConv (Bialgebra.comulAlgHom k H))).ofConv h).coeff n =
      Coalgebra.comul (R := k) h := by
    rw [coeff_conjugate, coeff_of_mem_lineGrading hh, if_pos rfl]
    rfl
  rw [hxy, map_mul] at e1
  rw [← e1]
  have e2 := AlgHom.convMul_apply
    (conjugate (H ⊗[k] H) l (toConv Algebra.TensorProduct.includeLeft))
    (conjugate (H ⊗[k] H) l (toConv Algebra.TensorProduct.includeRight)) h
  change ((_ * _ : WithConv (H →ₐ[k] LaurentPolynomial (H ⊗[k] H))) h).coeff n ∈ _
  rw [e2]
  exact coeff_lift_conjugate_mem _ n

end AlgMag.Reductive
