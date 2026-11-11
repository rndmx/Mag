/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.SliceTangentHyps
import AlgMag.Reductive.TangentRoots
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic

/-!
# The Lie algebra of a normal subgroup is a sum of root spaces

Bridge for the converse direction of the reductivity criterion (equivalence.tex, Theorem 5.1,
first paragraph): if `U = V(I)` is a normal closed subgroup of `G`, then `Lie U` is stable under the
weight decomposition of `Lie G` for the torus `T = D(X)`. Consequently, if `Lie U ≠ 0` and
`Lie U ∩ 𝔤_0 = 0`, then `Lie U` contains a nonzero vector of some root space `𝔤_α`, `α ≠ 0`.

* `mem_of_normal_of_coeff`: a normal Hopf ideal is homogeneous for the torus grading;
* `mem_lieSubalgebra_of_finsupp`: weight components of a tangent vector of `V(I)` are tangent to
  `V(I)`;
* `exists_rootSpace_lie_of_isNormal`: the bridge.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- Coefficient of `χ` on the left tensor factor: `k[X] ⊗ H → H`, `c ⊗ h ↦ c(χ) h`. -/
def coeffLeft (χ : X) : MonoidAlgebra k X ⊗[k] H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ
    LinearMap.rTensor H ((Finsupp.lapply χ) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)

omit [CommGroup X] [DecidableEq X] in
lemma coeffLeft_tmul (χ : X) (c : MonoidAlgebra k X) (h : H) :
    coeffLeft (k := k) (H := H) χ (c ⊗ₜ h) = c.coeff χ • h := by
  simp [coeffLeft, MonoidAlgebra.coeffLinearEquiv]
  rfl

omit [DecidableEq X] in
/-- `coeffLeft χ` maps the ideal `k[X] ⊗ I` into `I`. -/
lemma coeffLeft_mem_of_mem_rightTensorIdeal (I : Ideal H) (χ : X)
    {y : MonoidAlgebra k X ⊗[k] H}
    (hy : y ∈ Ideal.rightTensorIdeal (R := k) (A := MonoidAlgebra k X) I) :
    coeffLeft (k := k) (H := H) χ y ∈ I := by
  -- Strengthen: `∀ a, coeffLeft χ' (a * y) ∈ I` for all `χ'`.
  suffices key : ∀ a : MonoidAlgebra k X ⊗[k] H, ∀ χ' : X, coeffLeft (k := k) (H := H) χ' (a * y) ∈ I by
    simpa using key 1 χ
  rw [Ideal.rightTensorIdeal_def, Ideal.map, Ideal.span] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, rfl⟩ := hz
    intro a χ'
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c h =>
      change coeffLeft χ' ((c ⊗ₜ[k] h) * ((1 : MonoidAlgebra k X) ⊗ₜ[k] i)) ∈ I
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, coeffLeft_tmul]
      rw [Algebra.smul_def]
      exact I.mul_mem_left _ (I.mul_mem_left h hi)
    | add a b ha hb => rw [add_mul, map_add]; exact I.add_mem ha hb
  | zero => intro a χ'; simp
  | add y z _ _ hy hz => intro a χ'; rw [mul_add, map_add]; exact I.add_mem (hy a χ') (hz a χ')
  | smul b y _ hy =>
    intro a χ'
    rw [smul_eq_mul, ← mul_assoc]
    exact hy (a * b) χ'

/-- The coefficient of `χ` in the coaction of `h` is the weight-`χ` component of `h`. -/
lemma coeffLeft_torusCoactLeft (χ : Additive X) (h : H) :
    coeffLeft (k := k) (H := H) (Additive.toMul χ) (torusCoactLeft π h) =
      (DirectSum.decompose (torusGrading π) h χ : H) := by
  induction h using induction_torusGrading (π := π) with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, DirectSum.decompose_add,
      DirectSum.add_apply, Submodule.coe_add]
  | hmem ψ x hx =>
    rw [torusCoactLeft_of_mem hx, coeffLeft_tmul, MonoidAlgebra.coeff_single]
    by_cases hψ : ψ = χ
    · subst hψ
      rw [DirectSum.decompose_of_mem_same _ hx, Finsupp.single_eq_same, one_smul]
    · have hne : Additive.toMul ψ ≠ Additive.toMul χ := fun e => hψ (Additive.toMul.injective e)
      rw [DirectSum.decompose_of_mem_ne _ hx hψ, Finsupp.single_eq_of_ne hne.symm, zero_smul]

/-- **A normal Hopf ideal is homogeneous for the torus grading.** -/
theorem mem_of_normal_of_coeff {I : HopfIdeal k H} (hI : I.IsNormal) {x : H}
    (hx : x ∈ I.toIdeal) (χ : Additive X) :
    (DirectSum.decompose (torusGrading π) x χ : H) ∈ I.toIdeal := by
  rw [← coeffLeft_torusCoactLeft π]
  apply coeffLeft_mem_of_mem_rightTensorIdeal
  have hc := hI.conjugation_mem hx
  have hmap := Ideal.mem_map_of_mem
    (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id k H)).toRingHom hc
  rw [Ideal.rightTensorIdeal_def, Ideal.map_map] at hmap
  rw [Ideal.rightTensorIdeal_def]
  convert hmap using 2
  · exact RingHom.ext fun h => by simp
  · rfl

section Lie

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- Every tangent vector is a finite sum of root-space vectors. -/
theorem exists_rootSpace_decomp (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    ∃ f : Additive X →₀ Derivation k H (Bialgebra.CounitAlgebra k H k),
      (∀ α, f α ∈ rootSpace π α) ∧ (f.sum fun _ e => e) = d := by
  have hd : d ∈ ⨆ α, rootSpace π α := by rw [iSup_rootSpace π]; trivial
  exact (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hd

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- On a weight vector of weight `χ`, a sum of root-space vectors evaluates to its `χ`-term. -/
lemma finsupp_sum_apply_of_mem (f : Additive X →₀ Derivation k H (Bialgebra.CounitAlgebra k H k))
    (hf : ∀ α, f α ∈ rootSpace π α) {χ : Additive X} {h : H} (hh : h ∈ torusGrading π χ) :
    (f.sum fun _ e => e) h = f χ h := by
  classical
  have hev : ∀ s : Finset (Additive X), (∑ β ∈ s, f β) h = ∑ β ∈ s, f β h := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  rw [Finsupp.sum, hev, Finset.sum_eq_single χ]
  · intro β _ hβ
    exact hf β χ (Ne.symm hβ) h hh
  · intro hχ
    rw [Finsupp.notMem_support_iff.1 hχ]
    rfl

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- **Weight components of a tangent vector of a normal subgroup are tangent to it.** -/
theorem mem_lieSubalgebra_of_finsupp {I : HopfIdeal k H} (hI : I.IsNormal)
    {d : Derivation k H (Bialgebra.CounitAlgebra k H k)} (hd : d ∈ I.lieSubalgebra (B := k))
    (f : Additive X →₀ Derivation k H (Bialgebra.CounitAlgebra k H k))
    (hf : ∀ α, f α ∈ rootSpace π α) (hsum : (f.sum fun _ e => e) = d) (α : Additive X) :
    f α ∈ I.lieSubalgebra (B := k) := by
  classical
  rw [HopfIdeal.mem_lieSubalgebra_iff] at hd ⊢
  intro x hx
  rw [← DirectSum.sum_support_decompose (torusGrading π) x, map_sum, Finset.sum_eq_single α]
  · have hmem := (DirectSum.decompose (torusGrading π) x α).2
    rw [← finsupp_sum_apply_of_mem π f hf hmem, hsum]
    exact hd _ (mem_of_normal_of_coeff π hI hx α)
  · intro β _ hβ
    exact hf α β hβ _ (DirectSum.decompose (torusGrading π) x β).2
  · intro hα
    rw [DFinsupp.notMem_support_iff.1 hα]
    simp

/-- **Bridge for the converse of the reductivity criterion.** If `U = V(I)` is normal, `Lie U ≠ 0`
and `Lie U ∩ 𝔤_0 = 0`, then `Lie U` contains a nonzero vector of a root space `𝔤_α`, `α ≠ 0`. -/
theorem exists_rootSpace_lie_of_isNormal {I : HopfIdeal k H} (hI : I.IsNormal)
    {d : Derivation k H (Bialgebra.CounitAlgebra k H k)} (hd : d ∈ I.lieSubalgebra (B := k))
    (hd0 : d ≠ 0)
    (h0 : ∀ e ∈ I.lieSubalgebra (B := k), e ∈ rootSpace π 0 → e = 0) :
    ∃ α ≠ 0, ∃ e ∈ I.lieSubalgebra (B := k), e ∈ rootSpace π α ∧ e ≠ 0 := by
  obtain ⟨f, hf, hsum⟩ := exists_rootSpace_decomp π d
  by_contra hcon
  push Not at hcon
  apply hd0
  rw [← hsum, Finsupp.sum]
  refine Finset.sum_eq_zero fun α _ => ?_
  by_cases hα : α = 0
  · subst hα
    exact h0 _ (mem_lieSubalgebra_of_finsupp π hI hd f hf hsum 0) (hf 0)
  · exact hcon α hα _ (mem_lieSubalgebra_of_finsupp π hI hd f hf hsum α) (hf α)

/-- **Bridge, variant.** If `Lie V(I)` (`I` normal) is not contained in `𝔤_0`, it contains a
nonzero vector of a root space `𝔤_α`, `α ≠ 0`. -/
theorem exists_rootSpace_lie_of_isNormal_of_notMem {I : HopfIdeal k H} (hI : I.IsNormal)
    {d : Derivation k H (Bialgebra.CounitAlgebra k H k)} (hd : d ∈ I.lieSubalgebra (B := k))
    (hd0 : d ∉ rootSpace π 0) :
    ∃ α ≠ 0, ∃ e ∈ I.lieSubalgebra (B := k), e ∈ rootSpace π α ∧ e ≠ 0 := by
  obtain ⟨f, hf, hsum⟩ := exists_rootSpace_decomp π d
  by_contra hcon
  push Not at hcon
  apply hd0
  have hd' : d = f 0 := by
    rw [← hsum, Finsupp.sum]
    classical
    rw [Finset.sum_eq_single (0 : Additive X)]
    · intro α _ hα
      exact hcon α hα _ (mem_lieSubalgebra_of_finsupp π hI hd f hf hsum α) (hf α)
    · intro h0
      rw [Finsupp.notMem_support_iff.1 h0]
  rw [hd']
  exact hf 0

end Lie

end AlgMag.Reductive
