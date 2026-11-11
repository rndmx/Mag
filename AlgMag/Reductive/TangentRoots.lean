/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.Prop1610Field
import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
import TauCeti.Algebra.AlgebraicGroup.Tangent.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Tangent

/-!
# Tangent weights are the adjoint weights

For the conjugation action of `D(X)` on `G = Spec H` over a field `k`, a weight `χ` is a tangent
weight (some tangent vector at `e` does not vanish on the weight space `H_χ`) exactly when the
`χ`-weight space `𝔤_χ` of the adjoint representation is nonzero
(`mem_tangentWeights_iff_adjointWeightSpace_ne_bot`). Hence the nonzero tangent weights are the
roots `Φ` of `(G, D(X))`, i.e. the nontrivial weights of `D(X)` on `Lie(G)` (Tau Ceti
`Derivation.nontrivialAdjointWeights`), and the tangent-weight hypothesis of Proposition 16.10 (ii)
is the printed condition `N ∩ Φ = f⁻¹(ℕ) ∩ Φ`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- The roots `Φ` of `(G, D(X))`: the nontrivial weights of `D(X)` on `Lie(G)`. -/
def roots [Module.Finite k (Bialgebra.CotangentSpace k H)] : Set (Additive X) := Additive.toMul ⁻¹' Derivation.nontrivialAdjointWeights π

variable {π}

omit [DecidableEq X] in
lemma torusCoactLeft_of_mem {χ : Additive X} {h : H} (hh : h ∈ torusGrading π χ) :
    torusCoactLeft π h = MonoidAlgebra.single (Additive.toMul χ) 1 ⊗ₜ[k] h := by
  have h1 := mem_torusGrading.mp hh
  apply (TensorProduct.comm k (MonoidAlgebra k X) H).injective
  rw [TensorProduct.comm_tmul]
  exact h1

section CotangentFinite

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

omit [DecidableEq X] in
attribute [local instance] Derivation.adjointComodule in
/-- An adjoint weight vector of weight `α` vanishes on every weight space `H_χ`, `χ ≠ α`. -/
theorem cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace {α : X}
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : x ∈ Derivation.adjointWeightSpace π α) {χ : Additive X} (hχ : Additive.toMul χ ≠ α)
    {h : H} (hh : h ∈ torusGrading π χ) :
    Derivation.cotangentLinearEquiv (B := k) x h = 0 := by
  let A : CommAlgCat.{u} k := CommAlgCat.of k (MonoidAlgebra k X)
  let g : HopfAlgebra.points (H := H) A := toConv (π : H →ₐ[k] MonoidAlgebra k X)
  have ha := Derivation.endOfPoint_tmul_of_mem_adjointWeightSpace π
    (AlgHom.id k (MonoidAlgebra k X)) 1 hx
  rw [one_mul] at ha
  have hd := congrArg (Derivation.tangentScalarExtensionEquiv
    (R := k) (A := H) (B := A)) ha
  have he := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint A g
    ((1 : MonoidAlgebra k X) ⊗ₜ[k] x)
  have hcomp : (AlgHom.id k (MonoidAlgebra k X)).comp (π : H →ₐ[k] MonoidAlgebra k X) =
      g.ofConv := rfl
  rw [hcomp] at hd
  rw [hd, Derivation.tangentScalarExtensionEquiv_tmul,
    Derivation.tangentScalarExtensionEquiv_tmul, one_smul] at he
  set D := Derivation.mapValue (A := H) (Algebra.ofId k A)
    (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) x) with hD
  have hval := congrArg (fun E : Derivation k H (Bialgebra.CounitAlgebra k H A) =>
    Bialgebra.CounitAlgebra.algEquivSelf k H A (E h)) he
  rw [TauCeti.algEquivSelf_derivation_smul_apply,
    Derivation.adDerivation_eq_lift_conjugationAlgHom] at hval
  -- evaluate the conjugation through `π ⊗ id`
  have hlift : ∀ z : H ⊗[k] H,
      TensorProduct.lift ((LinearMap.mul k (Bialgebra.CounitAlgebra k H A)).compl₁₂
        (Derivation.pointInCounitAlgebra A g).ofConv.toLinearMap D.toLinearMap) z =
      TensorProduct.lift ((LinearMap.mul k (Bialgebra.CounitAlgebra k H A)).compl₁₂
        ((Bialgebra.CounitAlgebra.algEquivSelf k H A).symm.toAlgHom.toLinearMap)
          D.toLinearMap)
        (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id k H) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    | tmul a b =>
      simp only [TensorProduct.lift.tmul, Algebra.TensorProduct.map_tmul,
        LinearMap.compl₁₂_apply, AlgHom.toLinearMap_apply, AlgHom.id_apply]
      rfl
  rw [hlift] at hval
  have hc : Algebra.TensorProduct.map π.toAlgHom (AlgHom.id k H)
      (HopfAlgebra.conjugationAlgHom (R := k) (H := H) h) = torusCoactLeft π h := rfl
  rw [hc, torusCoactLeft_of_mem hh, TensorProduct.lift.tmul] at hval
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply,
    Derivation.coeFn_coe, map_mul, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at hval
  rw [BialgHom.algEquivSelf_mapValue_ofId_apply] at hval
  simp only [AlgHom.id_apply] at hval
  set c := Bialgebra.CounitAlgebra.algEquivSelf k H k
    (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) x h)
  have hval2 : c • MonoidAlgebra.single α (1 : k) =
      c • MonoidAlgebra.single (Additive.toMul χ) (1 : k) := by
    have e := hval
    rw [show (algebraMap k A) c = c • (1 : MonoidAlgebra k X) from
      Algebra.algebraMap_eq_smul_one c] at e
    simpa only [mul_smul_comm, mul_one] using e
  have hco := congrArg (fun f : MonoidAlgebra k X => f.coeff (Additive.toMul χ)) hval2
  simp only [MonoidAlgebra.coeff_smul] at hco
  have hc0 : c = 0 := by
    rw [MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, Finsupp.smul_apply,
      Finsupp.smul_apply, Finsupp.single_eq_same] at hco
    rw [Finsupp.single_eq_of_ne hχ] at hco
    simp only [smul_eq_mul, mul_zero, mul_one] at hco
    exact hco.symm
  exact (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective (hc0.trans (map_zero _).symm)

/-- **Tangent weights are adjoint weights.** `χ` is a tangent weight of `G` exactly when the
`χ`-weight space of `D(X)` on `Lie(G)` is nonzero. -/
theorem mem_tangentWeights_iff_adjointWeightSpace_ne_bot (χ : Additive X) :
    χ ∈ tangentWeights π k ↔ Derivation.adjointWeightSpace π (Additive.toMul χ) ≠ ⊥ := by
  constructor
  · rintro ⟨d, h, hh, hd⟩ hbot
    obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).surjective d
    apply hd
    clear hd
    have hx : x ∈ ⨆ α, Derivation.adjointWeightSpace π α := by
      rw [DirectSum.IsInternal.submodule_iSup_eq_top (dec_ι := Classical.decEq X)
        (Derivation.isInternal_adjointWeightSpace π)]; trivial
    induction hx using Submodule.iSup_induction' with
    | mem α y hy =>
      by_cases hα : Additive.toMul χ = α
      · subst hα
        rw [hbot, Submodule.mem_bot] at hy
        rw [hy, map_zero]; rfl
      · exact cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace hy hα hh
    | zero => rw [map_zero]; rfl
    | add y z _ _ hy hz => rw [map_add, Derivation.add_apply, hy, hz, add_zero]
  · intro hne
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    by_contra hW
    apply hx0
    apply (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).injective
    rw [map_zero]
    ext h
    have hh : h ∈ ⨆ β, torusGrading π β := by
      rw [(isInternal_torusGrading π).submodule_iSup_eq_top]; trivial
    induction hh using Submodule.iSup_induction' with
    | mem β y hy =>
      by_cases hβ : β = χ
      · subst hβ
        by_contra hy0
        exact hW ⟨_, y, hy, hy0⟩
      · exact cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace hx
          (fun e => hβ (Additive.toMul.injective e)) hy
    | zero => rw [map_zero]; rfl
    | add y z _ _ hy hz => rw [map_add, hy, hz]; simp

/-- The nonzero tangent weights are the roots. -/
theorem mem_tangentWeights_iff_mem_roots {χ : Additive X} (hχ : χ ≠ 0) :
    χ ∈ tangentWeights π k ↔ χ ∈ roots π := by
  rw [mem_tangentWeights_iff_adjointWeightSpace_ne_bot]
  exact ⟨fun h => ⟨hχ, h⟩, fun h => h.2⟩

/-- `tangentWeights ⊆ {0} ∪ Φ`, and `Φ ⊆ tangentWeights`. -/
theorem tangentWeights_subset_insert_roots : tangentWeights π k ⊆ insert 0 (roots π) := by
  intro χ hχ
  by_cases h0 : χ = 0
  · exact Or.inl h0
  · exact Or.inr ((mem_tangentWeights_iff_mem_roots h0).1 hχ)

theorem roots_subset_tangentWeights : roots π ⊆ tangentWeights π k := fun _ hχ =>
  (mem_tangentWeights_iff_mem_roots (π := π) hχ.1).2 hχ

variable (ψ : X →* Multiplicative ℤ)

/-- The tangent-weight hypothesis of Proposition 16.10 (ii) is `N ∩ Φ = f⁻¹(ℕ) ∩ Φ`. -/
theorem tangentWeights_condition_iff_roots (N : Magnet (Additive X)) :
    (∀ χ ∈ tangentWeights π k, χ ∈ N ↔ 0 ≤ pairingHom ψ χ) ↔
      ∀ χ ∈ roots π, χ ∈ N ↔ 0 ≤ pairingHom ψ χ := by
  constructor
  · intro h χ hχ
    exact h χ (roots_subset_tangentWeights hχ)
  · intro h χ hχ
    rcases tangentWeights_subset_insert_roots hχ with h0 | hr
    · subst h0
      simp only [map_zero, le_refl, iff_true]
      exact N.zero_mem
    · exact h χ hr

end CotangentFinite

variable (π) (ψ : X →* Multiplicative ℤ)

/-- **Proposition 16.10 (ii) of Algebraic Magnetism over a field, printed root form.** Let `G` be
smooth over `k` with an action of `D(X)`, `Φ` the roots (the nontrivial weights of `D(X)` on
`Lie(G)`), `f` a magnet map and `N ⊆ f⁻¹(ℕ)` a magnet with `N ∩ Φ = f⁻¹(ℕ) ∩ Φ`. If the Levi
subgroup `Z(λ_f)` is geometrically connected, then `G^N = P(λ_f)`. -/
theorem magnetIdeal_eq_parabolic_of_field_of_levi_roots [Algebra.Smooth k H]
    {N : Magnet (Additive X)} (hN : N ≤ natMagnet.comap (pairingHom ψ))
    (hΦ : {α | α ∈ N} ∩ roots π = {α | α ∈ natMagnet.comap (pairingHom ψ)} ∩ roots π)
    (hZ : ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k]
      (H ⧸ (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal)))) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  refine magnetIdeal_eq_parabolic_of_field_of_levi π ψ hN
    ((tangentWeights_condition_iff_roots ψ N).2 fun χ hχ => ?_) hZ
  have := congrArg (χ ∈ ·) hΦ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hχ, and_true, eq_iff_iff] at this
  exact this

end AlgMag.Reductive
