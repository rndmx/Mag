/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Weyl.Normalizer
import Mathlib.GroupTheory.Finiteness

/-!
# Rigidity of tori: the image of `N_G(T)` in `Aut(X)` is finite

For `T = D(X) ⊆ G = Spec H` (closed embedding `π : H → k[X]`, `X` finitely generated), the set
`weylImage π A` of automorphisms `σ` of `X` such that some `g ∈ G(A)` normalizes `T` with
automorphism `σ` is finite, for every nontrivial `k`-algebra `A` (in particular `A = k̄`).

Proof (rigidity). Let `U ∈ G(H ⊗ k[X])` be the conjugate of the universal torus point by the
universal point `id_H` of `G`. For `g ∈ G(A)`, `g t g⁻¹ = (g ⊗ id)_* U`. For a character `χ`
pick `h_χ` with `π h_χ = χ`; then `U(h_χ) ∈ H ⊗ k[X]` involves only finitely many characters
`F_χ`, and `g t g⁻¹ = σ_*(t)` evaluated at `h_χ` is `1 ⊗ σ(χ)`, so `σ(χ) ∈ F_χ`. As `X` is
finitely generated, `σ` is determined by finitely many values, each in a finite set.
No smoothness, finite type or algebraic closedness is needed.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv AlgMag.Weyl

namespace AlgMag.Reductive

universe u v w

variable {k : Type u} {H : Type v} {X : Type w}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

variable (A : Type*) [CommRing A] [Algebra k A]

/-- The image of `N_G(T)(A)` in `Aut(X)`. -/
def weylImage : Set (X ≃* X) := {σ | ∃ g : WithConv (H →ₐ[k] A), IsNormalizingWith π A g σ}

/-- The universal conjugate `id_H · t · id_H⁻¹ ∈ G(H ⊗ k[X])`. -/
def univConj : WithConv (H →ₐ[k] H ⊗[k] MonoidAlgebra k X) :=
  MulAut.conj (AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H)
    (B := MonoidAlgebra k X)) (toConv (AlgHom.id k H))) (torusPoint π H)

variable {A}

lemma conj_torusPoint_eq_map (g : WithConv (H →ₐ[k] A)) :
    MulAut.conj (AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A)
      (B := MonoidAlgebra k X)) g) (torusPoint π A) =
      AlgHom.mapValue (Algebra.TensorProduct.map g.ofConv (AlgHom.id k (MonoidAlgebra k X)))
        (univConj π) := by
  have h1 : AlgHom.mapValue (Algebra.TensorProduct.map g.ofConv (AlgHom.id k (MonoidAlgebra k X)))
      (AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H)
        (B := MonoidAlgebra k X)) (toConv (AlgHom.id k H))) =
      AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A)
        (B := MonoidAlgebra k X)) g := by
    apply WithConv.ofConv_injective
    ext x
    simp [AlgHom.mapValue_apply]
  have h2 : AlgHom.mapValue (Algebra.TensorProduct.map g.ofConv (AlgHom.id k (MonoidAlgebra k X)))
      (torusPoint π H) = torusPoint π A := by
    apply WithConv.ofConv_injective
    ext x
    simp [AlgHom.mapValue_apply, torusPoint]
  rw [univConj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, h1, h2]

omit [CommGroup X] in
/-- Every element of `M ⊗ k[X]` involves only finitely many characters. -/
lemma exists_finset_tensorComponent_eq_zero {M : Type*} [AddCommGroup M] [Module k M]
    (E : M ⊗[k] MonoidAlgebra k X) :
    ∃ s : Finset X, ∀ ψ ∉ s,
      LinearMap.tensorComponent (Comodule.monoidCoeff k X ψ) E = 0 := by
  classical
  induction E using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun ψ _ => map_zero _⟩
  | tmul m p =>
    refine ⟨p.coeff.support, fun ψ hψ => ?_⟩
    rw [LinearMap.tensorComponent_tmul, Comodule.monoidCoeff_apply]
    have : p.coeff ψ = 0 := Finsupp.notMem_support_iff.1 hψ
    rw [this, zero_smul]
  | add E F hE hF =>
    obtain ⟨s, hs⟩ := hE
    obtain ⟨t, ht⟩ := hF
    refine ⟨s ∪ t, fun ψ hψ => ?_⟩
    rw [Finset.mem_union, not_or] at hψ
    rw [map_add, hs ψ hψ.1, ht ψ hψ.2, add_zero]

lemma tensorComponent_map (f : H →ₐ[k] A) (ψ : X) (E : H ⊗[k] MonoidAlgebra k X) :
    LinearMap.tensorComponent (Comodule.monoidCoeff k X ψ)
        (Algebra.TensorProduct.map f (AlgHom.id k (MonoidAlgebra k X)) E) =
      f (LinearMap.tensorComponent (Comodule.monoidCoeff k X ψ) E) := by
  induction E using TensorProduct.induction_on with
  | zero => simp
  | tmul m p => simp [LinearMap.tensorComponent_tmul, map_smul]
  | add E F hE hF => rw [map_add, map_add, hE, hF, map_add, map_add]

/-- For each character `χ` there is a finite set containing `σ χ` for every `σ ∈ weylImage`. -/
lemma mem_of_mem_weylImage [Nontrivial A] {χ : X} {h : H} (hh : π h = MonoidAlgebra.single χ 1)
    {s : Finset X} (hs : ∀ ψ ∉ s,
      LinearMap.tensorComponent (Comodule.monoidCoeff k X ψ) ((univConj π).ofConv h) = 0)
    {σ : X ≃* X} (hσA : σ ∈ weylImage π A) : σ χ ∈ s := by
  classical
  obtain ⟨g, hg⟩ := hσA
  by_contra hσ
  have key := congrArg (fun p : WithConv (H →ₐ[k] A ⊗[k] MonoidAlgebra k X) =>
    LinearMap.tensorComponent (Comodule.monoidCoeff k X (σ χ)) (p.ofConv h)) hg
  simp only [conj_torusPoint_eq_map] at key
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, tensorComponent_map,
    hs _ hσ, map_zero] at key
  rw [twistPoint, ofConv_toConv, AlgHom.comp_apply, AlgHom.comp_apply] at key
  erw [hh] at key
  rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
    Algebra.TensorProduct.includeRight_apply, LinearMap.tensorComponent_tmul,
    Comodule.monoidCoeff_apply] at key
  simp at key

/-- **Rigidity of tori.** The image of `N_G(T)(A)` in `Aut(X)` is finite (`A` nontrivial, e.g.
`A = k̄`); equivalently the identity component of `N_G(T)` centralizes `T`. -/
theorem finite_weylImage [Group.FG X] (hπ : Function.Surjective π) (A : Type*) [CommRing A]
    [Algebra k A] [Nontrivial A] : (weylImage π A).Finite := by
  classical
  obtain ⟨S, hS⟩ := Group.fg_def.1 (inferInstance : Group.FG X)
  choose h hh using fun χ : X => hπ (MonoidAlgebra.single χ 1)
  choose F hF using fun χ : X => exists_finset_tensorComponent_eq_zero ((univConj π).ofConv (h χ))
  let f : (X ≃* X) → (S → X) := fun σ x => σ x
  have himg : f '' weylImage π A ⊆ Set.pi Set.univ fun x : S => (F x : Set X) := by
    rintro _ ⟨σ, hσ, rfl⟩ x _
    exact mem_of_mem_weylImage π (hh x) (hF x) hσ
  refine Set.Finite.of_finite_image ((Set.Finite.pi (ι := S) fun x => (F x).finite_toSet).subset himg) ?_
  intro σ _ τ _ he
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense hS
  intro x hx
  exact congrFun he ⟨x, hx⟩

end AlgMag.Reductive
