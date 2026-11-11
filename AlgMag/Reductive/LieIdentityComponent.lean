/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularSlice
import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import AlgMag.Reductive.PointDerivations

/-!
# Derivations of `O(K)` at a point = `Lie K = Lie G^N` (C2(d), part (a), item 2)

For a Hopf algebra `A` over a field `k` and a `k`-point `t`, derivations `A → k` at `t`
(`derAt t`) are identified with derivations at the identity by right translation by `t⁻¹`
(`derAtTranslate`). For `A = compAlg π N = O((G^N)°)`, derivations at `e` pull back along
`compMk π N : O(G) → O(K)` injectively onto `Lie G^N = (magnetHopfIdeal π N).lieSubalgebra`
(`range_derivationComp_compMk`). Hence `derAtCompEquiv t₀ : derAt t₀ ≃ₗ[k] Lie G^N`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.HopfIdeal TauCeti.HopfAlgebra WithConv

namespace AlgMag.Reductive

universe u

section Generic

variable {k A : Type*} [Field k] [CommRing A] [_root_.HopfAlgebra k A]

/-- Derivations `A → k` at the `k`-point `t`. -/
def derAt (t : WithConv (A →ₐ[k] k)) : Submodule k (A →ₗ[k] k) where
  carrier := {D | ∀ a b, D (a * b) = t.ofConv a * D b + t.ofConv b * D a}
  add_mem' {D E} hD hE a b := by
    simp only [LinearMap.add_apply, hD a b, hE a b]; ring
  zero_mem' a b := by simp
  smul_mem' c D hD a b := by
    simp only [LinearMap.smul_apply, smul_eq_mul, hD a b]; ring

lemma mem_derAt {t : WithConv (A →ₐ[k] k)} {D : A →ₗ[k] k} :
    D ∈ derAt t ↔ ∀ a b, D (a * b) = t.ofConv a * D b + t.ofConv b * D a := Iff.rfl

/-- Bridge to `PointDerivations.lean`. -/
lemma derAt_eq_pointDer (t : WithConv (A →ₐ[k] k)) : derAt t = pointDer t.ofConv := rfl

lemma comp_rightTranslation_mem_derAt {t : WithConv (A →ₐ[k] k)} (s : WithConv (A →ₐ[k] k))
    {D : A →ₗ[k] k} (hD : D ∈ derAt t) :
    D ∘ₗ (rightTranslationAlgHom s).toLinearMap ∈ derAt (t * s) := by
  intro a b
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul]
  rw [hD, ofConv_rightTranslationAlgHom, ofConv_rightTranslationAlgHom]

lemma rightTranslation_comp_inv (t : WithConv (A →ₐ[k] k)) (a : A) :
    rightTranslationAlgHom t⁻¹ (rightTranslationAlgHom t a) = a := by
  rw [← AlgHom.comp_apply, ← rightTranslationAlgHom_mul, inv_mul_cancel, rightTranslationAlgHom_one,
    AlgHom.id_apply]

lemma rightTranslation_inv_comp (t : WithConv (A →ₐ[k] k)) (a : A) :
    rightTranslationAlgHom t (rightTranslationAlgHom t⁻¹ a) = a := by
  rw [← AlgHom.comp_apply, ← rightTranslationAlgHom_mul, mul_inv_cancel, rightTranslationAlgHom_one,
    AlgHom.id_apply]

/-- Right translation by `t⁻¹` moves derivations at `t` to derivations at the identity. -/
def derAtTranslate (t : WithConv (A →ₐ[k] k)) :
    derAt t ≃ₗ[k] derAt (1 : WithConv (A →ₐ[k] k)) where
  toFun D := ⟨D.1 ∘ₗ (rightTranslationAlgHom t⁻¹).toLinearMap, by
    simpa [mul_inv_cancel] using comp_rightTranslation_mem_derAt t⁻¹ D.2⟩
  invFun E := ⟨E.1 ∘ₗ (rightTranslationAlgHom t).toLinearMap, by
    simpa using comp_rightTranslation_mem_derAt t E.2⟩
  map_add' D E := rfl
  map_smul' c D := rfl
  left_inv D := by
    ext a; simp [rightTranslation_comp_inv]
  right_inv E := by
    ext a; simp [rightTranslation_inv_comp]

@[simp]
lemma derAtTranslate_apply (t : WithConv (A →ₐ[k] k)) (D : derAt t) (a : A) :
    (derAtTranslate t D : A →ₗ[k] k) a = D.1 (rightTranslationAlgHom t⁻¹ a) := rfl

lemma ofConv_one_apply (a : A) :
    (1 : WithConv (A →ₐ[k] k)).ofConv a = Coalgebra.counit a := rfl

/-- Derivations at the identity are counit-valued derivations. -/
def derAtOneEquiv :
    derAt (1 : WithConv (A →ₐ[k] k)) ≃ₗ[k] Derivation k A (Bialgebra.CounitAlgebra k A k) where
  toFun D := Derivation.mk' ((Bialgebra.CounitAlgebra.algEquivSelf k A k).symm.toLinearMap ∘ₗ D.1)
    (fun a b => by
      apply (Bialgebra.CounitAlgebra.algEquivSelf k A k).injective
      simp only [LinearMap.coe_comp, Function.comp_apply, map_add,
        Bialgebra.CounitAlgebra.algEquivSelf_smul]
      simp [D.2 a b, Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]
      rfl)
  invFun d := ⟨(Bialgebra.CounitAlgebra.algEquivSelf k A k).toLinearMap ∘ₗ
      (d : A →ₗ[k] Bialgebra.CounitAlgebra k A k), fun a b => by
    have h := congrArg (Bialgebra.CounitAlgebra.algEquivSelf k A k) (d.leibniz a b)
    simp only [map_add, Bialgebra.CounitAlgebra.algEquivSelf_smul] at h
    simpa [ofConv_one_apply, add_comm] using h⟩
  map_add' D E := by ext; rfl
  map_smul' c D := by ext; rfl
  left_inv D := by ext; rfl
  right_inv d := by ext; rfl

end Generic

section Comp

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [_root_.HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [IsAlgClosed k] [Algebra.FiniteType k H]
variable {N : Magnet (Additive X)}

lemma derivationComp_compMk_mem (N : Magnet (Additive X))
    (d : Derivation k (compAlg π N) (Bialgebra.CounitAlgebra k (compAlg π N) k)) :
    derivationCompLieHom (B := k) (compMk π N) d ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k) :=
  range_derivationComp_compMk π N ▸ LieHom.mem_range_self _ d

/-- Pull-back along `compMk π N`, as a linear map into `Lie G^N`. -/
def derivationCompToLie (N : Magnet (Additive X)) :
    Derivation k (compAlg π N) (Bialgebra.CounitAlgebra k (compAlg π N) k) →ₗ[k]
      (magnetHopfIdeal π N).lieSubalgebra (B := k) where
  toFun d := ⟨_, derivationComp_compMk_mem π N d⟩
  map_add' d e := Subtype.ext (map_add (derivationCompLieHom (B := k) (compMk π N)) d e)
  map_smul' c d := Subtype.ext ((derivationCompLieHom (B := k) (compMk π N)).map_smul c d)

/-- Pull-back along `compMk π N`, as an equivalence onto `Lie G^N`. -/
def derivationCompEquiv (N : Magnet (Additive X)) :
    Derivation k (compAlg π N) (Bialgebra.CounitAlgebra k (compAlg π N) k) ≃ₗ[k]
      (magnetHopfIdeal π N).lieSubalgebra (B := k) :=
  LinearEquiv.ofBijective (derivationCompToLie π N)
    ⟨fun d e h => derivationCompLieHom_injective_of_surjective (B := k) (compMk π N)
        (compMk_surjective π N) (congrArg Subtype.val h),
      fun y => by
        obtain ⟨y, hy⟩ := y
        rw [← range_derivationComp_compMk] at hy
        obtain ⟨d, rfl⟩ := hy
        exact ⟨d, rfl⟩⟩

/-- **Item 2.** Derivations of `O(K)` at any `k`-point `t₀` (e.g. the regular torus point) are
`Lie K = Lie G^N`, via right translation by `t₀⁻¹` and pull-back along `O(G) → O(K)`. -/
def derAtCompEquiv (t₀ : WithConv (compAlg π N →ₐ[k] k)) :
    derAt t₀ ≃ₗ[k] (magnetHopfIdeal π N).lieSubalgebra (B := k) :=
  (derAtTranslate t₀).trans (derAtOneEquiv.trans (derivationCompEquiv π N))

lemma derAtCompEquiv_apply (t₀ : WithConv (compAlg π N →ₐ[k] k)) (D : derAt t₀) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf k H k
      (((derAtCompEquiv π t₀ D : (magnetHopfIdeal π N).lieSubalgebra (B := k)) :
        Derivation k H (Bialgebra.CounitAlgebra k H k)) h) =
      D.1 (rightTranslationAlgHom t₀⁻¹ (compMk π N h)) := by
  show Bialgebra.CounitAlgebra.algEquivSelf k H k (derivationComp (B := k) (compMk π N)
    (derAtOneEquiv (derAtTranslate t₀ D)) h) = _
  rw [algEquivSelf_derivationComp_apply]
  rfl

end Comp

end AlgMag.Reductive
