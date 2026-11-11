/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.PointDerivations
import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic

/-!
# Point derivations at the counit are the Lie algebra (C2(d), part (a))

* `pointDerCounitEquiv k H : pointDer (counitAlgHom k H) ≃ₗ[k] Derivation k H (CounitAlgebra k H k)`
  (the repo's `Lie G`); with `H = k[X]` this is `Lie T`.
* `pointDerQuotientEquiv I ε`: point derivations of `A ⧸ I` at `ε` are the point derivations of
  `A` at `ε ∘ mk` vanishing on `I`. With `mem_lieSubalgebra_iff` this gives `Lie U±`.
-/

namespace AlgMag.Reductive

open _root_.Bialgebra

variable (k H : Type*) [Field k] [CommRing H] [Bialgebra k H]

local notation "Cv" => TauCeti.Bialgebra.CounitAlgebra k H k

/-- **Point derivations at `e` = `Lie G`** (`Derivation k H (CounitAlgebra k H k)`). -/
noncomputable def pointDerCounitEquiv :
    pointDer (_root_.Bialgebra.counitAlgHom k H) ≃ₗ[k] Derivation k H Cv where
  toFun D := Derivation.mk' ((TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k H k).symm.toLinearMap ∘ₗ D.1)
    (fun a b => by
      apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
        map_add, TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul, AlgEquiv.apply_symm_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [pointDer_leibniz D a b, _root_.Bialgebra.counitAlgHom_apply,
        _root_.Bialgebra.counitAlgHom_apply])
  invFun d := ⟨(TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k H k).toLinearMap ∘ₗ
      (d.toLinearMap : H →ₗ[k] Cv), fun a b => by
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
      Derivation.coeFn_coe]
    rw [Derivation.leibniz, map_add, TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul,
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_smul, _root_.Bialgebra.counitAlgHom_apply,
      _root_.Bialgebra.counitAlgHom_apply, Algebra.algebraMap_self, RingHom.id_apply,
      RingHom.id_apply]⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  left_inv D := by ext a; exact TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_apply (R := k) (A := H) (B := k) _
  right_inv d := by ext a; exact TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_symm_apply (R := k) (A := H) (B := k) _

end AlgMag.Reductive

namespace AlgMag.Reductive

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Point derivations vanishing on `I`. -/
def pointDerVanishing (ε : A →ₐ[k] k) (I : Ideal A) : Submodule k (pointDer ε) where
  carrier := {D | ∀ x ∈ I, D.1 x = 0}
  add_mem' hD hE x hx := by simp [hD x hx, hE x hx]
  zero_mem' x _ := rfl
  smul_mem' c D hD x hx := by simp [hD x hx]

/-- Descent of a linear map vanishing on `I` to `A ⧸ I`. -/
noncomputable def descendLin (I : Ideal A) (D : A →ₗ[k] k) (hD : ∀ x ∈ I, D x = 0) :
    A ⧸ I →ₗ[k] k :=
  Submodule.liftQ (I.restrictScalars k) D hD ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k I).symm.toLinearMap

@[simp] lemma descendLin_mk (I : Ideal A) (D : A →ₗ[k] k) (hD : ∀ x ∈ I, D x = 0) (a : A) :
    descendLin I D hD (Ideal.Quotient.mk I a) = D a := rfl

/-- Point derivations of a quotient: those of `A` at `ε ∘ mk` vanishing on `I`. -/
noncomputable def pointDerQuotientEquiv (I : Ideal A) (ε : A ⧸ I →ₐ[k] k) :
    pointDer ε ≃ₗ[k] pointDerVanishing (ε.comp (Ideal.Quotient.mkₐ k I)) I where
  toFun D := ⟨⟨D.1 ∘ₗ (Ideal.Quotient.mkₐ k I).toLinearMap, fun a b => by
      simpa using pointDer_leibniz D (Ideal.Quotient.mk I a) (Ideal.Quotient.mk I b)⟩,
    fun x hx => by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]⟩
  invFun D := ⟨descendLin I D.1.1 (fun x hx => D.2 x hx), fun a b => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      have h := pointDer_leibniz D.1 a b
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
      rw [← map_mul]
      exact h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact descendLin_mk I _ _ a
  right_inv D := rfl

end AlgMag.Reductive
