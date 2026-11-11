/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.PointDerivationsLie
import AlgMag.Reductive.RegularSlice

/-!
# Point derivations of `O(U±)` and `O(K)` at `e` as Lie subalgebras (C2(d), part (a))

* `pointDerBialgEquiv f hf`: for a surjective bialgebra map `f : H → Q`, point derivations of
  `Q` at its counit are the derivations of `Lie G` vanishing on `ker f`.
* `pointDerSliceEquiv`: `pointDer (counit of H ⧸ U⁺) ≃ (sliceIdeal π N ψ).lieSubalgebra`.
* `pointDerCompEquiv`: `pointDer (counit of compAlg π N) ≃ vanishingDer (compIdeal π N)` (`Lie K`).
-/

namespace AlgMag.Reductive

open Magnetism TauCeti

universe u

section Generic

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [Bialgebra k H]

local notation "Cv" => TauCeti.Bialgebra.CounitAlgebra k H k

variable (k H) in
/-- Derivations in `Lie G` vanishing on `I`. -/
def vanishingDer (I : Ideal H) : Submodule k (Derivation k H Cv) where
  carrier := {d | ∀ x ∈ I, d x = 0}
  add_mem' hd he x hx := by rw [Derivation.add_apply, hd x hx, he x hx, add_zero]
  zero_mem' x _ := rfl
  smul_mem' c d hd x hx := by rw [Derivation.smul_apply, hd x hx]; exact smul_zero c

/-- Restriction of `pointDerCounitEquiv` to derivations vanishing on `I`. -/
noncomputable def pointDerVanishingEquiv (I : Ideal H) :
    pointDerVanishing (_root_.Bialgebra.counitAlgHom k H) I ≃ₗ[k] vanishingDer k H I where
  toFun D := ⟨pointDerCounitEquiv k H D.1, fun x hx => by
    change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k H k).symm (D.1.1 x) = 0
    rw [D.2 x hx, map_zero]⟩
  invFun d := ⟨(pointDerCounitEquiv k H).symm d.1, fun x hx => by
    change TauCeti.Bialgebra.CounitAlgebra.algEquivSelf k H k (d.1 x) = 0
    rw [d.2 x hx, map_zero]⟩
  map_add' _ _ := by ext1; exact map_add _ _ _
  map_smul' _ _ := by ext1; exact map_smul _ _ _
  left_inv D := by ext1; exact (pointDerCounitEquiv k H).symm_apply_apply D.1
  right_inv d := by ext1; exact (pointDerCounitEquiv k H).apply_symm_apply d.1

/-- Transport of `pointDerVanishing` along an equality of points. -/
noncomputable def pointDerVanishingCongr {A : Type*} [CommRing A] [Algebra k A]
    {ε₁ ε₂ : A →ₐ[k] k} (h : ε₁ = ε₂) (I : Ideal A) :
    pointDerVanishing ε₁ I ≃ₗ[k] pointDerVanishing ε₂ I := by
  subst h; exact LinearEquiv.refl _ _

variable {Q : Type u} [CommRing Q] [Bialgebra k Q]

lemma counitAlgHom_comp_bialgHom (f : H →ₐc[k] Q) :
    (_root_.Bialgebra.counitAlgHom k Q).comp (f : H →ₐ[k] Q) =
      _root_.Bialgebra.counitAlgHom k H := by
  ext x
  simp [_root_.Bialgebra.counitAlgHom_apply]

/-- **Point derivations of a surjective bialgebra quotient.** -/
noncomputable def pointDerBialgEquiv (f : H →ₐc[k] Q) (hf : Function.Surjective f) :
    pointDer (_root_.Bialgebra.counitAlgHom k Q) ≃ₗ[k]
      vanishingDer k H (RingHom.ker (f : H →ₐ[k] Q)) :=
  let hf' : Function.Surjective (f : H →ₐ[k] Q) := hf
  let e := Ideal.quotientKerAlgEquivOfSurjective hf'
  have hε : ((_root_.Bialgebra.counitAlgHom k Q).comp e.toAlgHom).comp
      (Ideal.Quotient.mkₐ k (RingHom.ker (f : H →ₐ[k] Q))) =
        _root_.Bialgebra.counitAlgHom k H := by
    rw [← counitAlgHom_comp_bialgHom f]
    ext x
    exact congrArg (_root_.Bialgebra.counitAlgHom k Q)
      (Ideal.quotientKerAlgEquivOfSurjective_mk hf' x)
  ((pointDerCongr e _).trans (pointDerQuotientEquiv _ _)).trans
    ((pointDerVanishingCongr hε _).trans (pointDerVanishingEquiv _))

end Generic

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable [Module.Finite k (TauCeti.Bialgebra.CotangentSpace k H)]

/-- **`Lie U⁺`**: point derivations of `H ⧸ U⁺` at `e`. -/
noncomputable def pointDerSliceEquiv (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ) :
    pointDer (_root_.Bialgebra.counitAlgHom k (H ⧸ (sliceIdeal π N ψ).toIdeal)) ≃ₗ[k]
      ((sliceIdeal π N ψ).lieSubalgebra (B := k)).toSubmodule :=
  (pointDerBialgEquiv (_root_.Bialgebra.Quotient.mkBialgHom (sliceIdeal π N ψ).toIdeal)
      Ideal.Quotient.mk_surjective).trans
    (LinearEquiv.ofEq _ _ (by
      refine Submodule.ext fun d => ?_
      simp only [LieSubalgebra.mem_toSubmodule, HopfIdeal.mem_lieSubalgebra_iff]
      change (∀ x ∈ RingHom.ker (Ideal.Quotient.mkₐ k (sliceIdeal π N ψ).toIdeal), d x = 0) ↔ _
      refine forall_congr' fun x => imp_congr_left ?_
      exact Ideal.Quotient.eq_zero_iff_mem))

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- **`Lie K`**: point derivations of `O(K) = compAlg π N` at `e`. -/
noncomputable def pointDerCompEquiv (N : Magnet (Additive X)) :
    pointDer (_root_.Bialgebra.counitAlgHom k (compAlg π N)) ≃ₗ[k]
      vanishingDer k H (compIdeal π N) :=
  pointDerBialgEquiv (compMk π N) (compMk_surjective π N)

end AlgMag.Reductive
