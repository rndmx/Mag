/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9General
import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.Basic
import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite
import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedAffineSections

/-!
# Bridge: Stacks quasi-coherent modules give `AlgMag.S9.IsQCoh`

For `G` a quasi-coherent module on the scheme `S`, the presheaf `T ↦ Γ(T, T.hom⁺ G)` on `S`-schemes
(Tag 03DS) is an `AlgMag.S9.IsQCoh` module. So §9 applies to every quasi-coherent module on `S`, not
only to modules given by the axioms of `IsQCoh`.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgMag.Leftover

open AlgMag.S9

variable {S : Scheme.{u}} (G : S.Modules) [G.IsQuasicoherent]

omit G in
/-- A base change, from a bijective map on the tensor product with the expected values. -/
lemma isBaseChange_of_bijective {A B E E' : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup E] [Module A E] [AddCommGroup E'] [Module A E'] [Module B E'] [IsScalarTower A B E']
    (f : E →ₗ[A] E') (Ψ : B ⊗[A] E →+ E') (hb : Function.Bijective Ψ)
    (h : ∀ c m, Ψ (c ⊗ₜ[A] m) = c • f m) : IsBaseChange B f := by
  unfold IsBaseChange IsTensorProduct
  convert hb using 1
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c m => rw [h]; simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit G in
/-- `AlgMag.S9.IsBC`, from a bijective map on the tensor product. -/
lemma isBC_of {A B M M' : Type u} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module B M'] (φ : A →+* B) (f : M →+ M')
    (hf : ∀ (r : A) (x : M), f (r • x) = φ r • f x)
    (Ψ : letI := φ.toAlgebra; B ⊗[A] M →+ M')
    (hb : Function.Bijective Ψ)
    (h : letI := φ.toAlgebra; ∀ (c : B) (m : M), Ψ (c ⊗ₜ[A] m) = c • f m) : IsBC φ f hf := by
  letI := φ.toAlgebra
  letI : Module A M' := Module.compHom M' φ
  haveI : IsScalarTower A B M' := ⟨fun r s x => by
    change (φ r * s) • x = φ r • s • x
    rw [mul_smul]⟩
  exact isBaseChange_of_bijective _ Ψ hb h

/-- The `𝒪`-module `T ↦ Γ(T, T.hom⁺ G)` on `S`-schemes. -/
noncomputable def assocPMod : PMod (GB.overO S) where
  obj U := Γ((Scheme.Modules.pullback U.unop.hom).obj G, ⊤)
  grp U := inferInstance
  mod U := inferInstanceAs (Module Γ(U.unop.left, ⊤) Γ((Scheme.Modules.pullback U.unop.hom).obj G, ⊤))
  map f := (pullbackSectionsMap G f.unop).hom
  map_smul f r x := pullbackSectionsMap_smul G f.unop r x
  map_id U x := by
    have := (quasiCoherentPresheafFunctor S G).map_id U
    exact congrArg (fun k => k.hom x) this
  map_comp f g x := by
    have := (quasiCoherentPresheafFunctor S G).map_comp f g
    exact congrArg (fun k => k.hom x) this

/-- **Bridge.** A Stacks quasi-coherent module on `S` gives a module with `IsQCoh`: the Zariski sheaf
condition is `quasiCoherentPresheaf_isSheaf_zariski`, base change `exists_bijective_sectionsBaseChange`
(Tag 03DX). -/
theorem isQCoh_assocPMod : IsQCoh (assocPMod G) where
  sheaf := by
    have h1 : Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
        (quasiCoherentPresheafFunctor S G ⋙ CategoryTheory.forget AddCommGrpCat) :=
      (Presheaf.isSheaf_of_iso_iff (quasiCoherentPresheafIsoPresheafHom G)).mpr
        (isSheaf_presheafHom fpqcDescentOfQuasicoherentHoms (Scheme.unitModule S) G)
    have h2 := isSheaf_zariski_of_isSheaf_fpqc S _ h1
    exact (isSheaf_iff_isSheaf_of_type _ _).1 h2
  base_change := by
    intro T T' s _ _
    let φ : Γ(T.left, ⊤) →+* Γ(T'.left, ⊤) := s.left.appTop.hom
    letI := φ.toAlgebra
    letI iE : Module Γ(T.left, ⊤) Γ((Scheme.Modules.pullback T'.hom).obj G, ⊤) :=
      Module.compHom _ φ
    obtain ⟨Ψ, hΨ, hΨ'⟩ := Stacks.Adequate.exists_bijective_sectionsBaseChange S G s
      (R := Γ(T.left, ⊤)) (Cc := Γ(T'.left, ⊤))
      (Algebra.toModule) inferInstance φ
      (by
        simp only [φ, Scheme.Hom.appLE, Scheme.Hom.appTop]
        congr 1
        exact (Category.comp_id _).symm.trans (congrArg _ (T'.left.presheaf.map_id _).symm))
      (RingEquiv.refl _) (AddEquiv.refl _)
      (fun r c => rfl) (fun r m => rfl)
    exact isBC_of φ (M := Γ((Scheme.Modules.pullback T.hom).obj G, ⊤))
      (M' := Γ((Scheme.Modules.pullback T'.hom).obj G, ⊤)) _ _ Ψ hΨ fun c m => hΨ' c m

end AlgMag.Leftover

#print axioms AlgMag.Leftover.isQCoh_assocPMod
