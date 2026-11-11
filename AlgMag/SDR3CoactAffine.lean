/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3CoactGamma
import AlgMag.SDR3CoactRing
import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# Lemma D, Step 3: the affine case of `Γ(V × D(Λ)) = Γ(V)[Λ]`; site membership (gap G4)

A base change of `Spec A[Λ] → Spec A` satisfies the affine hypothesis of
`SDR3Coact_φ_bijective`. G4: a locally of finite type scheme over a site scheme is in the site.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgMag.SD

section Ring

variable {Λ : Type u} [AddCommGroup Λ]

/-- A pushout of `A → A[Λ]` is `Rb → Rb[Λ]`. -/
theorem SDR3Coact_pushout_bijective {R0 R1 Rb T : CommRingCat.{u}} {f : R0 ⟶ R1} {g : R0 ⟶ Rb} {i : R1 ⟶ T}
    {j : Rb ⟶ T} (hP : IsPushout f g i j) {A : Type u} [CommRing A] (α : A ≃+* R0)
    (β : AddMonoidAlgebra A Λ ≃+* R1) (hβ : ∀ x, β (AddMonoidAlgebra.single 0 x) = f.hom (α x))
    (t : Multiplicative Λ →* T) (ht : ∀ d, t d = i.hom (β (AddMonoidAlgebra.single (Multiplicative.toAdd d) 1))) :
    Function.Bijective (SDR3Coact_lift j.hom t) := by
  let gα : A →+* Rb := g.hom.comp α.toRingHom
  let u : R1 ⟶ CommRingCat.of (AddMonoidAlgebra Rb Λ) :=
    CommRingCat.ofHom ((AddMonoidAlgebra.mapRingHom Λ gα).comp β.symm.toRingHom)
  let v : Rb ⟶ CommRingCat.of (AddMonoidAlgebra Rb Λ) := CommRingCat.ofHom AddMonoidAlgebra.singleZeroRingHom
  have huv : f ≫ u = g ≫ v := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    obtain ⟨x, rfl⟩ := α.surjective r
    change AddMonoidAlgebra.mapRingHom Λ gα (β.symm (f.hom (α x))) = AddMonoidAlgebra.single 0 (g.hom (α x))
    rw [← hβ, RingEquiv.symm_apply_apply]
    simp [gα]
  let D : T ⟶ CommRingCat.of (AddMonoidAlgebra Rb Λ) := hP.desc u v huv
  have hDi : ∀ y, D.hom (i.hom y) = u.hom y := fun y => congrArg (fun k => k.hom y) (hP.inl_desc u v huv)
  have hDj : ∀ y, D.hom (j.hom y) = v.hom y := fun y => congrArg (fun k => k.hom y) (hP.inr_desc u v huv)
  have hij : ∀ x, j.hom (g.hom x) = i.hom (f.hom x) := fun x => (congrArg (fun k => k.hom x) hP.w).symm
  have hΦD : ∀ y, SDR3Coact_lift j.hom t (D.hom y) = y := by
    let Φ : CommRingCat.of (AddMonoidAlgebra Rb Λ) ⟶ T := CommRingCat.ofHom (SDR3Coact_lift j.hom t)
    have : D ≫ Φ = 𝟙 T := by
      refine hP.hom_ext ?_ ?_
      · rw [← Category.assoc, hP.inl_desc, Category.comp_id]
        ext y
        obtain ⟨w, rfl⟩ := β.surjective y
        change SDR3Coact_lift j.hom t (AddMonoidAlgebra.mapRingHom Λ gα (β.symm (β w))) = i.hom (β w)
        rw [RingEquiv.symm_apply_apply]
        induction w using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => simp only [map_add, ha, hb]
        | single d r =>
          rw [AddMonoidAlgebra.mapRingHom_single, SDR3Coact_lift_single, ht]
          change j.hom (g.hom (α r)) * _ = _
          rw [hij, ← hβ, ← map_mul, ← map_mul, AddMonoidAlgebra.single_mul_single]
          simp
      · rw [← Category.assoc, hP.inr_desc, Category.comp_id]
        ext y
        change SDR3Coact_lift j.hom t (AddMonoidAlgebra.single 0 y) = j.hom y
        rw [SDR3Coact_lift_single]
        have : t (Multiplicative.ofAdd 0) = 1 := map_one t
        rw [this, mul_one]
    intro y
    exact congrArg (fun k => k.hom y) this
  have hDΦ : ∀ w, D.hom (SDR3Coact_lift j.hom t w) = w := by
    intro w
    induction w using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single d r =>
      rw [SDR3Coact_lift_single, map_mul, hDj, ht, hDi]
      change AddMonoidAlgebra.single 0 r * AddMonoidAlgebra.mapRingHom Λ gα (β.symm (β _)) = _
      rw [RingEquiv.symm_apply_apply, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.single_mul_single]
      simp [gα]
  exact ⟨Function.LeftInverse.injective hDΦ, Function.RightInverse.surjective hΦD⟩

end Ring

section Site

/-- **G4**: a scheme locally of finite type over a scheme of the site is in the site (étale over it, in particular). -/
theorem SDR3Coact_contains_of_lft {B : BigFppfSite.{u}} {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [CompactSpace X]
    (hY : B.Contains Y) : B.Contains X :=
  (Scheme.size_le_of_locallyOfFiniteType f).trans_lt hY

/-- **G4**, algebras: a finite type (for instance étale) `R`-algebra `R'` is in the site if `R` is. -/
theorem SDR3Coact_contains_of_finiteType {B : BigFppfSite.{u}} {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    [Algebra.FiniteType R R'] (hR : B.Contains (Spec (.of R))) : B.Contains (Spec (.of R')) := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  exact SDR3Coact_contains_of_lft (Spec.map (CommRingCat.ofHom (algebraMap R R'))) hR

end Site

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Coact_pushout_bijective
#print axioms AlgMag.SD.SDR3Coact_contains_of_lft
#print axioms AlgMag.SD.SDR3Coact_contains_of_finiteType
