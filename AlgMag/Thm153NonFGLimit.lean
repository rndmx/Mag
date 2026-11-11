/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.GroupTheory.Finiteness
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Opposites

/-!
# `A(P) = lim A(δ⁻¹ Γ_α)` (Lemma 1.1 of `notes/thm153-wall.md`)

`δ : P → Γ`, `Γ_α` running over the finitely generated subgroups of `Γ`. `R[P]` is the filtered colimit
of the rings `R[δ⁻¹ Γ_α]` in `CommRingCat`, so `Spec R[P]` is the cofiltered limit of the
`Spec R[δ⁻¹ Γ_α]` in schemes (`Spec` preserves limits).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.NonFG

variable {Γ : Type u} [AddCommGroup Γ]

/-- The finitely generated subgroups of `Γ`, directed by inclusion. -/
abbrev FGSub (Γ : Type u) [AddCommGroup Γ] := {G : AddSubgroup Γ // G.FG}

instance : IsDirectedOrder (FGSub Γ) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, AddSubgroup.FG.sup a.2 b.2⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

instance : Nonempty (FGSub Γ) := ⟨⟨⊥, ⟨∅, by simp⟩⟩⟩

variable (R : Type u) [CommRing R] {P : Type u} [AddCommMonoid P] (δ : P →+ Γ)

/-- `δ⁻¹ Γ_α`. -/
abbrev preim (G : FGSub Γ) : AddSubmonoid P := G.1.toAddSubmonoid.comap δ

lemma preim_mono {G H : FGSub Γ} (h : G ≤ H) : preim δ G ≤ preim δ H := fun _ hx => h hx

lemma md_comp {A B C : Type u} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] (f : A → B)
    (g : B → C) (x : AddMonoidAlgebra R A) :
    AddMonoidAlgebra.mapDomain g (AddMonoidAlgebra.mapDomain f x) =
      AddMonoidAlgebra.mapDomain (g ∘ f) x := by
  simp only [AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff]
  rw [← Finsupp.mapDomain_comp]

lemma md_id {A : Type u} [AddCommMonoid A] (x : AddMonoidAlgebra R A) :
    AddMonoidAlgebra.mapDomain id x = x := by
  simp [AddMonoidAlgebra.mapDomain]

/-- `Γ_α ↦ R[δ⁻¹ Γ_α]`. -/
noncomputable def ringSys : FGSub Γ ⥤ CommRingCat.{u} where
  obj G := CommRingCat.of (AddMonoidAlgebra R (preim δ G))
  map {G H} h := CommRingCat.ofHom
    (AddMonoidAlgebra.mapDomainRingHom R (AddSubmonoid.inclusion (preim_mono δ h.le)))
  map_id G := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    exact md_id R x
  map_comp {G H K} f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change AddMonoidAlgebra.mapDomain _ x =
      AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.mapDomain _ x)
    exact (md_comp R (AddSubmonoid.inclusion (preim_mono δ f.le))
      (AddSubmonoid.inclusion (preim_mono δ g.le)) x).symm

/-- The cocone with point `R[P]`. -/
noncomputable def ringCocone : Cocone (ringSys R δ) where
  pt := CommRingCat.of (AddMonoidAlgebra R P)
  ι :=
    { app G := CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R (preim δ G).subtype)
      naturality {G H} h := by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.mapDomain _ x) =
          AddMonoidAlgebra.mapDomain _ x
        exact md_comp R (AddSubmonoid.inclusion (preim_mono δ h.le)) (preim δ H).subtype x }

lemma mem_range_of_support' {Q : AddSubmonoid P} (x : AddMonoidAlgebra R P)
    (hx : ∀ p ∈ x.coeff.support, p ∈ Q) :
    x ∈ RingHom.range (AddMonoidAlgebra.mapDomainRingHom R Q.subtype) := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single x]
  refine Subring.sum_mem _ fun p hp => ?_
  exact ⟨AddMonoidAlgebra.single ⟨p, hx p hp⟩ (x.coeff p), by
    simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]⟩

/-- `R[P]` is the filtered colimit of the `R[δ⁻¹ Γ_α]`. -/
noncomputable def ringCocone_isColimit : IsColimit (ringCocone R δ) := by
  classical
  have : ReflectsColimit (ringSys R δ) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y h => ?_))
  · let t : Finset Γ := x.coeff.support.image δ
    let G : FGSub Γ := ⟨AddSubgroup.closure (t : Set Γ), ⟨t, rfl⟩⟩
    obtain ⟨xi, hxi⟩ := mem_range_of_support' R (Q := preim δ G) x fun p hp =>
      AddSubgroup.subset_closure (by simp [t]; exact ⟨p, Finsupp.mem_support_iff.1 hp, rfl⟩)
    exact ⟨G, xi, hxi.symm⟩
  · refine ⟨i, 𝟙 i, ?_⟩
    have hinj : Function.Injective
        (AddMonoidAlgebra.mapDomain (R := R) (preim δ i).subtype) :=
      AddMonoidAlgebra.mapDomain_injective Subtype.val_injective
    rw [hinj h]

/-- `Spec R[P]` is the cofiltered limit of the `Spec R[δ⁻¹ Γ_α]` in schemes. -/
noncomputable def specCone_isLimit :
    IsLimit (Scheme.Spec.mapCone (ringCocone R δ).op) :=
  isLimitOfPreserves Scheme.Spec (ringCocone_isColimit R δ).op

end AlgMag.NonFG

#print axioms AlgMag.NonFG.specCone_isLimit
