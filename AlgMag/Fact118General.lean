/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Final3Fact118

/-!
# Fact 11.8 and Lemma 11.9, at the printed generality

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), pp. 174-175. Printed context (proof of
Prop 11.7): `T = Spec R` affine, `Tbar = Spec (R/I)`, `Tbar → T` a first order thickening; here
`ι : D → D₁` surjective with square-zero kernel.

* `fact118_affine`: the push-out is an affine scheme (clause (B)).
* `fact118_equivariant_pushout`: existence, uniqueness and equivariance of the glued map for any
  algebraic space with `D(M)`-action and equivariant `f, g` (clauses (A), (C), (D) together).
* `lemma119`: `Spec (pushoutRing) → A(N)_T` is a first order thickening, as a morphism of schemes.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Fact118General

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes AlgMag.SpacesLift AlgMag.Final3Fact118

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]
  [SM B M] [DecidableEq M]
  (N : AddSubmonoid M) {F : AddSubmonoid M} (hF : IsFace F N)
  {D D₁ : Type u} [CommRing D] [CommRing D₁] [SR B D] [SR B D₁] (ι : D →+* D₁)

omit [SM B M] [DecidableEq M] [SR B D] [SR B D₁] in
/-- **Fact 11.8 (B)**: the push-out is an affine scheme. -/
theorem fact118_affine : IsAffine (Spec (CommRingCat.of (pushoutRing hF ι))) := inferInstance

omit [SM B M] [SR B D] [SR B D₁] in
/-- **Lemma 11.9**: the morphism `A(F)_T ⊔_{A(F)_Tbar} A(N)_Tbar → A(N)_T` is a first order
thickening of schemes. -/
theorem lemma119 (hι : Function.Surjective ι) (hsq : ∀ x y, ι x = 0 → ι y = 0 → x * y = 0) :
    Stacks.Thickenings.IsFirstOrderThickening (Spec.map (CommRingCat.ofHom (pushoutMap hF ι))) :=
  thick_of_ring _ (pushoutMap_surjective hF ι hι) (pushoutMap_mul_eq_zero hF ι hsq)

/-- **Fact 11.8**, push-out in the category of algebraic spaces with `D(M)`-equivariant morphisms:
for an algebraic space `X` with `D(M)`-action and `D(M)`-equivariant `f : A(F)_T → X`,
`g : A(N)_Tbar → X` agreeing on `A(F)_Tbar`, there is a unique `k` with `k ∘ ν₁ = f`, `k ∘ ν₂ = g`,
and `k` is `D(M)`-equivariant. -/
theorem fact118_equivariant_pushout (hι : Function.Surjective ι)
    (hsq : ∀ x y, ι x = 0 → ι y = 0 → x * y = 0)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (aX : AAction (fppfO B S hS) M X)
    (hX : IsAlgebraicSpace B S hS X)
    (s : Spec (CommRingCat.of (pushoutRing hF ι)) ⟶ S)
    (s₁ : Spec (CommRingCat.of (AddMonoidAlgebra (pushoutRing hF ι) M)) ⟶ S)
    (hρ : sp (coactP (M := M) N hF ι hι) ≫ s = s₁) (hc : sp (cst (pushoutRing hF ι) M) ≫ s = s₁)
    (f : X.obj (op (Sv B hS (sp (pFst N hF ι) ≫ s))))
    (g : X.obj (op (Sv B hS (sp (pSnd N hF ι) ≫ s))))
    (h : pb X (svHom B hS (AddMonoidAlgebra.mapRingHom F ι)
        (rfl : _ = sp (AddMonoidAlgebra.mapRingHom F ι) ≫ sp (pFst N hF ι) ≫ s)) f =
      pb X (svHom B hS (faceRingHom hF D₁) (by
        rw [← Category.assoc, ← Category.assoc, ← sp_comp, ← sp_comp]
        exact congrArg (fun φ => sp φ ≫ s) (RingHom.ext fun z => z.2.symm))) g)
    (hf : pb X (svHom B hS (coactN (M := M) F D) (fstR N hF ι hι s s₁ hρ)) f =
      ss aX (eS B hS _ (eU _ M)) (pb X (svHom B hS (cst _ M) (fstC N hF ι s s₁ hc)) f))
    (hg : pb X (svHom B hS (coactN (M := M) N D₁) (sndR N hF ι hι s s₁ hρ)) g =
      ss aX (eS B hS _ (eU _ M)) (pb X (svHom B hS (cst _ M) (sndC N hF ι s s₁ hc)) g)) :
    ∃! k : X.obj (op (Sv B hS s)),
      pb X (svHom B hS (pFst N hF ι) rfl) k = f ∧ pb X (svHom B hS (pSnd N hF ι) rfl) k = g ∧
      pb X (svHom B hS (coactP (M := M) N hF ι hι) hρ) k =
        ss aX (eS B hS s₁ (eU (pushoutRing hF ι) M)) (pb X (svHom B hS (cst _ M) hc) k) := by
  obtain ⟨k, ⟨hk₁, hk₂⟩, hu⟩ := fact118_pushout_spaces N hF ι hι hsq s X hX f g h
  refine ⟨k, ⟨hk₁, hk₂, ?_⟩, fun k' hk' => hu k' ⟨hk'.1, hk'.2.1⟩⟩
  refine fact118_equivariant_desc N hF ι aX hι s s₁ hsq hρ hc hX k ?_ ?_
  · rw [hk₁]; exact hf
  · rw [hk₂]; exact hg

end AlgMag.Fact118General
