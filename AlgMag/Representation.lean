/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Foundations

/-!
# Size and universes for attractors

Two points separate `AlgMag.attractor` from the statements of the paper.

* The values of a point of `X^N` are indexed by all objects of the site. If `𝔸(N)_T` is an object of
  the site, `AlgMag.attractorPtEquivOfUniversal` shows that such a point is the same as an element
  of `X(𝔸(N)_T)` satisfying equivariance, i.e. an equivariant morphism as in Definition 3.1.
* The attractor lands in a larger universe than the presheaves of the Stacks library.
  `AlgMag.RepresentsAttractor` says that a presheaf in the right universe has the same points.
-/

open CategoryTheory Opposite

universe u v

namespace AlgMag

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : Type*} [AddCommMonoid M] {F : Cᵒᵖ ⥤ Type u}

variable (𝒪) in
/-- `𝔸(N)_T` as an object of the site: an object over `T` with a universal point of `𝔸(N)`. -/
structure UniversalPoint (N : AddSubmonoid M) (T : C) where
  /-- The object `𝔸(N)_T`. -/
  P : C
  /-- The structure morphism to `T`. -/
  π : P ⟶ T
  /-- The universal point. -/
  u : APt 𝒪 N (op P)
  /-- The classifying morphism of a point. -/
  lift : ∀ {T' : C} (_ : T' ⟶ T), APt 𝒪 N (op T') → (T' ⟶ P)
  lift_π : ∀ {T' : C} (t : T' ⟶ T) (a : APt 𝒪 N (op T')), lift t a ≫ π = t
  res_lift : ∀ {T' : C} (t : T' ⟶ T) (a : APt 𝒪 N (op T')), APt.res (lift t a).op u = a
  uniq : ∀ {T' : C} (t : T' ⟶ T) (a : APt 𝒪 N (op T')) (s : T' ⟶ P),
    s ≫ π = t → APt.res s.op u = a → s = lift t a

variable {act : AAction 𝒪 M F} {N : AddSubmonoid M} {T : C}

/-- A point of the attractor is determined by its value at the universal point. -/
lemma AttractorPt.app_eq_of_universal (U : UniversalPoint 𝒪 N T) (φ : AttractorPt act N T)
    {T' : C} (t : T' ⟶ T) (a : APt 𝒪 N (op T')) :
    φ.app t a = F.map (U.lift t a).op (φ.app U.π U.u) := by
  have h := φ.naturality (U.lift t a) U.π U.u
  rwa [U.lift_π, U.res_lift] at h

lemma UniversalPoint.lift_comp (U : UniversalPoint 𝒪 N T) {T' T'' : C} (s : T'' ⟶ T')
    (t : T' ⟶ T) (a : APt 𝒪 N (op T')) :
    U.lift (s ≫ t) (APt.res s.op a) = s ≫ U.lift t a := by
  refine (U.uniq _ _ _ ?_ ?_).symm
  · rw [Category.assoc, U.lift_π]
  · rw [op_comp, APt.res_comp, U.res_lift]

lemma UniversalPoint.lift_self (U : UniversalPoint 𝒪 N T) : U.lift U.π U.u = 𝟙 U.P := by
  refine (U.uniq _ _ _ (Category.id_comp _) ?_).symm
  simp

/-- **Definition 3.1 on a site.** If `𝔸(N)_T` is an object of the site, a `T`-point of `X^N` is an
element of `X(𝔸(N)_T)` which is equivariant, that is, an equivariant `T`-morphism
`𝔸(N)_T → X_T`. -/
def attractorPtEquivOfUniversal (U : UniversalPoint 𝒪 N T) :
    AttractorPt act N T ≃ { x : F.obj (op U.P) // ∀ {T' : C} (t : T' ⟶ T) (h : APt 𝒪 M (op T'))
      (a : APt 𝒪 N (op T')), F.map (U.lift t (APt.toMagnet N h * a)).op x =
        act.smul h (F.map (U.lift t a).op x) } where
  toFun φ := ⟨φ.app U.π U.u, fun t h a => by
    rw [← φ.app_eq_of_universal U, ← φ.app_eq_of_universal U]
    exact φ.equivariant t h a⟩
  invFun x :=
    { app := fun t a => F.map (U.lift t a).op x.1
      naturality := fun s t a => by
        rw [U.lift_comp, op_comp, Functor.map_comp_apply]
      equivariant := fun t h a => x.2 t h a }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    exact (φ.app_eq_of_universal U t a).symm
  right_inv x := by
    refine Subtype.ext ?_
    change F.map (U.lift U.π U.u).op x.1 = x.1
    rw [U.lift_self]
    simp

variable (act N) in
/-- A presheaf `Z` in the universe of the Stacks library represents the attractor `X^N`: it has the
same points, naturally. -/
structure RepresentsAttractor (Z : Cᵒᵖ ⥤ Type u) where
  /-- The bijection on `T`-points. -/
  equiv : ∀ T : C, Z.obj (op T) ≃ AttractorPt act N T
  naturality : ∀ {T T' : C} (s : T' ⟶ T) (z : Z.obj (op T)),
    equiv T' (Z.map s.op z) = (equiv T z).baseChange s

end AlgMag
