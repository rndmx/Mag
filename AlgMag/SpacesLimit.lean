/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec6Atlas
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Limits of algebraic spaces: reduction of Theorems 6.8 and A.1 to finite type over `Z`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126-201, proofs of Theorems A.1, A.2.

* `AlgMag.SpacesLimit.exists_isZFPRAtlas_of_isPullback`: an FPR atlas of a stage gives one of the
  base change, by Lemma 6.7 (i).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLimit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The base change `a : X → X_λ` of an affine morphism of the base is affine. -/
theorem isAffine_of_isPullback {X Xk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V Vk : BigFppfOver B S hS} {π : V ⟶ Vk} {p : X ⟶ yoneda.obj V} {pk : Xk ⟶ yoneda.obj Vk}
    {a : X ⟶ Xk} (hpb : IsPullback p a (yoneda.map π) pk) (hπ : IsAffineHom ((SCH).map π)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (SCH))) a :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb
    ((Space.presheaf_yoneda_map_iff B S hS inferInstance π).2 hπ)

variable {X Xk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V Vk Uk : BigFppfOver B S hS} {π : V ⟶ Vk}
  {p : X ⟶ yoneda.obj V} {pk : Xk ⟶ yoneda.obj Vk} {a : X ⟶ Xk}
  {actX : AAction (fppfO B S hS) M X} {actXk : AAction (fppfO B S hS) M Xk}
  {actUk : AAction (fppfO B S hS) M (yoneda.obj Uk)} {f : yoneda.obj Uk ⟶ Xk} {Z : AddSubgroup M}

/-- **Base change of atlases** (the last step of the proof of Theorem 6.8/A.2). -/
theorem exists_isZFPRAtlas_of_isPullback (hpb : IsPullback p a (yoneda.map π) pk)
    (hπ : IsAffineHom ((SCH).map π)) (ha : IsEquivariant actX actXk a)
    (h : IsZFPRAtlas actUk actXk f Z) : ExistsZFPRAtlas actX Z :=
  ⟨_, _, _, lemma67_i (isAffine_of_isPullback hpb hπ) ha h⟩

end AlgMag.SpacesLimit
