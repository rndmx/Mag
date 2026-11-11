/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesLift

/-!
# Corollary 10.3 of *Algebraic Magnetism*: the printed square for algebraic spaces

`X' = Spec A₁`, `X = Spec A` with `A₁ → A` a square-zero surjection (the printed statement needs `X'` affine), with
actions `ρ`, `ρ₀` of `D(M)`, `Y → Z` an equivariant formally smooth morphism of algebraic spaces. The commutative square
of equivariant maps has an equivariant filler. The non-equivariant filler comes from formal smoothness; the
equivariant one from the integration of `g⁻¹ α g` (`AlgMag.SpacesLift.exists_equivariant_of_lift`). The printed route,
the torsor `LiftTorsor` under `p_* Hom(a^*Ω, C)`, is carried out for `Y`, `Z` schemes in `AlgMag.Sec10PrintedMain`.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]
  {A₁ A : Type u} [CommRing A₁] [CommRing A] [SR B A₁] [SR B A] [SM B M]

/-- **Corollary 10.3**, `X'` affine, `Y`, `Z` algebraic spaces. -/
theorem cor103_spaces (φ : A₁ →+* A) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (t : Spec (CommRingCat.of A₁) ⟶ S)
    (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
    (hρt : sp ρ ≫ t = sp (cst A₁ M) ≫ t)
    (hρφ : ∀ a, AddMonoidAlgebra.mapRingHom M φ (ρ a) = ρ₀ (φ a))
    (hco : ∀ a, AddMonoidAlgebra.mapRingHom M ρ (ρ a) = diag A₁ M (ρ a))
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (hQ : IsAlgebraicSpace B S hS Q)
    {aY : AAction (fppfO B S hS) M P} {aZ : AAction (fppfO B S hS) M Q} (f : EquivariantHom aY aZ)
    (hf : Space.FormallySmooth f.hom)
    (a : P.obj (op (Sv B hS (sp φ ≫ t)))) (b : Q.obj (op (Sv B hS t)))
    (hw : f.hom.app _ a = pb Q (svHom B hS φ rfl) b)
    (h₀ρ : sp ρ₀ ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (h₀c : sp (cst A M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (ha : pb P (svHom B hS ρ₀ h₀ρ) a = ss aY (eS B hS _ (eU A M)) (pb P (svHom B hS (cst A M) h₀c) a))
    (hb : pb Q (svHom B hS ρ hρt) b =
      ss aZ (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M)) (pb Q (svHom B hS (cst A₁ M) rfl) b)) :
    ∃ l : P.obj (op (Sv B hS t)), pb P (svHom B hS φ rfl) l = a ∧ f.hom.app _ l = b ∧
      pb P (svHom B hS ρ hρt) l =
        ss aY (eS B hS (sp (cst A₁ M) ≫ t) (eU A₁ M)) (pb P (svHom B hS (cst A₁ M) rfl) l) := by
  obtain ⟨α, hα₁, hα₂⟩ := hf _ _ (inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsAffine (Spec _))) (svHom B hS φ (s := t) rfl)
    (sqZero_svHom φ hs hq) a b hw
  exact exists_equivariant_of_lift φ hs hq t ρ ρ₀ hρt hρφ hco hP hQ f a b α hα₁ hα₂ h₀ρ h₀c ha hb

end AlgMag.SpacesLift

#print axioms AlgMag.SpacesLift.cor103_spaces
