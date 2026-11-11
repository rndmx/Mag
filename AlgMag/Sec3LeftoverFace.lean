/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec2OverB
import AlgMag.Sec12Topology
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# Algebraic Magnetism, Fact 3.16 for algebraic spaces and Definition 2.11

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026).

* `AlgMag.fact316_spaces`: Fact 3.16 with `X^N`, `X^F` algebraic spaces, by Stacks 03KP (3), the
  printed citation 0AGC being the same statement for schemes.
* `AlgMag.OverB.eS`, `AlgMag.OverB.eB`: the trivial monoid objects of Definition 2.11 (ii), (iii).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space Magnetism

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Fact316

variable {M : Type u} [AddCommMonoid M]
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M X}
variable {N F : AddSubmonoid M} {ZN ZF : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Fact 3.16**, algebraic spaces. If `X^N`, `X^F` are representable and `p_{N,F} : X^N → X^F` is
separated, then `ι_{F,N} : X^F → X^N` is a closed immersion. -/
theorem fact316_spaces (rN : RepresentsAttractor act N ZN) (rF : RepresentsAttractor act F ZF)
    (hF : IsFace F N) (hsep : IsSeparated B S hS (repFace rN rF hF)) :
    IsClosedImmersion B S hS (repMagnet rN rF hF.le) :=
  isClosedImmersion_of_isSeparated_of_section B S hS _ hsep _ (repMagnet_comp_repFace rN rF hF)

end Fact316

namespace OverB

/-- **Definition 2.11 (ii)**: `e_S = 𝔸(0)_S`. -/
noncomputable abbrev eS (S : Scheme.{u}) : Over S := GB.A PUnit.{u + 1} S

/-- `𝔸(0)_S` has exactly one `T`-point: `e_S` is `S` as a scheme over `S`. -/
noncomputable def eS_pts (T : Over S) : Unique (T ⟶ eS S) where
  default := (GB.pts T).symm 1
  uniq f := (GB.pts T).injective (by
    rw [Equiv.apply_symm_apply]
    refine MonoidHom.ext fun n => ?_
    have hn : n = 1 := Subsingleton.elim _ _
    subst hn
    simp)

variable (Bs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Definition 2.11 (iii)**: `e_B = 𝔸(0)_B`. -/
noncomputable abbrev eB : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := AB Bs PUnit.{u + 1}

/-- `e_B → B` is an isomorphism: `e_B` is `B` as an algebraic space over `B`. -/
instance isIso_pr_eB : IsIso (pr Bs PUnit.{u + 1}) := by
  have : ∀ U, IsIso ((pr Bs PUnit.{u + 1}).app U) := fun U => by
    rw [isIso_iff_bijective]
    constructor
    · rintro ⟨a, x⟩ ⟨b, y⟩ h
      have hab : a = b := Subsingleton.elim _ _
      subst hab
      exact Prod.ext rfl h
    · intro x
      exact ⟨(1, x), rfl⟩
  exact NatIso.isIso_of_isIso_app _

end OverB

end AlgMag
