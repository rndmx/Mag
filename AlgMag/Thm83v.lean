/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec8Limits

/-!
# Theorem 8.3 (v), relative form

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Theorem 8.3 (v): "If `X/S` is quasi-compact
then `X^N/S` is quasi-compact." Here quasi-compactness is that of the morphism to `S`, so `S` is arbitrary.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] countable_of_fg83

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}

/-- **Theorem 8.3 (v)** on the representing space: if `X → S` is quasi-compact, so is `X^N → S`. -/
theorem thm83_v_of_repr (hq : Space.IsQuasiCompact B S hS (terminal.from X)) {N : AddSubmonoid M}
    (r : Thm83Repr actX N) : Space.IsQuasiCompact B S hS (terminal.from r.P) :=
  isQuasiCompact_terminal_of_presheaf (P := @AlgebraicGeometry.IsAffineHom)
    (fun g _ => inferInstance) inferInstance r.affine_c
    (isQuasiCompact_terminal_of_presheaf (P := @IsClosedImmersion)
      (fun g _ => inferInstance) inferInstance r.closed_i hq)

/-- **Theorem 8.3 (v)**, under the hypotheses of Theorem 8.3 (agreed correction: `X` separated, and `N`
finitely generated or `X` limit preserving): `X^N` is representable, and if `X → S` is quasi-compact,
so is `X^N → S`. -/
theorem thm83_v (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (N : AddSubmonoid M)
    (hat : ExistsZFPRAtlas actX (unitsSub N)) (hb : N.FG ∨ IsLimitPreserving X) :
    ∃ r : Thm83Repr actX N,
      Space.IsQuasiCompact B S hS (terminal.from X) →
        Space.IsQuasiCompact B S hS (terminal.from r.P) := by
  obtain ⟨r⟩ := thm83_repr hX hsep N hat hb
  exact ⟨r, fun hq => thm83_v_of_repr hq r⟩

end AlgMag

#print axioms AlgMag.thm83_v
