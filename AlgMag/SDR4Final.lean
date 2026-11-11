/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Bridge

/-!
# Lemma D for algebraic spaces, and Propositions 3.31 (ii), 3.32 (ii), 15.1, unconditional

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). The statements of `SDR3AsmFinal`, with `SDR3Asm_ChartInput`
discharged by `SDR4_chartInput`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- `SDLocS_InvChart X (Lat r)`, for an algebraic space. -/
theorem SDR4_invChart (hX : IsAlgebraicSpace B S hS X) (r : ℕ) : SDLocS_InvChart X (Lat.{u} r) :=
  SDR3Asm_invChart (SDR4_chartInput hX r)

/-- The hypothesis `hL` of `SDFinal`, for an algebraic space. -/
theorem SDR4_localFactorAll (hX : IsAlgebraicSpace B S hS X) : SDLocS_LocalFactorAll X :=
  SDR3Asm_localFactorAll fun r => SDR4_chartInput hX r

/-- **Proposition 3.32 (ii)** for an algebraic space. -/
theorem prop332_space_final (hX : IsAlgebraicSpace B S hS X) {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {aX : AAction (fppfO B S hS) M X} {N L : AddSubmonoid M} (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T) :=
  prop332_space hX (SDR4_localFactorAll hX) T

/-- **Proposition 3.31 (ii)** for an algebraic space. -/
theorem prop331_space_final (hX : IsAlgebraicSpace B S hS X) {M Z : Type u} [AddCommGroup M] [AddCommGroup Z] [AddGroup.FG M]
    [AddGroup.FG Z] {f : M →+ Z} {Y : AddSubmonoid Z} {aX : AAction (fppfO B S hS) M X} (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong aX : AttractorPt aX (Y.comap f) T → AttractorPt (actAlong f aX) Y T) :=
  prop331_space hX (SDR4_localFactorAll hX) T

/-- **Proposition 15.1** for a separated algebraic space and a finitely generated `M`. -/
theorem prop151_space_final (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) {M : Type u} [AddCommGroup M]
    [AddMonoid.FG M] {aX : AAction (fppfO B S hS) M X} (N : AddSubmonoid M) :
    IsPure (attractorImage aX) N ↔ ∀ L, L < N → attractorImage aX L < attractorImage aX N :=
  prop151_space hX hsep (SDR4_localFactorAll hX) N

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_00UD
#print axioms AlgMag.SD.SDR4_chartInput
#print axioms AlgMag.SD.SDR4_invChart
#print axioms AlgMag.SD.prop331_space_final
#print axioms AlgMag.SD.prop332_space_final
#print axioms AlgMag.SD.prop151_space_final
