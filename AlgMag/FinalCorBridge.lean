/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalAtlasFree

/-!
# The two forms of "separated over `S`" and "locally of finite presentation over `S`"

`Space.IsSeparatedOver` against `AlgMag.IsSeparatedOver`, and the structure map to `yoneda (T1)` against the map to the terminal
presheaf. These are the same conditions; the corollaries of `FinalCorAtlas` take one form only.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The two forms of "separated over `S`" agree. -/
theorem isSeparatedOver_iff_space : Space.IsSeparatedOver B S hS X ↔ AlgMag.IsSeparatedOver X :=
  Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS
    (Limits.IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal) (toBase X)

/-- An isomorphism of presheaves is locally of finite presentation. -/
theorem lfp_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    Space.IsLocallyOfFinitePresentation B S hS e.hom :=
  Space.isLocallyOfFinitePresentation_of_isEtale B S hS
    (Space.isEtale_of_presheaf_etale B S hS (Space.presheaf_etale_of_iso B S hS e))

/-- The two forms of "locally of finite presentation over `S`" agree. -/
theorem lfp_toT1_iff (hX : IsAlgebraicSpace B S hS X) :
    Space.IsLocallyOfFinitePresentation B S hS (LimThm.toT1 X) ↔
      Space.IsLocallyOfFinitePresentation B S hS (terminal.from X) := by
  let e : yoneda.obj (LimOrbit.T1 B S hS) ≅ ⊤_ _ :=
    (LimOrbit.isTerminal_T1 B S hS).uniqueUpToIso terminalIsTerminal
  have hT := isAlgebraicSpace_yoneda B S hS (LimOrbit.T1 B S hS)
  have hTop := Space.isAlgebraicSpace_of_iso B S hS e hT
  constructor
  · intro h
    have := Space.isLocallyOfFinitePresentation_comp B S hS hX hT hTop _ _ h (lfp_of_iso e)
    rwa [terminalIsTerminal.hom_ext (LimThm.toT1 X ≫ e.hom) (terminal.from X)] at this
  · intro h
    have := Space.isLocallyOfFinitePresentation_comp B S hS hX hTop hT _ _ h (lfp_of_iso e.symm)
    rwa [(LimOrbit.isTerminal_T1 B S hS).hom_ext (terminal.from X ≫ e.symm.hom) (LimThm.toT1 X)] at this

end AlgMag.Final

#print axioms AlgMag.Final.isSeparatedOver_iff_space
#print axioms AlgMag.Final.lfp_toT1_iff
