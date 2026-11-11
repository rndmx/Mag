/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Conj69Separated
import AlgMag.FinalRem158
import AlgMag.FinalCorBridge

/-!
# Conjecture 15.7 of *Algebraic Magnetism*, for `S` separated and quasi-compact

`M` a finitely generated abelian group, `S` separated and quasi-compact, `X` a separated `S`-algebraic space of finite
presentation over `S` with an action of `D(M)_S`: the set of pure magnets is finite, and so is the set of attractors.
Conjecture 6.9 (ii) holds for `S` separated (`AlgMag.StronglyFPRNote.thm11_2`, clause (ii) of
`AlgMag.Conj69.conj69_separated`); Remark 15.8 (`AlgMag.Final.rem158`) turns it into Conjecture 15.7.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Conj157

open AlgMag.ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The two forms of "quasi-compact over `S`" agree: the structure map to `yoneda (T1)` against the map to the terminal
presheaf. -/
theorem qc_toT1_iff :
    Space.IsQuasiCompact B S hS (LimThm.toT1 X) ↔ Space.IsQuasiCompact B S hS (terminal.from X) := by
  let e : yoneda.obj (LimOrbit.T1 B S hS) ≅ ⊤_ _ :=
    (LimOrbit.isTerminal_T1 B S hS).uniqueUpToIso terminalIsTerminal
  constructor
  · intro h
    have sq : IsPullback (𝟙 X) (terminal.from X) (LimThm.toT1 X) e.inv :=
      IsPullback.of_horiz_isIso ⟨(LimOrbit.isTerminal_T1 B S hS).hom_ext _ _⟩
    exact Space.isQuasiCompact_of_isPullback B S hS sq h
  · intro h
    have sq : IsPullback (𝟙 X) (LimThm.toT1 X) (terminal.from X) e.hom :=
      IsPullback.of_horiz_isIso ⟨terminalIsTerminal.hom_ext _ _⟩
    exact Space.isQuasiCompact_of_isPullback B S hS sq h

/-- **Conjecture 6.9 (ii)**, as printed (`X` quasi-compact over `S`), for `S` separated and quasi-compact. -/
theorem conj69ii_separated [S.IsSeparated] [CompactSpace S] [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) : Final.Conj69iiRel B S hS M := by
  intro X aX hX hsep hfp hq
  obtain ⟨-, h2⟩ := Conj69.conj69_separated hZ hM hX ((Final.lfp_toT1_iff hX).2 hfp)
    (Final.isSeparatedOver_iff_space.2 hsep) aX
  obtain ⟨V, aV, v, hat, haff⟩ := h2 (qc_toT1_iff.2 hq) inferInstance
  exact ⟨V, (hasFiniteAffineDecomposition_iff _).mp haff.2, aV, v, hat⟩

/-- **Conjecture 15.7**, for `S` separated and quasi-compact and `M` a finitely generated abelian group: for every
separated `S`-algebraic space `X`, locally of finite presentation and quasi-compact over `S`, with an action of
`D(M)_S`, the set of pure magnets is finite. By Remark 15.8 from Conjecture 6.9 (ii). -/
theorem conj157_separated [S.IsSeparated] [CompactSpace S] [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) : Final.Conj157Rel B S hS M :=
  Final.rem158 B S hS M (conj69ii_separated hZ hM)

/-- **Conjecture 15.7**, unfolded, with the attractors: `Π(a)` and the set of attractors are finite. -/
theorem conj157_separated' [S.IsSeparated] [CompactSpace S] [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) (aX : AAction (fppfO B S hS) M X) (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompact B S hS (terminal.from X)) :
    (pureMagnets (attractorImage aX)).Finite ∧ (Set.range (attractorImage aX)).Finite := by
  obtain ⟨U, hU, aU, f, hat⟩ := conj69ii_separated hZ hM X aX hX hsep hfp hq
  exact thm154_ii_lfp hat hX hsep hfp

end AlgMag.Conj157

#print axioms AlgMag.Conj157.qc_toT1_iff
#print axioms AlgMag.Conj157.conj69ii_separated
#print axioms AlgMag.Conj157.conj157_separated
#print axioms AlgMag.Conj157.conj157_separated'
