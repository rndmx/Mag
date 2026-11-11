/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Final
import AlgMag.FinalNonQCLocal
import AlgMag.FinalCorBridge
import AlgMag.AppendixA
import AlgMag.Prop337General

/-!
# Theorem 15.3 for a cancellative monoid `M` with `M^gp` finitely generated

`X` separated and locally of finite presentation over an arbitrary `S`. Reduction to the group
`M^gp` by Proposition 3.31 (iii) (`AlgMag.fact334_iii_of`, Lemma E of `notes/thm153-close.md`), then
Fact 3.34 for `M^gp` (`AlgMag.Final.fact334_general`) and `AlgMag.pureEquivRange`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommMonoid M] [IsCancelAdd M] [AddMonoid.FG (Algebra.GrothendieckAddGroup M)]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Fact 3.34**, arbitrary nonempty family, `M` cancellative with `M^gp` finitely generated, `X`
separated and locally of finite presentation. -/
theorem fact334_cancel (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon (Algebra.GrothendieckAddGroup M))))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) {s : Set (AddSubmonoid M)} (y) (hne : s.Nonempty)
    (hy : ∀ N ∈ s, attractorImage act N = y) : attractorImage act (sInf s) = y := by
  have : AddGroup.FG (Algebra.GrothendieckAddGroup M) := AddGroup.fg_iff_addMonoid_fg.2 inferInstance
  exact fact334_iii_of (f := Algebra.GrothendieckAddGroup.of) Algebra.GrothendieckAddGroup.of_injective
    hX (isSeparatedOver_iff_space.1 hsep) hne y hy fun h =>
      fact334_general hZ hM hX hsep hfp _ y (hne.image _) h

/-- **Theorem 15.3**, `M` cancellative with `M^gp` finitely generated, `X` separated and locally of
finite presentation over an arbitrary `S`: pure magnets correspond to attractors. -/
noncomputable def thm153_cancel (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon (Algebra.GrothendieckAddGroup M))))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) :
    pureMagnets (attractorImage act) ≃ Set.range (attractorImage act) :=
  pureEquivRange
    { monotone := attractorImage_monotone act
      sInf_of_const := fun _ y hne hy => fact334_cancel hZ hM hX hsep hfp act y hne hy }

end AlgMag.Final

namespace AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommMonoid M] [IsCancelAdd M] [AddMonoid.FG (Algebra.GrothendieckAddGroup M)]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The terminal scheme `Spec ℤ` lies in every big fppf site. -/
lemma contains_terminal (B : BigFppfSite.{u}) : B.Contains (⊤_ Scheme.{u}) := by
  let e : (⊤_ Scheme.{u}) ≅ Spec (.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  have h : B.Contains (Spec (.of (ULift.{u} ℤ))) :=
    P337.contains_iff.2 (show Cardinal.mk (ULift.{u} ℤ) < B.cutoff by
      rw [Cardinal.mk_uLift, Cardinal.mk_int, Cardinal.lift_aleph0]; exact B.aleph0_lt_cutoff)
  exact (Scheme.size_le_of_isOpenImmersion e.hom).trans_lt h

/-- **Theorem 15.3**, `M` cancellative with `M^gp` finitely generated, `X` separated and locally of
finite presentation over an arbitrary `S`; no further hypothesis. -/
noncomputable def thm153_cancel' (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) :
    pureMagnets (attractorImage act) ≃ Set.range (attractorImage act) :=
  have : AddGroup.FG (Algebra.GrothendieckAddGroup M) := AddGroup.fg_iff_addMonoid_fg.2 inferInstance
  have : Countable (Algebra.GrothendieckAddGroup M) := countable_of_fg _
  thm153_cancel (contains_terminal B) (contains_zmon_of_countable hS _) hX hsep hfp act

end AlgMag.Final

#print axioms AlgMag.Final.thm153_cancel
#print axioms AlgMag.Final.thm153_cancel'
