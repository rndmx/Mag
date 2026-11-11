/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec15Final

/-!
# Double scalar action, Remark 5.1 (i), in a precise form

A. Mayeux, *Algebraic magnetism invariants of a double scalar action*, arXiv:2509.04274v3 (no published version), Remark 5.1 (i):
"The method presented in this paper allows one to compute the magnetic invariants of any action `a` on a space `X` that is
Zariski-covered by stable charts on which the action is linear."

Precise form: `U → X` is an `S`-affine strongly-FPR atlas, and `W ⊆ M` is a set such that the attractors of `U` depend only on
`N ∩ W`: on a linear chart `W` is the set of weights, by Example 1.2 of *Algebraic Magnetism* (`ex12_general`, `linAttractorEquiv`).
The hypothesis `hW` carries this input, it is not derived here from a coordinate description of `U`. Then the attractors of `X`
depend only on `N ∩ W`, and two consequences: every pure magnet of `a` is determined by its trace on `W`, and for `W` finite
`Π(a)` is finite, with at most `2^#W` elements. `Sec7Linearizable.fact73` provides the atlas for such actions.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
  {aX : AAction (fppfO B S hS) M X} {aU : AAction (fppfO B S hS) M (yoneda.obj U)}

/-- **Remark 5.1 (i)**: the attractors of `X` depend only on `N ∩ W`. -/
theorem rem51_attractor [AddGroup.FG M] [IsAffineHom U.hom.hom] {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) {W : Set M}
    (hW : ∀ N L : AddSubmonoid M, (N : Set M) ∩ W = (L : Set M) ∩ W →
      attractorImage aU N = attractorImage aU L)
    {N L : AddSubmonoid M} (h : (N : Set M) ∩ W = (L : Set M) ∩ W) :
    attractorImage aX N = attractorImage aX L :=
  prop155_printed hat hX hsep hlim (hW N L h)

/-- **Remark 5.1 (i)**: a pure magnet of `a` is determined by its trace on `W`. -/
theorem rem51_pure [AddGroup.FG M] [IsAffineHom U.hom.hom] {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) {W : Set M}
    (hW : ∀ N L : AddSubmonoid M, (N : Set M) ∩ W = (L : Set M) ∩ W →
      attractorImage aU N = attractorImage aU L) :
    Set.InjOn (fun N : AddSubmonoid M => (N : Set M) ∩ W) (pureMagnets (attractorImage aX)) := by
  intro N hN L hL h
  have he := rem51_attractor hat hX hsep hlim hW h
  exact le_antisymm (hN L he) (hL N he.symm)

/-- **Remark 5.1 (i)**: for `W` finite, `Π(a)` is finite. -/
theorem rem51_finite [AddGroup.FG M] [IsAffineHom U.hom.hom] {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) {W : Set M} (hfin : W.Finite)
    (hW : ∀ N L : AddSubmonoid M, (N : Set M) ∩ W = (L : Set M) ∩ W →
      attractorImage aU N = attractorImage aU L) :
    (pureMagnets (attractorImage aX)).Finite := by
  refine Set.Finite.of_finite_image (f := fun N : AddSubmonoid M => (N : Set M) ∩ W) ?_
    (rem51_pure hat hX hsep hlim hW)
  exact (hfin.finite_subsets).subset (by rintro _ ⟨N, -, rfl⟩; exact Set.inter_subset_right)

end AlgMag.Final

#print axioms AlgMag.Final.rem51_finite
