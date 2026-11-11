/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCClauses
import AlgMag.AppendixA

/-!
# Proposition 14.4, first and second assertions, with no site hypotheses

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, Proposition 14.4, alternative "`X` separated".
The site conditions `hZ`, `hM` of `prop144_general` / `prop144_rep_general` are discharged:
`B.contains_terminal` and `contains_zmon_of_countable` (`M` is countable, being finitely generated).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u

namespace AlgMag.Unrestrict

open AlgMag AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
  {Xi : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P Xi}

/-- **Proposition 14.4**, first and second assertions, alternative "`X` separated": `M` a finitely generated
abelian group, `X = colim X_i` with an ind-action of `D(M)`, terms separated and locally of finite presentation
over an arbitrary `S`, `N` an arbitrary magnet. Then the attractor functor is the ind-algebraic space
`colim X_i^N`, and `X^N → X` is representable by algebraic spaces. -/
theorem prop144 (a : IndAction M p) (N : AddSubmonoid M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i))
    (hsep : ∀ i, Space.IsSeparatedOver B S hS (p.obj i))
    (hfp : ∀ i, Space.IsLocallyOfFinitePresentation B S hS (terminal.from (p.obj i))) :
    haveI : Countable M := countable_of_fg83
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) ∧
      IndAttractorMapHasPropNat a N (fun {Z' _} _ => IsAlgebraicSpace B S hS Z') :=
  haveI : Countable M := countable_of_fg83
  ⟨prop144_general B.contains_terminal (contains_zmon_of_countable hS M) a N hX hsep hfp,
    prop144_rep_general B.contains_terminal (contains_zmon_of_countable hS M) a hX hsep hfp N⟩

/-- **Proposition 14.4**, resp. ind-schemes, first and second assertions, alternative "`X` separated": terms
separated schemes, locally of finite presentation; `colim X_i^N` is an ind-scheme and `X^N → X` is
representable by schemes. -/
theorem prop144_scheme (a : IndAction M p) (N : AddSubmonoid M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i))
    (hsep : ∀ i, Space.IsSeparatedOver B S hS (p.obj i))
    (hfp : ∀ i, Space.IsLocallyOfFinitePresentation B S hS (terminal.from (p.obj i)))
    (hS' : ∀ i, ∃ U : BigFppfOver B S hS, Nonempty (p.obj i ≅ yoneda.obj U)) :
    haveI : Countable M := countable_of_fg83
    IsIndScheme.{u, v} (attractor a.toAction N) ∧
      IndAttractorMapHasPropNat a N
        (fun {Z' _} _ => ∃ U : BigFppfOver B S hS, Nonempty (Z' ≅ yoneda.obj U)) :=
  haveI : Countable M := countable_of_fg83
  prop144_scheme_general B.contains_terminal (contains_zmon_of_countable hS M) a hX hsep hfp N hS'

end AlgMag.Unrestrict

#print axioms AlgMag.Unrestrict.prop144
#print axioms AlgMag.Unrestrict.prop144_scheme
