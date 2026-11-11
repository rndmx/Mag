/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.JoinAction
import AlgMag.Conj157Separated
import AlgMag.Rooted.MinimalRoot
/-!
# Join-dense by a unique minimal family

`S` separated and quasi-compact, `M` a finitely generated abelian group, `X` a separated algebraic space
over `S`, locally of finite presentation and quasi-compact, with an action of `D(M)_S`. Then the action is
join-dense by a unique minimal family of magnets, contained in every join-dense family: the finite family
of join-irreducible pure magnets.

Proof: the pure magnets are finite (Conjecture 15.7, `conj157_separated'`); the action is a join action
(`isPure_sSup_attractorImage`, with the `S`-affine strongly-FPR atlas of `conj69ii_separated`), so it is
join-dense by the family of all pure magnets; Theorem 14.4 (`existsUnique_minimal_root_of_finite`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Conj157

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Corollary.** The action is join-dense by a unique minimal family of magnets, contained in every
join-dense family. -/
theorem existsUnique_minimal_joinDense [S.IsSeparated] [CompactSpace S] [AddGroup.FG M]
    (hZ : B.Contains (⊤_ Scheme.{u})) (hM : B.Contains (Spec (ZMon M)))
    (aX : AAction (fppfO B S hS) M X) (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompact B S hS (terminal.from X)) :
    ∃! Φ₀ : Set (AddSubmonoid M), Rooted.IsJoinDense (IsPure (attractorImage aX)) Φ₀ ∧
      ∀ Φ, Rooted.IsJoinDense (IsPure (attractorImage aX)) Φ → Φ₀ ⊆ Φ := by
  haveI : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  obtain ⟨hfin, -⟩ := conj157_separated' hZ hM aX hX hsep hfp hq
  obtain ⟨U, hU, aU, f, hat⟩ := conj69ii_separated hZ hM X aX hX hsep hfp hq
  haveI := hU
  have hlim := isLimitPreserving_of_lfp hX hfp
  refine Rooted.existsUnique_minimal_root_of_finite hfin ⟨{N | IsPure (attractorImage aX) N}, ?_⟩
  refine Rooted.isJoinDense_of_hull (fun N hN => ?_) (fun N => ?_)
  · exact le_antisymm (Rooted.gen_trace_le N) (le_sSup ⟨hN, le_rfl⟩)
  · exact isPure_sSup_attractorImage hX hsep hat hlim fun I hI => hI.1

end AlgMag.Conj157

#print axioms AlgMag.Conj157.existsUnique_minimal_joinDense
