/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalThm68Single
import AlgMag.Sec15Final

/-!
# Statements whose printed proof takes an atlas from Theorem 6.8, with the atlas discharged

`X` separated and locally of finite presentation over a separated `S`, `M` a finitely generated abelian group. The atlas comes from
`thm68_qc_spaces` (`X` quasi-compact). `hlfp`, `hfp` are the same property for two choices of the terminal presheaf; `hsep`, `hsep'` are the two forms of separatedness used in the library.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- **Proposition 8.5**, no atlas in the hypotheses. -/
theorem prop85_free [S.IsSeparated] [CompactSpace S] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (hsep' : Space.IsSeparatedOver B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (LimThm.toT1 X))
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    ∃ (Nc : AddSubmonoid M) (hc : Nc ≤ N), Nc.FG ∧ unitsSub Nc = unitsSub N ∧
      ∀ T : BigFppfOver B S hS, Function.Bijective (AttractorPt.ofLE (act := act) (T := T) hc) := by
  obtain ⟨V, actV, v, -, h2, h3⟩ := thm68_qc_spaces hZ hM hX hlfp hsep' hq act
  exact prop85 hX hsep hfp N ⟨V, actV, v, h2 _, h3.2⟩

include hZ in
/-- **Proposition 3.32 (ii)**, no atlas in the hypotheses. -/
theorem prop332_free [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (hsep' : Space.IsSeparatedOver B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (LimThm.toT1 X))
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) (N L : AddSubmonoid M) (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt act (N ⊓ L) T → IterPt act N L T) := by
  obtain ⟨V, actV, v, h1, -, h3⟩ := thm68_qc_spaces hZ hM hX hlfp hsep' hq act
  haveI := (hasFiniteAffineDecomposition_iff _).mp h3.2
  exact prop332 hX hsep h1 (Or.inr (isLimitPreserving_of_lfp hX hfp)) T

include hZ in
/-- **Proposition 15.1**, no atlas in the hypotheses. -/
theorem prop151_free [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (hsep' : Space.IsSeparatedOver B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (LimThm.toT1 X))
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    IsPure (attractorImage act) N ↔ ∀ L, L < N → attractorImage act L < attractorImage act N := by
  obtain ⟨V, actV, v, h1, -, h3⟩ := thm68_qc_spaces hZ hM hX hlfp hsep' hq act
  haveI := (hasFiniteAffineDecomposition_iff _).mp h3.2
  exact prop151_of_atlas hX hsep h1 (isLimitPreserving_of_lfp hX hfp) N

include hZ in
/-- **Theorem 15.4 (ii) / Conjecture 15.7** for `X` quasi-compact: `Π(a)` is finite, with no linearizability, no atlas in the
hypotheses. `S` quasi-compact and separated. Conjecture 6.9 (ii) is `thm68_qc_spaces`. -/
theorem conj157_of_qc [S.IsSeparated] [CompactSpace S] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (hsep' : Space.IsSeparatedOver B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (LimThm.toT1 X))
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) :
    (pureMagnets (attractorImage act)).Finite := by
  obtain ⟨V, actV, v, h1, -, h3⟩ := thm68_qc_spaces hZ hM hX hlfp hsep' hq act
  haveI := (hasFiniteAffineDecomposition_iff _).mp h3.2
  exact (thm154_ii_lfp h1 hX hsep hfp).1

end AlgMag.Final

#print axioms AlgMag.Final.prop85_free
#print axioms AlgMag.Final.prop332_free
#print axioms AlgMag.Final.prop151_free
#print axioms AlgMag.Final.conj157_of_qc
