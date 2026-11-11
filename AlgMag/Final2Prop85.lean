/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalCorAtlas

/-!
# Proposition 8.5 of Algebraic Magnetism, atlas from Theorem 6.8

The printed proof takes "an `S`-affine `N^×`-FPR atlas as in Theorem 6.8". `X` is separated, so this is the
quasi-compact clause of Theorem 6.8 (`thm68_qc_spaces`, strongly FPR, hence `N^×`-FPR). Added: `S` separated
(Theorem 6.8, doubled-origin counterexample) and `S` quasi-compact (counterexample of the 8.5 notes).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Proposition 8.5**: `M` finitely generated, `X → S` quasi-compact, separated, locally of finite presentation,
`S` separated and quasi-compact. There is a finitely generated `N_c ⊆ N` with `N_c^× = N^×` and `X^{N_c} = X^N`. -/
theorem final2_prop85 [S.IsSeparated] [CompactSpace S] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    ∃ (Nc : AddSubmonoid M) (hc : Nc ≤ N), Nc.FG ∧ unitsSub Nc = unitsSub N ∧
      ∀ T : BigFppfOver B S hS, Function.Bijective (AttractorPt.ofLE (act := act) (T := T) hc) := by
  obtain ⟨V, actV, v, -, h2, h3⟩ := thm68_qc_spaces hZ hM hX ((lfp_toT1_iff hX).2 hfp) hsep hq act
  exact prop85 hX (isSeparatedOver_iff_space.1 hsep) hfp N ⟨V, actV, v, h2 _, h3.2⟩

end AlgMag.Final

#print axioms AlgMag.Final.final2_prop85
