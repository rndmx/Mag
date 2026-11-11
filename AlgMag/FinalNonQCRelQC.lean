/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCLocal
import AlgMag.ChartFinalSpaces
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase

/-!
# Theorem 6.8, quasi-compact clause, relative to `S`

`X → S` quasi-compact. For `S` quasi-compact and separated: an `S`-affine atlas. For `S` arbitrary: over each affine open `O` of `S`, an
`O`-affine atlas of the restriction of `X`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- **Theorem 6.8 (i), quasi-compact clause**: `X → S` quasi-compact, `S` quasi-compact and separated: an `S`-affine atlas, strongly-FPR. -/
theorem thm68_relqc [S.IsSeparated] [CompactSpace S]
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (hq : Space.IsQuasiCompact B S hS (toT1 X))
    (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v ∧
        (∀ Z : AddSubgroup M, IsZFPRAtlas actV act v Z) ∧ IsSAffineAtlas actV act v :=
  thm68_qc_spaces hZ hM hX hlfp hsep
    (by
      have hc : CompactSpace ((SCH).obj (T1 B S hS)) := inferInstanceAs (CompactSpace S)
      have h := hq (yoneda.obj (T1 B S hS)) (isAlgebraicSpace_yoneda B S hS _)
        (Space.isQuasiCompactSpace_yoneda_obj B S hS hc) (𝟙 _)
      have : IsIso (pullback.snd (𝟙 (yoneda.obj (T1 B S hS))) (toT1 X)) :=
        (IsPullback.of_hasPullback (𝟙 (yoneda.obj (T1 B S hS))) (toT1 X)).flip.isIso_fst_of_isIso
      exact Space.IsQuasiCompactSpace.of_iso B S hS h (asIso (pullback.snd (𝟙 (yoneda.obj (T1 B S hS))) (toT1 X)))) act

/-- The restriction of `X` to an object with quasi-compact underlying scheme is quasi-compact, when `X → S` is. -/
theorem res_qc (T₀ : BigFppfOver B S hS) [CompactSpace T₀.left.1] (hX : IsAlgebraicSpace B S hS X)
    (hq : Space.IsQuasiCompact B S hS (toT1 X)) :
    Space.IsQuasiCompactSpace B T₀.left.1 T₀.left.2 (Res X T₀) := by
  have h := hq (yoneda.obj (Over.mk T₀.hom)) (isAlgebraicSpace_yoneda B S hS _)
    (Space.isQuasiCompactSpace_yoneda_obj B S hS (inferInstanceAs (CompactSpace T₀.left.1))) (betaT T₀)
  have e := (res_sq (X := X) T₀).flip.isoPullback
  exact Space.isQuasiCompactSpace_of_relocalize B _ S T₀.left.2 hS T₀.hom _
    (Space.IsQuasiCompactSpace.of_iso B S hS h e.symm)

include hZ in
/-- **Theorem 6.8 (i), quasi-compact clause, local form**: `X → S` quasi-compact, `S` arbitrary, `O` an affine open of `S`: an `O`-affine
atlas of the restriction of `X` to `O`, strongly-FPR. -/
theorem thm68_relqc_local (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (hq : Space.IsQuasiCompact B S hS (toT1 X))
    (act : AAction (fppfO B S hS) M X) {O : S.Opens} (hO : IsAffineOpen O) :
    let T₀ := openBase (B := B) (hS := hS) O
    ∃ (V : BigFppfOver B T₀.left.1 T₀.left.2)
      (actV : AAction (fppfO B T₀.left.1 T₀.left.2) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ Res X T₀), IsStronglyFPRAtlas actV (resAct act) v ∧
        (∀ Z : AddSubgroup M, IsZFPRAtlas actV (resAct act) v Z) ∧
        IsSAffineAtlas actV (resAct act) v := by
  intro T₀
  have hAff : IsAffine T₀.left.1 := isAffine_openBase (B := B) (hS := hS) hO
  have hsepb : T₀.left.1.IsSeparated := inferInstance
  exact thm68_qc_spaces hZ hM (res_alg T₀ hX) (res_lfp T₀ hX hlfp) (res_sep T₀ hX hsep)
    (res_qc T₀ hX hq) (resAct act)

end AlgMag.Final

#print axioms AlgMag.Final.thm68_relqc
#print axioms AlgMag.Final.thm68_relqc_local
