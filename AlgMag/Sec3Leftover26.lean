/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec2OverB

/-!
# Algebraic Magnetism, Fact 2.6

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). `𝔸(N)_S → S` is flat (Fact 2.6 (i), the
affine part is `AlgMag.GB.instAffine_str`) and `𝔸(N)_B → B` is flat and affine (Fact 2.6 (ii)).
Affine over `B` means: after base change to any scheme `V → B` of the site it is an affine morphism
of schemes.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

namespace AlgMag.OverB

/-- **Fact 2.6 (i)**: `𝔸(N)_S → S` is flat. -/
theorem flat_str (S : Scheme.{u}) (N : Type u) [AddCommMonoid N] : Flat (GB.A N S).hom := by
  have : Flat (terminal.from (GB.AZ N)) := by
    let ρ : ULift.{u} ℤ →+* AddMonoidAlgebra ℤ N :=
      (algebraMap ℤ (AddMonoidAlgebra ℤ N)).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
    have hρ : ρ.Flat := by
      refine RingHom.Flat.comp (RingHom.Flat.of_bijective ULift.ringEquiv.bijective) ?_
      exact (RingHom.flat_algebraMap_iff).mpr inferInstance
    have h1 : Flat (Spec.map (CommRingCat.ofHom ρ)) :=
      (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hρ
    have h2 : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
      isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal _
    have e : terminal.from (GB.AZ N) = Spec.map (CommRingCat.ofHom ρ) ≫
        terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))) := terminal.hom_ext _ _
    rw [e]
    infer_instance
  apply MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (terminal.from S) (terminal.from (GB.AZ N))).flip
  infer_instance

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (Bs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hBs : IsAlgebraicSpace B S hS Bs)
variable (N : Type u) [AddCommMonoid N] (hN : B.Contains (GB.A N S).left)

local notation "SCH" => BigFppfOver.toScheme B S hS

include hBs hN in
/-- **Fact 2.6 (ii)**: `𝔸(N)_B → B` is a flat morphism of algebraic spaces. -/
theorem isFlat_pr : IsFlat B S hS (pr Bs N) :=
  chart_of_isPullback _ Flat.isEtaleLocalOnSourceAndTarget (isPullback_AB Bs N hN)
    (isAlgebraicSpace_AB hBs N hN) hBs (flat_str S N)

include hN in
/-- **Fact 2.6 (ii)**: `𝔸(N)_B → B` is affine: its base change along any `V → B`, with `V` a scheme of the
site, is an affine morphism of schemes `W → V`. -/
theorem exists_affine_chart_pr (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Bs) :
    ∃ (W : BigFppfOver B S hS) (k : W ⟶ V) (w : yoneda.obj W ⟶ AB Bs N),
      IsAffineHom ((SCH).map k) ∧ IsPullback w (yoneda.map k) (pr Bs N) v := by
  let c : V ⟶ T0 B S hS := Over.homMk V.hom (by simp)
  have ec : v ≫ toT0 Bs = yoneda.map c := by
    refine NatTrans.ext (funext fun U => ?_)
    refine ConcreteCategory.hom_ext _ _ fun x => hom_T0_ext _ _
  have sq := IsPullback.of_hasPullback c (strS hN)
  have sqY := sq.map (yoneda (C := BigFppfOver B S hS))
  have R := isPullback_AB Bs N hN
  let w : yoneda.obj (pullback c (strS hN)) ⟶ AB Bs N :=
    R.lift (yoneda.map (pullback.fst c (strS hN)) ≫ v) (yoneda.map (pullback.snd c (strS hN))) (by
      rw [Category.assoc, ec, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  have hw1 : w ≫ pr Bs N = yoneda.map (pullback.fst c (strS hN)) ≫ v := R.lift_fst _ _ _
  have hw2 : w ≫ prY Bs hN = yoneda.map (pullback.snd c (strS hN)) := R.lift_snd _ _ _
  refine ⟨pullback c (strS hN), pullback.fst _ _, w, ?_, ?_⟩
  · have hs : IsAffineHom ((SCH).map (strS hN)) :=
      inferInstanceAs (IsAffineHom (GB.A N S).hom)
    exact MorphismProperty.of_isPullback (P := @IsAffineHom.{u}) (sq.map (SCH)).flip hs
  · refine IsPullback.of_right (h₁₂ := prY Bs hN) (h₂₂ := toT0 Bs) (v₁₃ := yoneda.map (strS hN))
      ?_ hw1 R.flip
    rw [hw2, ec]
    exact sqY.flip

end AlgMag.OverB
