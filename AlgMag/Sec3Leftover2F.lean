/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover26
import AlgMag.Sec3Leftover26Sh

/-!
# Algebraic Magnetism, Fact 2.6 (ii): the algebra of `𝔸(N)_B`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). `AlgMag.OverB.fact26_ii_sections`: for `V → B`
with `V` a scheme of the site and `U ⊆ V` affine open, the base change `W → V` of `𝔸(N)_B → B` has
`Γ(W, k⁻¹ U) = 𝒪_V(U)[N]`. This is the value of `𝒪_B[N]` on the chart `V` (Definition 2.3 (iii)).
The algebra is treated; the comultiplication is not.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

noncomputable section

namespace AlgMag.GB

variable (N : Type u) [AddCommMonoid N]

/-- If `W → V` is a base change of `𝔸(N)_S → S` along `v : V → S`, then for `U ⊆ V` affine open,
`Γ(W, k⁻¹ U) = 𝒪_V(U)[N]` as `𝒪_V(U)`-algebras, the pull-back of `X^n` going to `X^n`. -/
theorem sections_of_isPullback {S V W : Scheme.{u}} {v : V ⟶ S} {k : W ⟶ V} {q : W ⟶ (A N S).left}
    (hP : IsPullback q k (A N S).hom v) {U : V.Opens} (hU : IsAffineOpen U) :
    ∃ e : Γ(W, k ⁻¹ᵁ U) ≃+* AddMonoidAlgebra Γ(V, U) N,
      (∀ n : N, e ((W.presheaf.map (homOfLE le_top).op).hom (q.appTop.hom
          (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n)))) = AddMonoidAlgebra.single n 1) ∧
      ∀ r : Γ(V, U), e ((k.app U).hom r) = AddMonoidAlgebra.single 0 r := by
  let s : Spec Γ(V, U) ⟶ V := hU.fromSpec
  have h0 := isPullback_jS N Γ(V, U) (s ≫ v)
  have hc : (jS N Γ(V, U) (s ≫ v)).left ≫ (A N S).hom = (piR N Γ(V, U) ≫ s) ≫ v := by
    rw [h0.w, Category.assoc]
  let j : PR N Γ(V, U) ⟶ W := hP.lift (jS N Γ(V, U) (s ≫ v)).left (piR N Γ(V, U) ≫ s) hc
  have hjq : j ≫ q = (jS N Γ(V, U) (s ≫ v)).left := hP.lift_fst _ _ _
  have hjk : j ≫ k = piR N Γ(V, U) ≫ s := hP.lift_snd _ _ _
  have hpb : IsPullback j (piR N Γ(V, U)) k s :=
    IsPullback.of_right (h₁₂ := q) (h₂₂ := v) (v₁₃ := (A N S).hom) (by rw [hjq]; exact h0) hjk hP
  haveI : IsOpenImmersion j :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip
      (inferInstanceAs (IsOpenImmersion hU.fromSpec))
  have hrange : j.opensRange = k ⁻¹ᵁ U := by
    apply TopologicalSpace.Opens.ext
    have e : j = hpb.isoPullback.hom ≫ pullback.fst k s := (IsPullback.isoPullback_hom_fst _).symm
    change Set.range j = _
    have hi : Set.range hpb.isoPullback.hom = Set.univ :=
      Set.range_eq_univ.mpr fun y => Surjective.surj y
    rw [e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hi, Set.image_univ,
      Scheme.Pullback.range_fst]
    change k ⁻¹' (s.opensRange : Set V) = _
    rw [hU.opensRange_fromSpec]
    rfl
  have hle : (⊤ : (PR N Γ(V, U)).Opens) ≤ j ⁻¹ᵁ (k ⁻¹ᵁ U) := by
    rw [← hrange, ← Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.preimage_image_eq]
  have hb := bijective_appLE j _ (by rw [Scheme.Hom.image_top_eq_opensRange, hrange]) hle
  let e0 := RingEquiv.ofBijective (j.appLE _ ⊤ hle).hom hb
  let G := Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra Γ(V, U) N))
  refine ⟨e0.trans G.commRingCatIsoToRingEquiv, fun n => ?_, fun r => ?_⟩
  · have h0' : (j.appLE _ ⊤ hle).hom ((W.presheaf.map (homOfLE le_top).op).hom (q.appTop.hom
        (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n)))) =
        j.appTop.hom (q.appTop.hom (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n))) := by
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      rfl
    have h1 : j.appTop.hom (q.appTop.hom (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n))) =
        a0PR N Γ(V, U) (Multiplicative.ofAdd n) := by
      have := ptsZ_jS N Γ(V, U) (s ≫ v)
      rw [ptsZ_comp, ← hjq] at this
      have t := DFunLike.congr_fun this (Multiplicative.ofAdd n)
      rw [← t]
      change _ = (j ≫ q).appTop.hom _
      rw [Scheme.Hom.comp_appTop]
      rfl
    change G.hom.hom ((j.appLE _ ⊤ hle).hom _) = _
    rw [h0', h1]
    simp [a0PR, homSpecEquiv, G]
  · have h0' : (j.appLE _ ⊤ hle).hom ((k.app U).hom r) =
        (piR N Γ(V, U)).appTop.hom ((Scheme.ΓSpecIso Γ(V, U)).inv.hom r) := by
      have hh : (⊤ : (PR N Γ(V, U)).Opens) ≤ (piR N Γ(V, U)) ⁻¹ᵁ (s ⁻¹ᵁ U) := by
        have : (piR N Γ(V, U) ≫ s) ⁻¹ᵁ U = (j ≫ k) ⁻¹ᵁ U := by rw [hjk]
        exact this.symm ▸ hle
      have c1 : (k.app U ≫ j.appLE _ ⊤ hle) =
          s.app U ≫ (piR N Γ(V, U)).appLE (s ⁻¹ᵁ U) ⊤ hh :=
        (Scheme.Hom.comp_appLE j k U ⊤ _).symm.trans
          ((appLE_congr hjk _ _ _ _).trans (Scheme.Hom.comp_appLE _ s U ⊤ _))
      rw [← CommRingCat.comp_apply, c1]
      change (hU.fromSpec.app U ≫ _).hom r = _
      rw [hU.fromSpec_app_self, Category.assoc, Scheme.Hom.map_appLE]
      rfl
    change G.hom.hom ((j.appLE _ ⊤ hle).hom _) = _
    rw [h0']
    have e2 := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (AddMonoidAlgebra.singleZeroRingHom : Γ(V, U) →+* AddMonoidAlgebra Γ(V, U) N))
    have e3 := congrArg (fun k => k.hom r) e2
    change (G.inv.hom _) = (piR N Γ(V, U)).appTop.hom _ at e3
    refine (congrArg G.hom.hom e3.symm).trans ?_
    change (G.inv ≫ G.hom).hom _ = _
    rw [G.inv_hom_id]
    rfl

end AlgMag.GB

namespace AlgMag.OverB

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (Bs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (N : Type u) [AddCommMonoid N] (hN : B.Contains (GB.A N S).left)

local notation "SCH" => BigFppfOver.toScheme B S hS

include hN in
/-- **Fact 2.6 (ii)**, the algebra: for `V → B`, `V` a scheme of the site, there is a base change
`k : W → V` of `𝔸(N)_B → B`, an affine morphism of schemes, with `Γ(W, k⁻¹ U) = 𝒪_V(U)[N]` for every
affine open `U ⊆ V`, compatibly with `𝒪_V(U)`. -/
theorem fact26_ii_sections (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Bs) :
    ∃ (W : BigFppfOver B S hS) (k : W ⟶ V) (w : yoneda.obj W ⟶ AB Bs N),
      IsAffineHom ((SCH).map k) ∧ IsPullback w (yoneda.map k) (pr Bs N) v ∧
      ∀ {U : ((SCH).obj V).Opens}, IsAffineOpen U →
        ∃ e : Γ((SCH).obj W, ((SCH).map k) ⁻¹ᵁ U) ≃+* AddMonoidAlgebra Γ((SCH).obj V, U) N,
          ∀ r, e ((((SCH).map k).app U).hom r) = AddMonoidAlgebra.single 0 r := by
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
  refine ⟨pullback c (strS hN), pullback.fst _ _, w, ?_, ?_, fun {U} hU => ?_⟩
  · have hs : IsAffineHom ((SCH).map (strS hN)) :=
      inferInstanceAs (IsAffineHom (GB.A N S).hom)
    exact MorphismProperty.of_isPullback (P := @IsAffineHom.{u}) (sq.map (SCH)).flip hs
  · refine IsPullback.of_right (h₁₂ := prY Bs hN) (h₂₂ := toT0 Bs) (v₁₃ := yoneda.map (strS hN))
      ?_ hw1 R.flip
    rw [hw2, ec]
    exact sqY.flip
  · have hP : IsPullback ((SCH).map (pullback.snd c (strS hN))) ((SCH).map (pullback.fst c (strS hN)))
        (GB.A N S).hom ((SCH).map c) := (sq.map (SCH)).flip
    obtain ⟨e, -, h⟩ := GB.sections_of_isPullback N hP hU
    exact ⟨e, h⟩

end AlgMag.OverB

#print axioms AlgMag.GB.sections_of_isPullback
#print axioms AlgMag.OverB.fact26_ii_sections
