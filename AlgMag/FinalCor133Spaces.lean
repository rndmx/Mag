/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec13Spaces
import AlgMag.SecFinal1316
import AlgMag.SecLeftover1615Spaces
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Corollary 13.3, the attractors being algebraic spaces

Mayeux, *Algebraic Magnetism*, Corollary 13.3, along the printed proof: `Bl_Y^D X → S` is smooth by
[Mayeux-Richarz-Romagny, Prop. 2.16] (`smooth_of_isDilatation`), so `(Bl_Y^D X)^N → S` is smooth by
Corollary 11.2, and Proposition 13.1 applies. `X`, `Y`, `Bl_Y^D X` are schemes as printed. The print writes
`Bl_{Y^N}^{D^N} X^N`, so it reads `X^N` as an algebraic space; `(Bl_Y^D X)^N` must be one for its smoothness to
mean anything. No attractor is assumed to be a scheme, and `Y^N` is any presheaf representing the attractor.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.DilSp

open Dil GB AlgMag.SpacesLift AlgMag.Leftover

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "C" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The universal property among all `S'`-regular schemes gives the one on the site. -/
theorem isSpDil_of_isDilatation {I : S.IdealSheafData} {X₀ Y₀ B₀ : C} {j₀ : Y₀ ⟶ X₀} {b₀ : B₀ ⟶ X₀}
    (hD : IsDilatation I ((toO (B := B) (hS := hS)).map j₀) ((toO (B := B) (hS := hS)).map b₀)) :
    IsSpDil I (yoneda.map j₀) (yoneda.map b₀) := by
  let G := toO (B := B) (hS := hS)
  refine isSpDil_of_site (isAlgebraicSpace_yoneda B S hS _).isSheaf
    (isAlgebraicSpace_yoneda B S hS _).isSheaf (spReg_yoneda hD.reg) ?_ ?_ ?_
  · intro T ξ Z s hZ
    obtain ⟨y, hy⟩ := hD.factors (G.map (s ≫ ξ)) hZ
    refine ⟨G.preimage y, G.map_injective ?_⟩
    change G.map (G.preimage y ≫ j₀) = G.map (s ≫ ξ ≫ b₀)
    rw [Functor.map_comp, G.map_preimage, hy, ← Category.assoc, Functor.map_comp G (s ≫ ξ) b₀]
  · intro W hW w hf
    have hfac : Factors I (G.map j₀) (G.map w) := by
      rw [factors_iff_pullback]
      have hZs : B.Contains (restr I (G.obj W)).left := contains_restr _ I W.left.2
      let s' : (ofO _ hZs : C) ⟶ W := preO hZs (restrι I (G.obj W))
      obtain ⟨y, hy⟩ := hf s' (liesOver_restr (G.obj W))
      have hy' : y ≫ j₀ = s' ≫ w := hy
      refine ⟨G.map y, ?_⟩
      have := congrArg G.map hy'
      rw [Functor.map_comp, Functor.map_comp, map_preO] at this
      exact this
    obtain ⟨l₀, hl₀⟩ := hD.exists_lift hW (G.map w) (fun _ _ => trivial) hfac
    refine ⟨G.preimage l₀, G.map_injective ?_⟩
    change G.map (G.preimage l₀ ≫ b₀) = G.map w
    rw [Functor.map_comp, G.map_preimage, hl₀]
  · intro W hW ξ₁ ξ₂ e
    refine G.map_injective (hD.uniq hW _ _ ?_)
    have e' : ξ₁ ≫ b₀ = ξ₂ ≫ b₀ := e
    rw [← Functor.map_comp, ← Functor.map_comp, e']

/-- The map from an object of the site to the terminal object. -/
noncomputable abbrev toTer (W : C) : W ⟶ Ter B S hS := Over.mkIdTerminal.from W

lemma toO_hom_eq (W : C) : ((toO (B := B) (hS := hS)).obj W).hom = (SCH).map (toTer W) := by
  have h : (toTer W).left.hom ≫ 𝟙 _ = W.hom.hom := congrArg (fun q => q.hom) (Over.w (toTer W))
  exact h.symm.trans (Category.comp_id _)

/-- The terminal presheaf is `yoneda` of the terminal object. -/
noncomputable def terIso : yoneda.obj (Ter B S hS) ≅ ⊤_ (Cᵒᵖ ⥤ Type u) :=
  (IsTerminal.isTerminalObj yoneda _ (Over.mkIdTerminal (X := B.obj hS))).uniqueUpToIso
    terminalIsTerminal

/-- A morphism of the site smooth as schemes is smooth as spaces (Stacks 03MJ, through
`holdsOnEveryEtaleChart_iff_representable`). -/
lemma isSmooth_yoneda_map {U V : C} (j : U ⟶ V) (hj : Smooth ((SCH).map j)) :
    Space.IsSmooth B S hS (yoneda.map j) := by
  show Space.HoldsOnEveryEtaleChart B S hS (@Smooth.{u} : MorphismProperty Scheme.{u}) (yoneda.map j)
  rw [Space.holdsOnEveryEtaleChart_iff_representable (B := B) (S := S) (hS := hS) (P := @Smooth.{u})
    Smooth.isEtaleLocalOnSourceAndTarget]
  let T := SCH
  let eV := yoneda.preimageIso (yoneda.obj U).reprW
  let eU := yoneda.preimageIso (yoneda.obj V).reprW
  have hreV : (yoneda.obj U).reprW.hom = yoneda.map eV.hom :=
    (Functor.map_preimage yoneda (yoneda.obj U).reprW.hom).symm
  have hreU : (yoneda.obj V).reprW.inv = yoneda.map eU.inv :=
    (Functor.map_preimage yoneda (yoneda.obj V).reprW.inv).symm
  have hpre : yoneda.preimage
      ((yoneda.obj U).reprW.hom ≫ yoneda.map j ≫ (yoneda.obj V).reprW.inv) =
      eV.hom ≫ j ≫ eU.inv := by
    rw [hreV, hreU, ← Functor.map_comp, ← Functor.map_comp]
    apply yoneda.map_injective
    simp
  rw [hpre, Functor.map_comp, Functor.map_comp]
  exact MorphismProperty.comp_mem @Smooth
    (T.map eV.hom ≫ T.map j) (T.map eU.inv)
    (MorphismProperty.comp_mem @Smooth (T.map eV.hom) (T.map j) inferInstance hj) inferInstance

/-- `W → S` smooth as schemes gives `W → S` smooth as spaces. -/
lemma isSmooth_terminal_of_smooth (W : C) (h : Smooth ((SCH).map (toTer W))) :
    Space.IsSmooth B S hS (terminal.from (yoneda.obj W)) := by
  have e : terminal.from (yoneda.obj W) = yoneda.map (toTer W) ≫ (terIso (B := B) (S := S) (hS := hS)).hom :=
    Subsingleton.elim _ _
  rw [e]
  exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_top B S hS) _ _ (isSmooth_yoneda_map _ h)
    (Space.isSmooth_of_isIso B S hS (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_top B S hS) _)

variable {M : Type u} [AddCommGroup M] [SM B M] {I : S.IdealSheafData}
  {X₀ Y₀ B₀ : BigFppfOver B S hS} {j₀ : Y₀ ⟶ X₀} {b₀ : B₀ ⟶ X₀}
  {act : AAction (fppfO B S hS) M (yoneda.obj X₀)} {actY : AAction (fppfO B S hS) M (yoneda.obj Y₀)}

/-- An algebraic space smooth over `S` has an étale atlas flat over `S`, hence is `S'`-regular if it
maps to an `S'`-regular object: the input of Proposition 13.1. -/
lemma exists_flat_atlas {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (h : Space.IsSmooth B S hS (terminal.from Z)) :
    ∃ (U₀ : C) (c₀ : yoneda.obj U₀ ⟶ Z),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) SCH).presheaf c₀ ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) SCH).presheaf c₀ ∧
      Flat ((toO (B := B) (hS := hS)).obj U₀).hom := by
  obtain ⟨U₀, c₀, hs₀, he₀⟩ := hZ.exists_atlas
  refine ⟨U₀, c₀, hs₀, he₀, ?_⟩
  have hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (terIso (B := B) (S := S) (hS := hS)).hom := by
    have := Space.isMultiplicative_presheaf_etale B S hS
    exact MorphismProperty.of_isIso _ _
  have h₃ : Smooth ((SCH).map (toTer U₀)) :=
    h U₀ (Ter B S hS) c₀ (terIso (B := B) (S := S) (hS := hS)).hom (toTer U₀) he₀ hb (Subsingleton.elim _ _)
  rw [toO_hom_eq]
  have h₄ : Smooth ((SCH).map (toTer U₀)) := h₃
  exact @AlgebraicGeometry.instFlatOfSmooth _ _ _ h₄

/-- **Corollary 13.3.** `S'` an effective Cartier divisor of `S`, `X` a smooth `S`-scheme with an action of
`D(M)_S`, `Y` a closed subscheme of `X|_{S'}`, smooth over `S'` and stable, `Bl_Y^D X` the dilatation, `N` a
submonoid of `M`. If `X^N` is a sheaf (for instance an algebraic space) and `(Bl_Y^D X)^N` is an algebraic
space, then `(Bl_Y^D X)^N → S` is smooth and `b^N` is the dilatation of `X^N` with center `Y^N`, so
`(Bl_Y^D X)^N = Bl_{Y^N}^{D^N} X^N` canonically over `X^N` for any model `B'` of the latter. -/
theorem cor13_3_spaces (hC : IsEffCartier I)
    [IsClosedImmersion ((toO (B := B) (hS := hS)).map j₀).left]
    [Mono ((toO (B := B) (hS := hS)).map j₀)]
    {l : ((toO (B := B) (hS := hS)).obj Y₀).left ⟶ I.subscheme}
    (hl : l ≫ I.subschemeι = ((toO (B := B) (hS := hS)).obj Y₀).hom) [Smooth l]
    [Smooth ((toO (B := B) (hS := hS)).obj X₀).hom]
    (hs : SpStable (yoneda.map j₀) act actY)
    (hD : IsDilatation I ((toO (B := B) (hS := hS)).map j₀) ((toO (B := B) (hS := hS)).map b₀))
    (hM : B.Contains (AZ (⊤ : AddSubmonoid M))) {N : AddSubmonoid M} (hN : B.Contains (AZ N))
    {ZX ZY ZB : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) ZX)
    (hZB : IsAlgebraicSpace B S hS ZB) (rX : RepresentsAttractor act N ZX)
    (rY : RepresentsAttractor actY N ZY)
    (rB : RepresentsAttractor (blAction hs (isSpDil_of_isDilatation hD) hM) N ZB)
    {B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {b' : B' ⟶ ZX}
    (hB' : IsSpDil I (jN hs rX rY) b') :
    Space.IsSmooth B S hS (terminal.from ZB) ∧
      IsSpDil I (jN hs rX rY) (bN hs (isSpDil_of_isDilatation hD) hM rX rB) ∧
      ∃ e : ZB ≅ B', e.hom ≫ b' = bN hs (isSpDil_of_isDilatation hD) hM rX rB := by
  haveI : Mono (yoneda.map j₀) := by
    have : Mono j₀ := (toO (B := B) (hS := hS)).mono_of_mono_map inferInstance
    infer_instance
  have hsB : Smooth ((toO (B := B) (hS := hS)).obj B₀).hom := smooth_of_isDilatation hC hl hD
  have hsmB : Space.IsSmooth B S hS (terminal.from (yoneda.obj B₀)) :=
    isSmooth_terminal_of_smooth B₀ (toO_hom_eq B₀ ▸ hsB)
  have hsm : Space.IsSmooth B S hS (terminal.from ZB) :=
    isSmooth_rep_spaces N (isAlgebraicSpace_yoneda B S hS _) hZB _ hsmB rB
  obtain ⟨U₀, c₀, hs₀, he₀, hfl⟩ := exists_flat_atlas hZB hsm
  obtain ⟨h₁, h₂⟩ := prop13_1_spaces hs (isSpDil_of_isDilatation hD) hM hN rX rY rB hZB.isSheaf hZX
    c₀ hs₀ he₀ hfl hB'
  exact ⟨hsm, h₁, h₂⟩

end AlgMag.DilSp

#print axioms AlgMag.DilSp.isSpDil_of_isDilatation
#print axioms AlgMag.DilSp.cor13_3_spaces
