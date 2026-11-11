/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalCor133
import AlgMag.FinalCor133Spaces
import AlgMag.FinalNonQCGeneral
import AlgMag.ChartStratum

/-!
# Corollary 13.3, no representability assumed

Mayeux, *Algebraic Magnetism*, Corollary 13.3 (p. 182). The attractors `X^N` and `(Bl_Y^D X)^N` are
produced by Theorem 8.3 (`thm83_general`) as algebraic spaces, and `cor13_3_spaces` applies. The hypotheses
are those of Theorem 8.3 in its agreed form: `M` finitely generated and `X → S` separated. Local finite
presentation of `X` and of `Bl_Y^D X` follows from smoothness, separatedness of `Bl_Y^D X` from
`Bl_Y^D X → X` affine. `Y^N` is the attractor functor itself.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.DilSp

open Dil GB AlgMag.SpacesLift AlgMag.Leftover AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "C" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS

/-- An object of the site separated over `S` as a scheme is separated over `S` as a space. -/
lemma isSeparatedOver_yoneda_of (W : C) (h : IsSeparated ((toO (B := B) (hS := hS)).obj W).hom) :
    Space.IsSeparatedOver B S hS (yoneda.obj W) := by
  refine (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS
    (IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal) (yoneda.map (toTer W))).2
    ((Space.isSeparated_yoneda_map_iff B S hS _).2 ?_)
  rw [← toO_hom_eq]
  exact h

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M] [SM B M] {I : S.IdealSheafData}
  {X₀ Y₀ B₀ : BigFppfOver B S hS} {j₀ : Y₀ ⟶ X₀} {b₀ : B₀ ⟶ X₀}
  {act : AAction (fppfO B S hS) M (yoneda.obj X₀)} {actY : AAction (fppfO B S hS) M (yoneda.obj Y₀)}

/-- **Corollary 13.3**, no representability assumed. `S'` an effective Cartier divisor of `S`, `M` a
finitely generated abelian group, `X` a smooth separated `S`-scheme with an action of `D(M)_S`, `Y` a closed
subscheme of `X|_{S'}`, smooth over `S'` and stable, `Bl_Y^D X` the dilatation, `N` a submonoid of `M`.
Then `X^N` and `(Bl_Y^D X)^N` are represented by algebraic spaces, `Y^N` by a presheaf,
`(Bl_Y^D X)^N → S` is smooth, `b^N` is the dilatation of `X^N` with center `Y^N`, and
`(Bl_Y^D X)^N = Bl_{Y^N}^{D^N} X^N` canonically over `X^N` for every model `B'` of the latter. -/
theorem cor13_3_free (hZ : B.Contains (⊤_ Scheme.{u})) (hM' : B.Contains (Spec (ZMon M)))
    (hC : IsEffCartier I)
    [IsClosedImmersion ((toO (B := B) (hS := hS)).map j₀).left]
    [Mono ((toO (B := B) (hS := hS)).map j₀)]
    {l : ((toO (B := B) (hS := hS)).obj Y₀).left ⟶ I.subscheme}
    (hl : l ≫ I.subschemeι = ((toO (B := B) (hS := hS)).obj Y₀).hom) [Smooth l]
    [Smooth ((toO (B := B) (hS := hS)).obj X₀).hom]
    [IsSeparated ((toO (B := B) (hS := hS)).obj X₀).hom]
    (hs : SpStable (yoneda.map j₀) act actY)
    (hD : IsDilatation I ((toO (B := B) (hS := hS)).map j₀) ((toO (B := B) (hS := hS)).map b₀))
    (hM : B.Contains (AZ (⊤ : AddSubmonoid M))) {N : AddSubmonoid M} (hN : B.Contains (AZ N)) :
    ∃ (ZX ZY ZB : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (rX : RepresentsAttractor act N ZX)
      (rY : RepresentsAttractor actY N ZY)
      (rB : RepresentsAttractor (blAction hs (isSpDil_of_isDilatation hD) hM) N ZB),
      IsAlgebraicSpace B S hS ZX ∧ IsAlgebraicSpace B S hS ZB ∧
      Space.IsSmooth B S hS (terminal.from ZB) ∧
      IsSpDil I (jN hs rX rY) (bN hs (isSpDil_of_isDilatation hD) hM rX rB) ∧
      ∀ {B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {b' : B' ⟶ ZX}, IsSpDil I (jN hs rX rY) b' →
        ∃ e : ZB ≅ B', e.hom ≫ b' = bN hs (isSpDil_of_isDilatation hD) hM rX rB := by
  let G := toO (B := B) (hS := hS)
  have hX := isAlgebraicSpace_yoneda B S hS X₀
  have hBa := isAlgebraicSpace_yoneda B S hS B₀
  -- `X`: smooth and separated
  have hsmX : Space.IsSmooth B S hS (terminal.from (yoneda.obj X₀)) :=
    isSmooth_terminal_of_smooth X₀ (toO_hom_eq X₀ ▸ (inferInstance : Smooth (G.obj X₀).hom))
  have hsepX := isSeparatedOver_yoneda_of X₀ inferInstance
  -- `Bl_Y^D X`: smooth (MRR 2.16) and separated (affine over `X`)
  have hsB : Smooth (G.obj B₀).hom := smooth_of_isDilatation hC hl hD
  have hsmB : Space.IsSmooth B S hS (terminal.from (yoneda.obj B₀)) :=
    isSmooth_terminal_of_smooth B₀ (toO_hom_eq B₀ ▸ hsB)
  have haff : IsAffineHom (G.map b₀).left := hD.isAffineHom_left ⟨l, hl⟩ hC.1
  have hsepB : IsSeparated (G.obj B₀).hom := by
    rw [← Over.w (G.map b₀)]
    infer_instance
  have hsepB' := isSeparatedOver_yoneda_of B₀ hsepB
  obtain ⟨rX, -⟩ := thm83_general hZ hM' hX hsepX
    (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsmX) act N
  obtain ⟨rB, -⟩ := thm83_general hZ hM' hBa hsepB'
    (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsmB)
    (blAction hs (isSpDil_of_isDilatation hD) hM) N
  have rY := attPRep actY N
  have : Mono (yoneda.map j₀) := by
    have : Mono j₀ := G.mono_of_mono_map inferInstance
    infer_instance
  have hsm : Space.IsSmooth B S hS (terminal.from rB.P) :=
    isSmooth_rep_spaces N hBa rB.algP _ hsmB rB.rP
  obtain ⟨U₀, c₀, hs₀, he₀, hfl⟩ := exists_flat_atlas rB.algP hsm
  have h := attractor_isSpDil hs (isSpDil_of_isDilatation hD) hM hN rX.rP rY rB.rP rB.algP.isSheaf
    rX.algP.isSheaf (spReg_attractor hs (isSpDil_of_isDilatation hD) hM rB.rP c₀ hs₀ he₀ hfl)
  exact ⟨rX.P, _, rB.P, rX.rP, rY, rB.rP, rX.algP, rB.algP, hsm, h, fun hB' => h.exists_iso hB'⟩

end AlgMag.DilSp

#print axioms AlgMag.DilSp.cor13_3_free
