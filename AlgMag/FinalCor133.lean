/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SecFinal1316

/-!
# Corollary 13.3 with no representability hypothesis, `X` affine over `S`

Mayeux, *Algebraic Magnetism*, Corollary 13.3. When `X → S` is affine, `Y → S` and `Bl_Y^D X → S` are
affine, and `X^N`, `Y^N`, `(Bl_Y^D X)^N` exist by Theorem 3.20. The printed proof then applies with
nothing added. For `X` not affine over `S`, see `AlgMag.FinalCor133Spaces`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgMag.Dil

open GB

variable {S : Scheme.{u}} {I : S.IdealSheafData} {X Y : Over S} {j : Y ⟶ X}

/-- The dilatation of `X` is affine over `X`, whichever model is taken. -/
lemma IsDilatation.isAffineHom_left {B : Over S} {b : B ⟶ X} (hD : IsDilatation I j b)
    [IsClosedImmersion j.left] (hYI : LiesOver I Y) (hP : LocPrincipal I) : IsAffineHom b.left := by
  obtain ⟨B₀, b₀, hD₀, haff⟩ := exists_dilatation j hYI hP
  obtain ⟨e, he⟩ := IsDilOn.exists_iso hD hD₀
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have h : b.left = e.hom.left ≫ b₀.left := by rw [← Over.comp_left, he]
  rw [h]
  infer_instance

/-- **Corollary 13.3**, `X` affine over `S`, no hypothesis on the attractors. `S'` an effective Cartier
divisor of `S`, `X` smooth over `S` with an action of `D(M)_S`, `Y` a closed subscheme of `X|_{S'}`,
smooth over `S'` and stable, `N` a submonoid of `M`. Then `D(M)_S` acts on `Bl_Y^D X` (`blAction`), the
three attractors exist (Theorem 3.20), `(Bl_Y^D X)^N → S` is smooth, and
`b^N : (Bl_Y^D X)^N → X^N` is the dilatation of `X^N` with center `Y^N`. -/
theorem cor13_3_affine {M : Type u} [AddCommGroup M] {B : Over S} {b : B ⟶ X}
    {act : AAction (overO S) M (yoneda.obj X)} {actY : AAction (overO S) M (yoneda.obj Y)}
    (hC : IsEffCartier I) [IsClosedImmersion j.left] [Mono j]
    {l : Y.left ⟶ I.subscheme} (hl : l ≫ I.subschemeι = Y.hom) [Smooth l] [Smooth X.hom]
    [IsAffineHom X.hom] (hs : Stable j act actY) (hD : IsDilatation I j b) (N : AddSubmonoid M) :
    haveI : IsAffineHom Y.hom := by
      rw [← Over.w j]; infer_instance
    haveI : IsAffineHom B.hom := by
      have := IsDilatation.isAffineHom_left hD ⟨l, hl⟩ hC.1
      rw [← Over.w b]; infer_instance
    Smooth (Zatt (blAction hs hD) N).hom ∧
      IsDilatation I (jN hs (representsAttractor act N) (representsAttractor actY N))
        (bN hs hD (representsAttractor act N) (representsAttractor (blAction hs hD) N)) := by
  haveI : IsAffineHom Y.hom := by
    rw [← Over.w j]; infer_instance
  haveI : IsAffineHom B.hom := by
    have := IsDilatation.isAffineHom_left hD ⟨l, hl⟩ hC.1
    rw [← Over.w b]; infer_instance
  haveI : Smooth B.hom := smooth_of_isDilatation hC hl hD
  have h : Smooth (Zatt (blAction hs hD) N).hom :=
    AlgMag.prop1615_ii_attr (blAction hs hD) N (representsAttractor (blAction hs hD) N)
  have : Flat (Zatt (blAction hs hD) N).hom := inferInstance
  exact ⟨h, prop13_1_of_isAffineHom hs hD N⟩

end AlgMag.Dil

#print axioms AlgMag.Dil.cor13_3_affine
