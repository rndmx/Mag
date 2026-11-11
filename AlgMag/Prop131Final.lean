/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec13Spaces
import AlgMag.Sec12Topology

/-!
# Proposition 13.1 for algebraic spaces, without a model of `Bl_{Y^N}^{D^N} X^N`

The dilatation `Bl_{Y^N}^{D^N} X^N` is constructed by `AlgMag.DilSp.exists_spDilatation`; its
inputs come from the standing hypotheses of §13: `X^N` is an algebraic space, `Y^N` is a sheaf,
`Y^N → X^N` is a closed immersion (Proposition 12.2 (ii)) and `Y^N` lies over `S'`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.DilSp

open Dil GB

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommMonoid M] {I : S.IdealSheafData}
  {X Y F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {j : Y ⟶ X} {b : F ⟶ X}
  {act : AAction (fppfO B S hS) M X} {actY : AAction (fppfO B S hS) M Y}
  {N : AddSubmonoid M}

/-- A presheaf representing the attractor of a sheaf is a sheaf. -/
lemma isSheaf_of_representsAttractor {A Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {ac : AAction (fppfO B S hS) M A}
    (hA : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A) (r : RepresentsAttractor ac N Z) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z := by
  rw [isSheaf_iff_isSheaf_of_type]
  let e : Z ⋙ uliftFunctor.{u + 1} ≅ attractor ac N :=
    NatIso.ofComponents (fun T => (Equiv.ulift.trans (r.equiv T.unop)).toIso) (fun {T T'} s => by
      ext z
      exact r.naturality s.unop z.down)
  have h : Presieve.IsSheaf (BigFppfOver.topology B S hS) (Z ⋙ uliftFunctor.{u + 1}) :=
    Presieve.isSheaf_iso _ e.symm
      (isSheaf_attractor ac N _ ((isSheaf_iff_isSheaf_of_type _ _).1 hA))
  exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 h

lemma mono_of_isClosedImm {A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : A ⟶ A'}
    (hf : IsClosedImm f) : Mono f := by
  have : ∀ T, Mono (f.app T) := fun T => by
    obtain ⟨T⟩ := T
    rw [mono_iff_injective]
    intro x x' h
    exact isClosedImm_injective hf h
  exact NatTrans.mono_of_mono_app f

/-- `𝔸(P)` is an object of the site when `#P` is below the cutoff. -/
lemma contains_AZ_of_cutoff (P : Type u) [AddCommMonoid P] [h : Fact (Cardinal.mk P < B.cutoff)] :
    B.Contains (AZ P) := by
  classical
  have hZ : Cardinal.mk (ULift.{u} ℤ) < B.cutoff := by
    rw [Cardinal.mk_uLift, Cardinal.mk_int, Cardinal.lift_aleph0]; exact B.aleph0_lt_cutoff
  refine contains_iff_card.2 (lt_of_le_of_lt (b := Cardinal.mk (Finset (P × ULift.{u} ℤ))) ?_ ?_)
  · refine Cardinal.mk_le_of_injective (f := fun x : AddMonoidAlgebra ℤ P =>
      (Finsupp.mapRange ULift.up (rfl : ULift.up (0 : ℤ) = 0) x.coeff).graph) ?_
    intro x y hxy
    have := Finsupp.mapRange_injective _ (rfl : ULift.up (0 : ℤ) = 0) ULift.up_injective
      (Finsupp.graph_injective _ _ hxy)
    ext m
    exact DFunLike.congr_fun this m
  · by_cases hf : Finite (P × ULift.{u} ℤ)
    · exact (Cardinal.lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff
    · have : Infinite (P × ULift.{u} ℤ) := not_finite_iff_infinite.1 hf
      rw [Cardinal.mk_finset_of_infinite, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le h.out hZ

/-- `j^N` is the attractor map of the equivariant morphism `j`. -/
lemma jN_eq (hs : SpStable j act actY) {ZX ZY : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor act N ZX) (rY : RepresentsAttractor actY N ZY) :
    jN hs rX rY = repAttractorMap ⟨j, fun h y => (hs h y).symm⟩ N rY rX := rfl

set_option maxHeartbeats 2000000 in
/-- **Proposition 13.1** (Mayeux, *Algebraic Magnetism*, §13) for algebraic spaces. `S'` closed
locally principal in `S`, `X` an algebraic space over `S` with an action of `𝔸(M)_S`, `Y` a closed
subspace of `X_{S'}` stable under the action, `b : Bl_Y^D X → X` the dilatation, `N` a magnet,
`X^N`, `Y^N`, `(Bl_Y^D X)^N` represented, `X^N` an algebraic space, `#M` below the cutoff of the
site (for instance `M` countable, `fact_cutoff_of_countable`), and `(Bl_Y^D X)^N` flat over
`S` (a surjective étale atlas flat over `S`). Then `Bl_{Y^N}^{D^N} X^N` exists as an algebraic space
affine over `X^N`, `b^N` is a dilatation of `X^N` with center `Y^N`, and
`(Bl_Y^D X)^N ≅ Bl_{Y^N}^{D^N} X^N` canonically over `X^N`. -/
theorem prop13_1_final [Fact (Cardinal.mk M < B.cutoff)] (hP : LocPrincipal I)
    (hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y) (hj : IsClosedImm j)
    (hYI : ∀ (Z : BigFppfOver B S hS) (_ : Y.obj (op Z)), Lies I Z)
    (hs : SpStable j act actY) (hD : IsSpDil I j b)
    {ZX ZY ZB : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rX : RepresentsAttractor act N ZX) (rY : RepresentsAttractor actY N ZY)
    (rB : RepresentsAttractor (blAction hs hD (contains_AZ_of_cutoff (⊤ : AddSubmonoid M))) N ZB)
    (hXN : IsAlgebraicSpace B S hS ZX)
    {U₀ : BigFppfOver B S hS} (c₀ : yoneda.obj U₀ ⟶ ZB)
    (hs₀ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c₀)
    (he₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c₀)
    (hfl : Flat ((toO (B := B) (hS := hS)).obj U₀).hom) :
    ∃ (B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (b' : B' ⟶ ZX), IsAlgebraicSpace B S hS B' ∧
      (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b' ∧
      IsSpDil I (jN hs rX rY) b' ∧ IsSpDil I (jN hs rX rY) (bN hs hD (contains_AZ_of_cutoff (⊤ : AddSubmonoid M)) rX rB) ∧
      ∃ e : ZB ≅ B', e.hom ≫ b' = bN hs hD (contains_AZ_of_cutoff (⊤ : AddSubmonoid M)) rX rB := by
  have : Mono j := mono_of_isClosedImm hj
  have hjN : IsClosedImm (jN hs rX rY) := by
    rw [jN_eq]
    exact isClosedImm_repAttractorMap _ hj N rY rX
  have hZY := isSheaf_of_representsAttractor hYs rY
  have hZYI : ∀ (Z : BigFppfOver B S hS) (_ : ZY.obj (op Z)), Lies I Z :=
    fun Z y => hYI Z (rY.equiv Z y).toPoint
  obtain ⟨B', b', hB'alg, hb'aff, hB'⟩ :=
    exists_spDilatation I hP hXN hZY (jN hs rX rY) hjN hZYI
  have hZB := isSheaf_of_representsAttractor hD.sheaf rB
  have h := attractor_isSpDil hs hD (contains_AZ_of_cutoff (⊤ : AddSubmonoid M)) (contains_AZ_of_cutoff N) rX rY rB hZB hXN.isSheaf
    (spReg_attractor hs hD (contains_AZ_of_cutoff (⊤ : AddSubmonoid M)) rB c₀ hs₀ he₀ hfl)
  exact ⟨B', b', hB'alg, hb'aff, hB', h, h.exists_iso hB'⟩

/-- **Proposition 13.1** for algebraic spaces, under the cutoff hypothesis `#M < B.cutoff`. -/
alias prop13_1_cutoff := prop13_1_final

end AlgMag.DilSp

#print axioms AlgMag.DilSp.prop13_1_final
