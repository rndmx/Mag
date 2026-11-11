/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Intersections
/-!
# Every action is a join action

`M` a finitely generated abelian group, `X` a separated algebraic space with an `S`-affine strongly
fixed-point-reflecting atlas, under the hypotheses of Proposition 3.32 (ii). Then the sum of every family
of pure magnets is pure: the action is a join action.

The proof: if `X^L ⊆ X^N`, then `X^L ⊆ X^{N ∩ L}` (the argument of `exists_iter_of_image_eq` with an
inclusion in place of an equality, then Proposition 3.32 (ii)); for `L` pure and `X^N = X^{sup}`, this
gives `X^{N ∩ L} = X^L`, hence `L ⊆ N`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {f : yoneda.obj U ⟶ X}

/-- If `X^L ⊆ X^N` as subfunctors of `X`, every point of `X^L` extends to a point of `(X^N)^L`.
The proof of `exists_iter_of_image_eq`, which only uses this inclusion. -/
theorem exists_iter_of_image_le (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    {N L : AddSubmonoid M} (h : attractorImage aX L ≤ attractorImage aX N)
    {T : BigFppfOver B S hS} (ψ : AttractorPt aX L T) :
    ∃ Ψ : IterPt aX N L T, Ψ.toPoint = ψ.toPoint := by
  classical
  have hinj := fun T => attractor_toPoint_injective_sep (aX := aX) hX hsep N T
  have hG : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (b : APt (fppfO B S hS) L (op T')),
      ∃ G : AttractorPt aX N T', G.toPoint = ψ.app t b := by
    intro T' t b
    have hm : ψ.app t b ∈ attractorImage aX L T' := by
      refine ⟨(magnetAction aX L).smul b (AttractorPt.baseChange t ψ), ?_⟩
      change ψ.app (𝟙 T' ≫ t) (APt.res (𝟙 T').op b * 1) = _
      have e : APt.res (𝟙 T').op b = b := APt.res_id b
      rw [e, mul_one, Category.id_comp]
    exact h T' hm
  choose G hGp using @hG
  refine ⟨⟨fun t b => G t b, ?_, ?_⟩, ?_⟩
  · intro T' T'' s t b
    apply hinj
    rw [hGp, AttractorPt.toPoint_baseChange, hGp, ψ.naturality]
  · intro T' t k b
    apply hinj
    rw [hGp, ψ.equivariant]
    change _ = aX.smul (APt.res (𝟙 T').op k) (G t b).toPoint
    have e : APt.res (𝟙 T').op k = k := APt.res_id k
    rw [e, hGp]
  · change (G (𝟙 T) 1).toPoint = _
    rw [hGp]
    rfl

/-- `X^L ⊆ X^N` implies `X^{N ∩ L} = X^L`. -/
theorem attractorImage_inf_of_le (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : IsStronglyFPRAtlas aU aX f) {N L : AddSubmonoid M}
    (hb : (N.FG ∧ L.FG) ∨ IsLimitPreserving X)
    (h : attractorImage aX L ≤ attractorImage aX N) :
    attractorImage aX (N ⊓ L) = attractorImage aX L := by
  refine le_antisymm (attractorImage_monotone aX inf_le_right) ?_
  intro T x hx
  obtain ⟨ψ, rfl⟩ := hx
  obtain ⟨Ψ, hΨ⟩ := exists_iter_of_image_le hX hsep h ψ
  obtain ⟨χ, hχ⟩ := exists_inf_of_bi hX hsep hat hb Ψ.toBi
  exact ⟨χ, by rw [hχ, IterPt.toPoint_toBi, hΨ]⟩

/-- **Every action is a join action**: the sum of every family of pure magnets is pure. `X` a
separated algebraic space with an `S`-affine strongly-FPR atlas, limit preserving, as in Proposition
3.32 (ii). -/
theorem isPure_sSup_attractorImage (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : IsStronglyFPRAtlas aU aX f) (hlim : IsLimitPreserving X) {s : Set (AddSubmonoid M)}
    (hs : ∀ N ∈ s, IsPure (attractorImage aX) N) :
    IsPure (attractorImage aX) (sSup s) := by
  intro K hK
  refine sSup_le fun N hN => ?_
  have hle : attractorImage aX N ≤ attractorImage aX K :=
    hK ▸ attractorImage_monotone aX (le_sSup hN)
  have e := attractorImage_inf_of_le hX hsep hat (Or.inr hlim) hle
  exact (hs N hN _ e.symm).trans inf_le_left

end Site

end AlgMag

#print axioms AlgMag.isPure_sSup_attractorImage
