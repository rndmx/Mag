/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Final
import AlgMag.Sec3Final

/-!
# Propositions 3.31 (ii), 3.32 (ii), 3.32 (iii) for algebraic spaces, as printed

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §3. No separatedness of `S` or `X`, no
finite presentation, no atlas: everything comes from Lemma D (`AlgMag.SD.prop331_space_final`,
`AlgMag.SD.prop332_space_final`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Unrestrict

open AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Proposition 3.31 (ii)**, as printed: `M`, `Z` finitely generated abelian groups, `f : M → Z`, `Y` a magnet of
`Z`; for any algebraic space `X` over any scheme `S`, `X^{f⁻¹(Y) ⊂ M} = X^{Y ⊂ Z}`. -/
theorem prop331_ii {M Z : Type u} [AddCommGroup M] [AddCommGroup Z] [AddGroup.FG M] [AddGroup.FG Z]
    (hX : IsAlgebraicSpace B S hS X) (act : AAction (fppfO B S hS) M X) (f : M →+ Z) (Y : AddSubmonoid Z)
    (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong act : AttractorPt act (Y.comap f) T → AttractorPt (actAlong f act) Y T) :=
  AlgMag.SD.prop331_space_final hX T

/-- **Proposition 3.32 (ii)**, as printed: `M` a finitely generated abelian group, `N`, `L` magnets; for any
algebraic space `X` over any scheme `S`, `X^{N ∩ L} = (X^N)^L`. -/
theorem prop332_ii {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    (hX : IsAlgebraicSpace B S hS X) (act : AAction (fppfO B S hS) M X) (N L : AddSubmonoid M)
    (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt act (N ⊓ L) T → IterPt act N L T) :=
  AlgMag.SD.prop332_space_final hX T

/-- **Proposition 3.32 (iii)** for algebraic spaces: `f : M → Z` injective into a finitely generated abelian
group (`M` cancellative, `Z = M^gp`), `X` a separated algebraic space over any `S`, `N`, `L` magnets of `M`:
`(X^N)^L = X^{N ∩ L}`. No atlas; the printed hypothesis "`X^N` separated" is not needed. -/
theorem prop332_iii_space {M Z : Type u} [AddCommMonoid M] [AddCommGroup Z] [AddMonoid.FG Z]
    {f : M →+ Z} (hf : Function.Injective f) {aX : AAction (fppfO B S hS) M X}
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (N L : AddSubmonoid M)
    (T : BigFppfOver B S hS) :
    Function.Bijective fun χ : AttractorPt aX (N ⊓ L) T =>
      (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L) (hKinf' N L)) :=
  prop332_iii_of hf hX hsep (fun {T'} φ => by
    have : AddGroup.FG Z := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
    obtain ⟨χ, hχ⟩ := (AlgMag.SD.prop332_space_final hX (aX := actAlong f aX)
      (N := N.map f) (L := L.map f) T').2 ((iterEquivBi T').symm φ)
    have h : χ.toBi _ = φ := (iterEquivBi T').symm.injective hχ
    exact ⟨χ, by rw [← h]; exact (AttractorPt.toPoint_toBi _ χ).symm⟩) T

/-- **Proposition 3.32 (iii)** as printed, for algebraic spaces: `M` cancellative, `M^gp` finitely generated,
`X` a separated algebraic space. -/
theorem prop332_iii_space_gp {M : Type u} [AddCommMonoid M] [IsCancelAdd M]
    [AddMonoid.FG (Algebra.GrothendieckAddGroup M)] {aX : AAction (fppfO B S hS) M X}
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (N L : AddSubmonoid M)
    (T : BigFppfOver B S hS) :
    Function.Bijective fun χ : AttractorPt aX (N ⊓ L) T =>
      (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L) (hKinf' N L)) :=
  prop332_iii_space (f := Algebra.GrothendieckAddGroup.of) Algebra.GrothendieckAddGroup.of_injective hX hsep N L T

end AlgMag.Unrestrict

#print axioms AlgMag.Unrestrict.prop331_ii
#print axioms AlgMag.Unrestrict.prop332_ii
#print axioms AlgMag.Unrestrict.prop332_iii_space
#print axioms AlgMag.Unrestrict.prop332_iii_space_gp
