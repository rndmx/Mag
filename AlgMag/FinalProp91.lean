/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge2Printed

/-!
# Proposition 9.1 of *Algebraic Magnetism* as an isomorphism of sheaves

`prop91_printed` gives the printed canonical map, a bijection, on one affine `T`. Here the family over all
affine objects of the site of `B`, and its compatibility with the restrictions: this is an isomorphism of
sheaves on the affine objects, which form a base of the site. `(f_* f^* G)(T) = PushSec X G T`, `𝒜(T) = 𝒪(T ×_B X)`.
The tensor product is read on affine objects, where `G ⊗_𝒪 𝒜` has the values `𝒜(T) ⊗_{𝒪(T)} G(T)`: the presheaf
tensor product is not sheafified as an object.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace AlgMag.Final

open AlgMag.S9B AlgMag.S9BF AlgMag.S9BS AlgMag.S9BR AlgMag.S9BP AlgMag.B2
open AlgMag.S9 (PMod)

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} {G : PMod (OB Bsp)} {X : (SB Bsp)ᵒᵖ ⥤ Type u}

/-- Restriction of a section of `f_* f^* G` along `s : T' → T`. -/
def pushRes {T T' : SB Bsp} (s : T' ⟶ T) (σ : PushSec X G T) : PushSec X G T' where
  val t x := σ.val (t ≫ s) x
  naturality := fun q t x => by
    rw [Category.assoc]
    exact σ.naturality q (t ≫ s) x

/-- `𝒜(T) ⊗_{𝒪(T)} G(T)`, the value of `G ⊗_𝒪 𝒜` on an affine `T`. -/
abbrev TensAt (r : AffOver X) (G : PMod (OB Bsp)) (T : SB Bsp) [IsAffine T.left] : Type u :=
  letI := ((OB Bsp).map (r.pr T).op).hom.toAlgebra
  (OB Bsp).obj (op (r.P T)) ⊗[(OB Bsp).obj (op T)] G.obj (op T)

/-- The pure tensor `a ⊗ g` in `TensAt`. -/
abbrev tmulAt (r : AffOver X) (T : SB Bsp) [IsAffine T.left] (a : (OB Bsp).obj (op (r.P T)))
    (g : G.obj (op T)) : TensAt r G T :=
  letI := ((OB Bsp).map (r.pr T).op).hom.toAlgebra
  a ⊗ₜ g

/-- **Proposition 9.1**: `G ⊗_𝒪 𝒜 ≅ f_* f^* G` on affine objects. `Φ` is the printed canonical map, additive,
bijective at each affine `T`, and it commutes with the restrictions along `s : T' → T`, where on `𝒜 ⊗ G` the
restriction of `a ⊗ g` is `(s ×_B X)^* a ⊗ s^* g`. -/
theorem prop91_iso (r : AffOver X) (hG : PrintedQCoh G) :
    ∃ Φ : ∀ (T : SB Bsp) [IsAffine T.left], TensAt r G T ≃ PushSec X G T,
      (∀ (T : SB Bsp) [IsAffine T.left] (p q : TensAt r G T) {T' : SB Bsp} (t : T' ⟶ T) (x : X.obj (op T')),
        (Φ T (p + q)).val t x = (Φ T p).val t x + (Φ T q).val t x) ∧
      (∀ (T : SB Bsp) [IsAffine T.left] (a : (OB Bsp).obj (op (r.P T))) (g : G.obj (op T))
        {T' : SB Bsp} (t : T' ⟶ T) (x : X.obj (op T')),
        (Φ T (tmulAt r T a g)).val t x = ((OB Bsp).map (r.lift t x).op).hom a • G.map t.op g) ∧
      ∀ {T T' : SB Bsp} [IsAffine T.left] [IsAffine T'.left] (s : T' ⟶ T)
        (a : (OB Bsp).obj (op (r.P T))) (g : G.obj (op T)),
        Φ T' (tmulAt r T' (((OB Bsp).map (r.lift (r.pr T' ≫ s) (r.univ T')).op).hom a) (G.map s.op g)) =
          pushRes s (Φ T (tmulAt r T a g)) := by
  choose Φ h1 h2 using fun (T : {T : SB Bsp // IsAffine T.left}) =>
    haveI := T.2; prop91_printed r hG T.1
  refine ⟨fun T _ => Φ ⟨T, ‹_›⟩, fun T _ p q _ t x => h1 ⟨T, ‹_›⟩ p q t x,
    fun T _ a g _ t x => h2 ⟨T, ‹_›⟩ a g t x, ?_⟩
  intro T T' _ _ s a g
  ext W t x
  change (Φ ⟨T', ‹_›⟩ _).val t x = (Φ ⟨T, ‹_›⟩ _).val (t ≫ s) x
  rw [show (Φ ⟨T', ‹_›⟩ (tmulAt r T' _ _)).val t x = _ from h2 ⟨T', ‹_›⟩ _ _ t x,
    show (Φ ⟨T, ‹_›⟩ (tmulAt r T a g)).val (t ≫ s) x = _ from h2 ⟨T, ‹_›⟩ a g (t ≫ s) x]
  have e : r.lift t x ≫ r.lift (r.pr T' ≫ s) (r.univ T') = r.lift (t ≫ s) x := by
    rw [r.comp_lift, ← Category.assoc, r.lift_pr, r.lift_univ]
  have e2 : ((OB Bsp).map (r.lift t x).op).hom
      (((OB Bsp).map (r.lift (r.pr T' ≫ s) (r.univ T')).op).hom a) =
      ((OB Bsp).map (r.lift (t ≫ s) x).op).hom a := by
    rw [← e, op_comp, Functor.map_comp]; rfl
  rw [e2, op_comp, G.map_comp]

end AlgMag.Final

#print axioms AlgMag.Final.prop91_iso
