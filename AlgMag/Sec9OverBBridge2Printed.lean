/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge2DX

/-!
# §9 of *Algebraic Magnetism* over an algebraic space `B`, for the printed notion of quasi-coherence

`PrintedQCoh F`: `F` is a Zariski sheaf and, over each affine `T` of the site of `B`, it restricts to a
quasi-coherent sheaf of modules on `(Sch/T)_fppf` (Stacks `IsQuasicoherentOnSite`). By `fppf03DX` this
is `IsQCoh F` with no further hypothesis, so Propositions 9.1, 9.9-9.13 and Remark 9.14 hold for it.

A module of `Space.Modules` on the small étale site of `B` is not shown here to give a `PrintedQCoh`
module.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

namespace AlgMag.B2

open AlgMag.S9B AlgMag.S9BF AlgMag.S9BS AlgMag.S9BR AlgMag.S9BP
open AlgMag.S9 (PMod HModule)

/-- Quasi-coherent `𝒪_B`-modules, in the printed sense read on the fppf sites of the affine `T`. -/
def PrintedQCoh (F : PMod (OB Bsp)) : Prop :=
  (∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (R : Sieve T),
    coverSieve T 𝒰 ≤ R → Presieve.IsSheafFor F.toPresheaf R.arrows) ∧
  ∀ (T : SB Bsp) [IsAffine T.left], IsQCohAt F T

/-- `IsQCoh` is discharged from the printed notion. -/
theorem PrintedQCoh.isQCoh {F : PMod (OB Bsp)} (h : PrintedQCoh F) : IsQCoh F :=
  (isQCoh_iff_printed F).2 h

variable {F G : PMod (OB Bsp)}

/-- **Proposition 9.1** on affine `T`, with the printed canonical map, for the printed notion. -/
theorem prop91_printed {X : (SB Bsp)ᵒᵖ ⥤ Type u} (r : AffOver X) (hG : PrintedQCoh G) (T : SB Bsp)
    [IsAffine T.left] :
    letI := ((OB Bsp).map (r.pr T).op).hom.toAlgebra
    ∃ Φ : ((OB Bsp).obj (op (r.P T)) ⊗[(OB Bsp).obj (op T)] G.obj (op T)) ≃ PushSec X G T,
      (∀ p q {T' : SB Bsp} (t : T' ⟶ T) (x : X.obj (op T')),
        (Φ (p + q)).val t x = (Φ p).val t x + (Φ q).val t x) ∧
      ∀ (a : (OB Bsp).obj (op (r.P T))) (g : G.obj (op T)) {T' : SB Bsp} (t : T' ⟶ T)
        (x : X.obj (op T')),
        (Φ (a ⊗ₜ g)).val t x = ((OB Bsp).map (r.lift t x).op).hom a • G.map t.op g :=
  prop91_canonical r hG.isQCoh T

/-- **Proposition 9.9** for an affine morphism of algebraic spaces, for the printed notion. -/
def prop99_printed {Y : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ Bsp)
    (hp : Space.IsAffineHom Bs S hS p) (hG : PrintedQCoh G) :
    HomAt F G (Vp p) ≃ HomPush F G (affOverOfIsAffineHom p hp) :=
  prop99_space p hp hG.isQCoh

/-- **Proposition 9.10** for an affine monoid algebraic space, for the printed notion. -/
def prop910_printed {Y : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ Bsp)
    (hp : Space.IsAffineHom Bs S hS p) {H : (SB Bsp)ᵒᵖ ⥤ MonCat.{u}} (e : Vp p ≅ H ⋙ forget MonCat)
    (hF : PrintedQCoh F) :
    HModule H F ≃ CoactionAff F (affOverOfIso (affOverOfIsAffineHom p hp) e) :=
  prop910_space p hp e hF.isQCoh

variable {M : Type u} [AddCommMonoid M] [Countable M]

/-- **Propositions 9.10 and 9.11** for `𝔸(M)_B`, for the printed notion. -/
def prop911_printed (hF : PrintedQCoh F) :
    CoactionAff F (affOverHm (M := M) (Bsp := Bsp)) ≃ Decomp F M :=
  coactionEquivDecomp hF.isQCoh

/-- **Proposition 9.12** over a quasi-compact algebraic space, for the printed notion. -/
theorem prop912_printed {n : ℕ} {Y : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} (hF : PrintedQCoh F)
    (p : Y ⟶ Bsp) (hY : IsAlgebraicSpace Bs S hS Y) (hq : Space.IsQuasiCompactSpace Bs S hS Y) :
    Nonempty (CochainV F M (Vp p) n ≃ ((Fin n → M) →₀ SecF F (Vp p))) :=
  prop912_space hF.isQCoh p hY hq

/-- **Proposition 9.13 and Remark 9.14**, for the printed notion. -/
theorem prop913_printed {n : ℕ} (hF : PrintedQCoh F)
    (R : CoactionAff F (affOverHm (M := M) (Bsp := Bsp)))
    {V : (SB Bsp)ᵒᵖ ⥤ Type u} (c : CochainV F M V (n + 1))
    (hc : ∀ {T : SB Bsp} (t : V.obj (op T)) g,
      (deltaV ((hModuleEquivCoaction _ hF.isQCoh).symm R) c).app t g = 0) :
    ∃ e : CochainV F M V n, deltaV ((hModuleEquivCoaction _ hF.isQCoh).symm R) e = c :=
  prop913_of_coaction hF.isQCoh R c hc

end AlgMag.B2

#print axioms AlgMag.B2.PrintedQCoh.isQCoh
#print axioms AlgMag.B2.prop91_printed
#print axioms AlgMag.B2.prop99_printed
#print axioms AlgMag.B2.prop910_printed
#print axioms AlgMag.B2.prop911_printed
#print axioms AlgMag.B2.prop912_printed
#print axioms AlgMag.B2.prop913_printed
