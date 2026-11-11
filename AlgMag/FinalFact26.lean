/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FixesFact26ii
import AlgMag.Sec9OverB

/-!
# Fact 2.6 (ii) of *Algebraic Magnetism*: `𝒪_B[N]` as a presheaf of bialgebras

The site is the big site `SB` of `B` of §9 (schemes `T` of the site with a point `T → B`), with structure presheaf `OB`.
`ONB N` is `T ↦ 𝒪_B(T)[N]`, the presheaf of **Definition 2.3 (iii)**, whose values are bialgebras over `𝒪_B(T)` and
whose restrictions send `X^n` to `X^n`.

`fact26_ii_presheaf`: the sections of `q_* 𝒪` on `𝔸(N)_T`, which is the base change of `𝔸(N)_B → B` to `T`
(`fact26_ii_chart`), receive `ONB N` compatibly with the restrictions, bijectively on affine `T`. So on the base of affine
objects `q_* 𝒪` is `ONB N`, and the bialgebra structure is that of the monoid space: comultiplication `fact26_i_comul`,
counit `fact26_i_counit`, on each `T`; compatibility of the multiplications in `T`, `baseHom_mul`.

The printed `B_{spaces,étale}` is replaced by `SB`, as in §9.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace AlgMag.Final

open AlgMag.S9B AlgMag.GB

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  (Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u) (N : Type u) [AddCommMonoid N]

/-- **Definition 2.3 (iii)**: the presheaf `T ↦ 𝒪_B(T)[N]` on the site of `B`. -/
def ONB : (SB Bsp)ᵒᵖ ⥤ CommRingCat.{u} where
  obj T := CommRingCat.of (AddMonoidAlgebra ((OB Bsp).obj T) N)
  map f := CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom N ((OB Bsp).map f).hom)
  map_id T := by
    refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_) <;> simp
  map_comp f g := by
    refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_) <;> simp

variable {Bsp N}

/-- The comparison at `T`: `𝒪_B(T)[N] → Γ(𝔸(N)_T, 𝒪)`, `X^n ↦ X^n`. -/
def cmpT (T : SB Bsp) : AddMonoidAlgebra Γ(T.left, ⊤) N →+* Γ((A N T.left).left, (A N T.left).hom ⁻¹ᵁ ⊤) :=
  evalU N (A N T.left) (GB.univ N T.left) ⊤

/-- **Fact 2.6 (ii)**, the algebra: on affine `T`, `𝒪_B(T)[N]` is the ring of functions of `𝔸(N)_T`. -/
theorem cmpT_bijective (T : SB Bsp) [IsAffine T.left] : Function.Bijective (cmpT (N := N) T) :=
  cmp_bijective N T.left (isAffineOpen_top T.left)

/-- **Fact 2.6 (ii)**, compatibility with the restrictions along `t : T' → T`. -/
theorem cmpT_natural {T T' : SB Bsp} (t : T' ⟶ T) :
    ((baseA N (SB.Hom.left t)).appLE _ _ (preimage_baseA (SB.Hom.left t) ⊤)).hom.comp (cmpT (N := N) T) =
      (cmpT (N := N) T').comp (AddMonoidAlgebra.mapRingHom N ((SB.Hom.left t).app ⊤).hom) :=
  evalU_baseA (SB.Hom.left t) ⊤

/-- **Fact 2.6 (ii)**, the comultiplication at `T`: that of `𝒪_B(T)[N]` is the multiplication of `𝔸(N)_T`. -/
theorem cmpT_comul (T : SB Bsp) :
    (overPull (mul N T.left) ⊤).hom.comp (cmpT (N := N) T) =
      (evalTensor N (A2 N T.left) (pts _ (CartesianMonoidalCategory.fst _ _))
        (pts _ (CartesianMonoidalCategory.snd _ _)) ⊤).comp
        (Bialgebra.comulAlgHom Γ(T.left, ⊤) (AddMonoidAlgebra Γ(T.left, ⊤) N)).toRingHom :=
  fact26_i_comul N T.left ⊤

/-- **Fact 2.6 (ii)**, the counit at `T`. -/
theorem cmpT_counit (T : SB Bsp) :
    (overPull (unitA N T.left) ⊤).hom.comp (cmpT (N := N) T) =
      ((baseO T.left).hom.app ⊤).hom.comp
        (Bialgebra.counitAlgHom Γ(T.left, ⊤) (AddMonoidAlgebra Γ(T.left, ⊤) N)).toRingHom :=
  fact26_i_counit N T.left ⊤

/-- **Fact 2.6 (ii)**, the restrictions of `ONB N` are maps of bialgebras: `X^n ↦ X^n`, and `Δ X^n = X^n ⊗ X^n`,
`ε X^n = 1`, hold in every value. -/
theorem onb_map_single {T T' : (SB Bsp)ᵒᵖ} (f : T ⟶ T') (n : N) :
    ((ONB Bsp N).map f).hom (AddMonoidAlgebra.single n (1 : (OB Bsp).obj T)) =
      AddMonoidAlgebra.single n (1 : (OB Bsp).obj T') := by
  change AddMonoidAlgebra.mapRingHom N ((OB Bsp).map f).hom _ = _
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

end AlgMag.Final

#print axioms AlgMag.Final.cmpT_bijective
#print axioms AlgMag.Final.cmpT_natural
#print axioms AlgMag.Final.cmpT_comul
#print axioms AlgMag.Final.cmpT_counit
#print axioms AlgMag.Final.onb_map_single
