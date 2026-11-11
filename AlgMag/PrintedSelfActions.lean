/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SelfActionsMain
import AlgMag.Sec3Functorial

/-!
# Self-actions, Proposition 4.2: the printed proof

Mayeux, *Algebraic magnetism invariants of self-actions of diagonalizable monoid schemes*, Semigroup Forum
112 (2026) 532–540, Proposition 4.2: "By [11, Fact 3.15] we have an equivariant morphism
`𝔸(M)_S → 𝔸(M^×)_S`. We have `(𝔸(M^×)_S)^N = 𝔸(M^×)_S^{M^× ∩ N}`. So by Lemma 4.1 we have
`(𝔸(M^×)_S)^N = ∅`. This implies that `(𝔸(M)_S)^N = ∅`."

`AlgMag.SelfActions.prop42` proves the same statement by the ideal inclusion, and stays.
-/

suppress_compilation

open CategoryTheory AlgebraicGeometry Magnetism Opposite

universe u

namespace AlgMag.SelfActions

open AlgMag.GB

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]

/-- The equivariant morphism `𝔸(L')_S → 𝔸(L)_S` for `L ≤ L'`, by restriction of characters. -/
def restrictHom {L L' : AddSubmonoid M} (h : L ≤ L') (S : Scheme.{u}) :
    EquivariantHom (aAction L' S) (aAction L S) where
  hom := yoneda.map (Amap (AddSubmonoid.inclusion h) S)
  map_smul := by
    intro U g x
    refine (pts (unop U)).injective ?_
    change pts (unop U) (((pts (unop U)).symm _) ≫ Amap (AddSubmonoid.inclusion h) S) =
      pts (unop U) ((pts (unop U)).symm _)
    rw [pts_comp_Amap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine MonoidHom.ext fun l => ?_
    change _ = _ * (pts (unop U) (x ≫ Amap (AddSubmonoid.inclusion h) S)) l
    rw [pts_comp_Amap]
    rfl

/-- **Proposition 4.2**, printed proof: a `T`-point of `(𝔸(M)_S)^N`, `M^× ⊄ N`, is sent to a `T`-point of
`(𝔸(M^×)_S)^N`, and `T` is empty by Lemma 4.1 for the group `M^×`. -/
theorem prop42_printed {N : AddSubmonoid M} (h : ¬ unitsOf M ≤ N) :
    IsEmpty (Zatt (aAction (⊤ : AddSubmonoid M) S) N).left := by
  have h1 := monIdeal_eq_of_group (L := unitsOf M) (N := N)
    (fun _ hx => unitsFace_isGroup _ hx) h
  have h0 : (0 : M) ∈ monIdeal (unitsOf M) N := h1.symm ▸ zero_mem (unitsOf M)
  exact isEmpty_of_zero_mem (unitsOf M) h0
    (AttractorPt.push (restrictHom le_top S) (attEquiv (aAction (⊤ : AddSubmonoid M) S) N _ (𝟙 _)))

end AlgMag.SelfActions

#print axioms AlgMag.SelfActions.prop42_printed
