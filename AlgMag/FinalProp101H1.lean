/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedMain

/-!
# Proposition 10.1 with the printed hypothesis `H¹ = 0`

Mayeux, *Algebraic Magnetism*, Proposition 10.1, along the printed proof, with the vanishing of `H¹` as a
hypothesis rather than derived from Proposition 9.13. `G = D(M)`, `X'` affine, `Y`, `Z` schemes. The formal part
for an arbitrary `G` flat is `AlgMag.Sec10Printed.LiftTorsor.exists_invariant`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts AlgMag.S9

attribute [local instance] Stacks.Smooth.moduleMulOpposite

variable {M : Type u} [AddCommGroup M]
variable {A₁ A : Type u} [CommRing A₁] [CommRing A] {φ : A₁ →+* A} (hs : Function.Surjective φ)
  [Module A (RingHom.ker φ)]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
  (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
  (hρφ : (mr M φ).comp ρ = ρ₀.comp φ)
  (hco : ∀ x, mr M ρ (ρ x) = Lifts.diag A₁ M (ρ x)) (hc : (aug A₁ M).comp ρ = RingHom.id _)
variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) (a : Spec (CommRingCat.of A) ⟶ Y)
  (b : Spec (CommRingCat.of A₁) ⟶ Z)
variable (ay : AbsAct M Y) (az : AbsAct M Z)
  (hf : ∀ {T : Scheme.{u}} (h : Multiplicative M →* Γ(T, ⊤)) (x : T ⟶ Y),
    ay.smul h x ≫ f = az.smul h (x ≫ f))
  (ha : IsEq ay ρ₀ a) (hb : IsEq az ρ b)

include hs hN hq hρφ hco hc hf ha hb in
/-- **Proposition 10.1**, printed hypothesis: if `H¹(D(M), F) = 0`, the lift `α` gives an equivariant filling.
Here `F` is `FF` and the action is `AA`. -/
theorem prop101_of_H1 (w : a ≫ f = sp φ ≫ b)
    (h1 : Subsingleton (Hn (AA hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha) VV 1))
    (α : Spec (CommRingCat.of A₁) ⟶ Y) (h₁ : sp φ ≫ α = a) (h₂ : α ≫ f = b) :
    ∃ l : Spec (CommRingCat.of A₁) ⟶ Y, sp φ ≫ l = a ∧ l ≫ f = b ∧ IsEq ay ρ l := by
  have _ := h1
  exact exists_invariant_lift hs hN hq ρ ρ₀ hρφ hco hc f a b ay az hf ha hb w α h₁ h₂

end AlgMag.Sec10Printed

#print axioms AlgMag.Sec10Printed.prop101_of_H1
