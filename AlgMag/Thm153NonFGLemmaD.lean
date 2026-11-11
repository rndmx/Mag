/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Final

/-!
# Lemma 1.1 of `notes/thm153-wall.md` at a finite level: invariance on the universal point gives Lemma D

`δ : P → Γ` with `Γ` finitely generated, `P` countable. If `x ∈ X(𝔸(P)_T)` satisfies
`x ∘ act = x ∘ pr` on `D(Γ) × 𝔸(P)_T = 𝔸(Γ × P)_T` (the universal point), then `x` is invariant
(`IsInvPt`), hence (Lemma D, unconditional by `AlgMag.SD.SDR4_localFactorAll`) `x` descends uniquely
to `𝔸(δ⁻¹ 0)_T`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.NonFGD

open AlgMag AlgMag.SD

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {Γ P : Type u} [AddCommGroup Γ] [Countable Γ] [AddCommMonoid P] [Countable P] (δ : P →+ Γ)

/-- The coaction `p ↦ (δ p, p)`. -/
def actH : P →+ Γ × P := (δ.prod (AddMonoidHom.id P))

/-- The projection `p ↦ (0, p)`. -/
def prH : P →+ Γ × P := (AddMonoidHom.inr Γ P)

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The pair point `(g, c)` of `𝔸(Γ × P)`. -/
noncomputable def pairPt {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) Γ (op T'))
    (c : APt (fppfO B S hS) P (op T')) : APt (fppfO B S hS) (Γ × P) (op T') :=
  g.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst Γ P)) *
    c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd Γ P))

omit [Countable Γ] [Countable P] in
lemma along_act_pair {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) Γ (op T'))
    (c : APt (fppfO B S hS) P (op T')) :
    APt.along (actH δ) (pairPt g c) = g.comp (AddMonoidHom.toMultiplicative δ) * c := by
  ext p
  rfl

omit [Countable Γ] [Countable P] in
lemma along_pr_pair {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) Γ (op T'))
    (c : APt (fppfO B S hS) P (op T')) : APt.along (prH (Γ := Γ) (P := P)) (pairPt g c) = c := by
  ext p
  change g (Multiplicative.ofAdd 0) * c p = c p
  rw [ofAdd_zero, map_one, one_mul]

/-- **Invariance from the universal point**: `x ∘ act = x ∘ pr` on `𝔸(Γ × P)_T` gives `IsInvPt`. -/
theorem isInvPt_of_univ (x : X.obj (op (specObj P T)))
    (h : X.map (specAlong T (actH δ)).op x = X.map (specAlong T (prH (Γ := Γ) (P := P))).op x) :
    IsInvPt X δ x := by
  intro T' t g c
  rw [← along_act_pair δ g c, specLift_along, op_comp, Functor.map_comp_apply, h,
    ← Functor.map_comp_apply, ← op_comp, ← specLift_along, along_pr_pair]

/-- **Lemma 1.1 at level `β`**: `X` an algebraic space, `Γ` finitely generated, `P` countable,
`x ∈ X(𝔸(P)_T)` invariant on the universal point. Then `x` comes from a unique point over `𝔸(δ⁻¹ 0)_T`. -/
theorem existsUnique_desc_of_univ [AddGroup.FG Γ] (hX : IsAlgebraicSpace B S hS X)
    (x : X.obj (op (specObj P T)))
    (h : X.map (specAlong T (actH δ)).op x = X.map (specAlong T (prH (Γ := Γ) (P := P))).op x) :
    ∃! x₀ : X.obj (op (specObj (AddSubmonoid.comap δ ⊥) T)),
      X.map (specAlong T (AddSubmonoid.comap δ ⊥).subtype).op x₀ = x := by
  have hD := lemmaD_space hX (SDR4_localFactorAll hX)
  have hj : Function.Injective (AddSubmonoid.comap δ ⊥).subtype := Subtype.val_injective
  have hk : ∀ p, δ p = 0 ↔ p ∈ Set.range (AddSubmonoid.comap δ ⊥).subtype := fun p =>
    ⟨fun hp => ⟨⟨p, hp⟩, rfl⟩, fun ⟨q, hq⟩ => hq ▸ q.2⟩
  obtain ⟨x₀, hx₀⟩ := hD.desc δ _ hj hk T x (isInvPt_of_univ δ x h)
  exact ⟨x₀, hx₀, fun y hy => hD.uniq δ _ hj hk T y x₀ (hy.trans hx₀.symm)⟩

end AlgMag.NonFGD

#print axioms AlgMag.NonFGD.existsUnique_desc_of_univ
