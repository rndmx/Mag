/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.AppendixA3

/-!
# Remark A.7 of *Algebraic Magnetism*: `G` infinitesimal, for `G = D(M)`

The content of Remark A.7 is the conclusion "`X^G → X` is closed" for `G` infinitesimal, with a second proof through
the quotient `X/G` ([30, Th. 5.3], not in Lean). The conclusion is proved here from `thmA1_closed` (Theorem A.1, printed
route), since an infinitesimal `D(M)` has connected fibres. The second proof is not formalized.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.AppR AlgMag.AppA3

/-- `D(M)` has infinitesimal fibres over `S`: the augmentation ideal of `K[M]` is nilpotent for all fields `K → S`. -/
def InfinitesimalFibres (M : Type u) [AddCommGroup M] (S : Scheme.{u}) : Prop :=
  ∀ (K : Type u) [Field K], (Spec (.of K) ⟶ S) → ∃ k : ℕ, augI K M ^ k = ⊥

/-- Infinitesimal fibres imply connected fibres. -/
theorem connectedFibres_of_infinitesimal (M : Type u) [AddCommGroup M] (S : Scheme.{u})
    (h : InfinitesimalFibres M S) : ConnectedFibres M S := by
  intro K _ f
  obtain ⟨k, hk⟩ := h K f
  have hmax : (augI K M).IsMaximal := by
    rw [← ker_augHom]
    exact RingHom.ker_isMaximal_of_surjective _ fun r => ⟨AddMonoidAlgebra.single 0 r, by simp [augHom]⟩
  haveI : Subsingleton (PrimeSpectrum (AddMonoidAlgebra K M)) := by
    refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
    have key : ∀ p : PrimeSpectrum (AddMonoidAlgebra K M), p.asIdeal = augI K M := by
      intro p
      refine (hmax.eq_of_le p.2.ne_top ?_).symm
      intro x hx
      have : x ^ k ∈ augI K M ^ k := Ideal.pow_mem_pow hx k
      rw [hk] at this
      exact p.2.mem_of_pow_mem k (by rw [(Ideal.mem_bot.mp this)]; exact p.asIdeal.zero_mem)
    rw [key, key]
  haveI : Nonempty (PrimeSpectrum (AddMonoidAlgebra K M)) := ⟨⟨augI K M, hmax.isPrime⟩⟩
  haveI : PreconnectedSpace (PrimeSpectrum (AddMonoidAlgebra K M)) := ⟨Set.Subsingleton.isPreconnected Set.subsingleton_of_subsingleton⟩
  exact { toNonempty := inferInstance }

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Remark A.7**, conclusion, `G = D(M)` infinitesimal: `X^G → X` is a closed immersion. -/
theorem remA7 [AddGroup.FG M] [IsLocallyNoetherian S] (hX : IsAlgebraicSpace B S hS X)
    (hC : ChartsOfFiniteType X) (act : AAction (fppfO B S hS) M X) (h : InfinitesimalFibres M S) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) (fixedPoints act).ι :=
  thmA1_closed hX hC act (torsionResidue_of_connected M S (connectedFibres_of_infinitesimal M S h))

end AlgMag.Final

#print axioms AlgMag.Final.remA7
