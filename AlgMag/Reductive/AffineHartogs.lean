/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import StacksFrontier.AlgebraicGeometry.Divisors.PuncturedSpectrumAffineCriterion

/-!
# (G2) Affine Hartogs: removing a closed point of local dimension ≥ 2 destroys affineness

Lemma (G2) of `equivalence-reductive/T-steps.md`: if `V` is an affine scheme and `v` a closed
point whose local ring has dimension `≥ 2`, then `V ∖ {v}` is not affine.  For a smooth
irreducible affine variety of dimension `≥ 2` over an algebraically closed field the local ring at
a closed point has dimension `dim V ≥ 2`, so this is the form used in step 6 of T4.

No normality is needed: the proof is Stacks Tag 0BCU (AxiomMath Stacks,
`Stacks.Divisors.krullDimLE_one_stalk_at_genericPoint_compl_affineOpenImmersion`), which rests on
Tag 0BCR (the punctured spectrum of a Noetherian local ring is affine iff `dim ≤ 1`).  The
complement of `V ∖ {v}` is the point `{v}`, whose only irreducible component has generic point `v`.
-/

open AlgebraicGeometry CategoryTheory Topology

universe u

namespace AlgMag.Reductive

/-- The open subscheme `X ∖ {x}` for a closed point `x`. -/
def puncturedOpen {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X)) : X.Opens :=
  ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩

/-- **(G2), scheme form.**  Let `X` be an affine locally Noetherian scheme and `x` a closed point
with `dim 𝒪_{X,x} ≥ 2`.  Then `X ∖ {x}` is not an affine open. -/
theorem not_isAffineOpen_puncturedOpen (X : Scheme.{u}) [IsAffine X] [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X)) (hdim : ¬ Ring.KrullDimLE 1 (X.presheaf.stalk x)) :
    ¬ IsAffineOpen (puncturedOpen x hx) := by
  intro hU
  set U := puncturedOpen x hx
  have : IsAffine U.toScheme := hU
  have : IsAffineHom U.ι := isAffineHom_of_isAffine _
  have hcompl : ((U : Set X)ᶜ) = {x} := by
    simp [U, puncturedOpen]
  let ξ : ↑((U : Set X)ᶜ) := ⟨x, by rw [hcompl]; rfl⟩
  have : Subsingleton ↑((U : Set X)ᶜ) := by
    rw [hcompl]; infer_instance
  have : Nonempty ↑((U : Set X)ᶜ) := ⟨ξ⟩
  have : IrreducibleSpace ↑((U : Set X)ᶜ) :=
    { isPreirreducible_univ := (Set.subsingleton_of_subsingleton).isPreirreducible
      toNonempty := inferInstance }
  have hZ : (Set.univ : Set ↑((U : Set X)ᶜ)) ∈ irreducibleComponents ↑((U : Set X)ᶜ) := by
    rw [irreducibleComponents_eq_singleton]; rfl
  have hξ : IsGenericPoint ξ (Set.univ : Set ↑((U : Set X)ᶜ)) := by
    rw [IsGenericPoint, Set.eq_univ_iff_forall]
    intro y
    rw [Subsingleton.elim y ξ]
    exact subset_closure rfl
  exact hdim (Stacks.Divisors.krullDimLE_one_stalk_at_genericPoint_compl_affineOpenImmersion
    X U hZ hξ)

/-- **(G2), algebraic form.**  For a Noetherian ring `A` and a maximal ideal `𝔪` of height `≥ 2`,
the punctured spectrum `Spec A ∖ {𝔪}` is not affine. -/
theorem not_isAffineOpen_spec_puncturedOpen (A : Type u) [CommRing A] [IsNoetherianRing A]
    (m : Ideal A) [hm : m.IsMaximal] (hht : 2 ≤ m.height) :
    ¬ IsAffineOpen (puncturedOpen (X := Spec (.of A)) (⟨m, hm.isPrime⟩ : PrimeSpectrum A)
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm)) := by
  apply not_isAffineOpen_puncturedOpen
  intro h1
  let x : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  let k : Algebra A ((Spec (.of A)).presheaf.stalk x) := StructureSheaf.stalkAlgebra A x
  have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk x) m :=
    StructureSheaf.IsLocalization.to_stalk A x
  have hd := Ring.krullDimLE_iff.1 h1
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m ((Spec (.of A)).presheaf.stalk x)] at hd
  have : m.height ≤ 1 := by exact_mod_cast hd
  exact absurd (hht.trans this) (by decide)

end AlgMag.Reductive
