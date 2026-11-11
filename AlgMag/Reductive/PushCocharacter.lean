/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TorusGrading
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Cocharacter

/-!
# One-parameter subgroups of the torus and magnets `f⁻¹(ℕ)`, `f⁻¹(0)`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Proposition 3.31 and the proof of
Proposition 16.10.

Let `π : H →ₐc[R] R[X]` present `D(X) → G` and let `f : M → ℤ`, `M = Additive X`, be a morphism
(a magnet map to `ℤ`; it corresponds to `ψ : X →* Multiplicative ℤ`). The `𝔾_m`-action on `G`
through `D(X)` and `f` is conjugation by Tau Ceti's one-parameter subgroup `π.cocharacter ψ`.
We show:

* `conjugationAlgHom_cocharacter` : the universal conjugate by `π.cocharacter ψ` is the torus
  coaction followed by `ψ` (identification of the two conjugation formalisms);
* `torusGrading_le_lineGrading` : `H_χ ⊆ H_{f χ}`;
* `magnetIdeal_lineGrading_eq` : for every magnet `Y ⊆ ℤ`,
  `J_Y(ℤ-grading) = J_{f⁻¹(Y)}(M-grading)` (Proposition 3.31 for the conjugation action);
* `magnetIdeal_torusGrading_comap_nat` : `G^{f⁻¹(ℕ)}` is the dynamic parabolic `P(λ_f)`;
* `magnetIdeal_torusGrading_comap_bot` : `G^{f⁻¹(0)}` is the dynamic Levi `Z(λ_f)`.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u v w

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X) (ψ : X →* Multiplicative ℤ)

/-- The algebra map `R[X] ⊗ H → H[T;T⁻¹]`, `single χ r ⊗ h ↦ r h T^{ψ χ}`. -/
def cocharEval : MonoidAlgebra R X ⊗[R] H →ₐ[R] LaurentPolynomial H :=
  Algebra.TensorProduct.productMap
    ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R H)).comp
      ((BialgHom.id R (MonoidAlgebra R X)).cocharacter ψ).toAlgHom)
    (IsScalarTower.toAlgHom R H (LaurentPolynomial H))

/-- **The two conjugation formalisms agree.** Tau Ceti's universal conjugation by the
one-parameter subgroup `π.cocharacter ψ` is the torus coaction `torusCoactLeft π` followed by
`ψ`. -/
theorem conjugationAlgHom_cocharacter :
    conjugationAlgHom (π.cocharacter ψ) = (cocharEval ψ).comp (torusCoactLeft π) := by
  have hpm : ∀ (F : MonoidAlgebra R X →ₐ[R] LaurentPolynomial H)
      (G : H →ₐ[R] LaurentPolynomial H),
      (Algebra.TensorProduct.productMap F G).comp
          (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id R H)) =
        Algebra.TensorProduct.productMap (F.comp π.toAlgHom) (G.comp (AlgHom.id R H)) := by
    intro F G
    apply Algebra.TensorProduct.ext'
    intro a b
    simp
  rw [torusCoactLeft, ← AlgHom.comp_assoc, cocharEval, hpm]
  rw [show ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R H)).comp
      ((BialgHom.id R (MonoidAlgebra R X)).cocharacter ψ).toAlgHom).comp π.toAlgHom =
      (toConv ((AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R H)).comp
        (π.cocharacter ψ).toAlgHom)).ofConv by
    rw [ofConv_toConv, AlgHom.comp_assoc]
    congr 1]
  rw [show (IsScalarTower.toAlgHom R H (LaurentPolynomial H)).comp (AlgHom.id R H) =
      (toConv (IsScalarTower.toAlgHom R H (LaurentPolynomial H))).ofConv by
    rw [ofConv_toConv, AlgHom.comp_id]]
  rw [HopfAlgebra.productMap_comp_conjugationAlgHom, conjugationAlgHom, conjugate_apply,
    ← genericPoint_ofConv (A := H), toConv_ofConv]
  rfl

variable {π ψ}

/-- **`H_χ ⊆ H_{f χ}`**: a weight vector of weight `χ` for the torus is homogeneous of degree
`⟨χ, ψ⟩` for the one-parameter subgroup. -/
theorem torusGrading_le_lineGrading (χ : Additive X) :
    torusGrading π χ ≤ lineGrading (π.cocharacter ψ) (ψ (Additive.toMul χ)).toAdd := by
  intro h hh
  rw [mem_torusGrading] at hh
  have hl : torusCoactLeft π h = MonoidAlgebra.single (Additive.toMul χ) 1 ⊗ₜ[R] h := by
    have := congrArg (TensorProduct.comm R _ _) hh
    simpa [torusCoact] using this
  rw [mem_lineGrading, conjugationAlgHom_cocharacter, AlgHom.comp_apply, hl, cocharEval,
    Algebra.TensorProduct.productMap_apply_tmul]
  simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, BialgHom.cocharacter_id_single,
    IsScalarTower.coe_toAlgHom']
  rw [AddMonoidAlgebra.mapAlgHom_single, map_one, LaurentPolynomial.algebraMap_apply]
  change _ * AddMonoidAlgebra.single 0 _ = _
  rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul, Algebra.algebraMap_self,
    RingHom.id_apply]


variable (ψ) in
/-- The magnet map `f : M → ℤ`, `f(χ) = ⟨χ, ψ⟩`, attached to `ψ : X →* Multiplicative ℤ`. -/
def pairingHom : Additive X →+ ℤ where
  toFun χ := (ψ (Additive.toMul χ)).toAdd
  map_zero' := by simp
  map_add' a b := by simp

@[simp] lemma pairingHom_apply (χ : Additive X) :
    pairingHom ψ χ = (ψ (Additive.toMul χ)).toAdd := rfl

variable [DecidableEq X]

/-- **Proposition 3.31 for the conjugation action** (`𝔾_m` acting through `D(X)` and `f`):
for every magnet `Y ⊆ ℤ`, the magnet ideal of `Y` for the `ℤ`-grading of the one-parameter
subgroup `λ_f = π.cocharacter ψ` is the magnet ideal of `f⁻¹(Y)` for the torus grading. So
`G^Y` (for `λ_f`) is `G^{f⁻¹(Y)}` (for the torus). -/
theorem magnetIdeal_lineGrading_eq (Y : Magnet ℤ) :
    magnetIdeal (lineGrading (π.cocharacter ψ)) Y =
      magnetIdeal (torusGrading π) (Y.comap (pairingHom ψ)) := by
  classical
  apply le_antisymm
  · rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff]
    intro n hn a ha
    have hsum := DirectSum.sum_support_decompose (torusGrading π) a
    have hcoeff : (conjugationAlgHom (π.cocharacter ψ) a).coeff n = a := by
      rw [coeff_of_mem_lineGrading ha, if_pos rfl]
    rw [SetLike.mem_coe, ← hcoeff, ← hsum, map_sum, AddMonoidAlgebra.coeff_sum,
      Finsupp.finset_sum_apply]
    refine Ideal.sum_mem _ fun χ _ => ?_
    rw [coeff_of_mem_lineGrading (torusGrading_le_lineGrading χ (SetLike.coe_mem _))]
    split_ifs with h
    · refine mem_magnetIdeal_of_notMem (m := χ) ?_ (SetLike.coe_mem _)
      rw [AddSubmonoid.mem_comap]
      exact fun hY => hn (h ▸ hY)
    · exact zero_mem _
  · rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff]
    intro χ hχ a ha
    exact mem_magnetIdeal_of_notMem (m := pairingHom ψ χ) hχ (torusGrading_le_lineGrading χ ha)

/-- **The dynamic parabolic as an attractor of the torus (Proposition 3.31 with
[CGP 2.1.8], as used in the proof of Proposition 16.10 of Algebraic Magnetism).** For a
magnet map `f : M → ℤ`, the attractor `G^{f⁻¹(ℕ)}` of the conjugation action of `D(X)` is the
dynamic parabolic `P(λ_f)`. -/
theorem magnetIdeal_torusGrading_comap_nat :
    magnetIdeal (torusGrading π) (natMagnet.comap (pairingHom ψ)) =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  rw [← magnetIdeal_lineGrading_eq, magnetIdeal_lineGrading_nat]

/-- **The dynamic Levi as an attractor of the torus.** For a magnet map `f : M → ℤ`, the
attractor `G^{f⁻¹(0)}` of the conjugation action of `D(X)` is the Levi subgroup `Z(λ_f)`. -/
theorem magnetIdeal_torusGrading_comap_bot :
    magnetIdeal (torusGrading π) ((⊥ : Magnet ℤ).comap (pairingHom ψ)) =
      (leviDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  rw [← magnetIdeal_lineGrading_eq, magnetIdeal_lineGrading_bot]

/-- Points form of `magnetIdeal_torusGrading_comap_nat`: `G^{f⁻¹(ℕ)}(A) = P(λ_f)(A)`. -/
theorem magnetIdeal_torusGrading_comap_nat_le_ker_iff {A : Type*} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) :
    magnetIdeal (torusGrading π) (natMagnet.comap (pairingHom ψ)) ≤ RingHom.ker g.ofConv ↔
      g ∈ parabolic A (π.cocharacter ψ) := by
  rw [← magnetIdeal_lineGrading_eq]
  exact magnetIdeal_lineGrading_nat_le_ker_iff g

/-- Points form of `magnetIdeal_torusGrading_comap_bot`: `G^{f⁻¹(0)}(A) = Z(λ_f)(A)`. -/
theorem magnetIdeal_torusGrading_comap_bot_le_ker_iff {A : Type*} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) :
    magnetIdeal (torusGrading π) ((⊥ : Magnet ℤ).comap (pairingHom ψ)) ≤ RingHom.ker g.ofConv ↔
      g ∈ levi A (π.cocharacter ψ) := by
  rw [← magnetIdeal_lineGrading_eq]
  exact magnetIdeal_lineGrading_bot_le_ker_iff g

end AlgMag.Reductive
