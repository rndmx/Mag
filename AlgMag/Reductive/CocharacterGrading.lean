/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Affine
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability

/-!
# The `ℤ`-grading of `O(G)` given by a one-parameter subgroup, and its attractors

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Proposition 2.22 and §16.5.

Let `G = Spec H` be an affine group over `R` and `l : H →ₐc[R] R[T;T⁻¹]` a morphism of
groups `𝔾_m → G` (Tau Ceti's `Cocharacter` API). The action of `𝔾_m` on `G` by conjugation
through `l` is recorded by Tau Ceti's universal conjugation `conjugationAlgHom l : H → H[T;T⁻¹]`.
By Proposition 2.22 it is a `ℤ`-grading of `H`, with degree `n` part the `h` whose universal
conjugate is `h T^n`:

* `AlgMag.Reductive.lineGrading l : ℤ → Submodule R H` and its `GradedAlgebra` instance;
* `AlgMag.Reductive.magnetIdeal_lineGrading_nat` : the magnet `ℕ ⊆ ℤ` has magnet ideal
  Tau Ceti's `parabolicDefiningHopfIdeal l`, so `G^ℕ` is the dynamic parabolic `P(l)`;
* `AlgMag.Reductive.magnetIdeal_lineGrading_bot` : the magnet `0` gives the Levi `Z(l)`.
-/

suppress_compilation

open TensorProduct Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u v

variable {R : Type u} {H : Type v}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable (l : H →ₐc[R] LaurentPolynomial R)

/-- **The `ℤ`-grading of `O(G)` given by conjugation through a one-parameter subgroup
(Proposition 2.22 of Algebraic Magnetism).** The degree `n` part consists of the `h` whose
universal conjugate is the monomial `h T^n`. -/
def lineGrading (n : ℤ) : Submodule R H where
  carrier := {h | conjugationAlgHom l h = AddMonoidAlgebra.single n h}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha, hb, AddMonoidAlgebra.single_add]
  zero_mem' := by simp
  smul_mem' r a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_smul, ha, AddMonoidAlgebra.smul_single]

variable {l}

lemma mem_lineGrading {n : ℤ} {h : H} :
    h ∈ lineGrading l n ↔ conjugationAlgHom l h = AddMonoidAlgebra.single n h := Iff.rfl

/-- The coefficients of the universal conjugate are homogeneous (Tau Ceti
`coeff_conjugationAlgHom_coeff`). -/
lemma coeff_mem_lineGrading (h : H) (n : ℤ) :
    (conjugationAlgHom l h).coeff n ∈ lineGrading l n := by
  rw [mem_lineGrading]
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m => ?_)
  change (conjugationAlgHom l ((conjugationAlgHom l h).coeff n)).coeff m = _
  rw [coeff_conjugationAlgHom_coeff]
  change _ = (Finsupp.single n _ : ℤ →₀ H) m
  rw [Finsupp.single_apply]
  by_cases hmn : m = n
  · subst hmn; simp
  · rw [if_neg hmn, if_neg (Ne.symm hmn)]

lemma coeff_of_mem_lineGrading {n m : ℤ} {h : H} (hh : h ∈ lineGrading l n) :
    (conjugationAlgHom l h).coeff m = if m = n then h else 0 := by
  rw [mem_lineGrading.mp hh]
  change (Finsupp.single n h : ℤ →₀ H) m = _
  rw [Finsupp.single_apply]
  by_cases hmn : m = n
  · subst hmn; simp
  · rw [if_neg hmn, if_neg (Ne.symm hmn)]

/-- Evaluating the universal conjugate at `T = 1` gives back the coordinate: `h = ∑ₙ hₙ`. -/
lemma sum_coeff_conjugationAlgHom (h : H) :
    ∑ n ∈ (conjugationAlgHom l h).coeff.support, (conjugationAlgHom l h).coeff n = h := by
  have key := congrArg (fun g : WithConv (H →ₐ[R] H) => g.ofConv h)
    (mapValue_laurentEval_one_conjugate (A := H) (l := l) (toConv (AlgHom.id R H)))
  simp only at key
  have hc : (conjugate H l (toConv (AlgHom.id R H))).ofConv h = conjugationAlgHom l h := rfl
  rw [AlgHom.mapValue_apply] at key
  simp only [AlgHom.comp_apply, hc, AlgHom.id_apply] at key
  refine Eq.trans ?_ key
  simp only [AlgHom.coe_restrictScalars', laurentEval, AddMonoidAlgebra.lift_apply,
    Finsupp.sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply, zpowersHom_apply,
    one_zpow, Units.val_one, smul_eq_mul, mul_one]

/-- The projection onto the degree `n` part. -/
def lineProj (n : ℤ) (h : H) : lineGrading l n :=
  ⟨(conjugationAlgHom l h).coeff n, coeff_mem_lineGrading h n⟩


/-- The decomposition `h ↦ (hₙ)ₙ`. -/
def lineDecompose [DecidableEq H] (h : H) : DirectSum ℤ fun n => lineGrading l n :=
  ∑ n ∈ (conjugationAlgHom l h).coeff.support, DirectSum.of (fun n => lineGrading l n) n (lineProj n h)

lemma lineDecompose_apply [DecidableEq H] (h : H) (n : ℤ) :
    ((lineDecompose (l := l) h) n : H) = (conjugationAlgHom l h).coeff n := by
  rw [lineDecompose, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  by_cases hn : n ∈ (conjugationAlgHom l h).coeff.support
  · rw [Finset.sum_eq_single n]
    · rw [DirectSum.of_apply, dif_pos rfl]; rfl
    · intro b _ hb
      rw [DirectSum.of_apply, dif_neg hb]; rfl
    · intro hn'; exact absurd hn hn'
  · rw [Finset.sum_eq_zero]
    · exact (Finsupp.notMem_support_iff.mp hn).symm
    · intro b hb
      have : b ≠ n := fun e => hn (e ▸ hb)
      rw [DirectSum.of_apply, dif_neg this]; rfl

instance lineDecomposition [DecidableEq H] : DirectSum.Decomposition (lineGrading l) where
  decompose' := lineDecompose
  left_inv h := by
    rw [lineDecompose, map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    exact sum_coeff_conjugationAlgHom h
  right_inv x := by
    ext n
    rw [lineDecompose_apply]
    induction x using DirectSum.induction_on with
    | zero => simp
    | of m y =>
      rw [DirectSum.coeAddMonoidHom_of, coeff_of_mem_lineGrading y.2]
      by_cases hmn : n = m
      · subst hmn; simp
      · rw [if_neg hmn, DirectSum.of_apply, dif_neg (Ne.symm hmn)]; rfl
    | add x y hx hy =>
      rw [map_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy,
        DirectSum.add_apply, Submodule.coe_add]

/-- **Proposition 2.22 for `𝔾_m` acting on `G` by conjugation through `l`**: `O(G)` is a
`ℤ`-graded algebra. -/
instance lineGradedAlgebra [DecidableEq H] : GradedAlgebra (lineGrading l) where
  one_mem := by
    change conjugationAlgHom l 1 = AddMonoidAlgebra.single 0 1
    rw [map_one]
    rfl
  mul_mem i j a b ha hb := by
    change conjugationAlgHom l a = AddMonoidAlgebra.single i a at ha
    change conjugationAlgHom l b = AddMonoidAlgebra.single j b at hb
    change conjugationAlgHom l (a * b) = AddMonoidAlgebra.single (i + j) (a * b)
    rw [map_mul, ha, hb, AddMonoidAlgebra.single_mul_single]

/-! ### The attractors of the magnets `ℕ` and `0` -/

/-- The magnet `ℕ ⊆ ℤ` of nonnegative integers. -/
def natMagnet : Magnet ℤ where
  carrier := Set.Ici 0
  add_mem' ha hb := Set.mem_Ici.2 (add_nonneg (Set.mem_Ici.1 ha) (Set.mem_Ici.1 hb))
  zero_mem' := Set.mem_Ici.2 le_rfl

@[simp] lemma mem_natMagnet {n : ℤ} : n ∈ natMagnet ↔ 0 ≤ n := Set.mem_Ici

/-- **The attractor of the magnet `ℕ` is the dynamic parabolic (Proposition 16.10 (i) of
Algebraic Magnetism, ideal-theoretic form).** The magnet ideal `J_ℕ` of the grading of
`O(G)` by conjugation through `l` is Tau Ceti's defining ideal of the dynamic parabolic `P(l)`. -/
theorem magnetIdeal_lineGrading_nat :
    magnetIdeal (lineGrading l) natMagnet = (parabolicDefiningHopfIdeal l).toIdeal := by
  rw [parabolicDefiningHopfIdeal_toIdeal, magnetIdeal]
  apply le_antisymm
  · rw [Ideal.span_le]
    simp only [Set.iUnion_subset_iff, mem_natMagnet, not_le]
    intro n hn a ha
    refine Ideal.subset_span ⟨a, n, hn, ?_⟩
    rw [coeff_of_mem_lineGrading ha, if_pos rfl]
  · rw [Ideal.span_le]
    rintro _ ⟨h, n, hn, rfl⟩
    refine Ideal.subset_span ?_
    simp only [Set.mem_iUnion, SetLike.mem_coe, mem_natMagnet, not_le]
    exact ⟨n, hn, coeff_mem_lineGrading h n⟩

/-- **Proposition 16.10 (i) of Algebraic Magnetism, on points.** For every `R`-algebra `A`,
the `A`-points of `G` lying in the attractor `G^ℕ` (those killing `J_ℕ`) are exactly the points
of the dynamic parabolic `P(l)(A)`, i.e. the `g` for which `lim_{t→0} l(t) g l(t)⁻¹` exists. -/
theorem magnetIdeal_lineGrading_nat_le_ker_iff {A : Type*} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) :
    magnetIdeal (lineGrading l) natMagnet ≤ RingHom.ker g.ofConv ↔ g ∈ parabolic A l := by
  rw [magnetIdeal_lineGrading_nat, parabolicDefiningHopfIdeal_toIdeal]
  exact negativeCoefficientIdeal_le_ker_iff l g


lemma mem_lineGrading_of_coeff {n : ℤ} {h : H}
    (hh : ∀ m, (conjugationAlgHom l h).coeff m = if m = n then h else 0) :
    h ∈ lineGrading l n := by
  rw [mem_lineGrading]
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m => ?_)
  change (conjugationAlgHom l h).coeff m = (Finsupp.single n h : ℤ →₀ H) m
  rw [hh, Finsupp.single_apply]
  by_cases hmn : m = n
  · subst hmn; simp
  · rw [if_neg hmn, if_neg (Ne.symm hmn)]

/-- Reversing the one-parameter subgroup reverses the grading. -/
lemma coeff_conjugationAlgHom_oppositeCocharacter (h : H) (n : ℤ) :
    (conjugationAlgHom l.oppositeCocharacter h).coeff n = (conjugationAlgHom l h).coeff (-n) := by
  have key := congrArg (fun g : WithConv (H →ₐ[R] LaurentPolynomial H) => g.ofConv h)
    (conjugate_oppositeCocharacter (A := H) l (toConv (AlgHom.id R H)))
  change conjugationAlgHom l.oppositeCocharacter h = _ at key
  rw [key, AlgHom.mapValue_apply]
  exact LaurentPolynomial.invert_apply _ n

lemma mem_lineGrading_oppositeCocharacter {n : ℤ} {h : H} (hh : h ∈ lineGrading l (-n)) :
    h ∈ lineGrading l.oppositeCocharacter n := by
  refine mem_lineGrading_of_coeff fun m => ?_
  rw [coeff_conjugationAlgHom_oppositeCocharacter, coeff_of_mem_lineGrading hh]
  simp only [neg_inj]

/-- **The attractor of the magnet `0` is the Levi subgroup (Proposition 16.10 (ii) of Algebraic
Magnetism, ideal-theoretic form).** The magnet ideal `J_{0}` (fixed points of `𝔾_m`,
Proposition 3.35) is Tau Ceti's defining ideal of the dynamic Levi `Z(l) = P(l) ∩ P(l⁻¹)`. -/
theorem magnetIdeal_lineGrading_bot :
    magnetIdeal (lineGrading l) (⊥ : Magnet ℤ) = (leviDefiningHopfIdeal l).toIdeal := by
  rw [leviDefiningHopfIdeal_def, TauCeti.HopfIdeal.sup_toIdeal, ← magnetIdeal_lineGrading_nat,
    ← magnetIdeal_lineGrading_nat]
  apply le_antisymm
  · rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff, AddSubmonoid.mem_bot]
    intro m hm a ha
    rcases lt_or_gt_of_ne hm with hm | hm
    · exact Ideal.mem_sup_left (mem_magnetIdeal_of_notMem (by simpa using hm) ha)
    · refine Ideal.mem_sup_right (mem_magnetIdeal_of_notMem (m := -m) (by simpa using hm) ?_)
      exact mem_lineGrading_oppositeCocharacter (by simpa using ha)
  · refine sup_le ?_ ?_
    · rw [magnetIdeal, Ideal.span_le]
      simp only [Set.iUnion_subset_iff, mem_natMagnet, not_le]
      intro m hm a ha
      exact mem_magnetIdeal_of_notMem (by simpa using hm.ne) ha
    · rw [magnetIdeal, Ideal.span_le]
      simp only [Set.iUnion_subset_iff, mem_natMagnet, not_le]
      intro m hm a ha
      refine mem_magnetIdeal_of_notMem (m := -m) (by simpa using hm.ne) ?_
      have := mem_lineGrading_oppositeCocharacter (l := l.oppositeCocharacter) (n := -m)
        (by simpa using ha)
      rwa [BialgHom.oppositeCocharacter_oppositeCocharacter] at this

/-- **Proposition 16.10 (ii) of Algebraic Magnetism, on points.** The `A`-points of `G` lying
in the attractor `G^{0}` are exactly the points of the Levi subgroup `Z(l)(A)`, the centralizer
of the one-parameter subgroup. -/
theorem magnetIdeal_lineGrading_bot_le_ker_iff {A : Type*} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] A)) :
    magnetIdeal (lineGrading l) (⊥ : Magnet ℤ) ≤ RingHom.ker g.ofConv ↔ g ∈ levi A l := by
  rw [magnetIdeal_lineGrading_bot, leviDefiningHopfIdeal_def, TauCeti.HopfIdeal.sup_toIdeal,
    sup_le_iff, ← magnetIdeal_lineGrading_nat, ← magnetIdeal_lineGrading_nat,
    magnetIdeal_lineGrading_nat_le_ker_iff, magnetIdeal_lineGrading_nat_le_ker_iff,
    ← Subgroup.mem_inf, parabolic_inf_oppositeCocharacter]

end AlgMag.Reductive
