/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SelfActionsMonoid
import AlgMag.Affine.Representability

/-!
# Self-actions over a ring: Proposition 2.1

Mayeux, *Algebraic magnetism invariants of self-actions of diagonalizable monoid schemes*,
Semigroup Forum 112 (2026) 532–540, doi:10.1007/s00233-025-10572-9 (the published version, read from
the publisher's PDF; numbering and quotations below are those of the journal).
§2, for `S = Spec R`. The scheme statement over `Spec ℤ` is `AlgMag.SelfActions.prop21_specZ`.

## Main results

* `magnetIdeal_eq_span`, `map_magnetIdeal_int`, `attractorSelfEquiv`, `attractorIntEquiv`:
  Proposition 2.1.
* `magnetIdeal_eq_iff`: over `R ≠ 0`, `J_N = J_{N'}` iff the monoid ideals agree. This is what the
  paper's "we can assume that `S = Spec(ℤ)` by base change" needs.
* `pureMagnets_ring`: over `R ≠ 0`, `Π(a) = pureMagnets (monIdeal L)`.
* `pureMagnets_ring_subsingleton`: over `R = 0`, i.e. `S = ∅`, `Π(a) = {0}`. So the results of the
  paper, stated over "a base scheme", fail over the empty base.
-/

open Magnetism Set

set_option linter.unusedSectionVars false

noncomputable section

namespace AlgMag.SelfActions

variable {M : Type*} [AddCommMonoid M] [DecidableEq M]
variable (R : Type*) [CommRing R] (L : AddSubmonoid M) (N N' : AddSubmonoid M)

/-- The monomial `X^m` of `R[L]`. -/
abbrev mono (m : L) : AddMonoidAlgebra R L := AddMonoidAlgebra.single m 1

lemma single_eq_smul_mono (m : L) (c : R) :
    AddMonoidAlgebra.single m c = c • mono R L m := by
  simp [mono, AddMonoidAlgebra.smul_single]

/-- **Proposition 2.1**, the ideal: `J_N = ⟨R X^m | m ∈ L ∖ (N ∩ L)⟩`. -/
theorem magnetIdeal_eq_span :
    magnetIdeal (magnetGrading L R) N =
      Ideal.span {a | ∃ m : L, (m : M) ∉ N ∧ a = mono R L m} := by
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · simp only [Set.iUnion_subset_iff]
    intro m hm a ha
    by_cases hmL : m ∈ L
    · obtain ⟨c, rfl⟩ := exists_single_of_mem_magnetGrading hmL ha
      have : AddMonoidAlgebra.single (⟨m, hmL⟩ : L) c =
          (AddMonoidAlgebra.single (0 : L) c) * mono R L ⟨m, hmL⟩ := by
        rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
      rw [SetLike.mem_coe, this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨m, hmL⟩, hm, rfl⟩)
    · rw [magnetGrading_eq_bot hmL] at ha
      have ha0 : a = 0 := by simpa using ha
      rw [ha0]
      exact zero_mem _
  · rintro _ ⟨m, hm, rfl⟩
    exact mem_magnetIdeal_of_notMem hm (single_mem_magnetGrading m 1)

/-- The base change `ℤ[L] → R[L]`. -/
abbrev baseChangeRing : AddMonoidAlgebra ℤ L →+* AddMonoidAlgebra R L :=
  AddMonoidAlgebra.mapRingHom L (Int.castRingHom R)

/-- **§2**, "attractors commute with base change": `J_N` of `R[L]` is the extension of `J_N` of
`ℤ[L]`. -/
theorem map_magnetIdeal_int :
    (magnetIdeal (magnetGrading L ℤ) N).map (baseChangeRing R L) =
      magnetIdeal (magnetGrading L R) N := by
  rw [magnetIdeal_eq_span, magnetIdeal_eq_span, Ideal.map_span]
  congr 1
  ext a
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, by simp [baseChangeRing, mono, AddMonoidAlgebra.mapRingHom_single]⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, ⟨m, hm, rfl⟩, by simp [baseChangeRing, mono, AddMonoidAlgebra.mapRingHom_single]⟩

variable {R L N N'}

lemma quotientChars_kills {C : Type*} [CommRing C] [Algebra R C]
    (φ : {φ : Multiplicative L →* C // ∀ m : L, (m : M) ∉ N → φ (Multiplicative.ofAdd m) = 0}) :
    ∀ a ∈ magnetIdeal (magnetGrading L R) N, AddMonoidAlgebra.lift R C L φ.1 a = 0 := by
  intro a ha
  rw [magnetIdeal_eq_span] at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨m, hm, rfl⟩
    have := φ.2 m hm
    simpa [mono, AddMonoidAlgebra.lift_single] using this
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- The points of `Spec (R[L]/J_N)` are the monoid maps `L → (C, ·)` killing `L ∖ N`. -/
def quotientChars (C : Type*) [CommRing C] [Algebra R C] :
    ((AddMonoidAlgebra R L ⧸ magnetIdeal (magnetGrading L R) N) →ₐ[R] C) ≃
      {φ : Multiplicative L →* C // ∀ m : L, (m : M) ∉ N → φ (Multiplicative.ofAdd m) = 0} where
  toFun F := ⟨(AddMonoidAlgebra.lift R C L).symm
      (F.comp (Ideal.Quotient.mkₐ R (magnetIdeal (magnetGrading L R) N))), fun m hm => by
    change (F.comp (Ideal.Quotient.mkₐ R _)) (mono R L m) = 0
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr (mem_magnetIdeal_of_notMem hm
        (single_mem_magnetGrading m (1 : R))), map_zero]⟩
  invFun φ := Ideal.Quotient.liftₐ _ (AddMonoidAlgebra.lift R C L φ.1) (quotientChars_kills φ)
  left_inv F := by
    refine AlgHom.ext fun a => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have := DFunLike.congr_fun ((AddMonoidAlgebra.lift R C L).apply_symm_apply
      (F.comp (Ideal.Quotient.mkₐ R (magnetIdeal (magnetGrading L R) N)))) a
    exact this
  right_inv φ := by
    refine Subtype.ext (MonoidHom.ext fun m => ?_)
    have h : AddMonoidAlgebra.lift R C L φ.1 (mono R L (Multiplicative.toAdd m)) = φ.1 m := by
      simp [mono, AddMonoidAlgebra.lift_single]
    exact h

/-- **Proposition 2.1**, lines 1-4 of the display, on `C`-points of `X = 𝔸(L)_R`:
`X^N(C) = Hom^{M-graded}_R(R[L], C[N]) = Hom_R(R[L]/J_N, C)`, and these are the monoid maps
`L → (C, ·)` killing `L ∖ N`. -/
def attractorSelfEquiv (C : Type*) [CommRing C] [Algebra R C] :
    Attractor (magnetGrading L R) N C ≃
      {φ : Multiplicative L →* C // ∀ m : L, (m : M) ∉ N → φ (Multiplicative.ofAdd m) = 0} :=
  (attractorEquiv (magnetGrading L R) N C).symm.trans (quotientChars C)

/-- **Proposition 2.1**, the complete display for `R`-points: `X^N(R) = Hom_ℤ(ℤ[L]/J_N, R)`, i.e.
`X^N = Spec(ℤ[L]/J_N)`. -/
def attractorIntEquiv :
    Attractor (magnetGrading L R) N R ≃
      ((AddMonoidAlgebra ℤ L ⧸ magnetIdeal (magnetGrading L ℤ) N) →ₐ[ℤ] R) :=
  (attractorSelfEquiv R).trans (quotientChars R).symm

variable (R L)

/-- "The ideal `J` of `A` corresponds to the monoid-ideal `MonIdeal`" (proof of Proposition 3.1,
journal p. 536). A monomial `X^x` of `R[L]`, `R ≠ 0`, lies in `J_N` iff `x ∈ MonIdeal(L ∖ N)`. -/
theorem mono_mem_magnetIdeal_iff [Nontrivial R] (x : L) :
    mono R L x ∈ magnetIdeal (magnetGrading L R) N ↔ (x : M) ∈ monIdeal L N := by
  constructor
  · intro h
    by_contra hx
    have := coeff_eq_zero_of_mem_magnetIdeal R h (k := x)
      ((mem_divisorCore_iff x.2).2 hx)
    simp [mono, AddMonoidAlgebra.coeff_single] at this
  · rintro ⟨m, hm, hmN, t, ht, e⟩
    have hx : x = ⟨m, hm⟩ + ⟨t, ht⟩ := Subtype.ext e
    have : mono R L x = mono R L ⟨m, hm⟩ * mono R L ⟨t, ht⟩ := by
      rw [hx, AddMonoidAlgebra.single_mul_single, one_mul]
    rw [this]
    exact Ideal.mul_mem_right _ _ (mem_magnetIdeal_of_notMem hmN (single_mem_magnetGrading _ _))

/-- Over `R ≠ 0`: `J_N = J_{N'}` iff `MonIdeal(L ∖ N) = MonIdeal(L ∖ N')`. The paper reduces to
`S = Spec ℤ` "by base change"; this needs `R ≠ 0`, see `pureMagnets_ring_subsingleton`. -/
theorem magnetIdeal_eq_iff [Nontrivial R] :
    magnetIdeal (magnetGrading L R) N = magnetIdeal (magnetGrading L R) N' ↔
      monIdeal L N = monIdeal L N' := by
  constructor
  · intro h
    ext x
    by_cases hx : x ∈ L
    · have h1 := mono_mem_magnetIdeal_iff R L (N := N) ⟨x, hx⟩
      have h2 := mono_mem_magnetIdeal_iff R L (N := N') ⟨x, hx⟩
      rw [h] at h1
      exact h1.symm.trans h2
    · exact ⟨fun h' => absurd (monIdeal_subset h') hx, fun h' => absurd (monIdeal_subset h') hx⟩
  · intro h
    have hc := monIdeal_eq_iff_divisorCore.1 h
    have e := fun K : AddSubmonoid M => magnetIdeal_closure_nonvanishing (magnetGrading L R) K
    rw [← e N, ← e N', nonvanishingDegrees_eq_divisorCore, nonvanishingDegrees_eq_divisorCore, hc]

/-- **§2**: over `S = Spec R ≠ ∅`, the pure magnets of `𝔸(L)_S` are those of the monoid ideals. -/
theorem pureMagnets_ring [Nontrivial R] :
    pureMagnets (affineY (magnetGrading L R)) = pureMagnets (monIdeal L) := by
  ext K
  refine forall_congr' fun K' => ?_
  rw [affineY_eq_iff, magnetIdeal_eq_iff]

/-- **Counterexample over the empty scheme to "an arbitrary base scheme" (journal p. 533)**: over `R = 0`, i.e. `S = ∅`, all
attractors are equal, so `Π(a) = {0}`. For `L = ℕ`, this contradicts Theorem 4.6, which gives
`{0, ℕ}`: the results require `S ≠ ∅`. -/
theorem pureMagnets_ring_subsingleton [Subsingleton R] :
    pureMagnets (affineY (magnetGrading L R)) = {⊥} := by
  have h : Subsingleton (AddMonoidAlgebra R L) := by
    refine ⟨fun a b => AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun x => Subsingleton.elim _ _)⟩
  ext K
  simp only [mem_singleton_iff]
  constructor
  · intro hK
    refine le_bot_iff.mp (hK ⊥ ?_)
    exact (affineY_eq_iff _).2 (Subsingleton.elim _ _)
  · rintro rfl
    exact isPure_bot

end AlgMag.SelfActions

#print axioms AlgMag.SelfActions.magnetIdeal_eq_span
#print axioms AlgMag.SelfActions.map_magnetIdeal_int
#print axioms AlgMag.SelfActions.attractorSelfEquiv
#print axioms AlgMag.SelfActions.attractorIntEquiv
#print axioms AlgMag.SelfActions.magnetIdeal_eq_iff
#print axioms AlgMag.SelfActions.pureMagnets_ring
#print axioms AlgMag.SelfActions.pureMagnets_ring_subsingleton
