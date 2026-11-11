/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3SchemeQuotient
import AlgMag.Sec3Remaining
import AlgMag.Sec2Monoids
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Proposition 3.31 (ii) for `Y = ℕ`, `f = d`: the map `(u, x) ↦ u x^d`

`R[ℕ] → R[ℤ × ℕ]`, `t ↦ u x^d`, is free with a nonzero basis and of finite presentation: the monoid `ℤ × ℕ` is free over
`ℕ`, with basis `{(i, j) : 0 ≤ j < d}`.
-/

universe u

noncomputable section

namespace AlgMag.FinalMisc

open AlgMag

/-- `m ↦ d m`. -/
def mulD (d : ℕ) : ℤ →+ ℤ := (zmultiplesHom ℤ) (d : ℤ)

@[simp] lemma mulD_apply (d : ℕ) (m : ℤ) : mulD d m = m * d := by
  simp [mulD]

variable (d : ℕ) (hd : 0 < d)

/-- `N₀ = {m : d m ≥ 0}`. -/
abbrev N₀ : AddSubmonoid ℤ := posN.comap (mulD d)

/-- `m ↦ (m, d m)`. -/
def jnD : N₀ d →+ ℤ × posN where
  toFun n := ((n : ℤ), ⟨mulD d n, n.2⟩)
  map_zero' := Prod.ext rfl (Subtype.ext (map_zero _))
  map_add' a b := Prod.ext rfl (Subtype.ext (map_add _ _ _))

include hd in
lemma mem_N₀ (m : ℤ) : m ∈ N₀ d ↔ 0 ≤ m := by
  change 0 ≤ mulD d m ↔ _
  have : (0 : ℤ) < d := by exact_mod_cast hd
  rw [mulD_apply]
  constructor
  · intro h; exact nonneg_of_mul_nonneg_left h this
  · intro h; positivity

lemma eq_of_mul_add {a b p q D : ℤ} (h : a * D + p = b * D + q) (p0 : 0 ≤ p) (p1 : p < D) (q0 : 0 ≤ q)
    (q1 : q < D) : a = b := by
  have hD : 0 < D := by omega
  rcases lt_trichotomy a b with hl | he | hl
  · have : (a + 1) * D ≤ b * D := mul_le_mul_of_nonneg_right (by omega) hD.le
    nlinarith
  · exact he
  · have : (b + 1) * D ≤ a * D := mul_le_mul_of_nonneg_right (by omega) hD.le
    nlinarith

include hd in
theorem isFreeAlong_jnD : IsFreeAlong (jnD d) := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  refine ⟨{p | (p.2 : ℤ) < d}, ?_, ?_⟩
  · rintro ⟨n, ⟨p, hp⟩⟩ ⟨n', ⟨p', hp'⟩⟩ h
    have h1 : (n : ℤ) + p.1 = (n' : ℤ) + p'.1 := congrArg Prod.fst h
    have h2 : mulD d n + (p.2 : ℤ) = mulD d n' + (p'.2 : ℤ) :=
      congrArg (fun z : ℤ × posN => (z.2 : ℤ)) h
    rw [mulD_apply, mulD_apply] at h2
    have en : (n : ℤ) = n' := eq_of_mul_add h2 p.2.2 hp p'.2.2 hp'
    have e1 : n = n' := Subtype.ext en
    subst e1
    have e2 : p.1 = p'.1 := by omega
    have e3 : (p.2 : ℤ) = p'.2 := by omega
    have : p = p' := Prod.ext e2 (Subtype.ext e3)
    subst this
    rfl
  · rintro ⟨i, y⟩
    have y0 : (0 : ℤ) ≤ y := y.2
    have q0 : 0 ≤ (y : ℤ) / d := Int.ediv_nonneg y0 hd'.le
    have r0 := Int.emod_nonneg (y : ℤ) hd'.ne'
    have r1 := Int.emod_lt_of_pos (y : ℤ) hd'
    refine ⟨⟨⟨(y : ℤ) / d, (mem_N₀ d hd _).2 q0⟩, ⟨(i - (y : ℤ) / d, ⟨(y : ℤ) % d, r0⟩), r1⟩⟩, ?_⟩
    refine Prod.ext (by change (y : ℤ) / d + (i - (y : ℤ) / d) = i; ring) (Subtype.ext ?_)
    change mulD d ((y : ℤ) / d) + (y : ℤ) % d = y
    rw [mulD_apply, mul_comm]
    exact Int.mul_ediv_add_emod _ _

variable (R : Type u) [CommRing R]

instance fg_posN : AddMonoid.FG posN := by
  refine AddMonoid.fg_of_surjective (M := ℕ)
    { toFun := fun n => ⟨(n : ℤ), Int.natCast_nonneg n⟩, map_zero' := rfl
      map_add' := fun _ _ => Subtype.ext (by simp) } fun y => ?_
  have y0 : (0 : ℤ) ≤ y := y.2
  exact ⟨(y : ℤ).toNat, Subtype.ext (Int.toNat_of_nonneg y0)⟩

include hd in
theorem fg_N₀ : AddMonoid.FG (N₀ d) := by
  refine AddMonoid.fg_of_surjective (M := ℕ)
    { toFun := fun n => ⟨(n : ℤ), (mem_N₀ d hd _).2 (Int.natCast_nonneg n)⟩, map_zero' := rfl
      map_add' := fun _ _ => Subtype.ext (by simp) } fun y => ?_
  have y0 : (0 : ℤ) ≤ y := (mem_N₀ d hd _).1 y.2
  exact ⟨(y : ℤ).toNat, Subtype.ext (Int.toNat_of_nonneg y0)⟩

/-- `R[P]` is of finite presentation over `R`, `P` a finitely generated monoid. -/
theorem fp_monoidAlgebra (P : Type) [AddCommMonoid P] [AddMonoid.FG P] :
    Algebra.FinitePresentation R (AddMonoidAlgebra R P) := by
  have h : Algebra.FinitePresentation ℤ (AddMonoidAlgebra ℤ P) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have h2 := Algebra.FinitePresentation.baseChange (R := ℤ) (A := AddMonoidAlgebra ℤ P) (B := R)
  exact Algebra.FinitePresentation.equiv (AddMonoidAlgebra.scalarTensorEquiv ℤ R)

include hd in
/-- `R[ℕ] → R[ℤ × ℕ]`, `t ↦ u x^d` is of finite presentation. -/
theorem fp_jnD : (AddMonoidAlgebra.mapDomainRingHom R (jnD d)).FinitePresentation := by
  have := fg_N₀ d hd
  refine RingHom.FinitePresentation.of_comp_finiteType (algebraMap R (AddMonoidAlgebra R (N₀ d))) ?_ ?_
  · have : (AddMonoidAlgebra.mapDomainRingHom R (jnD d)).comp (algebraMap R (AddMonoidAlgebra R (N₀ d))) =
        algebraMap R (AddMonoidAlgebra R (ℤ × posN)) := by
      refine RingHom.ext fun r => ?_
      change AddMonoidAlgebra.mapDomain (jnD d) (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
      rw [AddMonoidAlgebra.mapDomain_single, map_zero]
    rw [this, RingHom.finitePresentation_algebraMap]
    exact fp_monoidAlgebra R (ℤ × posN)
  · rw [RingHom.finiteType_algebraMap]
    infer_instance

/-- The freeness in the proof of `flat_of_isFreeAlong`. -/
theorem free_of_isFreeAlong {P Q : Type*} [AddCommMonoid P] [AddCommMonoid Q] {θ : P →+ Q} (h : IsFreeAlong θ) :
    letI := (AddMonoidAlgebra.mapDomainRingHom R θ).toAlgebra
    Module.Free (AddMonoidAlgebra R P) (AddMonoidAlgebra R Q) := by
  obtain ⟨S, hS⟩ := h
  let e : P × S ≃ Q := Equiv.ofBijective _ hS
  have he : ∀ (p : P) (s : S), e.symm (θ p + (s : Q)) = (p, s) := fun p s =>
    e.symm_apply_apply (p, s)
  have he' : ∀ q : Q, θ (e.symm q).1 + ((e.symm q).2 : Q) = q := fun q => e.apply_symm_apply q
  let := (AddMonoidAlgebra.mapDomainRingHom R θ).toAlgebra
  have hsmul : ∀ (a : AddMonoidAlgebra R P) (b : AddMonoidAlgebra R Q),
      a • b = AddMonoidAlgebra.mapDomainRingHom R θ a * b := fun a b => rfl
  let F : (S →₀ AddMonoidAlgebra R P) →ₗ[AddMonoidAlgebra R P] AddMonoidAlgebra R Q :=
    Finsupp.linearCombination _ (fun s : S => AddMonoidAlgebra.single (s : Q) (1 : R))
  let g₀ : (Q →₀ R) →+ (S →₀ AddMonoidAlgebra R P) :=
    Finsupp.liftAddHom fun q =>
      (Finsupp.singleAddHom (e.symm q).2).comp
        ((AddMonoidAlgebra.coeffAddEquiv (R := R) (M := P)).symm.toAddMonoidHom.comp
          (Finsupp.singleAddHom (e.symm q).1))
  let g : AddMonoidAlgebra R Q →+ (S →₀ AddMonoidAlgebra R P) :=
    g₀.comp (AddMonoidAlgebra.coeffAddEquiv (R := R) (M := Q)).toAddMonoidHom
  have hg : ∀ (q : Q) (c : R), g (AddMonoidAlgebra.single q c) =
      Finsupp.single (e.symm q).2 (AddMonoidAlgebra.single (e.symm q).1 c) := by
    intro q c
    simp only [g, g₀, AddMonoidHom.comp_apply]
    change Finsupp.liftAddHom _ (Finsupp.single q c) = _
    simp only [Finsupp.liftAddHom_apply_single]
    rfl
  have hF : ∀ (s : S) (p : P) (c : R),
      F (Finsupp.single s (AddMonoidAlgebra.single p c)) =
        AddMonoidAlgebra.single (θ p + (s : Q)) c := by
    intro s p c
    simp [F, Finsupp.linearCombination_single, hsmul, AddMonoidAlgebra.single_mul_single]
  have left : ∀ y, g (F y) = y := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single s a =>
      induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [Finsupp.single_add, map_add, ha, hb]
      | single p c => rw [hF, hg, he]
  have right : ∀ x, F (g x) = x := by
    intro x
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single q c => rw [hg, hF, he']
  let E := LinearEquiv.ofBijective F
    ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩
  exact Module.Free.of_equiv E

include hd in
/-- `Spec R[ℤ × ℕ] → Spec R[ℕ]` is surjective. -/
theorem comap_jnD_surjective :
    Function.Surjective (PrimeSpectrum.comap (AddMonoidAlgebra.mapDomainRingHom R (jnD d))) := by
  intro p
  letI := (AddMonoidAlgebra.mapDomainRingHom R (jnD d)).toAlgebra
  have hfr := free_of_isFreeAlong R (isFreeAlong_jnD d hd)
  have hne : Nontrivial (AddMonoidAlgebra R (N₀ d)) := PrimeSpectrum.nontrivial p
  have hR : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hne
      exact hxy (AddMonoidAlgebra.coeff_injective (Finsupp.ext fun _ => Subsingleton.elim _ _))
    · exact h
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := AddMonoidAlgebra R (N₀ d))
    (B := AddMonoidAlgebra R (ℤ × posN)) p

end AlgMag.FinalMisc
