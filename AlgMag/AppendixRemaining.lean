/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.AppendixA
import AlgMag.Sec6Atlas
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# What remains of Appendix A (by M. Romagny), for `D(M)`

* `torsionResidue_of_connected`: `D(M)` has connected fibres iff the torsion of `M` is killed by
  powers of the residue characteristics (the direct implication, by the idempotent argument).
* `lemmaA5`: **Lemma A.5** for `G = D(M)`: no étale localization and no Cohen-Macaulay argument are
  needed. Write `M = T ⊕ ℤ^r`, with basis `e₁, …, e_r` of the free part. The closed subschemes
  `F_n = V((X^{e_i} - 1)^n)` of `D(M)_R` are finite free over `R`, and cofinal with the infinitesimal
  neighbourhoods of the unit section, if the fibres are connected.
* `lemmaA3_affine`: **Lemma A.3** for `F_n`, on the affine side: the fixed points of `F_n` on
  `Spec A` are `V(J)`, `J` the image of the stabilizer ideal under the linear forms of `F_n`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w₁

namespace AlgMag.AppR

open AddMonoidAlgebra

noncomputable section

/-! ### Connected fibres (the idempotent argument) -/

section Idem

variable {R : Type*} [Field R] {M : Type*} [AddCommGroup M]

/-- If `m` has finite order `n`, invertible in `R`, then `e = (1/n) Σ_{i<n} X^{i m}` is an idempotent
of `R[M]`; if `n > 1` it is nontrivial. -/
theorem exists_nontrivial_idempotent (m : M) {n : ℕ} (hn : 1 < n) (hm : addOrderOf m = n)
    (hnR : (n : R) ≠ 0) :
    ∃ e : AddMonoidAlgebra R M, e * e = e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  have hn0 : 0 < n := by omega
  let x : AddMonoidAlgebra R M := single m 1
  let s : AddMonoidAlgebra R M := ∑ i ∈ Finset.range n, x ^ i
  have hxn : x ^ n = 1 := by
    have : x ^ n = single (n • m) 1 := by
      simp [x, AddMonoidAlgebra.single_pow]
    rw [this, ← hm, addOrderOf_nsmul_eq_zero]
    rfl
  have hxs : x * s = s := by
    have h := Finset.sum_range_succ' (fun i => x ^ i) n
    have h' := Finset.sum_range_succ (fun i => x ^ i) n
    simp only [s, Finset.mul_sum]
    have e1 : ∑ i ∈ Finset.range n, x * x ^ i = ∑ i ∈ Finset.range n, x ^ (i + 1) :=
      Finset.sum_congr rfl fun i _ => (pow_succ' x i).symm
    rw [e1]
    have h3 := h.symm.trans h'
    simp only [pow_zero, hxn] at h3
    exact add_right_cancel h3
  have hxis : ∀ i, x ^ i * s = s := by
    intro i
    induction i with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, hxs, ih]
  have hss : s * s = single 0 (n : R) * s := by
    conv_lhs => rw [show s = ∑ i ∈ Finset.range n, x ^ i from rfl]
    rw [Finset.sum_mul, Finset.sum_congr rfl fun i _ => hxis i, Finset.sum_const, Finset.card_range]
    rw [nsmul_eq_mul]
    congr 1
  let c : AddMonoidAlgebra R M := single 0 (n : R)⁻¹
  have hcn : c * single 0 (n : R) = 1 := by
    simp only [c, AddMonoidAlgebra.single_mul_single, add_zero]
    rw [inv_mul_cancel₀ hnR]
    rfl
  refine ⟨c * s, ?_, ?_, ?_⟩
  · calc c * s * (c * s) = c * c * (s * s) := by ring
      _ = c * c * (single 0 (n : R) * s) := by rw [hss]
      _ = c * (c * single 0 (n : R)) * s := by ring
      _ = c * s := by rw [hcn, mul_one]
  all_goals
    have hcoef : ∀ i, i < n → (c * s).coeff (i • m) = (n : R)⁻¹ := by
      intro i hi
      have hs : s = ∑ j ∈ Finset.range n, single (j • m) (1 : R) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [x, AddMonoidAlgebra.single_pow]
      have hc : c * s = ∑ j ∈ Finset.range n, single (j • m) (n : R)⁻¹ := by
        rw [hs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [c, AddMonoidAlgebra.single_mul_single]
      rw [hc]
      have hinj : ∀ j ∈ Finset.range n, j • m = i • m → j = i := by
        intro j hj hji
        have := (nsmul_injOn_Iio_addOrderOf (x := m))
        rw [hm] at this
        exact this (Finset.mem_range.1 hj) hi hji
      have : (∑ j ∈ Finset.range n, single (j • m) (n : R)⁻¹ : AddMonoidAlgebra R M).coeff (i • m) =
          ∑ j ∈ Finset.range n, (single (j • m) (n : R)⁻¹ : AddMonoidAlgebra R M).coeff (i • m) := by
        generalize Finset.range n = t
        induction t using Finset.induction_on with
        | empty => simp
        | insert a t ha ih => simp [Finset.sum_insert ha, AddMonoidAlgebra.coeff_add]
      rw [this, Finset.sum_eq_single i]
      · simp
      · intro j hj hne
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne]
        exact fun h => hne (hinj j hj h.symm)
      · intro h
        exact absurd (Finset.mem_range.2 hi) h
    have hne : (n : R)⁻¹ ≠ 0 := inv_ne_zero hnR
  · intro h
    have := hcoef 0 hn0
    rw [h] at this
    exact hne (by simpa using this.symm)
  · intro h
    have h1 := hcoef 1 hn
    rw [h, one_smul] at h1
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [addOrderOf_zero] at hm
      omega
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hm0] at h1
    exact hne h1.symm

/-- The fibres of `D(M)` over `S` are connected, after any field extension: the hypothesis of
**Theorem A.1**, **A.2 (ii)**. -/
def ConnectedFibres (M : Type u) [AddCommGroup M] (S : Scheme.{u}) : Prop :=
  ∀ (K : Type u) [Field K], (Spec (.of K) ⟶ S) → ConnectedSpace (PrimeSpectrum (AddMonoidAlgebra K M))

/-- A field of exponential characteristic `q`: if `R[M]` has connected spectrum, then every torsion
element of `M` is killed by a power of `q`. -/
theorem nsmul_eq_zero_of_connected (M : Type*) [AddCommGroup M] (q : ℕ) [ExpChar R q]
    (hc : ConnectedSpace (PrimeSpectrum (AddMonoidAlgebra R M))) (m : M) (hm : IsOfFinAddOrder m) :
    ∃ N : ℕ, q ^ N • m = 0 := by
  classical
  have hq : 1 ≤ q := (expChar_pos R q)
  have hd : 0 < addOrderOf m := hm.addOrderOf_pos
  -- write the order as `q^a * n` with `n` prime to `q` (`a = 0` if `q = 1`)
  obtain ⟨a, n, hnq, hdn⟩ : ∃ a n : ℕ, (q = 1 ∨ ¬ q ∣ n) ∧ addOrderOf m = q ^ a * n := by
    rcases eq_or_lt_of_le hq with h1 | h1
    · exact ⟨0, addOrderOf m, Or.inl h1.symm, by simp⟩
    · obtain ⟨a, n, hn, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' q (by omega)
      exact ⟨a, n, Or.inr hn, e⟩
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [mul_zero] at hdn; omega
    · exact h
  by_cases hn1 : n = 1
  · refine ⟨a, ?_⟩
    have : addOrderOf m = q ^ a := by rw [hdn, hn1, mul_one]
    rw [← this, addOrderOf_nsmul_eq_zero]
  exfalso
  have hn2 : 1 < n := by omega
  -- `q^a • m` has order `n`
  have hord : addOrderOf (q ^ a • m) = n := by
    have hdvd : q ^ a ∣ addOrderOf m := ⟨n, hdn⟩
    rw [addOrderOf_nsmul' _ (pow_pos hq a).ne', hdn, Nat.gcd_eq_right (Dvd.intro _ rfl),
      Nat.mul_div_cancel_left _ (pow_pos hq a)]
  have hnR : (n : R) ≠ 0 := by
    cases ‹ExpChar R q› with
    | zero => exact Nat.cast_ne_zero.2 hn0.ne'
    | prime hp =>
      intro h0
      have hd' := (CharP.cast_eq_zero_iff R q n).1 h0
      rcases hnq with h | h
      · exact hp.one_lt.ne' h
      · exact h hd'
  obtain ⟨e, he, he0, he1⟩ := exists_nontrivial_idempotent (R := R) (q ^ a • m) hn2 hord hnR
  have hid : IsIdempotentElem e := he
  let C := PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, hid⟩
  rcases isClopen_iff.1 C.isClopen with h | h
  · have hb : PrimeSpectrum.basicOpen e = ⊥ := by
      apply TopologicalSpace.Opens.ext
      exact h
    obtain ⟨k, hk⟩ := PrimeSpectrum.basicOpen_eq_bot_iff e |>.1 hb
    apply he0
    rcases k with _ | k
    · rw [pow_zero] at hk
      have : (1 : AddMonoidAlgebra R M) = 0 := hk
      rw [← mul_one e, this, mul_zero]
    · rwa [hid.pow_succ_eq] at hk
  · have hb : IsUnit e := by
      by_contra hne
      obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits hne
      have hp : (⟨I, hI.isPrime⟩ : PrimeSpectrum (AddMonoidAlgebra R M)) ∈
          (C : Set (PrimeSpectrum (AddMonoidAlgebra R M))) := by
        rw [h]
        trivial
      exact hp hmem
    apply he1
    exact hb.mul_left_cancel (by rw [he, mul_one])

/-- **The idempotent argument**: if the fibres of `D(M)` over `S` are connected, then at each point
of `S` the torsion of `M` is killed by a power of the residue exponential characteristic. -/
theorem torsionResidue_of_connected (M : Type u) [AddCommGroup M] (S : Scheme.{u})
    (h : ConnectedFibres M S) : TorsionResidue M S := by
  intro s q hq m hm
  have : ExpChar (S.residueField s) q := hq
  exact nsmul_eq_zero_of_connected (R := S.residueField s) M q
    (h (S.residueField s) (S.fromSpecResidueField s)) m hm

end Idem

end

end AlgMag.AppR

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag.AppR

noncomputable section

open AddMonoidAlgebra
open scoped DirectSum

/-! ### Lemma A.5 for `D(M)` -/

section Aug

variable (A : Type*) [CommRing A] (N : Type*) [AddCommGroup N]

/-- The ideal of the unit section of `D(N)` over `A`: the augmentation ideal, generated by the
`X^m - 1`. The `n`-th order thickening of the unit section is `V(I^{n})`. -/
def augI : Ideal (AddMonoidAlgebra A N) := Ideal.span (Set.range fun m : N => single m 1 - 1)

/-- The unit section of `D(N)`: `X^m ↦ 1`. -/
noncomputable def augHom : AddMonoidAlgebra A N →+* A :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id A) (1 : Multiplicative N →* A)
    (fun _ _ => by simp)

variable {A N}

@[simp] lemma augHom_single (m : N) (a : A) : augHom A N (single m a) = a := by
  simp [augHom]

/-- `I` is the ideal of the unit section. -/
theorem ker_augHom : RingHom.ker (augHom A N) = augI A N := by
  apply le_antisymm
  · intro f hf
    have key : ∀ f : AddMonoidAlgebra A N, f - single 0 (augHom A N f) ∈ augI A N := by
      intro f
      induction f using AddMonoidAlgebra.induction_linear with
      | zero => simp [AddMonoidAlgebra.single_zero]
      | add f g hf hg =>
        have := (augI A N).add_mem hf hg
        have e : (f + g) - single 0 (augHom A N (f + g)) =
            (f - single 0 (augHom A N f)) + (g - single 0 (augHom A N g)) := by
          rw [map_add, AddMonoidAlgebra.single_add]
          ring
        rwa [e]
      | single m a =>
        rw [augHom_single]
        have : single m a - single 0 a = single 0 a * (single m 1 - 1 : AddMonoidAlgebra A N) := by
          rw [mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, zero_add, mul_one]
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)
    have := key f
    rw [RingHom.mem_ker.1 hf] at this
    simpa [AddMonoidAlgebra.single_zero] using this
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨m, rfl⟩
    simp [RingHom.mem_ker, AddMonoidAlgebra.one_def]

variable (A) in
/-- The ideal defining `F_n`: generated by the `(X^e - 1)^n`, for `e ∈ E`. -/
def Jn (E : Set N) (n : ℕ) : Ideal (AddMonoidAlgebra A N) :=
  Ideal.span ((fun e => (single e 1 - 1 : AddMonoidAlgebra A N) ^ n) '' E)

end Aug

section Laurent

variable (D : Type*) [CommRing D]

/-- `D[x^{±1}] / (x - 1)^n`. -/
abbrev LQ (n : ℕ) : Type _ :=
  AddMonoidAlgebra D ℤ ⧸ Ideal.span {(single (1 : ℤ) 1 - 1 : AddMonoidAlgebra D ℤ) ^ n}

/-- A linear equivalence from a ring isomorphism compatible with scalars. -/
def linEquivOfRing {A Q Q' : Type*} [CommRing A] [AddCommGroup Q] [Module A Q] [AddCommGroup Q']
    [Module A Q'] (f : Q ≃+ Q') (h : ∀ (a : A) (x : Q), f (a • x) = a • f x) : Q ≃ₗ[A] Q' :=
  { f with map_smul' := h }

variable {D}

/-- `D[x^{±1}] / (x - 1)^n` is finite free over `D`: it is `D[y]/(y^n)`, `x = 1 + y`. -/
theorem lq_free_finite (n : ℕ) : Module.Free D (LQ D n) ∧ Module.Finite D (LQ D n) := by
  classical
  let W := AdjoinRoot (Polynomial.X ^ n : Polynomial D)
  have hm : (Polynomial.X ^ n : Polynomial D).Monic := Polynomial.monic_X_pow n
  let pb := AdjoinRoot.powerBasis' hm
  have hF : Module.Free D W := Module.Free.of_basis pb.basis
  have hf : Module.Finite D W := pb.finite
  let y : W := AdjoinRoot.root _
  have hyn : y ^ n = 0 := by
    have := AdjoinRoot.eval₂_root (Polynomial.X ^ n : Polynomial D)
    simpa using this
  have hun : IsUnit (1 + y) := IsNilpotent.isUnit_one_add ⟨n, hyn⟩
  let u : Wˣ := hun.unit
  let χ : Multiplicative ℤ →* W := (Units.coeHom W).comp (zpowersHom Wˣ u)
  let g : AddMonoidAlgebra D ℤ →+* W :=
    AddMonoidAlgebra.liftNCRingHom (AdjoinRoot.of _) χ (fun _ _ => mul_comm _ _)
  have gs : ∀ (k : ℤ) (r : D), g (single k r) = AdjoinRoot.of _ r * χ (Multiplicative.ofAdd k) := by
    intro k r
    change AddMonoidAlgebra.liftNC _ _ _ = _
    rw [AddMonoidAlgebra.liftNC_single]
    rfl
  have χ1 : χ (Multiplicative.ofAdd 1) = 1 + y := by
    change ((zpowersHom Wˣ u (Multiplicative.ofAdd 1) : Wˣ) : W) = _
    rw [zpowersHom_apply]
    simp [u]
  have gx : g (single 1 1) = 1 + y := by
    rw [gs, map_one, one_mul, χ1]
  have g1 : g ((single (1 : ℤ) 1 - 1) ^ n) = 0 := by
    rw [map_pow, map_sub, gx, map_one, add_sub_cancel_left, hyn]
  let fr : LQ D n →+* W := Ideal.Quotient.lift _ g (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, g1, mul_zero])
  let om : D →+* LQ D n := (Ideal.Quotient.mk _).comp AddMonoidAlgebra.singleZeroRingHom
  let tt : W →+* LQ D n := AdjoinRoot.lift om (Ideal.Quotient.mk _ (single (1 : ℤ) 1 - 1)) (by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl))
  have tt_y : tt y = Ideal.Quotient.mk _ (single (1 : ℤ) 1 - 1) := AdjoinRoot.lift_root _
  have tt_of : ∀ d, tt (AdjoinRoot.of _ d) = om d := fun d => AdjoinRoot.lift_of _
  have h1 : ∀ z : W, fr (tt z) = z := by
    intro z
    have : fr.comp tt = RingHom.id W := by
      refine AdjoinRoot.ringHom_ext ?_ ?_
      · ext d
        simp only [RingHom.comp_apply]
        rw [tt_of]
        change g (single 0 d) = _
        rw [gs]
        have : χ (Multiplicative.ofAdd 0) = 1 := map_one χ
        rw [this, mul_one]
        rfl
      · simp only [RingHom.comp_apply]
        change fr (tt y) = y
        rw [tt_y]
        change g (single (1 : ℤ) 1 - 1) = y
        rw [map_sub, gx, map_one, add_sub_cancel_left]
    exact congrArg (fun k => k z) this
  have h2 : ∀ z : LQ D n, tt (fr z) = z := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hc : tt.comp g = Ideal.Quotient.mk _ := by
      refine AddMonoidAlgebra.ringHom_ext ?_ ?_
      · intro d
        change tt (g (single 0 d)) = _
        rw [gs]
        have : χ (Multiplicative.ofAdd 0) = 1 := map_one χ
        rw [this, mul_one, tt_of]
        rfl
      · intro k
        have hmh : (tt : W →* LQ D n).comp χ =
            ((Ideal.Quotient.mk _ : AddMonoidAlgebra D ℤ →+* LQ D n) : AddMonoidAlgebra D ℤ →* LQ D n).comp
              (AddMonoidAlgebra.of D ℤ) := by
          refine MonoidHom.ext_mint ?_
          change tt (χ (Multiplicative.ofAdd 1)) = Ideal.Quotient.mk _ (single (1 : ℤ) 1)
          rw [χ1, map_add, map_one, tt_y, map_sub, map_one, add_sub_cancel]
        have := DFunLike.congr_fun hmh (Multiplicative.ofAdd k)
        change tt (g (single k 1)) = _
        rw [gs, map_one, one_mul]
        exact this
    exact congrArg (fun k => k z) hc
  let e : W ≃ₗ[D] LQ D n := linEquivOfRing
    { toFun := tt, invFun := fr, left_inv := h1, right_inv := h2, map_add' := map_add tt } (by
      intro d z
      change tt (d • z) = d • tt z
      rw [Algebra.smul_def, map_mul, Algebra.smul_def]
      congr 1
      exact tt_of d)
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

end Laurent

section Step

variable {A N : Type*} [CommRing A] [AddCommGroup N]

/-- The inclusion `A[N] → A[N × ℤ]`. -/
def inlR : AddMonoidAlgebra A N →+* AddMonoidAlgebra A (N × ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom A (AddMonoidHom.inl N ℤ)

@[simp] lemma inlR_single (m : N) (a : A) : inlR (single m a) = single (m, (0 : ℤ)) a := by
  simp [inlR]

/-- The generators of `F_n` for `N × ℤ` from those for `N`. -/
def stepE (E : Set N) : Set (N × ℤ) := (fun e => (e, (0 : ℤ))) '' E ∪ {((0 : N), (1 : ℤ))}

lemma mem_Jn_step (E : Set N) (n : ℕ) (e : N) (he : e ∈ E) :
    (single (e, (0 : ℤ)) 1 - 1 : AddMonoidAlgebra A (N × ℤ)) ^ n ∈ Jn A (stepE E) n :=
  Ideal.subset_span ⟨_, Or.inl ⟨e, he, rfl⟩, rfl⟩

lemma mem_Jn_step' (E : Set N) (n : ℕ) :
    (single ((0 : N), (1 : ℤ)) 1 - 1 : AddMonoidAlgebra A (N × ℤ)) ^ n ∈ Jn A (stepE E) n :=
  Ideal.subset_span ⟨_, Or.inr rfl, rfl⟩

/-- **The inductive step of Lemma A.5**: if `A[N]/J` is finite free over `A`, so is
`A[N × ℤ]/(J, (X - 1)^n)`. -/
theorem step_free (E : Set N) (n : ℕ) (hF : Module.Free A (AddMonoidAlgebra A N ⧸ Jn A E n))
    (hf : Module.Finite A (AddMonoidAlgebra A N ⧸ Jn A E n)) :
    Module.Free A (AddMonoidAlgebra A (N × ℤ) ⧸ Jn A (stepE E) n) ∧
      Module.Finite A (AddMonoidAlgebra A (N × ℤ) ⧸ Jn A (stepE E) n) := by
  classical
  let J := Jn A E n
  let J' := Jn A (stepE E) n
  let D := AddMonoidAlgebra A N ⧸ J
  let Q := LQ D n
  have hLQ := lq_free_finite (D := D) n
  have hLQF : Module.Free D Q := hLQ.1
  have hLQf : Module.Finite D Q := hLQ.2
  let mkQ : AddMonoidAlgebra D ℤ →+* Q := Ideal.Quotient.mk _
  let mkD : AddMonoidAlgebra A N →+* D := Ideal.Quotient.mk _
  let mon : Multiplicative (N × ℤ) →* Q :=
    { toFun := fun p => mkQ (single (Multiplicative.toAdd p).2 (mkD (single (Multiplicative.toAdd p).1 1)))
      map_one' := by
        change mkQ (single 0 (mkD (single 0 1))) = 1
        have : mkD (single 0 1) = 1 := map_one mkD
        rw [this]
        exact map_one mkQ
      map_mul' := fun p q => by
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, ← map_mul,
          AddMonoidAlgebra.single_mul_single, mul_one]
        rfl }
  let c₀ : A →+* Q := mkQ.comp (AddMonoidAlgebra.singleZeroRingHom.comp
    (mkD.comp AddMonoidAlgebra.singleZeroRingHom))
  let ψ₀ : AddMonoidAlgebra A (N × ℤ) →+* Q :=
    AddMonoidAlgebra.liftNCRingHom c₀ mon (fun _ _ => mul_comm _ _)
  have ψs : ∀ p (a : A), ψ₀ (single p a) = c₀ a * mon (Multiplicative.ofAdd p) := by
    intro p a
    change AddMonoidAlgebra.liftNC _ _ _ = _
    rw [AddMonoidAlgebra.liftNC_single]
    rfl
  have ψinl : ∀ g : AddMonoidAlgebra A N, ψ₀ (inlR g) = mkQ (single 0 (mkD g)) := by
    intro g
    have : ψ₀.comp inlR = mkQ.comp (AddMonoidAlgebra.singleZeroRingHom.comp mkD) := by
      refine AddMonoidAlgebra.ringHom_ext ?_ ?_
      · intro a
        simp only [RingHom.comp_apply]
        rw [inlR_single, ψs]
        have : mon (Multiplicative.ofAdd ((0 : N), (0 : ℤ))) = 1 := map_one mon
        rw [this, mul_one]
        rfl
      · intro m
        simp only [RingHom.comp_apply]
        rw [inlR_single, ψs]
        have : c₀ 1 = 1 := map_one c₀
        rw [this, one_mul]
        rfl
    exact DFunLike.congr_fun this g
  have ψgen1 : ∀ e ∈ E, ψ₀ ((single (e, (0 : ℤ)) 1 - 1) ^ n) = 0 := by
    intro e he
    have h1 : (single (e, (0 : ℤ)) 1 - 1 : AddMonoidAlgebra A (N × ℤ)) ^ n =
        inlR ((single e 1 - 1) ^ n) := by
      rw [map_pow, map_sub, inlR_single, map_one]
    rw [h1, ψinl]
    have : mkD ((single e 1 - 1) ^ n) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨e, he, rfl⟩)
    rw [this, AddMonoidAlgebra.single_zero, map_zero]
  have ψx : ψ₀ (single ((0 : N), (1 : ℤ)) 1) = mkQ (single (1 : ℤ) 1) := by
    rw [ψs]
    have : c₀ 1 = 1 := map_one c₀
    rw [this, one_mul]
    change mkQ (single (1 : ℤ) (mkD (single 0 1))) = _
    have : mkD (single 0 1) = 1 := map_one mkD
    rw [this]
  have ψgen2 : ψ₀ ((single ((0 : N), (1 : ℤ)) 1 - 1) ^ n) = 0 := by
    rw [map_pow, map_sub, ψx, map_one, ← map_one mkQ, ← map_sub, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have ψker : ∀ a ∈ J', ψ₀ a = 0 := by
    intro a ha
    have : J' ≤ RingHom.ker ψ₀ := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨e, (⟨e', he', rfl⟩ | rfl), rfl⟩
      · exact ψgen1 e' he'
      · exact ψgen2
    exact this ha
  let ψ : (AddMonoidAlgebra A (N × ℤ) ⧸ J') →+* Q := Ideal.Quotient.lift _ ψ₀ ψker
  let mk' : AddMonoidAlgebra A (N × ℤ) →+* (AddMonoidAlgebra A (N × ℤ) ⧸ J') := Ideal.Quotient.mk _
  let θ₁ : D →+* (AddMonoidAlgebra A (N × ℤ) ⧸ J') := Ideal.Quotient.lift _ (mk'.comp inlR) (by
    intro a ha
    have : J ≤ RingHom.ker (mk'.comp inlR) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨e, he, rfl⟩
      change mk' (inlR _) = 0
      rw [map_pow, map_sub, inlR_single, map_one]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_Jn_step E n e he)
    exact this ha)
  let mon' : Multiplicative ℤ →* (AddMonoidAlgebra A (N × ℤ) ⧸ J') :=
    { toFun := fun k => mk' (single ((0 : N), Multiplicative.toAdd k) 1)
      map_one' := map_one mk'
      map_mul' := fun p q => by
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
        congr 2
        exact Prod.ext (add_zero 0).symm rfl }
  let θ₂ : AddMonoidAlgebra D ℤ →+* (AddMonoidAlgebra A (N × ℤ) ⧸ J') :=
    AddMonoidAlgebra.liftNCRingHom θ₁ mon' (fun _ _ => mul_comm _ _)
  have θs : ∀ (k : ℤ) (d : D), θ₂ (single k d) = θ₁ d * mon' (Multiplicative.ofAdd k) := by
    intro k d
    change AddMonoidAlgebra.liftNC _ _ _ = _
    rw [AddMonoidAlgebra.liftNC_single]
    rfl
  let θ : Q →+* (AddMonoidAlgebra A (N × ℤ) ⧸ J') := Ideal.Quotient.lift _ θ₂ (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have hθ1 : θ₁ 1 = 1 := map_one θ₁
    have hθx : θ₂ (single (1 : ℤ) 1 - 1) = mk' (single ((0 : N), (1 : ℤ)) 1 - 1) := by
      rw [map_sub, map_one θ₂, θs, hθ1, one_mul, map_sub, map_one mk']
      rfl
    have h0 : mk' ((single ((0 : N), (1 : ℤ)) 1 - 1) ^ n) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (mem_Jn_step' E n)
    rw [map_mul, map_pow, hθx, ← map_pow, h0, mul_zero])
  have hθψ : ∀ z, θ (ψ z) = z := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have : θ.comp ψ₀ = mk' := by
      refine AddMonoidAlgebra.ringHom_ext ?_ ?_
      · intro a
        change θ (ψ₀ (single 0 a)) = _
        rw [ψs]
        have : mon (Multiplicative.ofAdd (0 : N × ℤ)) = 1 := map_one mon
        rw [this, mul_one]
        change θ₂ (single 0 (mkD (single 0 a))) = _
        rw [θs]
        have : mon' (Multiplicative.ofAdd 0) = 1 := map_one mon'
        rw [this, mul_one]
        change mk' (inlR (single 0 a)) = _
        rw [inlR_single]
        rfl
      · rintro ⟨m, k⟩
        change θ (ψ₀ (single (m, k) 1)) = _
        rw [ψs]
        have : c₀ 1 = 1 := map_one c₀
        rw [this, one_mul]
        change θ₂ (single k (mkD (single m 1))) = _
        rw [θs]
        change mk' (inlR (single m 1)) * mk' (single ((0 : N), k) 1) = _
        rw [inlR_single, ← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
        congr 2
        exact Prod.ext (add_zero m) (zero_add k)
    exact DFunLike.congr_fun this z
  have hψθ : ∀ z, ψ (θ z) = z := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have : ψ.comp θ₂ = mkQ := by
      refine AddMonoidAlgebra.ringHom_ext ?_ ?_
      · intro d
        obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective d
        change ψ (θ₂ (single 0 (mkD g))) = _
        rw [θs]
        have : mon' (Multiplicative.ofAdd 0) = 1 := map_one mon'
        rw [this, mul_one]
        change ψ₀ (inlR g) = _
        rw [ψinl]
      · intro k
        change ψ (θ₂ (single k 1)) = _
        rw [θs, map_one, one_mul]
        change ψ₀ (single ((0 : N), k) 1) = _
        rw [ψs]
        have : c₀ 1 = 1 := map_one c₀
        rw [this, one_mul]
        change mkQ (single k (mkD (single 0 1))) = _
        have : mkD (single 0 1) = 1 := map_one mkD
        rw [this]
    exact DFunLike.congr_fun this z
  have hsmul : ∀ (a : A) (z : AddMonoidAlgebra A (N × ℤ)), ψ₀ (a • z) = a • ψ₀ z := by
    intro a z
    have e1 : a • z = single 0 a * z := by
      rw [Algebra.smul_def]
      rfl
    have e2 : a • ψ₀ z = mkQ (single 0 (mkD (single 0 a))) * ψ₀ z := by
      rw [Algebra.smul_def]
      rfl
    rw [e1, map_mul, e2, ψs]
    have : mon (Multiplicative.ofAdd (0 : N × ℤ)) = 1 := map_one mon
    rw [this, mul_one]
    rfl
  let e : (AddMonoidAlgebra A (N × ℤ) ⧸ J') ≃ₗ[A] Q := linEquivOfRing
    { toFun := ψ, invFun := θ, left_inv := hθψ, right_inv := hψθ, map_add' := map_add ψ } (by
      intro a z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact hsmul a z)
  have hFQ : Module.Free A Q := Module.Free.trans (S := D)
  have hfQ : Module.Finite A Q := Module.Finite.trans D Q
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- Passing to `N × ℤ`: `J` of `F_n` is below `I^n` as soon as it is for `N`. -/
theorem step_le (E : Set N) (n : ℕ) (h : Jn A E n ≤ augI A N ^ n) :
    Jn A (stepE E) n ≤ augI A (N × ℤ) ^ n := by
  refine Ideal.span_le.2 ?_
  have hI : (augI A N).map (inlR (A := A)) ≤ augI A (N × ℤ) := by
    refine (Ideal.map_le_iff_le_comap).2 (Ideal.span_le.2 ?_)
    rintro _ ⟨m, rfl⟩
    change inlR _ ∈ augI A (N × ℤ)
    rw [map_sub, inlR_single, map_one]
    exact Ideal.subset_span (Set.mem_range_self _)
  rintro _ ⟨e, (⟨e', he', rfl⟩ | rfl), rfl⟩
  · have h1 : (single (e', (0 : ℤ)) 1 - 1 : AddMonoidAlgebra A (N × ℤ)) ^ n =
        inlR ((single e' 1 - 1) ^ n) := by
      rw [map_pow, map_sub, inlR_single, map_one]
    change (single (e', (0 : ℤ)) 1 - 1 : AddMonoidAlgebra A (N × ℤ)) ^ n ∈ _
    rw [h1]
    have h2 := h (Ideal.subset_span (Set.mem_image_of_mem _ he'))
    have h3 := Ideal.mem_map_of_mem (inlR (A := A)) h2
    rw [Ideal.map_pow] at h3
    exact Ideal.pow_right_mono hI n h3
  · exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self _)) n

/-- Passing to `N × ℤ`: infinitesimality. -/
theorem step_nil (E : Set N) (n : ℕ) (h : ∃ k, augI A N ^ k ≤ Jn A E n) :
    ∃ k, augI A (N × ℤ) ^ k ≤ Jn A (stepE E) n := by
  obtain ⟨k, hk⟩ := h
  have hmap : (augI A N ^ k).map (inlR (A := A)) ≤ Jn A (stepE E) n := by
    refine le_trans (Ideal.map_mono hk) ?_
    refine (Ideal.map_le_iff_le_comap).2 (Ideal.span_le.2 ?_)
    rintro _ ⟨e, he, rfl⟩
    change inlR _ ∈ Jn A (stepE E) n
    rw [map_pow, map_sub, inlR_single, map_one]
    exact mem_Jn_step E n e he
  let x : AddMonoidAlgebra A (N × ℤ) := single ((0 : N), (1 : ℤ)) 1
  have hsplit : augI A (N × ℤ) ≤ (augI A N).map (inlR (A := A)) ⊔ Ideal.span {x - 1} := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨m, l⟩, rfl⟩
    let Q := AddMonoidAlgebra A (N × ℤ) ⧸ ((augI A N).map (inlR (A := A)) ⊔ Ideal.span {x - 1})
    let mk'' : AddMonoidAlgebra A (N × ℤ) →+* Q := Ideal.Quotient.mk _
    have hx : mk'' x = 1 := by
      rw [← sub_eq_zero, ← map_one mk'', ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hm : mk'' (single (m, (0 : ℤ)) 1) = 1 := by
      rw [← sub_eq_zero, ← map_one mk'', ← map_sub]
      refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left ?_)
      have := Ideal.mem_map_of_mem (inlR (A := A)) (Ideal.subset_span ⟨m, rfl⟩ :
        (single m 1 - 1 : AddMonoidAlgebra A N) ∈ augI A N)
      rwa [map_sub, inlR_single, map_one] at this
    let χ : Multiplicative ℤ →* Q :=
      (mk'' : _ →* Q).comp ((AddMonoidAlgebra.of A (N × ℤ)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inr N ℤ)))
    have hχ : χ = 1 := by
      refine MonoidHom.ext_mint ?_
      exact hx
    have hl : mk'' (single ((0 : N), l) 1) = 1 := DFunLike.congr_fun hχ (Multiplicative.ofAdd l)
    have hsplit' : (single (m, l) 1 : AddMonoidAlgebra A (N × ℤ)) =
        single (m, (0 : ℤ)) 1 * single ((0 : N), l) 1 := by
      rw [AddMonoidAlgebra.single_mul_single, mul_one]
      congr 1
      exact Prod.ext (add_zero m).symm (zero_add l).symm
    refine (Ideal.Quotient.eq_zero_iff_mem).1 ?_
    change mk'' _ = 0
    rw [map_sub, map_one, hsplit', map_mul, hm, hl, one_mul, sub_self]
  refine ⟨k + n, le_trans (Ideal.pow_right_mono hsplit _) (le_trans Ideal.sup_pow_add_le_pow_sup_pow ?_)⟩
  refine sup_le ?_ ?_
  · rw [← Ideal.map_pow]
    exact hmap
  · rw [Ideal.span_singleton_pow, Ideal.span_le]
    rintro _ rfl
    exact mem_Jn_step' E n

end Step

section Base

variable {A : Type*} [CommRing A] {T : Type*} [AddCommGroup T]

lemma base_free [Finite T] (n : ℕ) :
    Module.Free A (AddMonoidAlgebra A T ⧸ Jn A (∅ : Set T) n) ∧
      Module.Finite A (AddMonoidAlgebra A T ⧸ Jn A (∅ : Set T) n) := by
  have hb : Jn A (∅ : Set T) n = ⊥ := by simp [Jn]
  let hc : AddMonoidAlgebra A T ≃ₗ[A] (T →₀ A) :=
    { AddMonoidAlgebra.coeffEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hF0 : Module.Free A (AddMonoidAlgebra A T) := Module.Free.of_equiv hc.symm
  have hf0 : Module.Finite A (AddMonoidAlgebra A T) := Module.Finite.equiv hc.symm
  let e : AddMonoidAlgebra A T ≃ₗ[A] (AddMonoidAlgebra A T ⧸ Jn A (∅ : Set T) n) :=
    linEquivOfRing
      { toFun := Ideal.Quotient.mk _
        invFun := Ideal.Quotient.lift _ (RingHom.id _) (by
          intro a ha
          rw [hb] at ha
          simpa using ha)
        left_inv := fun x => by simp
        right_inv := fun x => by
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          simp
        map_add' := map_add _ } (fun _ _ => rfl)
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- `T` is killed by powers of the characteristic at every point of `Spec A`. -/
def TorsResRing (A : Type w₁) (T : Type*) [CommRing A] [AddCommGroup T] : Prop :=
  ∀ (K : Type w₁) [Field K] (_ : A →+* K) (q : ℕ) [ExpChar K q] (t : T), ∃ N : ℕ, q ^ N • t = 0

/-- For a finite `T`, the augmentation ideal of `A[T]` is nilpotent, when `T` is killed by powers of
the characteristic at every point of `Spec A`: the fibres of `D(T)` are infinitesimal. -/
lemma base_nil {A T : Type w₁} [CommRing A] [AddCommGroup T] [Finite T] (h : TorsResRing A T) (n : ℕ) :
    ∃ k, augI A T ^ k ≤ Jn A (∅ : Set T) n := by
  classical
  have hb : Jn A (∅ : Set T) n = ⊥ := by simp [Jn]
  rw [hb]
  have hfg : (augI A T).FG := by
    refine ⟨(Set.finite_range fun m : T => (single m 1 - 1 : AddMonoidAlgebra A T)).toFinset, ?_⟩
    simp [augI]
  have hle : augI A T ≤ (⊥ : Ideal (AddMonoidAlgebra A T)).radical := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨t, rfl⟩
    change _ ∈ (⊥ : Ideal (AddMonoidAlgebra A T)).radical
    rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.2 ?_
    rintro P ⟨-, hP⟩
    let K := FractionRing (AddMonoidAlgebra A T ⧸ P)
    let ι : AddMonoidAlgebra A T →+* K :=
      (algebraMap (AddMonoidAlgebra A T ⧸ P) K).comp (Ideal.Quotient.mk P)
    obtain ⟨q, hq⟩ := ExpChar.exists K
    obtain ⟨N, hN⟩ := h K (ι.comp AddMonoidAlgebra.singleZeroRingHom) q t
    let τ : K := ι (single t 1)
    have hτ : τ ^ (q ^ N) = 1 := by
      change ι (single t 1) ^ (q ^ N) = 1
      rw [← map_pow, AddMonoidAlgebra.single_pow, hN, one_pow]
      exact map_one ι
    have h0 : (τ - 1) ^ (q ^ N) = 0 := by
      rw [sub_pow_expChar_pow, hτ, one_pow, sub_self]
    have h1 : ι (single t 1 - 1) = 0 := by
      rw [map_sub, map_one]
      exact pow_eq_zero_iff (pow_pos (expChar_pos K q) N).ne' |>.1 h0
    have hinj := IsFractionRing.injective (AddMonoidAlgebra A T ⧸ P) K
    have h2 : Ideal.Quotient.mk P (single t 1 - 1) = 0 :=
      hinj (by rw [map_zero]; exact h1)
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  exact Ideal.exists_pow_le_of_le_radical_of_fg hle hfg

end Base

section Transport

variable {A N N' : Type*} [CommRing A] [AddCommGroup N] [AddCommGroup N']

/-- The ring isomorphism `A[N] ≃ A[N']`. -/
def domR (e : N ≃+ N') : AddMonoidAlgebra A N ≃+* AddMonoidAlgebra A N' :=
  (AddMonoidAlgebra.domCongr A A e).toRingEquiv

@[simp] lemma domR_single (e : N ≃+ N') (m : N) (a : A) : domR e (single m a) = single (e m) a := by
  simp [domR]

lemma map_Jn (e : N ≃+ N') (E : Set N) (n : ℕ) :
    (Jn A E n).map (domR (A := A) e) = Jn A (e '' E) n := by
  rw [Jn, Ideal.map_span, Jn]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨e m, ⟨m, hm, rfl⟩, ?_⟩
    simp [map_pow, map_sub]
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    simp [map_pow, map_sub]

lemma map_augI (e : N ≃+ N') :
    (augI A N).map (domR (A := A) e) = augI A N' := by
  rw [augI, Ideal.map_span, augI]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨e m, by simp⟩
  · rintro ⟨m, rfl⟩
    exact ⟨_, ⟨e.symm m, rfl⟩, by simp⟩

theorem transport_free (e : N ≃+ N') (E : Set N) (n : ℕ)
    (h : Module.Free A (AddMonoidAlgebra A N ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A N ⧸ Jn A E n)) :
    Module.Free A (AddMonoidAlgebra A N' ⧸ Jn A (e '' E) n) ∧
      Module.Finite A (AddMonoidAlgebra A N' ⧸ Jn A (e '' E) n) := by
  have hm : Jn A (e '' E) n = (Jn A E n).map (domR (A := A) e) :=
    (map_Jn e E n).symm
  let f := Ideal.quotientEquiv (Jn A E n) (Jn A (e '' E) n) (domR e) hm
  let L : (AddMonoidAlgebra A N ⧸ Jn A E n) ≃ₗ[A] (AddMonoidAlgebra A N' ⧸ Jn A (e '' E) n) :=
    linEquivOfRing f.toAddEquiv (by
      intro a x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk _ (domR e (a • x)) = a • Ideal.Quotient.mk _ (domR e x)
      have : domR e (a • x) = a • domR e x := by
        simp [domR]
      rw [this]
      rfl)
  have := h.1
  have := h.2
  exact ⟨Module.Free.of_equiv L, Module.Finite.equiv L⟩

theorem transport_le (e : N ≃+ N') (E : Set N) (n : ℕ) (h : Jn A E n ≤ augI A N ^ n) :
    Jn A (e '' E) n ≤ augI A N' ^ n := by
  rw [← map_Jn e E n, ← map_augI e, ← Ideal.map_pow]
  exact Ideal.map_mono h

theorem transport_nil (e : N ≃+ N') (E : Set N) (n : ℕ) (h : ∃ k, augI A N ^ k ≤ Jn A E n) :
    ∃ k, augI A N' ^ k ≤ Jn A (e '' E) n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [← map_Jn e E n, ← map_augI e, ← Ideal.map_pow]
  exact Ideal.map_mono hk

end Transport

section Main

/-- `T × ℤ^{r+1} = (T × ℤ^r) × ℤ`. -/
def splitE (T : Type*) [AddCommGroup T] (r : ℕ) :
    ((T × (Fin r → ℤ)) × ℤ) ≃+ (T × (Fin (r + 1) → ℤ)) where
  toFun p := (p.1.1, Fin.cons p.2 p.1.2)
  invFun p := ((p.1, Fin.tail p.2), p.2 0)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by
    refine Prod.ext rfl (funext fun i => ?_)
    refine Fin.cases rfl (fun j => rfl) i

/-- The conclusion of Lemma A.5, for a fixed set of generators `E`. -/
def GoodE (T : Type) [AddCommGroup T] (N : Type u) [AddCommGroup N] (E : Set N) : Prop :=
  ∀ (A : Type u) [CommRing A] (n : ℕ),
    Module.Free A (AddMonoidAlgebra A N ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A N ⧸ Jn A E n) ∧
      Jn A E n ≤ augI A N ^ n ∧
      (TorsResRing A T → ∃ k, augI A N ^ k ≤ Jn A E n)

theorem exists_good (T : Type) [AddCommGroup T] [Finite T] :
    ∀ (r : ℕ) (N : Type u) [AddCommGroup N] (e : (ULift.{u} T × (Fin r → ℤ)) ≃+ N), ∃ E : Set N, GoodE T N E
  | 0, N, _, e => by
    let e0 : ULift.{u} T ≃+ (ULift.{u} T × (Fin 0 → ℤ)) :=
      { toFun := fun t => (t, 0), invFun := fun p => p.1, left_inv := fun _ => rfl
        right_inv := fun p => Prod.ext rfl (Subsingleton.elim _ _)
        map_add' := fun a b => Prod.ext rfl (Subsingleton.elim _ _) }
    let e1 : ULift.{u} T ≃+ N := e0.trans e
    refine ⟨e1 '' ∅, fun A _ n => ?_⟩
    have h1 := transport_free (A := A) e1 ∅ n (base_free n)
    refine ⟨h1.1, h1.2, ?_, fun hT => ?_⟩
    · refine transport_le e1 ∅ n ?_
      simp [Jn]
    · have hT' : TorsResRing A (ULift.{u} T) := by
        intro K _ f q _ t
        obtain ⟨N, hN⟩ := hT K f q t.down
        exact ⟨N, ULift.ext _ _ hN⟩
      exact transport_nil e1 ∅ n (base_nil hT' n)
  | r + 1, N, _, e => by
    obtain ⟨E₀, hE₀⟩ := exists_good T r (ULift.{u} T × (Fin r → ℤ)) (AddEquiv.refl _)
    let e1 : ((ULift.{u} T × (Fin r → ℤ)) × ℤ) ≃+ N := (splitE (ULift.{u} T) r).trans e
    refine ⟨e1 '' stepE E₀, fun A _ n => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hE₀ A n
    have hs := transport_free (A := A) e1 _ n (step_free E₀ n h1 h2)
    exact ⟨hs.1, hs.2, transport_le e1 _ n (step_le E₀ n h3),
      fun hT => transport_nil e1 _ n (step_nil E₀ n (h4 hT))⟩

/-- **Lemma A.5** for `G = D(M)`, `M` a finitely generated abelian group. There is a set `E ⊆ M`
(a basis of a free complement of the torsion) such that over every ring `A`, the closed subschemes
`F_n = V(J_n)` of `D(M)_A`, `J_n = ((X^e - 1)^n, e ∈ E)`, satisfy:

* `F_n` is finite free over `A`;
* `F_n` contains the `n`-th thickening of the unit section: `J_n ≤ I^n` (in particular, for `n ≥ 1`,
  `F_n` contains the unit section);
* if the torsion of `M` is killed by the residue characteristics, in particular if `D(M)` has
  connected fibres (`torsionResidue_of_connected`), then `F_n` is an infinitesimal neighbourhood of
  the unit section: `I^k ≤ J_n` for some `k`. So `{F_n}` is cofinal with `{V(I^k)}`.

This improves the paper for `D(M)`: `F_n` exists globally, without étale localization on `S`, and is
defined over `ℤ`. The sequence `V(I^n)` itself is not flat in general: for `M = ℤ/2`, `A = ℤ/4`,
`A[M]/I^2 = A ⊕ A/2`. -/
theorem lemmaA5 (M : Type u) [AddCommGroup M] [AddGroup.FG M] :
    ∃ E : Set M, ∀ (A : Type u) [CommRing A] (n : ℕ),
      Module.Free A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Jn A E n ≤ augI A M ^ n ∧
      (TorsionResidue M (Spec (.of A)) → ∃ k, augI A M ^ k ≤ Jn A E n) := by
  obtain ⟨r, ι, _, p, hp, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i, ZMod (p i ^ e i)
  have hT : Finite T :=
    Finite.of_equiv (∀ i, ZMod (p i ^ e i)) (DirectSum.addEquivProd _).symm.toEquiv
  let ψ : (ULift.{u} T × (Fin r → ℤ)) ≃+ M :=
    ((AddEquiv.ulift.prodCongr (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin r)).symm.toAddEquiv).trans
      AddEquiv.prodComm).trans φ.symm
  obtain ⟨E, hE⟩ := exists_good T r M ψ
  refine ⟨E, fun A _ n => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hE A n
  refine ⟨h1, h2, h3, fun hA => h4 ?_⟩
  intro K _ f q _ t
  let g : Spec (.of K) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom f)
  let x := Scheme.SpecToEquivOfField K (Spec (.of A)) g
  obtain ⟨q', hq'⟩ := ExpChar.exists ((Spec (.of A)).residueField x.1)
  have hK : ExpChar K q' := expChar_of_injective_ringHom (f := x.2.hom) x.2.hom.injective q'
  have hqq : q = q' := ExpChar.eq ‹_› hK
  subst hqq
  let m : M := ψ (⟨t⟩, 0)
  have hm : IsOfFinAddOrder m := by
    have : IsOfFinAddOrder t := by
      exact isOfFinAddOrder_of_finite t
    obtain ⟨d, hd, hd'⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 this
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨d, hd, ?_⟩
    change d • ψ (⟨t⟩, 0) = 0
    rw [← map_nsmul]
    have : d • ((⟨t⟩, 0) : ULift.{u} T × (Fin r → ℤ)) = 0 := by
      refine Prod.ext (ULift.ext _ _ hd') (by simp)
      |> fun h => h
    rw [this, map_zero]
  obtain ⟨N, hN⟩ := hA x.1 q hq' m hm
  refine ⟨N, ?_⟩
  have h0 : ψ (q ^ N • ((⟨t⟩, 0) : ULift.{u} T × (Fin r → ℤ))) = ψ 0 := by
    rw [map_nsmul, map_zero]
    exact hN
  have := ψ.injective h0
  exact congrArg ULift.down (congrArg Prod.fst this)

end Main

section LemmaA3

variable {A R' N : Type*} [CommRing A] [CommRing R'] [AddCommGroup N]

/-- `u[N] : A[N] → R'[N]`, base change of functions of `D(N)` along `u : A → R'`. -/
def baseR (u : A →+* R') : AddMonoidAlgebra A N →+* AddMonoidAlgebra R' N :=
  AddMonoidAlgebra.mapRingHom N u

@[simp] lemma baseR_single (u : A →+* R') (m : N) (a : A) :
    baseR u (single m a) = single m (u a) := by
  simp [baseR]

lemma baseR_mem_Jn (u : A →+* R') (E : Set N) (n : ℕ) {x : AddMonoidAlgebra A N}
    (hx : x ∈ Jn A E n) : baseR u x ∈ Jn R' E n := by
  have : Jn A E n ≤ (Jn R' E n).comap (baseR u) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨e, he, rfl⟩
    change baseR (N := N) u _ ∈ Jn R' E n
    have h : baseR u ((single e 1 - 1 : AddMonoidAlgebra A N) ^ n) =
        (single e 1 - 1 : AddMonoidAlgebra R' N) ^ n := by
      rw [map_pow, map_sub, baseR_single, map_one, map_one]
    rw [h]
    exact Ideal.subset_span ⟨e, he, rfl⟩
  exact this hx

/-- The ideal of the stabilizer of the action of `F` on `Spec A`, for the coaction `ρ : A → A[N]`,
before reduction modulo `J_n`: generated by the `ρ(a) - a`. It is the ideal `I` of the printed proof
of Lemma A.3, for `Stab ⊆ F × X`. -/
def stabI (ρ : A → AddMonoidAlgebra A N) : Ideal (AddMonoidAlgebra A N) :=
  Ideal.span (Set.range fun a => ρ a - single 0 a)

/-- The ideal `J = im(I ⊗ A^∨ → O_X)` of the printed proof of Lemma A.3, for `F = F_n`: generated by
the values of all `A`-linear forms of `A[N]/J_n` on the stabilizer ideal. -/
def fixedJ (ρ : A → AddMonoidAlgebra A N) (E : Set N) (n : ℕ) : Ideal A :=
  Ideal.span {c | ∃ (φ : (AddMonoidAlgebra A N ⧸ Jn A E n) →ₗ[A] A) (w : AddMonoidAlgebra A N),
    w ∈ stabI ρ ∧ c = φ (Ideal.Quotient.mk _ w)}

/-- The form `φ` of `A[N]/J_n`, base changed along `u`. -/
def formBase (u : A →+* R') {E : Set N} {n : ℕ} (φ : (AddMonoidAlgebra A N ⧸ Jn A E n) →ₗ[A] A)
    (f : AddMonoidAlgebra R' N) : R' :=
  f.coeff.sum fun m r => r * u (φ (Ideal.Quotient.mk _ (single m 1)))

lemma formBase_add (u : A →+* R') {E : Set N} {n : ℕ} (φ : (AddMonoidAlgebra A N ⧸ Jn A E n) →ₗ[A] A)
    (f g : AddMonoidAlgebra R' N) : formBase u φ (f + g) = formBase u φ f + formBase u φ g := by
  classical
  exact Finsupp.sum_add_index' (by simp) (by intros; ring)

lemma formBase_single (u : A →+* R') {E : Set N} {n : ℕ}
    (φ : (AddMonoidAlgebra A N ⧸ Jn A E n) →ₗ[A] A) (m : N) (r : R') :
    formBase u φ (single m r) = r * u (φ (Ideal.Quotient.mk _ (single m 1))) := by
  classical
  exact Finsupp.sum_single_index (by simp)

lemma formBase_baseR (u : A →+* R') {E : Set N} {n : ℕ}
    (φ : (AddMonoidAlgebra A N ⧸ Jn A E n) →ₗ[A] A) (m : N) (r : R') (v : AddMonoidAlgebra A N) :
    formBase u φ (single m r * baseR u v) =
      r * u (φ (Ideal.Quotient.mk _ (single m 1 * v))) := by
  induction v using AddMonoidAlgebra.induction_linear with
  | zero => simp [show formBase u φ 0 = 0 from Finsupp.sum_zero_index]
  | add f g hf hg =>
    rw [map_add, mul_add, formBase_add, hf, hg, mul_add, map_add, map_add, map_add, mul_add]
  | single k a =>
    rw [baseR_single, AddMonoidAlgebra.single_mul_single, formBase_single]
    have e : (single m 1 * single k a : AddMonoidAlgebra A N) = a • single (m + k) 1 := by
      rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one,
        one_mul]
    have e2 : (Ideal.Quotient.mk (Jn A E n) (a • single (m + k) 1)) =
        a • Ideal.Quotient.mk (Jn A E n) (single (m + k) 1) := rfl
    rw [e, e2, map_smul, smul_eq_mul, map_mul]
    ring

lemma formBase_eq_zero (u : A →+* R') {E : Set N} {n : ℕ}
    (φ : (AddMonoidAlgebra A N ⧸ Jn A E n) →ₗ[A] A) {x : AddMonoidAlgebra R' N}
    (hx : x ∈ Jn R' E n) : formBase u φ x = 0 := by
  have hzero : formBase u φ (0 : AddMonoidAlgebra R' N) = 0 := Finsupp.sum_zero_index
  have key : ∀ y : AddMonoidAlgebra R' N, formBase u φ (y * x) = 0 := by
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, he, rfl⟩ := hz
      intro y
      have hg : (fun e => (single e 1 - 1 : AddMonoidAlgebra R' N) ^ n) e =
          baseR u ((single e 1 - 1 : AddMonoidAlgebra A N) ^ n) := by
        simp only []
        rw [map_pow, map_sub, baseR_single, map_one, map_one]
      rw [hg]
      induction y using AddMonoidAlgebra.induction_linear with
      | zero => rw [zero_mul, hzero]
      | add f g hf hg' => rw [add_mul, formBase_add, hf, hg', add_zero]
      | single m r =>
        rw [formBase_baseR]
        have : Ideal.Quotient.mk (Jn A E n)
            (single m 1 * (single e 1 - 1 : AddMonoidAlgebra A N) ^ n) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2
            (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e, he, rfl⟩))
        rw [this, map_zero, map_zero, mul_zero]
    | zero => intro y; rw [mul_zero, hzero]
    | add a b _ _ ha hb => intro y; rw [mul_add, formBase_add, ha, hb, add_zero]
    | smul c a _ ha =>
      intro y
      rw [smul_eq_mul, ← mul_assoc]
      exact ha _
  simpa using key 1

/-- **Lemma A.3** for `F = F_n ⊆ D(N)`, on the affine side. Let `X = Spec A` with coaction `ρ` (any
map; `ρ(a) = Σ a_m X^m` for the action of `D(N)`), and suppose `F_n` is finite free over `A`
(`lemmaA5`). A point `u : A → R'` of `X` is fixed by `F_n`, i.e. `ρ(a) = a` in `R'[N]/J_n` for all
`a`, if and only if it factors through the closed subscheme `V(J)`, where `J = fixedJ`. -/
theorem lemmaA3_affine (ρ : A → AddMonoidAlgebra A N) (E : Set N) (n : ℕ)
    (hF : Module.Free A (AddMonoidAlgebra A N ⧸ Jn A E n))
    (hf : Module.Finite A (AddMonoidAlgebra A N ⧸ Jn A E n)) (u : A →+* R') :
    (∀ a, baseR u (ρ a) - single 0 (u a) ∈ Jn R' E n) ↔ fixedJ ρ E n ≤ RingHom.ker u := by
  classical
  constructor
  · intro h
    refine Ideal.span_le.2 ?_
    rintro _ ⟨φ, w, hw, rfl⟩
    have hle : stabI ρ ≤ (Jn R' E n).comap (baseR u) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      change baseR (N := N) u _ ∈ Jn R' E n
      rw [map_sub, baseR_single]
      exact h a
    have h0 := formBase_eq_zero u φ (hle hw)
    have h1 := formBase_baseR u φ 0 1 w
    rw [AddMonoidAlgebra.one_def.symm, one_mul, one_mul, ← AddMonoidAlgebra.one_def, one_mul] at h1
    rw [h0] at h1
    exact h1.symm
  · intro h a
    let C := AddMonoidAlgebra A N ⧸ Jn A E n
    let w : AddMonoidAlgebra A N := ρ a - single 0 a
    have hw : w ∈ stabI ρ := Ideal.subset_span ⟨a, rfl⟩
    let b := Module.Free.chooseBasis A C
    have : Fintype (Module.Free.ChooseBasisIndex A C) := Module.Free.ChooseBasisIndex.fintype A C
    have hc : ∀ i, u (b.coord i (Ideal.Quotient.mk _ w)) = 0 := fun i =>
      h (Ideal.subset_span ⟨b.coord i, w, hw, rfl⟩)
    choose l hl using fun i => Ideal.Quotient.mk_surjective (b i)
    have hsum : w - ∑ i, b.coord i (Ideal.Quotient.mk _ w) • l i ∈ Jn A E n := by
      refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
      rw [map_sub, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (Ideal.Quotient.mk _ w)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      change _ • b i = Ideal.Quotient.mk _ (_ • l i)
      rw [← hl i]
      rfl
    have h2 := baseR_mem_Jn u E n hsum
    have e0 : baseR u (∑ i, b.coord i (Ideal.Quotient.mk _ w) • l i) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      have : baseR u (algebraMap A (AddMonoidAlgebra A N) (b.coord i (Ideal.Quotient.mk _ w))) = 0 := by
        change baseR u (single 0 _) = 0
        rw [baseR_single]
        have h3 : u (algebraMap A A (b.coord i (Ideal.Quotient.mk _ w))) = 0 := hc i
        rw [h3, AddMonoidAlgebra.single_zero]
      rw [this, zero_mul]
    rw [map_sub, e0, sub_zero] at h2
    have e1 : baseR u w = baseR u (ρ a) - single 0 (u a) := by
      simp only [w]
      rw [map_sub, baseR_single]
    rwa [← e1]

end LemmaA3

end

end AlgMag.AppR

#print axioms AlgMag.AppR.torsionResidue_of_connected
#print axioms AlgMag.AppR.ker_augHom
#print axioms AlgMag.AppR.lemmaA5
#print axioms AlgMag.AppR.lemmaA3_affine
