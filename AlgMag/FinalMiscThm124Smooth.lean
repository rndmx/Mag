/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalMiscThm124Local
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.FibreInput
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SequenceSpreadingOut
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.IdealEquality
import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic.RegularIsQuasiRegular
import StacksFrontier.RingTheory.Smooth.Syntomic

/-!
# Theorem 12.4: the printed route through Tags 067U, 063M, ring form

`A₀`, `B` smooth over `R`, `π : B → A₀` a retraction. The printed proof takes from Tags 067U, 063M that
`Spec A₀ → Spec B` is regular and that `I/I²` is finite projective. Here:

* `isQRAt_of_smooth`: the content of Tag 067U at a prime (`exists_isRegular_fibre_of_smooth_of_syntomic`
  and the spreading out of Tags 062Y, 046Y), read as `IsQRAt` through Tag 00LN.
* `projective_conormal_of_smooth`: `I/I²` is a direct summand of `A₀ ⊗_B Ω_{B/R}` (Tag 031I).
* `printed_ring_smooth`: **Theorem 12.4**, the ring statement, with no smoothness of `A₀ → B` assumed.
-/

open AlgMag.SymRing MvPolynomial Stacks.QuasiregularSequence RingTheory.Sequence
open scoped TensorProduct

universe u

namespace AlgMag.Sec12Printed

section QS

variable {R : Type*} [CommRing R]

lemma qs_of_weaklyRegular (rs : List R) (h : IsWeaklyRegular R rs) : IsQuasiregularSeq rs R := by
  induction rs using List.reverseRecOn with
  | nil => exact isQuasiregularSeq_nil R
  | append_singleton init g ih =>
    rw [isWeaklyRegular_append_iff] at h
    obtain ⟨h1, h2⟩ := h
    rw [isWeaklyRegular_singleton_iff] at h2
    exact isQuasiregularSeq_snoc R init g (ih h1) h2

/-- Tag 00LN for a weakly regular family indexed by `Fin r`. -/
lemma qr_fin {r : ℕ} (f : Fin r → R) (h : IsWeaklyRegular R (List.ofFn f)) (n : ℕ)
    (m : (Fin r → ℕ) → R)
    (hs : (∑ I ∈ Finset.Nat.antidiagonalTuple r n, (∏ i, f i ^ I i) * m I) ∈
      Ideal.span (Set.range f) ^ (n + 1)) :
    ∀ I ∈ Finset.Nat.antidiagonalTuple r n, m I ∈ Ideal.span (Set.range f) := by
  have key : ∀ (rs : List R) (e : rs.length = r), (∀ i : Fin r, rs[i.cast e.symm] = f i) →
      IsQuasiregularSeq rs R →
      ∀ I ∈ Finset.Nat.antidiagonalTuple r n, m I ∈ Ideal.span (Set.range f) := by
    intro rs e he hq
    subst e
    obtain rfl : f = fun i : Fin rs.length => rs[i] := funext fun i => (he i).symm
    have hspan := ofList_eq_span_range rs
    have := hq n m (by
      rw [smul_eq_mul, Ideal.mul_top, hspan]
      simpa [listPow] using hs)
    intro I hI
    have := this I hI
    rwa [smul_eq_mul, Ideal.mul_top, hspan] at this
  exact key (List.ofFn f) (List.length_ofFn) (fun i => by simp) (qs_of_weaklyRegular _ h)

end QS

variable {A₀ B R : Type u} [CommRing A₀] [CommRing B] [CommRing R] [Algebra A₀ B]
  {π : B →ₐ[A₀] A₀}

/-- **Tag 067U at a prime, read as `IsQRAt`.** -/
theorem isQRAt_of_smooth [Algebra R B] [Algebra R A₀] [Algebra.Smooth R B] [Algebra.Smooth R A₀]
    (φ : B →ₐ[R] A₀) (hφ : ∀ b, φ b = π b) (q : Ideal A₀) [hq : q.IsPrime] : IsQRAt π q := by
  have surj : Function.Surjective φ := fun a => ⟨algebraMap A₀ B a, by rw [hφ]; exact π.commutes a⟩
  have hkI : ∀ b, b ∈ RingHom.ker φ ↔ π b = 0 := fun b => by rw [RingHom.mem_ker, hφ]
  let Q : Ideal B := q.comap π.toRingHom
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
  have hle : RingHom.ker φ ≤ Q := fun b hb => by
    change π b ∈ q
    rw [(hkI b).1 hb]
    exact q.zero_mem
  have : Algebra.Syntomic R A₀ := Algebra.Smooth.syntomic R A₀
  have : Algebra.Syntomic R B := Algebra.Smooth.syntomic R B
  obtain ⟨r, f, hfI, hfQ, hreg, hsup⟩ :=
    Stacks.RingTheory.SpreadingOut.exists_isRegular_fibre_of_smooth_of_syntomic φ surj Q hle
  obtain ⟨g₁, hg₁, hwr, -⟩ :=
    Stacks.RingTheory.SpreadingOut.exists_notMem_isWeaklyRegular_and_flat_quotient_away
      (A := R) Q f hfQ hreg
  have hflat : Module.Flat R (B ⧸ RingHom.ker φ) :=
    Module.Flat.of_linearEquiv (Ideal.quotientKerAlgEquivOfSurjective surj).toLinearEquiv
  obtain ⟨g₂, hg₂, heq⟩ := Stacks.RingTheory.SpreadingOut.exists_notMem_map_eq_map_away (A := R) Q
    (Ideal.span (Set.range f)) (RingHom.ker φ)
    (Ideal.span_le.mpr (Set.range_subset_iff.mpr hfI))
    (Submodule.fg_span (Set.finite_range f))
    (Algebra.FinitePresentation.ker_fG_of_surjective φ surj)
    (Stacks.RingTheory.SpreadingOut.flat_quotient_localization _ Q hflat) hsup
  have hI : ∀ i, f i ∈ augI π := fun i => (hkI _).1 (hfI i)
  have hJI : ∀ z ∈ Ideal.span (Set.range f), π z = 0 := fun z hz => by
    have : Ideal.span (Set.range f) ≤ RingHom.ker φ :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr hfI)
    exact (hkI z).1 (this hz)
  -- clearing `g₂`
  have clear : ∀ (k : ℕ), ∀ a ∈ augI π ^ k, ∃ n : ℕ, g₂ ^ n * a ∈ Ideal.span (Set.range f) ^ k := by
    intro k a ha
    have ha' : a ∈ RingHom.ker φ ^ k := by
      have : augI π = RingHom.ker φ := Ideal.ext fun b => (hkI b).symm
      rwa [this] at ha
    have h1 : algebraMap B (Localization.Away g₂) a ∈ (RingHom.ker φ ^ k).map (algebraMap B _) :=
      Ideal.mem_map_of_mem _ ha'
    rw [Ideal.map_pow, heq, ← Ideal.map_pow,
      IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g₂)] at h1
    obtain ⟨⟨y, s⟩, hy⟩ := h1
    have h2 := (IsLocalization.eq_iff_exists (Submonoid.powers g₂) (Localization.Away g₂)).1
      ((by simpa using hy) : algebraMap B (Localization.Away g₂) (a * s.1) = algebraMap B _ y.1)
    obtain ⟨c, hc⟩ := h2
    obtain ⟨n₁, hn₁⟩ := c.2
    obtain ⟨n₂, hn₂⟩ := s.2
    replace hn₁ : g₂ ^ n₁ = c.1 := hn₁
    replace hn₂ : g₂ ^ n₂ = s.1 := hn₂
    refine ⟨n₁ + n₂, ?_⟩
    have : g₂ ^ (n₁ + n₂) * a = c.1 * y.1 := by
      rw [pow_add, hn₁, hn₂, ← hc]
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ y.2
  refine ⟨r, f, hI, ?_, ?_⟩
  · intro a ha
    obtain ⟨n, hn⟩ := clear 1 a (by simpa using ha)
    refine ⟨g₂ ^ n, ?_, by simpa using hn⟩
    rw [map_pow]
    exact fun h => hg₂ (hq.mem_of_pow_mem _ h)
  · intro k P hP hmem
    obtain ⟨n, hn⟩ := clear (k + 1) _ hmem
    let c : (Fin r → ℕ) → B := fun I =>
      g₂ ^ n * algebraMap A₀ B (coeff (Finsupp.equivFunOnFinite.symm I) P)
    have hsum : aeval f P =
        ∑ I ∈ Finset.Nat.antidiagonalTuple r k, (∏ i, f i ^ I i) *
          algebraMap A₀ B (coeff (Finsupp.equivFunOnFinite.symm I) P) := by
      rw [aeval_def, eval₂_eq']
      refine Finset.sum_of_injOn (⇑Finsupp.equivFunOnFinite)
        Finsupp.equivFunOnFinite.injective.injOn ?_ ?_ ?_
      · intro e he
        have h3 := hP (mem_support_iff.1 he)
        rw [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple]
        rw [← h3, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
        simp
      · intro I hI hne
        have : coeff (Finsupp.equivFunOnFinite.symm I) P = 0 := by
          by_contra h0
          exact hne ⟨_, mem_support_iff.2 h0, by simp⟩
        rw [this, map_zero, mul_zero]
      · intro e _
        simp [mul_comm]
    have e2 : Ideal.span (Set.range fun i => algebraMap B (Localization.Away g₁) (f i)) =
        (Ideal.span (Set.range f)).map (algebraMap B (Localization.Away g₁)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    have hrel : (∑ I ∈ Finset.Nat.antidiagonalTuple r k,
        (∏ i, (algebraMap B (Localization.Away g₁) (f i)) ^ I i) *
          algebraMap B (Localization.Away g₁) (c I)) ∈
        Ideal.span (Set.range fun i => algebraMap B (Localization.Away g₁) (f i)) ^ (k + 1) := by
      have e1 : (∑ I ∈ Finset.Nat.antidiagonalTuple r k,
          (∏ i, (algebraMap B (Localization.Away g₁) (f i)) ^ I i) *
            algebraMap B (Localization.Away g₁) (c I)) =
          algebraMap B (Localization.Away g₁) (g₂ ^ n * aeval f P) := by
        rw [hsum, Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        simp only [c, map_mul, map_prod, map_pow]
        ring
      rw [e1, e2, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hn
    have hc := qr_fin _ hwr k _ hrel
    have hl : ∀ I ∈ Finset.Nat.antidiagonalTuple r k,
        ∃ l : ℕ, g₁ ^ l * c I ∈ Ideal.span (Set.range f) := by
      intro I hI
      have h1 := hc I hI
      rw [e2, IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g₁)] at h1
      obtain ⟨⟨y, s⟩, hy⟩ := h1
      obtain ⟨d, hd⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers g₁) (Localization.Away g₁)).1
        ((by simpa using hy) : algebraMap B (Localization.Away g₁) (c I * s.1) = algebraMap B _ y.1)
      obtain ⟨n₁, hn₁⟩ := d.2
      obtain ⟨n₂, hn₂⟩ := s.2
      replace hn₁ : g₁ ^ n₁ = d.1 := hn₁
      replace hn₂ : g₁ ^ n₂ = s.1 := hn₂
      refine ⟨n₁ + n₂, ?_⟩
      have : g₁ ^ (n₁ + n₂) * c I = d.1 * y.1 := by
        rw [pow_add, hn₁, hn₂, ← hd]
        ring
      rw [this]
      exact Ideal.mul_mem_left _ _ y.2
    choose! l hl using hl
    let L := (Finset.Nat.antidiagonalTuple r k).sup l
    refine ⟨π g₁ ^ L * π g₂ ^ n, ?_, ?_⟩
    · intro h
      rcases hq.mem_or_mem h with h | h
      · exact hg₁ (hq.mem_of_pow_mem _ h)
      · exact hg₂ (hq.mem_of_pow_mem _ h)
    · ext e
      rw [coeff_smul, coeff_zero, smul_eq_mul]
      by_cases h0 : coeff e P = 0
      · rw [h0, mul_zero]
      have hmem : (⇑e : Fin r → ℕ) ∈
          Finset.Nat.antidiagonalTuple r k := by
        have h3 := hP h0
        rw [Finset.Nat.mem_antidiagonalTuple, ← h3, Finsupp.weight_apply,
          Finsupp.sum_fintype _ _ (by simp)]
        simp
      have h4 := hJI _ (hl _ hmem)
      have hLl : l ⇑e ≤ L := Finset.le_sup hmem
      simp only [c, map_mul, map_pow, Finsupp.equivFunOnFinite_symm_coe] at h4
      have h5 : π (algebraMap A₀ B (coeff e P)) = coeff e P := π.commutes _
      rw [h5] at h4
      rw [← Nat.sub_add_cancel hLl, pow_add, mul_assoc, mul_assoc, h4, mul_zero]

/-- Tag 031I: `I/I²` is a direct summand of `A₀ ⊗_B Ω_{B/R}`, which is what Tag 063M gives in the
printed proof. -/
theorem projective_conormal_of_smooth [Algebra R B] [Algebra R A₀] [Algebra.FormallySmooth R B]
    [Algebra.FormallySmooth R A₀] (φ : B →ₐ[R] A₀) (hφ : ∀ b, φ b = π b) :
    Module.Projective A₀ (Conormal π) := by
  letI : Algebra B A₀ := π.toRingHom.toAlgebra
  have hmap : ∀ b, algebraMap B A₀ b = π b := fun _ => rfl
  haveI : IsScalarTower R B A₀ := IsScalarTower.of_algebraMap_eq fun r => by
    rw [hmap, ← hφ]; exact (φ.commutes r).symm
  have surj : Function.Surjective (algebraMap B A₀) := fun a =>
    ⟨algebraMap A₀ B a, by rw [hmap]; exact π.commutes a⟩
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := R) surj).1 inferInstance
  have hsm : ∀ (a : A₀) (y : A₀ ⊗[B] Ω[B⁄R]), algebraMap A₀ B a • y = a • y := by
    intro a y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, hx, hy]
    | tmul x w =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def,
        hmap]
      congr 1
      exact congrArg (· * x) (π.commutes a)
  let i : Conormal π →ₗ[A₀] A₀ ⊗[B] Ω[B⁄R] :=
    { toFun := fun x => KaehlerDifferential.kerCotangentToTensor R B A₀ x
      map_add' := fun x y => map_add _ _ _
      map_smul' := fun a x => by
        rw [RingHom.id_apply, ← hsm, ← map_smul]
        congr 1
        exact (algebraMap_smul B a x).symm }
  let s : A₀ ⊗[B] Ω[B⁄R] →ₗ[A₀] Conormal π :=
    { toFun := fun y => l y
      map_add' := fun x y => map_add _ _ _
      map_smul' := fun a y => by
        rw [RingHom.id_apply, ← hsm]
        refine (map_smul l _ y).trans ?_
        exact algebraMap_smul B a (l y) }
  have hsi : s ∘ₗ i = LinearMap.id := LinearMap.ext fun x => LinearMap.congr_fun hl x
  exact Module.Projective.of_split i s hsi

/-- **Theorem 12.4**, ring statement, printed route: `B`, `A₀` smooth over `R`, `π` the retraction, `B`
graded with `A₀` as augmentation. Then `Sym_{A₀}(I/I²) ≅ B`. Formal smoothness of `A₀ → B` is not assumed.
The inputs are the content of Tags 067U, 063M, 062Z. -/
theorem printed_ring_smooth {Y : Type u} [AddCommMonoid Y] [DecidableEq Y]
    {𝒜 : Y → Submodule A₀ B} [GradedAlgebra 𝒜] {w : Y → ℕ}
    [Algebra R B] [Algebra R A₀] [Algebra.Smooth R B] [Algebra.Smooth R A₀]
    (φ : B →ₐ[R] A₀) (hφ : ∀ b, φ b = π b) (H : IsAug 𝒜 π w) :
    Module.Projective A₀ (Conormal π) ∧ Nonempty (SymmetricAlgebra A₀ (Conormal π) ≃ₐ[A₀] B) := by
  have hp := projective_conormal_of_smooth φ hφ
  exact ⟨hp, printed_ring_qr (fun q hq => by
    haveI := hq.isPrime
    exact isQRAt_of_smooth φ hφ q) H⟩

#print axioms isQRAt_of_smooth
#print axioms projective_conormal_of_smooth
#print axioms printed_ring_smooth

end AlgMag.Sec12Printed
