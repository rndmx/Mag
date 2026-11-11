/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FinitePresentation
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Constructible
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Commutative algebra for "Existence of strongly-FPR atlases"

Mayeux, *Existence of strongly-FPR atlases*, §2. For `U = Spec A` with a morphism to `X`, the
stabilizer group `G'` of the image is a closed subscheme `V(I)` of `D(M)_U = Spec A[M]`, stable under
the powers `g ↦ g^n`, and the stabilizer of `U` is open and closed in it, the complement `C'` being
`V(I) ∩ D(e)` with `e` idempotent modulo `I`.

* `AlgMag.StronglyFPR.isClosed_image_of_idem`: the image in `Spec A` of a clopen part of
  `Spec A[L]` is closed (coefficient ideal of an idempotent is idempotent). This replaces the
  decomposition `K = K^t × F` in the proof of Lemma 2.1 (1), and holds for every `L`.
* `AlgMag.StronglyFPR.mem_coeffIdeal_of_prime`: a point `g` of `G'` with `Y = ker g` lies in a whole
  `D(M/Y) ⊆ G'` (Vandermonde on the powers of `g`). This replaces [SGA3, VIII] in the note.
* `AlgMag.StronglyFPR.isClosed_badImage`: the image of `C'` in `Spec A` is closed, for `A` noetherian
  and `M` finitely generated. This is the set `⋃_Y C_Y` of Lemma 2.3; Chevalley's theorem plays the
  role of Lemma 2.2.
* `AlgMag.StronglyFPR.exists_coeff_notMem`: homogeneous functions separate a point from a stable
  closed set (the graded ideal in Lemma 2.3).
-/

open PrimeSpectrum Topology

namespace AlgMag.StronglyFPR

noncomputable section

section Coeff

variable {A L : Type*} [CommRing A] [AddCommMonoid L]

local notation "AL" => AddMonoidAlgebra A L

lemma coeff_mul_mem {J J' : Ideal A} {x y : AL} (hx : ∀ a, x.coeff a ∈ J)
    (hy : ∀ a, y.coeff a ∈ J') (a : L) : (x * y).coeff a ∈ J * J' := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  refine Ideal.sum_mem _ fun a₁ _ => Ideal.sum_mem _ fun a₂ _ => ?_
  dsimp only
  split_ifs
  · exact Ideal.mul_mem_mul (hx _) (hy _)
  · exact Ideal.zero_mem _

/-- The ideal of the elements with all coefficients in `q`. -/
def coeffIdealOf (q : Ideal A) : Ideal AL where
  carrier := {x | ∀ a, x.coeff a ∈ q}
  add_mem' hx hy a := by
    simpa using q.add_mem (hx a) (hy a)
  zero_mem' a := by simp
  smul_mem' c x hx a := by
    have := coeff_mul_mem (J := ⊤) (J' := q) (x := c) (y := x) (fun _ => trivial) hx a
    simpa using this

lemma mem_of_mem_map {q : Ideal A} {x : AL} (hx : x ∈ q.map (algebraMap A AL)) (a : L) :
    x.coeff a ∈ q := by
  have : q.map (algebraMap A AL) ≤ coeffIdealOf q := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr a
    classical
    change (algebraMap A AL r).coeff a ∈ q
    change (AddMonoidAlgebra.single 0 r : AL).coeff a ∈ q
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact hr
    · exact q.zero_mem
  exact this hx a

lemma single_eq_algebraMap_mul (a : L) (r : A) :
    (AddMonoidAlgebra.single a r : AL) = algebraMap A AL r * AddMonoidAlgebra.single a 1 := by
  change _ = AddMonoidAlgebra.single 0 r * AddMonoidAlgebra.single a 1
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

/-- An element whose coefficients lie in the contraction of an ideal `p` of `A[L]` lies in `p`. -/
lemma mem_of_coeff_mem {p : Ideal AL} {x : AL} (h : ∀ a, algebraMap A AL (x.coeff a) ∈ p) :
    x ∈ p := by
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine Ideal.sum_mem _ fun a _ => ?_
  rw [single_eq_algebraMap_mul]
  exact p.mul_mem_right _ (h a)

/-- The primes of `A[L]` not containing `e`, seen in `Spec A`. -/
def imageSet (e : AL) : Set (PrimeSpectrum A) :=
  {q | ∃ p : PrimeSpectrum AL, e ∉ p.asIdeal ∧ comap (algebraMap A AL) p = q}

/-- Lemma 2.1 (1), the step on the clopen part of `Spec A[L]`: the coefficient ideal of an idempotent
of `A[L]` is finitely generated and idempotent. Hence the image in `Spec A` of the locus `e ≠ 0` is
closed (and open), for any commutative monoid `L`. -/
theorem isClosed_image_of_idem {e : AL} (he : IsIdempotentElem e) : IsClosed (imageSet e) := by
  classical
  let c : Ideal A := Ideal.span (e.coeff '' (e.coeff.support : Set L))
  have hfg : c.FG := ⟨e.coeff.support.image e.coeff, by simp [c]⟩
  have hmem : ∀ a, e.coeff a ∈ c := by
    intro a
    by_cases h : a ∈ e.coeff.support
    · exact Ideal.subset_span ⟨a, h, rfl⟩
    · rw [Finsupp.notMem_support_iff.mp h]; exact c.zero_mem
  have hc : IsIdempotentElem c := by
    refine le_antisymm Ideal.mul_le_left ?_
    rw [Ideal.span_le]
    rintro _ ⟨a, -, rfl⟩
    have := coeff_mul_mem hmem hmem a
    rwa [he.eq] at this
  obtain ⟨d, hd, hcd0⟩ := (Ideal.isIdempotentElem_iff_of_fg c hfg).mp hc
  have hcd : c = Ideal.span {d} := hcd0
  have key : imageSet e = zeroLocus {1 - d} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_zeroLocus, Set.singleton_subset_iff]
      have hnd : d ∉ (comap (algebraMap A AL) p).asIdeal := by
        intro hdq
        apply hp
        refine mem_of_coeff_mem fun a => ?_
        have h1 : e.coeff a ∈ Ideal.span {d} := hcd ▸ hmem a
        have h2 : Ideal.span {d} ≤ (comap (algebraMap A AL) p).asIdeal := by
          rwa [Ideal.span_singleton_le_iff_mem]
        exact h2 h1
      have h0 : d * (1 - d) ∈ (comap (algebraMap A AL) p).asIdeal := by
        have : d * (1 - d) = 0 := by rw [mul_sub, mul_one, hd.eq, sub_self]
        rw [this]; exact Ideal.zero_mem _
      exact ((comap (algebraMap A AL) p).isPrime.mem_or_mem h0).resolve_left hnd
    · intro hq
      rw [mem_zeroLocus, Set.singleton_subset_iff] at hq
      have hq' : (1 - d) ∈ q.asIdeal := hq
      have hdq : d ∉ q.asIdeal := fun h => q.isPrime.ne_top
        ((Ideal.eq_top_iff_one _).mpr (by simpa using q.asIdeal.add_mem hq' h))
      obtain ⟨a₀, ha₀⟩ : ∃ a, e.coeff a ∉ q.asIdeal := by
        by_contra! hall
        have : c ≤ q.asIdeal := by
          rw [Ideal.span_le]
          rintro _ ⟨a, -, rfl⟩
          exact hall a
        exact hdq (this (hcd ▸ Ideal.mem_span_singleton_self d))
      let W : Submonoid AL :=
        { carrier := {x | ∃ s, s ∉ q.asIdeal ∧ (x = algebraMap A AL s ∨ x = algebraMap A AL s * e)}
          one_mem' := ⟨1, fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), Or.inl (map_one _).symm⟩
          mul_mem' := by
            rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
            have hss : s * s' ∉ q.asIdeal := fun h =>
              (q.isPrime.mem_or_mem h).elim hs hs'
            refine ⟨s * s', hss, ?_⟩
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · left; rw [map_mul]
            · right; rw [map_mul, mul_assoc]
            · right; rw [map_mul]; ring
            · right
              rw [map_mul]
              calc _ = algebraMap A AL s * algebraMap A AL s' * (e * e) := by ring
                _ = _ := by rw [he.eq] }
      have hdisj : Disjoint ((q.asIdeal.map (algebraMap A AL) : Ideal AL) : Set AL) (W : Set AL) := by
        rw [Set.disjoint_left]
        rintro x hx ⟨s, hs, hxs⟩
        rcases hxs with rfl | rfl
        · apply hs
          have := mem_of_mem_map hx 0
          have e0 : (algebraMap A AL s).coeff 0 = s := by
            change (AddMonoidAlgebra.single 0 s : AL).coeff 0 = s
            simp
          rwa [e0] at this
        · have := mem_of_mem_map hx a₀
          have e0 : (algebraMap A AL s * e).coeff a₀ = s * e.coeff a₀ := by
            change (AddMonoidAlgebra.single 0 s * e : AL).coeff a₀ = _
            rw [AddMonoidAlgebra.coeff_single_zero_mul]
          rw [e0] at this
          exact (q.isPrime.mem_or_mem this).elim hs ha₀
      obtain ⟨P, hP, hle, hdP⟩ := Ideal.exists_le_prime_disjoint _ W hdisj
      refine ⟨⟨P, hP⟩, ?_, ?_⟩
      · intro heP
        have : e ∈ W := ⟨1, fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h),
          Or.inr (by rw [map_one, one_mul])⟩
        exact (Set.disjoint_left.mp hdP heP) this
      · ext s
        constructor
        · intro hs
          by_contra hsq
          have : algebraMap A AL s ∈ W := ⟨s, hsq, Or.inl rfl⟩
          exact (Set.disjoint_left.mp hdP hs) this
        · intro hs
          exact hle (Ideal.mem_map_of_mem _ hs)
  rw [key]
  exact isClosed_zeroLocus _

end Coeff

section Main

variable {A M : Type*} [CommRing A] [AddCommGroup M]

local notation "RR" => AddMonoidAlgebra A M

/-- The ring map of `g ↦ g^n` on `D(M)_U`. -/
def powMap (A : Type*) [CommRing A] {M : Type*} [AddCommGroup M] (n : ℕ) :
    AddMonoidAlgebra A M →+* AddMonoidAlgebra A M :=
  AddMonoidAlgebra.mapDomainRingHom A (nsmulAddMonoidHom n)

/-- The image in `Spec A` of `V(I) ∩ D(e)`. -/
def badImage (I : Ideal RR) (e : RR) : Set (PrimeSpectrum A) :=
  {q | ∃ p : PrimeSpectrum RR, I ≤ p.asIdeal ∧ e ∉ p.asIdeal ∧ comap (algebraMap A RR) p = q}

/-- The character `χ_m` of `D(M)`. -/
abbrev chi (A : Type*) [CommRing A] {M : Type*} [AddCommGroup M] (m : M) : AddMonoidAlgebra A M :=
  AddMonoidAlgebra.single m 1

lemma chi_add (m n : M) : (chi A (m + n)) = chi A m * chi A n := by
  simp [chi, AddMonoidAlgebra.single_mul_single]

lemma chi_zero : chi A (0 : M) = 1 := rfl

variable {D : Type*} [CommRing D] (φ : AddMonoidAlgebra A M →+* D)

/-- The subgroup `Y` of `M` of the characters trivial on the point `φ` of `D(M)`. -/
def kerSub : AddSubgroup M where
  carrier := {m | φ (chi A m) = 1}
  zero_mem' := by
    change φ (chi A 0) = 1
    rw [chi_zero, map_one]
  add_mem' {a b} ha hb := by
    change φ (chi A (a + b)) = 1
    rw [chi_add, map_mul, show φ (chi A a) = 1 from ha, show φ (chi A b) = 1 from hb, one_mul]
  neg_mem' {a} ha := by
    change φ (chi A (-a)) = 1
    have h : φ (chi A (-a)) * φ (chi A a) = 1 := by
      rw [← map_mul, ← chi_add, neg_add_cancel, chi_zero, map_one]
    rwa [show φ (chi A a) = 1 from ha, mul_one] at h

lemma mem_kerSub {m : M} : m ∈ kerSub φ ↔ φ (chi A m) = 1 := Iff.rfl

lemma map_chi_eq {a b : M} (h : -a + b ∈ kerSub φ) : φ (chi A a) = φ (chi A b) := by
  have e : chi A b = chi A a * chi A (-a + b) := by
    rw [← chi_add, add_neg_cancel_left]
  rw [e, map_mul, show φ (chi A (-a + b)) = 1 from h, mul_one]

lemma map_chi_ne_zero [Nontrivial D] (a : M) : φ (chi A a) ≠ 0 := by
  intro h0
  have h : φ (chi A (-a)) * φ (chi A a) = 1 := by
    rw [← map_mul, ← chi_add, neg_add_cancel, chi_zero, map_one]
  rw [h0, mul_zero] at h
  exact zero_ne_one h

/-- The character of `M/Y` with values in `D`. -/
def charQuot : Multiplicative (M ⧸ kerSub φ) →* D where
  toFun c := φ (chi A (Function.surjInv (QuotientAddGroup.mk_surjective (s := kerSub φ))
    (Multiplicative.toAdd c)))
  map_one' := by
    rw [← map_one φ, ← chi_zero (A := A) (M := M)]
    apply map_chi_eq
    rw [← QuotientAddGroup.eq]
    exact Function.surjInv_eq _ _
  map_mul' c d := by
    rw [← map_mul, ← chi_add]
    apply map_chi_eq
    rw [← QuotientAddGroup.eq]
    have hs := Function.surjInv_eq (QuotientAddGroup.mk_surjective (s := kerSub φ))
    rw [hs, QuotientAddGroup.mk_add, hs, hs]
    rfl

lemma charQuot_mk (m : M) :
    charQuot φ (Multiplicative.ofAdd (m : M ⧸ kerSub φ)) = φ (chi A m) := by
  apply map_chi_eq
  rw [← QuotientAddGroup.eq]
  exact Function.surjInv_eq _ _

lemma charQuot_injective [IsDomain D] : Function.Injective (charQuot φ) := by
  intro c d h
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd c)
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd d)
  have hc : c = Multiplicative.ofAdd (a : M ⧸ kerSub φ) := by rw [ha]; rfl
  have hd : d = Multiplicative.ofAdd (b : M ⧸ kerSub φ) := by rw [hb]; rfl
  rw [hc, hd, charQuot_mk, charQuot_mk] at h
  rw [hc, hd]
  congr 1
  rw [QuotientAddGroup.eq]
  change φ (chi A (-a + b)) = 1
  have e : chi A b = chi A a * chi A (-a + b) := by
    rw [← chi_add, add_neg_cancel_left]
  rw [e, map_mul] at h
  exact (mul_eq_left₀ (map_chi_ne_zero φ a)).mp h.symm

/-- The projection `A[M] → A[M/Y]`, dual to `D(M/Y) ⊆ D(M)`. -/
abbrev quotHom (A : Type*) [CommRing A] {M : Type*} [AddCommGroup M] (Y : AddSubgroup M) :
    AddMonoidAlgebra A M →+* AddMonoidAlgebra A (M ⧸ Y) :=
  AddMonoidAlgebra.mapDomainRingHom A (QuotientAddGroup.mk' Y)

/-- The ideal of the coefficients of the image of `I` in `A[M/Y]`: its zero locus `V_Y` is the locus
of `U` over which `D(M/Y)` lies in `V(I)`. -/
def coeffIdeal (I : Ideal RR) (Y : AddSubgroup M) : Ideal A :=
  Ideal.span {r | ∃ x ∈ I, ∃ c, r = (quotHom A Y x).coeff c}

/-- The map `A[M/Y] → D` induced by `φ`, with `n`-th power of the character. -/
def liftPow (n : ℕ) : AddMonoidAlgebra A (M ⧸ kerSub φ) →+* D :=
  AddMonoidAlgebra.liftNCRingHom (φ.comp (algebraMap A RR)) (charQuot φ ^ n)
    (fun _ _ => mul_comm _ _)

lemma liftPow_single (n : ℕ) (c : M ⧸ kerSub φ) (r : A) :
    liftPow φ n (AddMonoidAlgebra.single c r) =
      φ (algebraMap A RR r) * charQuot φ (Multiplicative.ofAdd c) ^ n := by
  simp [liftPow, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

lemma liftPow_quotHom (n : ℕ) (x : RR) : liftPow φ n (quotHom A (kerSub φ) x) = φ (powMap A n x) := by
  have : (liftPow φ n).comp (quotHom A (kerSub φ)) = φ.comp (powMap A n) := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · simp [liftPow_single, powMap]
    · have e : powMap A n (AddMonoidAlgebra.single m 1) = chi A m ^ n := by
        simp [powMap, chi, AddMonoidAlgebra.single_pow]
      have e2 : quotHom A (kerSub φ) (AddMonoidAlgebra.single m 1) =
          AddMonoidAlgebra.single (m : M ⧸ kerSub φ) 1 := by simp
      change liftPow φ n (quotHom A (kerSub φ) (AddMonoidAlgebra.single m 1)) =
        φ (powMap A n (AddMonoidAlgebra.single m 1))
      rw [e, map_pow, e2, liftPow_single, charQuot_mk, map_one, map_one, one_mul]
  exact congrArg (fun k => k x) this

/-- **Vandermonde step.** A point `φ` of `D(M)` in `V(I)`, for `I` stable under the powers, with
`Y = ker φ`: the coefficients of `I` in `A[M/Y]` vanish at `φ`. So `D(M/Y)` lies in `V(I)` over the
image of `φ`; this is all that is used of the classification of subgroups of `D(M)` ([SGA3, VIII]). -/
theorem map_coeff_eq_zero [IsDomain D] {I : Ideal RR} (hI : ∀ x ∈ I, ∀ n, powMap A n x ∈ I)
    (hφ : ∀ x ∈ I, φ x = 0) {x : RR} (hx : x ∈ I) (c : M ⧸ kerSub φ) :
    φ (algebraMap A RR ((quotHom A (kerSub φ) x).coeff c)) = 0 := by
  classical
  set y := quotHom A (kerSub φ) x with hy
  have hsum : ∀ n : ℕ, ∑ d ∈ y.coeff.support, φ (algebraMap A RR (y.coeff d)) *
      charQuot φ (Multiplicative.ofAdd d) ^ n = 0 := by
    intro n
    have h1 : liftPow φ n y = 0 := by rw [hy, liftPow_quotHom]; exact hφ _ (hI x hx n)
    rw [← AddMonoidAlgebra.sum_coeff_single y, Finsupp.sum, map_sum] at h1
    simpa [liftPow_single] using h1
  by_cases hc : c ∈ y.coeff.support
  · let E := y.coeff.support.equivFin
    let v : Fin y.coeff.support.card → D := fun j => φ (algebraMap A RR (y.coeff (E.symm j)))
    let f : Fin y.coeff.support.card → D := fun j => charQuot φ (Multiplicative.ofAdd (E.symm j : M ⧸ kerSub φ))
    have hf : Function.Injective f := fun i j h => by
      have := charQuot_injective φ h
      exact E.symm.injective (Subtype.ext (Multiplicative.ofAdd.injective this))
    have hv : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf fun i => by
      have h := hsum i
      rw [← Finset.sum_coe_sort] at h
      rw [← h]
      exact Fintype.sum_equiv E.symm _ _ fun j => rfl
    have := congrFun hv (E ⟨c, hc⟩)
    simpa [v] using this
  · rw [Finsupp.notMem_support_iff.mp hc]; simp

/-- `A[M] → (A/𝔠)[M/Y]`. -/
def quotBar (I : Ideal RR) (Y : AddSubgroup M) :
    AddMonoidAlgebra A M →+* AddMonoidAlgebra (A ⧸ coeffIdeal I Y) (M ⧸ Y) :=
  (AddMonoidAlgebra.mapRingHom (M ⧸ Y) (Ideal.Quotient.mk (coeffIdeal I Y))).comp (quotHom A Y)

lemma quotBar_eq_zero {I : Ideal RR} {Y : AddSubgroup M} {x : RR} (hx : x ∈ I) :
    quotBar I Y x = 0 := by
  ext c
  change Ideal.Quotient.mk _ ((quotHom A Y x).coeff c) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨x, hx, c, rfl⟩

lemma quotBar_algebraMap (I : Ideal RR) (Y : AddSubgroup M) (r : A) :
    quotBar I Y (algebraMap A RR r) =
      algebraMap (A ⧸ coeffIdeal I Y) (AddMonoidAlgebra (A ⧸ coeffIdeal I Y) (M ⧸ Y))
        (Ideal.Quotient.mk _ r) := by
  change quotBar I Y (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 _
  simp [quotBar]

/-- The closed set `C_Y` of Lemma 2.3 (the open and closed part of `V_Y`), as an image. -/
def setCY (I : Ideal RR) (e : RR) (Y : AddSubgroup M) : Set (PrimeSpectrum A) :=
  comap (Ideal.Quotient.mk (coeffIdeal I Y)) '' imageSet (quotBar I Y e)

/-- **Lemma 2.1 (1) in the form used by Lemma 2.3**: `C_Y` is closed. -/
theorem isClosed_setCY {I : Ideal RR} {e : RR} (he : e * e - e ∈ I) (Y : AddSubgroup M) :
    IsClosed (setCY I e Y) := by
  have hid : IsIdempotentElem (quotBar I Y e) := by
    have := quotBar_eq_zero (Y := Y) he
    rw [map_sub, map_mul, sub_eq_zero] at this
    exact this
  exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).isClosedMap _ (isClosed_image_of_idem hid)

lemma setCY_subset (I : Ideal RR) (e : RR) (Y : AddSubgroup M) : setCY I e Y ⊆ badImage I e := by
  rintro _ ⟨_, ⟨p', hp', rfl⟩, rfl⟩
  refine ⟨comap (quotBar I Y) p', fun x hx => ?_, hp', ?_⟩
  · change quotBar I Y x ∈ p'.asIdeal
    rw [quotBar_eq_zero hx]
    exact Ideal.zero_mem _
  · ext r
    change quotBar I Y (algebraMap A RR r) ∈ p'.asIdeal ↔ _
    rw [quotBar_algebraMap]
    rfl

/-- `u ∈ C'` lies in `C_Y`, for `Y` the kernel of the point: the set of Lemma 2.3 is a union of the
`C_Y`. -/
lemma badImage_subset {I : Ideal RR} {e : RR} (hI : ∀ x ∈ I, ∀ n, powMap A n x ∈ I)
    {q : PrimeSpectrum A} (hq : q ∈ badImage I e) :
    ∃ Y : AddSubgroup M, q ∈ setCY I e Y := by
  obtain ⟨p, hIp, hep, rfl⟩ := hq
  have := p.isPrime
  let φ : AddMonoidAlgebra A M →+* AddMonoidAlgebra A M ⧸ p.asIdeal := Ideal.Quotient.mk _
  let Y := kerSub φ
  have hφ : ∀ x ∈ I, φ x = 0 := fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hIp hx)
  refine ⟨Y, ?_⟩
  have hc : coeffIdeal I Y ≤ RingHom.ker (φ.comp (algebraMap A RR)) := by
    rw [coeffIdeal, Ideal.span_le]
    rintro _ ⟨x, hx, c, rfl⟩
    exact map_coeff_eq_zero φ hI hφ hx c
  let ϕ : AddMonoidAlgebra (A ⧸ coeffIdeal I Y) (M ⧸ Y) →+* AddMonoidAlgebra A M ⧸ p.asIdeal :=
    AddMonoidAlgebra.liftNCRingHom (Ideal.Quotient.lift _ (φ.comp (algebraMap A RR))
      (fun r hr => RingHom.mem_ker.mp (hc hr))) (charQuot φ) (fun _ _ => mul_comm _ _)
  have hϕs : ∀ (c : M ⧸ Y) (r : A ⧸ coeffIdeal I Y), ϕ (AddMonoidAlgebra.single c r) =
      Ideal.Quotient.lift _ (φ.comp (algebraMap A RR)) (fun r hr => RingHom.mem_ker.mp (hc hr)) r *
        charQuot φ (Multiplicative.ofAdd c) := by
    intro c r
    simp [ϕ, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]
  have hϕ : ϕ.comp (quotBar I Y) = φ := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · have e2 : quotBar I Y (AddMonoidAlgebra.single 0 r) =
          AddMonoidAlgebra.single (0 : M ⧸ Y) (Ideal.Quotient.mk _ r) := by simp [quotBar]
      change ϕ (quotBar I Y (AddMonoidAlgebra.single 0 r)) = _
      rw [e2, hϕs, Ideal.Quotient.lift_mk]
      have : charQuot φ (Multiplicative.ofAdd (0 : M ⧸ Y)) = 1 := map_one _
      rw [this, mul_one]
      rfl
    · have e2 : quotBar I Y (AddMonoidAlgebra.single m 1) =
          AddMonoidAlgebra.single (m : M ⧸ Y) 1 := by simp [quotBar]
      change ϕ (quotBar I Y (AddMonoidAlgebra.single m 1)) = _
      rw [e2, hϕs, map_one, one_mul]
      exact charQuot_mk φ m
  have hker : (RingHom.ker ϕ).IsPrime := RingHom.ker_isPrime ϕ
  let p' : PrimeSpectrum (AddMonoidAlgebra (A ⧸ coeffIdeal I Y) (M ⧸ Y)) := ⟨RingHom.ker ϕ, hker⟩
  refine ⟨comap (algebraMap _ _) p', ⟨p', ?_, rfl⟩, ?_⟩
  · intro h
    have h' : ϕ (quotBar I Y e) = 0 := h
    have h2 : φ e = 0 := by rw [← hϕ]; exact h'
    exact hep (Ideal.Quotient.eq_zero_iff_mem.mp h2)
  · ext r
    change ϕ (algebraMap _ _ (Ideal.Quotient.mk _ r)) = 0 ↔ algebraMap A RR r ∈ p.asIdeal
    rw [← quotBar_algebraMap]
    change (ϕ.comp (quotBar I Y)) _ = 0 ↔ _
    rw [hϕ]
    exact Ideal.Quotient.eq_zero_iff_mem

/-- **Lemma 2.3, closedness.** For `A` noetherian and `M` finitely generated, with `I` stable under
the powers and `e` idempotent modulo `I`, the image of `V(I) ∩ D(e)` in `Spec A` is closed.

The note gets this from `⋃_Y C_Y`, with the set of `Y` finite by Lemma 2.2. Here: the image is
constructible by Chevalley, and stable under specialization because it is a union of closed sets. -/
theorem isClosed_badImage [IsNoetherianRing A] [AddMonoid.FG M] {I : Ideal RR} {e : RR}
    (he : e * e - e ∈ I) (hI : ∀ x ∈ I, ∀ n, powMap A n x ∈ I) : IsClosed (badImage I e) := by
  have hft : Algebra.FiniteType A RR := inferInstance
  have hnoeth : IsNoetherianRing RR := Algebra.FiniteType.isNoetherianRing A RR
  have hfp : Algebra.FinitePresentation A RR := Algebra.FinitePresentation.of_finiteType.mp hft
  have hretro : ∀ s : Set (PrimeSpectrum RR), IsRetrocompact s := fun s U _ _ =>
    TopologicalSpace.NoetherianSpace.isCompact _
  have hcl : IsConstructible (zeroLocus (I : Set RR)) := by
    have h := ((hretro (zeroLocus (I : Set RR))ᶜ).isConstructible
      (isClosed_zeroLocus _).isOpen_compl).compl
    rwa [compl_compl] at h
  have hs : IsConstructible (zeroLocus (I : Set RR) ∩ (basicOpen e : Set (PrimeSpectrum RR))) :=
    hcl.inter ((hretro _).isConstructible (basicOpen e).isOpen)
  have himg : badImage I e = comap (algebraMap A RR) '' (zeroLocus (I : Set RR) ∩ (basicOpen e : Set (PrimeSpectrum RR))) := by
    ext q
    constructor
    · rintro ⟨p, h1, h2, rfl⟩
      exact ⟨p, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
      exact ⟨p, h1, h2, rfl⟩
  refine isClosed_of_stableUnderSpecialization_of_isConstructible ?_ ?_
  · intro q q' hqq hq
    obtain ⟨Y, hY⟩ := badImage_subset hI hq
    exact setCY_subset I e Y ((isClosed_setCY he Y).stableUnderSpecialization hqq hY)
  · rw [himg]
    exact isConstructible_comap_image (RingHom.finitePresentation_algebraMap.mpr hfp) hs

/-- Homogeneous functions separate a point from a stable closed set (graded ideal of Lemma 2.3).
`ρ` is the coaction, `ρ a = ∑ a_m χ_m`, and the output `(ρ a).coeff m` is a coefficient. Stability is
meant set-theoretically, so one passes to a power of the first function: the reduced ideal of a stable
closed set need not be graded when `D(M)` is not reduced. -/
theorem exists_coeff_notMem (ρ : A →+* RR) (haug : ∀ a, (ρ a).coeff.sum (fun _ r => r) = a)
    {C : Set (PrimeSpectrum A)} (hC : IsClosed C)
    (hst : ∀ w : PrimeSpectrum RR, comap (algebraMap A RR) w ∈ C → comap ρ w ∈ C)
    {q₀ : PrimeSpectrum A} (hq₀ : q₀ ∉ C) :
    ∃ (a : A) (m : M), (ρ a).coeff m ∉ q₀.asIdeal ∧ ∀ q ∈ C, (ρ a).coeff m ∈ q.asIdeal := by
  classical
  obtain ⟨Z, rfl⟩ := (isClosed_iff_zeroLocus _).mp hC
  obtain ⟨a₀, ha₀Z, ha₀⟩ : ∃ a ∈ Z, a ∉ q₀.asIdeal := by
    by_contra! h
    exact hq₀ h
  let J : Ideal A := Ideal.span Z
  have hrad : ρ a₀ ∈ (J.map (algebraMap A RR)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hP, hPp⟩
    let w : PrimeSpectrum RR := ⟨P, hPp⟩
    have hw : comap (algebraMap A RR) w ∈ zeroLocus Z := by
      intro z hz
      exact hP (Ideal.mem_map_of_mem _ (Ideal.subset_span hz))
    exact hst w hw ha₀Z
  obtain ⟨N, hN⟩ := hrad
  rw [← map_pow] at hN
  have hcoef := mem_of_mem_map hN
  set a := a₀ ^ N with ha
  have hanot : a ∉ q₀.asIdeal := fun h => ha₀ (q₀.isPrime.mem_of_pow_mem _ h)
  obtain ⟨m, -, hm⟩ : ∃ m ∈ (ρ a).coeff.support, (ρ a).coeff m ∉ q₀.asIdeal := by
    by_contra! h
    apply hanot
    rw [← haug a, Finsupp.sum]
    exact Ideal.sum_mem _ h
  refine ⟨a, m, hm, fun q hq => ?_⟩
  have : J ≤ q.asIdeal := Ideal.span_le.mpr hq
  exact this (hcoef m)

end Main

--MAIN
end

end AlgMag.StronglyFPR
