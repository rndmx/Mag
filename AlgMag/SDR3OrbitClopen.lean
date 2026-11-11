/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3SchemeQuotient
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Lemma D, a section of an unramified map is clopen

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`. Let `π : T → K` be a
`K`-algebra map with `π d` a unit and `T_d` unramified and of finite presentation over `K`. Then an idempotent `ε` of `T`
has `π ε = 1` and `J ε = 0` for `J = ker π`: thus `ε T = K`. `T` itself need not be of finite type. Idempotents of a
torsion-free grading have degree `0` (`SDR3Orbit_idem_deg0`).
-/

universe u

namespace AlgMag.SD

open AlgMag.SQ

section Unram

variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]

/-- An unramified `K`-algebra with a section has idempotent augmentation ideal. -/
theorem SDR3Orbit_ker_sq [Algebra.FormallyUnramified K A] (π : A →ₐ[K] K) {a : A} (ha : π a = 0) :
    a ∈ RingHom.ker π.toRingHom ^ 2 := by
  let J : Ideal A := RingHom.ker π.toRingHom
  let I : Ideal (A ⧸ J ^ 2) := J.map (Ideal.Quotient.mk (J ^ 2))
  have hI : I ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  let f₁ : A →ₐ[K] A ⧸ J ^ 2 := Ideal.Quotient.mkₐ K (J ^ 2)
  let f₂ : A →ₐ[K] A ⧸ J ^ 2 := (Algebra.ofId K (A ⧸ J ^ 2)).comp π
  have hJ : ∀ x : A, x - algebraMap K A (π x) ∈ J := fun x => by
    change π (x - algebraMap K A (π x)) = 0
    rw [map_sub, AlgHom.commutes]
    simp
  have heq : (Ideal.Quotient.mkₐ K I).comp f₁ = (Ideal.Quotient.mkₐ K I).comp f₂ := by
    ext x
    change Ideal.Quotient.mk I (f₁ x) = Ideal.Quotient.mk I (f₂ x)
    rw [Ideal.Quotient.eq]
    have : f₁ x - f₂ x = Ideal.Quotient.mk (J ^ 2) (x - algebraMap K A (π x)) := by
      rw [map_sub]
      rfl
    rw [this]
    exact Ideal.mem_map_of_mem _ (hJ x)
  have h := Algebra.FormallyUnramified.comp_injective I hI heq
  have h2 : f₁ a = f₂ a := by rw [h]
  have h3 : f₁ a = 0 := by
    rw [h2]
    change algebraMap K (A ⧸ J ^ 2) (π a) = 0
    rw [ha, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h3

end Unram

variable {K T : Type u} [CommRing K] [CommRing T] [Algebra K T]

/-- **G3.** `V(ker π)` is clopen, algebraically: `ε T = K`. -/
theorem SDR3Orbit_clopen (π : T →ₐ[K] K) (d : T) (hd : IsUnit (π d))
    [Algebra.FormallyUnramified K (Localization.Away d)] [Algebra.FinitePresentation K (Localization.Away d)] :
    ∃ ε : T, IsIdempotentElem ε ∧ π ε = 1 ∧ ∀ j, π j = 0 → j * ε = 0 := by
  classical
  let ι : T →+* Localization.Away d := algebraMap T (Localization.Away d)
  have huι : IsUnit (π.toRingHom d) := hd
  let πd₀ : Localization.Away d →+* K := IsLocalization.Away.lift d huι
  have hπd₀ : ∀ t, πd₀ (ι t) = π t := fun t => IsLocalization.Away.lift_eq d huι t
  let πd : Localization.Away d →ₐ[K] K :=
    { πd₀ with
      commutes' := fun r => by
        have e : algebraMap K (Localization.Away d) r = ι (algebraMap K T r) := IsScalarTower.algebraMap_apply K T (Localization.Away d) r
        change πd₀ _ = _
        rw [e, hπd₀, AlgHom.commutes]
        }
  have hπd : ∀ t, πd (ι t) = π t := hπd₀
  have hsurj : Function.Surjective πd := fun k => ⟨algebraMap K (Localization.Away d) k, πd.commutes k⟩
  have hfg : (RingHom.ker πd.toRingHom).FG := Algebra.FinitePresentation.ker_fG_of_surjective πd hsurj
  have hidem : IsIdempotentElem (RingHom.ker πd.toRingHom) := by
    change _ * _ = _
    refine le_antisymm Ideal.mul_le_left fun a ha => ?_
    have := SDR3Orbit_ker_sq πd (a := a) ha
    rwa [pow_two] at this
  obtain ⟨f, hf, hJf⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).1 hidem
  have hfJ : πd f = 0 := by
    have : f ∈ RingHom.ker πd.toRingHom := by
      rw [hJf]
      exact Ideal.mem_span_singleton_self f
    exact this
  have hmemJ : ∀ y, πd y = 0 → y * (1 - f) = 0 := by
    intro y hy
    have : y ∈ RingHom.ker πd.toRingHom := hy
    rw [hJf] at this
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 this
    rw [mul_assoc, mul_sub, mul_one, hf.eq, sub_self, mul_zero]
  -- `g = 1 - f = a / d ^ n`
  obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj (Submonoid.powers d) (1 - f)
  obtain ⟨n, hn⟩ := m.2
  change d ^ n = _ at hn
  have ham' : (1 - f) * ι d ^ n = ι a := by
    rw [← map_pow, hn]
    exact ham
  have hπa : π a = π d ^ n := by
    rw [← hπd, ← ham', map_mul, map_sub, map_one, hfJ, sub_zero, one_mul, map_pow, hπd]
  have hua : IsUnit (π a) := by rw [hπa]; exact hd.pow n
  have hj : ∀ j, π j = 0 → ∃ k : ℕ, d ^ k * (j * a) = 0 := by
    intro j hj
    have h0 : ι (j * a) = 0 := by
      rw [map_mul, ← ham', ← mul_assoc, hmemJ _ (by rw [hπd, hj]), zero_mul]
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers d) (Localization.Away d) _).1 h0
    obtain ⟨k, hk⟩ := c.2
    change d ^ k = _ at hk
    exact ⟨k, by rw [hk]; exact hc⟩
  have hprime : ∀ (p : Ideal T) [p.IsPrime], (∀ j, π j = 0 → j ∈ p) ↔ a * d ∉ p := by
    intro p _
    have hu : ∀ t, IsUnit (π t) → (∀ j, π j = 0 → j ∈ p) → t ∉ p := by
      intro t ht hJ htp
      obtain ⟨v, hv⟩ := ht.exists_right_inv
      have h1 : t * algebraMap K T v - 1 ∈ p := hJ _ (by simp [hv])
      have h2 : t * algebraMap K T v ∈ p := p.mul_mem_right _ htp
      exact (Ideal.ne_top_iff_one p).1 (Ideal.IsPrime.ne_top ‹_›) (by simpa using p.sub_mem h2 h1)
    constructor
    · intro hJ hm
      obtain h | h := Ideal.IsPrime.mem_or_mem ‹_› hm
      · exact hu a hua hJ h
      · exact hu d hd hJ h
    · intro hm j hj0
      obtain ⟨k, hk⟩ := hj j hj0
      have h0 : d ^ k * (j * a) ∈ p := by rw [hk]; exact p.zero_mem
      have had : a ∉ p := fun h => hm (p.mul_mem_right _ h)
      have hdd : d ∉ p := fun h => hm (p.mul_mem_left _ h)
      obtain h | h := Ideal.IsPrime.mem_or_mem ‹_› h0
      · exact absurd (Ideal.IsPrime.mem_of_pow_mem ‹_› _ h) hdd
      · exact (Ideal.IsPrime.mem_or_mem ‹_› h).resolve_right had
  -- clopen
  let Z : Set (PrimeSpectrum T) := PrimeSpectrum.zeroLocus (RingHom.ker π.toRingHom : Set T)
  have hZ : Z = PrimeSpectrum.basicOpen (a * d) := by
    ext p
    change (RingHom.ker π.toRingHom : Set T) ⊆ p.asIdeal ↔ a * d ∉ p.asIdeal
    rw [← hprime p.asIdeal]
    exact Iff.rfl
  have hcl : IsClopen Z :=
    ⟨PrimeSpectrum.isClosed_zeroLocus _, by rw [hZ]; exact (PrimeSpectrum.basicOpen _).isOpen⟩
  obtain ⟨ε, ε', hmul, hadd, hε⟩ := PrimeSpectrum.isClopen_iff_mul_add.1 hcl
  have hidemε : IsIdempotentElem ε := by
    change ε * ε = ε
    have : ε' = 1 - ε := eq_sub_of_add_eq' hadd
    rw [this, mul_sub, mul_one, sub_eq_zero] at hmul
    exact hmul.symm
  have hmemε : ∀ (p : Ideal T) [p.IsPrime], ε ∉ p ↔ ∀ j, π j = 0 → j ∈ p := by
    intro p hp
    have e : (⟨p, hp⟩ : PrimeSpectrum T) ∈ Z ↔ (⟨p, hp⟩ : PrimeSpectrum T) ∈ PrimeSpectrum.basicOpen ε := by rw [hε]; rfl
    exact e.symm.trans Iff.rfl
  -- `π ε = 1`
  have hπε : π ε = 1 := by
    have hid : IsIdempotentElem (π ε) := by change _ * _ = _; rw [← map_mul, hidemε.eq]
    have hunit : IsUnit (π ε) := by
      by_contra hn
      obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
      have hp : (m.comap π.toRingHom).IsPrime := Ideal.comap_isPrime _ _
      have h1 : ε ∈ m.comap π.toRingHom := hmem
      refine (hmemε (m.comap π.toRingHom)).2 (fun j hj => ?_) h1
      change π j ∈ m
      rw [hj]
      exact m.zero_mem
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    calc π ε = π ε * (π ε * v) := by rw [hv, mul_one]
      _ = π ε * π ε * v := by ring
      _ = π ε * v := by rw [hid.eq]
      _ = 1 := hv
  -- `ε ∈ (d)` up to radical, hence `d` is a unit on the corner
  have hdvd : ∃ w, ε = d * w := by
    by_contra hcon
    have hmem : ε ∉ Ideal.span {d} := fun h => by
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 h
      exact hcon ⟨w, by rw [← hw, mul_comm]⟩
    have hrad : ε ∉ (Ideal.span {d}).radical := fun h => by
      obtain ⟨k, hk⟩ := h
      apply hmem
      rw [← hidemε.pow_succ_eq k, pow_succ]
      exact Ideal.mul_mem_right _ _ hk
    rw [Ideal.radical_eq_sInf] at hrad
    simp only [Ideal.mem_sInf, Set.mem_setOf_eq, not_forall] at hrad
    obtain ⟨p, ⟨hdp, hp⟩, hεp⟩ := hrad
    have hJ := (hmemε p).1 hεp
    obtain ⟨v, hv⟩ := hd.exists_right_inv
    have h1 : d * algebraMap K T v - 1 ∈ p := hJ _ (by simp [hv])
    have h2 : d * algebraMap K T v ∈ p := p.mul_mem_right _ (hdp (Ideal.mem_span_singleton_self d))
    exact (Ideal.ne_top_iff_one p).1 hp.ne_top (by simpa using p.sub_mem h2 h1)
  obtain ⟨w, hw⟩ := hdvd
  -- the image of `ε` kills `f`
  have hef : ι ε * f = 0 := by
    have hid : IsIdempotentElem (ι ε * f) := by
      change _ * _ = _
      calc ι ε * f * (ι ε * f) = ι (ε * ε) * (f * f) := by rw [map_mul]; ring
        _ = ι ε * f := by rw [hidemε.eq, hf.eq]
    have hnil : ι ε * f ∈ nilradical (Localization.Away d) := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      intro P hP
      have hP' : P.IsPrime := hP
      by_cases hmemP : ι ε ∈ P
      · exact P.mul_mem_right _ hmemP
      · have hJ := (hmemε (P.comap ι)).1 hmemP
        -- `f = x / d ^ k` with `x ∈ ker π`
        obtain ⟨⟨x, m'⟩, hx⟩ := IsLocalization.surj (Submonoid.powers d) f
        obtain ⟨k, hk⟩ := m'.2
        change d ^ k = _ at hk
        have hx' : f * ι d ^ k = ι x := by rw [← map_pow, hk]; exact hx
        have hπx : π x = 0 := by rw [← hπd, ← hx', map_mul, hfJ, zero_mul]
        have hxP : ι x ∈ P := hJ x hπx
        rw [← hx'] at hxP
        obtain h | h := hP'.mem_or_mem hxP
        · exact P.mul_mem_left _ h
        · exact absurd (hP'.mem_of_pow_mem _ h) (fun hdP =>
            hmemP (by rw [hw, map_mul]; exact P.mul_mem_right _ hdP))
    obtain ⟨k, hk⟩ := hnil
    rw [← hid.pow_succ_eq k, pow_succ, hk, zero_mul]
  refine ⟨ε, hidemε, hπε, fun j hj0 => ?_⟩
  have h0 : ι (j * ε) = 0 := by
    have hjJ : ι j ∈ RingHom.ker πd.toRingHom := by
      change πd (ι j) = 0
      rw [hπd, hj0]
    rw [hJf] at hjJ
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hjJ
    rw [map_mul, ← hz, mul_assoc, mul_comm f, hef, mul_zero]
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers d) (Localization.Away d) _).1 h0
  obtain ⟨k, hk⟩ := c.2
  change d ^ k = _ at hk
  have hk0 : d ^ k * (j * ε) = 0 := by rw [hk]; exact hc
  have hε1 := hidemε.pow_succ_eq k
  calc j * ε = j * ε ^ (k + 1) := by rw [hε1]
    _ = j * ε * ε ^ k := by rw [pow_succ']; ring
    _ = d ^ k * (j * ε) * w ^ k := by
      have e : ε ^ k = d ^ k * w ^ k := by rw [← mul_pow, ← hw]
      rw [e]; ring
    _ = 0 := by rw [hk0, zero_mul]

/-- An idempotent of a torsion-free grading has degree `0`: two idempotents differing by a nilpotent are equal. -/
theorem SDR3Orbit_idem_deg0 {A Γ : Type u} [CommRing A] [AddCommGroup Γ] [UniqueSums Γ] (c : Coact A Γ) {e : A}
    (he : IsIdempotentElem e) : c.IsHom 0 e := by
  classical
  have hE : IsIdempotentElem (c.σ e) := by
    change _ * _ = _
    rw [← map_mul, he.eq]
  have hprime : ∀ p : Ideal A, p.IsPrime → (∀ d, d ≠ 0 → c.comp d e ∈ p) := by
    intro p hp d hd
    haveI := hp
    let φ := AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk p)
    have hφ : IsIdempotentElem (φ (c.σ e)) := by
      change _ * _ = _
      rw [← map_mul, hE.eq]
    have e1 : (φ (c.σ e)).coeff d = Ideal.Quotient.mk p (c.comp d e) := AddMonoidAlgebra.coeff_mapRingHom ..
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← e1]
    obtain h | h := IsIdempotentElem.iff_eq_zero_or_one.1 hφ
    · rw [h]; rfl
    · rw [h, AddMonoidAlgebra.one_def]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hd.symm]
  have hnil : ∀ d, d ≠ 0 → IsNilpotent (c.comp d e) := by
    intro d hd
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    exact fun p hp => hprime p hp d hd
  let s := (c.σ e).coeff.support
  have hsum : e = c.comp 0 e + ∑ d ∈ s.erase 0, c.comp d e := by
    have h1 : e = ∑ d ∈ insert 0 s, c.comp d e := by
      conv_lhs => rw [← c.sum_eq e, Finsupp.sum]
      refine Finset.sum_subset (Finset.subset_insert _ _) fun d _ hd => ?_
      exact Finsupp.notMem_support_iff.1 hd
    have h2 : insert 0 s = insert 0 (s.erase 0) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_erase]
      tauto
    calc e = ∑ d ∈ insert 0 s, c.comp d e := h1
      _ = _ := by rw [h2, Finset.sum_insert (Finset.notMem_erase 0 s)]
  have hn0 : IsNilpotent (c.comp 0 e - e) := by
    have : c.comp 0 e - e = -∑ d ∈ s.erase 0, c.comp d e := by
      linear_combination -hsum
    rw [this]
    exact (isNilpotent_sum fun d hd => hnil d (Finset.ne_of_mem_erase hd)).neg
  let z : AddMonoidAlgebra A Γ := c.σ e - AddMonoidAlgebra.single 0 e
  have hzc : ∀ d, IsNilpotent (z.coeff d) := by
    intro d
    by_cases hd : d = 0
    · subst hd
      have : z.coeff 0 = c.comp 0 e - e := by simp [z, Coact.comp]
      rw [this]
      exact hn0
    · have : z.coeff d = c.comp d e := by
        simp [z, Coact.comp, Finsupp.single_apply, Ne.symm hd]
      rw [this]
      exact hnil d hd
  have hz : IsNilpotent z := by
    rw [← AddMonoidAlgebra.sum_coeff_single z, Finsupp.sum]
    refine isNilpotent_sum fun d _ => ?_
    obtain ⟨n, hn⟩ := hzc d
    refine ⟨n, ?_⟩
    rw [AddMonoidAlgebra.single_pow, hn, AddMonoidAlgebra.single_zero]
  have hid2 : IsIdempotentElem (AddMonoidAlgebra.single (0 : Γ) e) := by
    change _ * _ = _
    rw [AddMonoidAlgebra.single_mul_single, add_zero, he.eq]
  have hz3 : ∀ k : ℕ, z = z ^ (2 * k + 1) := by
    have h3 : z ^ 3 = z := by
      have ha := hE.eq
      have hb := hid2.eq
      simp only [z]
      linear_combination (c.σ e + 1 - 3 * AddMonoidAlgebra.single 0 e) * ha + (3 * c.σ e - AddMonoidAlgebra.single 0 e - 1) * hb
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, pow_add, h3, ← pow_succ]
      exact ih
  obtain ⟨n, hn⟩ := hz
  have hz0 : z = 0 := by
    rw [hz3 n, show 2 * n + 1 = n + (n + 1) by ring, pow_add, hn, zero_mul]
  exact sub_eq_zero.1 hz0

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Orbit_ker_sq
#print axioms AlgMag.SD.SDR3Orbit_clopen
#print axioms AlgMag.SD.SDR3Orbit_idem_deg0
