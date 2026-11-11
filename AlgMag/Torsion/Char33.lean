/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Torsion.Step33
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Data.Nat.Prime.Int

/-!
# The character `x_j` of Prop 3.3

For `Z ⊆ M` whose torsion in `M/Z` is killed by `p^b`, and `z ∉ Z` with `p z ∈ Z`, there is
`x : M →+ ℝ` with `p^b x ∈ M^∨` and `(Z + ℤ z) ∩ M_x = Z`.
-/

namespace AlgMag.Torsion

open Set RD

variable {M : Type*} [AddCommGroup M]

namespace RD

/-- The saturation `Z₀ = {m | ∃ n ≠ 0, n m ∈ Z}`. -/
def sat (Z : AddSubgroup M) : AddSubgroup M where
  carrier := {m | ∃ n : ℤ, n ≠ 0 ∧ n • m ∈ Z}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro a b ⟨n, hn, ha⟩ ⟨k, hk, hb⟩
    refine ⟨n * k, mul_ne_zero hn hk, ?_⟩
    have h1 : (n * k) • (a + b) = k • (n • a) + n • (k • b) := by
      rw [smul_add, mul_comm n k, mul_smul, mul_smul, smul_comm k n b]
    rw [h1]; exact Z.add_mem (Z.zsmul_mem ha _) (Z.zsmul_mem hb _)
  neg_mem' := by
    rintro a ⟨n, hn, ha⟩
    exact ⟨n, hn, by rw [smul_neg]; exact Z.neg_mem ha⟩

lemma sat_sat (Z : AddSubgroup M) (m : M) (n : ℤ) (hn : n ≠ 0) (h : n • m ∈ sat Z) :
    m ∈ sat Z := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k * n, mul_ne_zero hk hn, by rw [mul_smul]; exact h⟩

lemma le_sat (Z : AddSubgroup M) : Z ≤ sat Z := fun m hm => ⟨1, one_ne_zero, by simpa using hm⟩

variable [Module.Free ℤ M] [Module.Finite ℤ M]

/-- A `ℤ`-linear retraction of `M` onto the saturation. -/
lemma exists_retraction (Z : AddSubgroup M) :
    ∃ r : M →+ M, (∀ m, r m ∈ sat Z) ∧ ∀ m ∈ sat Z, r m = m := by
  haveI : NoZeroSMulDivisors ℤ (M ⧸ sat Z) := by
    refine ⟨fun {n q} h => ?_⟩
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      by_cases hn : n = 0
      · exact Or.inl hn
      · right
        have : n • m ∈ sat Z := by
          rw [← QuotientAddGroup.eq_zero_iff]
          exact h
        exact (QuotientAddGroup.eq_zero_iff m).2 (sat_sat Z m n hn this)
  haveI : Module.Finite ℤ (M ⧸ sat Z) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' (sat Z)).toIntLinearMap
      QuotientAddGroup.mk_surjective
  haveI : Module.Free ℤ (M ⧸ sat Z) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (QuotientAddGroup.mk' (sat Z)).toIntLinearMap (LinearMap.id) QuotientAddGroup.mk_surjective
  have hs' : ∀ q, (QuotientAddGroup.mk' (sat Z)) (s q) = q := fun q =>
    LinearMap.congr_fun hs q
  refine ⟨AddMonoidHom.id M - s.toAddMonoidHom.comp (QuotientAddGroup.mk' (sat Z)), ?_, ?_⟩
  · intro m
    have e : (QuotientAddGroup.mk' (sat Z)) (m - s ((QuotientAddGroup.mk' (sat Z)) m)) = 0 := by
      rw [map_sub, hs', sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).1 e
  · intro m hm
    have h0 : (QuotientAddGroup.mk' (sat Z)) m = 0 := (QuotientAddGroup.eq_zero_iff m).2 hm
    show m - s ((QuotientAddGroup.mk' (sat Z)) m) = m
    rw [h0, map_zero, sub_zero]

/-- The character `x`. -/
theorem exists_char {p : ℕ} (hp : p.Prime) {b : ℕ} (Z : AddSubgroup M)
    (hZ : ∀ (m : M) (n : ℤ), n ≠ 0 → n • m ∈ Z → ((p ^ b : ℕ) : ℤ) • m ∈ Z) {z : M}
    (hz : z ∉ Z) (hpz : (p : ℤ) • z ∈ Z) :
    ∃ x : M →+ ℝ, ((p ^ b : ℕ) : ℤ) • x ∈ (intPts : AddSubgroup (M →+ ℝ)) ∧
      ∀ y ∈ Z ⊔ AddSubgroup.zmultiples z, (y ∈ Z ↔ y ∈ Mx x) := by
  obtain ⟨r, hr1, hr2⟩ := exists_retraction Z
  have hne : (QuotientAddGroup.mk z : M ⧸ Z) ≠ 0 := fun h => hz ((QuotientAddGroup.eq_zero_iff z).1 h)
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero (A := M ⧸ Z) hne
  let χ : M →+ AddCircle (1 : ℚ) := c.comp ((QuotientAddGroup.mk' Z).comp r)
  have hχ : ∀ m, χ m = c (QuotientAddGroup.mk (r m)) := fun m => rfl
  have F1 : ∀ ζ ∈ Z, χ ζ = 0 := by
    intro ζ hζ
    rw [hχ, hr2 ζ (le_sat Z hζ)]
    have : (QuotientAddGroup.mk ζ : M ⧸ Z) = 0 := (QuotientAddGroup.eq_zero_iff ζ).2 hζ
    rw [this, map_zero]
  have hzs : z ∈ sat Z := ⟨p, by exact_mod_cast hp.ne_zero, hpz⟩
  have F4 : χ z = c (QuotientAddGroup.mk z) := by rw [hχ, hr2 z hzs]
  have F5 : ((p : ℤ)) • χ z = 0 := by
    rw [F4, ← map_zsmul]
    have : (p : ℤ) • (QuotientAddGroup.mk z : M ⧸ Z) = 0 := by
      rw [← QuotientAddGroup.mk_zsmul]; exact (QuotientAddGroup.eq_zero_iff _).2 hpz
    rw [this, map_zero]
  have F6 : χ z ≠ 0 := by rw [F4]; exact hc
  have F3 : ∀ m, ((p ^ b : ℕ) : ℤ) • χ m = 0 := by
    intro m
    rw [hχ, ← map_zsmul]
    obtain ⟨n, hn, hn2⟩ := hr1 m
    have h1 := hZ (r m) n hn hn2
    have : ((p ^ b : ℕ) : ℤ) • (QuotientAddGroup.mk (r m) : M ⧸ Z) = 0 := by
      rw [← QuotientAddGroup.mk_zsmul]; exact (QuotientAddGroup.eq_zero_iff _).2 h1
    rw [this, map_zero]
  -- lift `χ` to `ℚ`
  let bs := Module.Free.chooseBasis ℤ M
  have hsurj : ∀ t : AddCircle (1 : ℚ), ∃ a : ℚ, (a : AddCircle (1 : ℚ)) = t :=
    fun t => QuotientAddGroup.mk_surjective t
  choose f hf using fun i => hsurj (χ (bs i))
  let q : M →ₗ[ℤ] ℚ := bs.constr ℤ f
  have hq : ∀ m, ((q m : ℚ) : AddCircle (1 : ℚ)) = χ m := by
    have : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap ∘ₗ q =
        χ.toIntLinearMap := by
      refine bs.ext fun i => ?_
      simp [q, bs.constr_basis, hf]
    intro m
    exact LinearMap.congr_fun this m
  let x : M →+ ℝ := (Rat.castHom ℝ).toAddMonoidHom.comp q.toAddMonoidHom
  have hx : ∀ m, x m = ((q m : ℚ) : ℝ) := fun m => rfl
  have hint : ∀ m, (∃ k : ℤ, x m = k) ↔ χ m = 0 := by
    intro m
    constructor
    · rintro ⟨k, hk⟩
      rw [hx] at hk
      have : q m = k := by exact_mod_cast hk
      rw [← hq, this]
      exact (AddCircle.coe_eq_zero_iff (p := (1 : ℚ))).2 ⟨k, by simp⟩
    · intro h
      rw [← hq] at h
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℚ))).1 h
      exact ⟨n, by rw [hx, ← hn]; simp⟩
  have hirr : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.1 hp).irreducible
  refine ⟨x, ?_, ?_⟩
  · intro m
    have h0 : χ (((p ^ b : ℕ) : ℤ) • m) = 0 := by rw [map_zsmul]; exact F3 m
    obtain ⟨k, hk⟩ := (hint _).2 h0
    refine ⟨k, ?_⟩
    rw [← hk, map_zsmul]
    simp
  · intro y hy
    obtain ⟨a, ha, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hy
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
    have hya : χ (a + k • z) = k • χ z := by
      rw [map_add, F1 a ha, zero_add, map_zsmul]
    rw [Mx]
    show _ ↔ (∃ k' : ℤ, x (a + k • z) = k')
    rw [hint, hya]
    constructor
    · intro h
      have hk : k • χ z = 0 := by
        have : (a + k • z) ∈ Z → k • z ∈ Z := fun h' => by simpa using Z.sub_mem h' ha
        have h2 : k • z ∈ Z := this h
        rw [← map_zsmul]; exact F1 _ h2
      exact hk
    · intro h
      have hdvd : (p : ℤ) ∣ k := by
        by_contra hndv
        have hcop : IsCoprime (p : ℤ) k := (Irreducible.coprime_iff_not_dvd hirr).2 hndv
        obtain ⟨u, v, huv⟩ := hcop
        apply F6
        have : χ z = (u * p + v * k) • χ z := by rw [huv, one_smul]
        rw [this, add_smul, mul_smul, mul_smul, F5, h]
        simp
      obtain ⟨k', rfl⟩ := hdvd
      have : ((p : ℤ) * k') • z = k' • ((p : ℤ) • z) := by rw [mul_comm, mul_smul]
      rw [this]
      exact Z.add_mem ha (Z.zsmul_mem hpz _)

end RD

end AlgMag.Torsion
