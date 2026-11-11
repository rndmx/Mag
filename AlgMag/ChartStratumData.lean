/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumBack

/-!
# The integer `N` and the subgroup `K` (affine stratum lemma, step 1)

Let `n` kill the torsion of `M`. If `n` is invertible somewhere on `X`, take `N = n` and `K = 0`.
Otherwise a field point of `X` has characteristic a prime `q ∣ n`; take `N` the prime-to-`q` part of `n`
and `K = M[q^∞]`. Every field point of `X[1/N]` then has characteristic `q`, so kills `K`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- There is `n > 0` killing the torsion of a finitely generated abelian group. -/
lemma exists_torsion_bound (M : Type u) [AddCommGroup M] [AddGroup.FG M] :
    ∃ n : ℕ, 0 < n ∧ ∀ x : M, IsOfFinAddOrder x → n • x = 0 := by
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let T := AddCommGroup.torsion M
  haveI : Module.Finite ℤ (AddSubgroup.toIntSubmodule T) := inferInstance
  haveI hfg : AddGroup.FG T :=
    Module.Finite.iff_addGroup_fg.mp (inferInstance : Module.Finite ℤ (AddSubgroup.toIntSubmodule T))
  have hT : AddMonoid.IsTorsion T := by
    rintro ⟨x, hx⟩
    obtain ⟨d, hd, hdx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨d, hd, Subtype.ext hdx⟩
  haveI : Finite T := AddCommGroup.finite_of_fg_torsion T hT
  refine ⟨Nat.card T, Nat.card_pos, fun x hx => ?_⟩
  have := card_nsmul_eq_zero' (G := T) (x := ⟨x, hx⟩)
  exact congrArg Subtype.val this

/-- Over the spectrum of a field, an integer is a unit exactly when it is nonzero. -/
lemma isUnit_natCast_spec {k : Type u} [Field k] (N : ℕ) :
    IsUnit (N : Γ(Spec (.of k), ⊤)) ↔ (N : k) ≠ 0 := by
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have h : e (N : Γ(Spec (.of k), ⊤)) = (N : k) := map_natCast e N
  rw [← isUnit_map_iff e, h]
  exact isUnit_iff_ne_zero

/-- A section over the spectrum of a field of characteristic `q`, with a `q`-power power equal to `1`,
is `1`. -/
lemma eq_one_of_pow_spec {k : Type u} [Field k] (q : ℕ) (hq : q.Prime) (h0 : (q : k) = 0) (m : ℕ)
    (v : Γ(Spec (.of k), ⊤)) (hv : v ^ (q ^ m) = 1) : v = 1 := by
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP k q := by
    have := CharP.ringChar_of_prime_eq_zero hq h0
    exact this ▸ ringChar.charP k
  have h1 : (e v) ^ (q ^ m) = 1 := by rw [← map_pow, hv, map_one]
  have h2 : (e v - 1) ^ (q ^ m) = 0 := by rw [sub_pow_char_pow, h1, one_pow, sub_self]
  have h3 : e v = 1 := sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ hq.ne_zero) |>.1 h2)
  exact e.injective (h3.trans (map_one e).symm)

variable {M : Type u} [AddCommGroup M] [Countable M] [AddGroup.FG M]

/-- The `q`-primary part. -/
def primaryPart (M : Type u) [AddCommGroup M] (q : ℕ) : AddSubgroup M where
  carrier := {m | ∃ b : ℕ, q ^ b • m = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [smul_add, pow_add, mul_comm, mul_smul, ha, smul_zero, zero_add, mul_comm, mul_smul, hb,
      smul_zero]
  neg_mem' := by
    rintro x ⟨a, ha⟩
    exact ⟨a, by rw [smul_neg, ha, neg_zero]⟩

/-- **Affine stratum lemma, step 1**: the choice of `N` and `K`. -/
theorem exists_unit_data (hne : Nonempty (Space.points B S hS X)) :
    ∃ (N : ℕ) (K : AddSubgroup M),
      (∃ (T : BigFppfOver B S hS), Nonempty ((SCH).obj T) ∧ Nonempty (X.obj (op T)) ∧
        IsUnit (N : Γ((SCH).obj T, ⊤))) ∧
      (∀ x : M ⧸ K, IsOfFinAddOrder x → N • x = 0) ∧
      (∀ {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
        (_ : X.obj (op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))),
        IsUnit (N : Γ(Spec (.of k), ⊤)) →
        ∀ h : APt (fppfO B S hS) M (op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))), TrivialOn K h) := by
  obtain ⟨n, hn0, hn⟩ := exists_torsion_bound M
  by_cases hcase : ∃ (T : BigFppfOver B S hS), Nonempty ((SCH).obj T) ∧ Nonempty (X.obj (op T)) ∧
      IsUnit (n : Γ((SCH).obj T, ⊤))
  · refine ⟨n, ⊥, hcase, ?_, ?_⟩
    · intro x
      induction x using QuotientAddGroup.induction_on with
      | H z =>
        intro hz
        have hz' : IsOfFinAddOrder z := by
          obtain ⟨d, hd, hdz⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hz
          refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨d, hd, ?_⟩
          have : ((d • z : M) : M ⧸ (⊥ : AddSubgroup M)) = 0 := by
            rw [QuotientAddGroup.mk_nsmul]; exact hdz
          simpa using (QuotientAddGroup.eq_zero_iff _).1 this
        rw [← QuotientAddGroup.mk_nsmul, hn z hz']
        rfl
    · intro k _ hk b _ _ h
      rw [trivialOn_iff]
      intro z hz
      have hz0 : z = 0 := hz
      rw [hz0]
      exact map_one h
  · obtain ⟨z⟩ := hne
    induction z using Quot.ind with
    | mk p =>
    rcases p with ⟨k, hk, b, y⟩
    -- the hypothesis of the case, at a field point
    have hnon : ∀ {k' : Type u} [Field k'] (hk' : B.Contains (Spec (.of k'))) (b' : Spec (.of k') ⟶ S)
        (_ : X.obj (op (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS)))), (n : k') = 0 := by
      intro k' _ hk' b' y'
      by_contra hne0
      have hu : IsUnit (n : Γ(Spec (.of k'), ⊤)) := (isUnit_natCast_spec n).2 hne0
      exact hcase ⟨Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS),
        inferInstanceAs (Nonempty (Spec (.of k'))), ⟨y'⟩, hu⟩
    have hnk : (n : k) = 0 := hnon hk b y
    obtain ⟨q, hqc⟩ := CharP.exists k
    have hq0 : q ≠ 0 := by
      rintro rfl
      haveI := hqc
      haveI : CharZero k := CharP.charP_to_charZero k
      exact hn0.ne' (by exact_mod_cast hnk)
    have hq : q.Prime := (CharP.char_is_prime_or_zero k q).resolve_right hq0
    obtain ⟨a, n', hn'q, hne⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' q hq.ne_one
    have hn'k : (n' : k) ≠ 0 := fun h => hn'q ((CharP.cast_eq_zero_iff k q _).1 h)
    refine ⟨n', primaryPart M q, ⟨Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS),
      inferInstanceAs (Nonempty (Spec (.of k))), ⟨y⟩, (isUnit_natCast_spec n').2 hn'k⟩, ?_, ?_⟩
    · intro x
      induction x using QuotientAddGroup.induction_on with
      | H z =>
        intro hz
        have hz' : IsOfFinAddOrder z := by
          obtain ⟨d, hd, hdz⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hz
          have h1 : ((d • z : M) : M ⧸ primaryPart M q) = 0 := by
            rw [QuotientAddGroup.mk_nsmul]; exact hdz
          obtain ⟨c, hc⟩ := (QuotientAddGroup.eq_zero_iff _).1 h1
          refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q ^ c * d, Nat.mul_pos (pow_pos hq.pos _) hd, ?_⟩
          rw [mul_smul, hc]
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
        refine ⟨a, ?_⟩
        have := hn z hz'
        rw [hne, mul_smul] at this
        exact this
    · intro k' _ hk' b' y' hu h
      have hnk' : (n : k') = 0 := hnon hk' b' y'
      have hn'k' : (n' : k') ≠ 0 := (isUnit_natCast_spec n').1 hu
      have hqk' : (q : k') = 0 := by
        rw [hne] at hnk'
        push_cast at hnk'
        have := (mul_eq_zero.1 hnk').resolve_right hn'k'
        exact IsReduced.eq_zero _ ⟨a, this⟩
      rw [trivialOn_iff]
      rintro z ⟨c, hc⟩
      have hv : (h (Multiplicative.ofAdd z)) ^ (q ^ c) = 1 := by
        rw [← map_pow, ← ofAdd_nsmul, hc]
        exact map_one h
      exact eq_one_of_pow_spec q hq hqk' c _ hv

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.exists_unit_data
