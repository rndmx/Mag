/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularCentralizer
import AlgMag.Reductive.PushCocharacter

/-!
# Regular torus points exist

* `exists_pow_ne_one`: in an infinite field, some `c ≠ 0` has `c ^ n ≠ 1` for `1 ≤ n ≤ M`.
* `regularPoints_nonempty`: given a cocharacter `ψ` generic on the roots in `N` (finitely many),
  `τ = ψ(c)` is regular for `c` of order `> max |⟨α, ψ⟩|`.
-/

suppress_compilation

open Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u

/-- In an infinite field there is `c ≠ 0` with `c ^ (n + 1) ≠ 1` for all `n < M`. -/
lemma exists_pow_ne_one {k : Type*} [Field k] [Infinite k] (M : ℕ) :
    ∃ c : k, c ≠ 0 ∧ ∀ n < M, c ^ (n + 1) ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (insert (0 : k) ((Finset.range M).biUnion fun n => (Polynomial.nthRoots (n + 1) (1 : k)).toFinset))
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range, Multiset.mem_toFinset,
    not_or, not_exists, not_and] at hc
  refine ⟨c, hc.1, fun n hn h => hc.2 n hn ?_⟩
  rw [Polynomial.mem_nthRoots (Nat.succ_pos n)]
  exact h

lemma zpow_ne_one_of_natAbs {k : Type*} [Field k] {c : k} (hc0 : c ≠ 0) {M : ℕ}
    (hc : ∀ n < M, c ^ (n + 1) ≠ 1) {m : ℤ} (hm : m ≠ 0) (hmM : m.natAbs ≤ M) :
    (Units.mk0 c hc0) ^ m ≠ 1 := by
  have hpos : 0 < m.natAbs := Int.natAbs_pos.2 hm
  have key : c ^ m.natAbs ≠ 1 := by
    have := hc (m.natAbs - 1) (by omega)
    rwa [Nat.sub_add_cancel hpos] at this
  intro h
  apply key
  have h' : ((Units.mk0 c hc0) ^ m.natAbs : kˣ) = 1 := by
    rcases Int.natAbs_eq m with he | he
    · rw [he] at h; exact_mod_cast h
    · rw [he, zpow_neg, inv_eq_one] at h; exact_mod_cast h
  have := congrArg Units.val h'
  simpa using this

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **Regular torus points exist** (over an infinite field), given a cocharacter `ψ` generic
on the finitely many roots in `N`. -/
theorem regularPoints_nonempty [Infinite k] (N : Magnet (Additive X)) (hfin : (roots π).Finite)
    (ψ : X →* Multiplicative ℤ) (hψ : ∀ α ∈ roots π, α ∈ N → pairingHom ψ α ≠ 0) :
    (regularPoints π N).Nonempty := by
  classical
  set M := hfin.toFinset.sup fun α => (pairingHom ψ α).natAbs
  obtain ⟨c, hc0, hc⟩ := exists_pow_ne_one (k := k) M
  let χ : X →* k := (Units.coeHom k).comp
    ((zpowersHom kˣ (Units.mk0 c hc0)).comp ψ)
  let τ : MonoidAlgebra k X →ₐ[k] k := MonoidAlgebra.lift k k X χ
  refine ⟨toConv (τ.comp π.toAlgHom), τ, rfl, fun α hα hN => ?_⟩
  have hτ : τ (MonoidAlgebra.single (Additive.toMul α) 1) =
      ((Units.mk0 c hc0 ^ pairingHom ψ α : kˣ) : k) := by
    simp [τ, χ, MonoidAlgebra.lift_single, pairingHom]
  rw [hτ]
  intro h
  refine zpow_ne_one_of_natAbs hc0 hc (hψ α hα hN) ?_ (Units.val_eq_one.1 h)
  exact Finset.le_sup (f := fun α => (pairingHom ψ α).natAbs) (hfin.mem_toFinset.2 hα)

end AlgMag.Reductive
