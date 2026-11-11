/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootDatumFromGPairing

/-!
# Rank one: the Weyl element of `Z_G((ker α)°)` is a reflection at `α`

For a root `α`, `L_α := M ∩ ℚα` (`lineMagnet α`) is a group magnet and `G^{L_α}` is the
centralizer of `(ker α)°`. A point `n ∈ G^{L_α}` normalizing `T` with automorphism `σ`
satisfies `(1 - σ)M ⊆ L_α` (`sub_mem_lineMagnet`, by `mem_attractorSubgroup_iff_joinIrredWeylMagnets`).
Lattice part (`M` torsion-free, a finite group acting faithfully):
* `smul_self_eq_neg_of_line`: if `(1 - w)M ⊆ M ∩ ℚα` and `w ≠ 1` then `w α = -α`;
* `mem_zmultiples_of_mem_lineMagnet`: if `α` is primitive then `M ∩ ℚα = ℤα`.

Group part:
* `isReflectionOn_of_rankOne`: `n ∈ G^{L_α}(k̄)` normalizing `T` with `σ ≠ 1` acts by a
  reflection at `α`, given `M ∩ ℚα = ℤα` (e.g. `α` primitive) or `(1 - σ)M ⊆ ℤα`;
* `WithReflections.ofRankOne`: `WithReflections` from such an `n` for each root.

The existence of `n ∈ G^{L_α}(k̄) ∩ N_G(T)(k̄)` with `σ ≠ 1`, and the integrality
`(1 - σ)M ⊆ ℤα` for non-primitive `α` (`α = 2β` in `PGL_2`), are not consequences of
`SplitReductiveData` (which has no reductivity axiom: a Borel subgroup of `SL_2` satisfies all
its fields with `W = 1`); they remain the hypotheses of `ofRankOne`.
-/

suppress_compilation

open Set Function Module TauCeti WithConv Magnetism

namespace AlgMag.Reductive

open AlgMag.Weyl LatticeReflection

namespace RankOne

variable {M : Type*} [AddCommGroup M]

/-- The group magnet `L_α = M ∩ ℚα`: the `x` with `n x ∈ ℤα` for some `n ≠ 0`. -/
def lineMagnet (α : M) : AddSubmonoid M where
  carrier := {x | ∃ n c : ℤ, n ≠ 0 ∧ n • x = c • α}
  zero_mem' := ⟨1, 0, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨n, c, hn, hc⟩ ⟨n', c', hn', hc'⟩
    refine ⟨n * n', n' * c + n * c', mul_ne_zero hn hn', ?_⟩
    have e1 : (n * n') • x = (n' * c) • α := by
      rw [mul_comm n n', mul_smul, hc, smul_smul]
    have e2 : (n * n') • y = (n * c') • α := by
      rw [mul_smul, hc', smul_smul]
    rw [smul_add, e1, e2, add_smul]

lemma mem_lineMagnet {α x : M} : x ∈ lineMagnet α ↔ ∃ n c : ℤ, n ≠ 0 ∧ n • x = c • α :=
  Iff.rfl

lemma zmultiples_le_lineMagnet (α : M) {x : M} (hx : x ∈ AddSubgroup.zmultiples α) :
    x ∈ lineMagnet α := by
  obtain ⟨c, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  exact ⟨1, c, one_ne_zero, one_smul _ _⟩

variable [Module.IsTorsionFree ℤ M]

/-- **Primitive roots**: if `α` is primitive (`n β = α` forces `n = ±1`), `M ∩ ℚα = ℤα`. -/
theorem mem_zmultiples_of_mem_lineMagnet {α : M}
    (hprim : ∀ (n : ℤ) (β : M), n • β = α → IsUnit n) {x : M} (hx : x ∈ lineMagnet α) :
    x ∈ AddSubgroup.zmultiples α := by
  obtain ⟨n, c, hn, hc⟩ := hx
  set g := Int.gcd n c
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_left c hn
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  set n' := n / g
  set c' := c / g
  have hn1 : n = g * n' := (Int.mul_ediv_cancel' (Int.gcd_dvd_left n c)).symm
  have hc1 : c = g * c' := (Int.mul_ediv_cancel' (Int.gcd_dvd_right n c)).symm
  have hc' : n' • x = c' • α := by
    have h0 : (g : ℤ) • (n' • x - c' • α) = 0 := by
      rw [smul_sub, smul_smul, smul_smul, ← hn1, ← hc1, hc, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_right hgz).mp h0)
  have hcop : Int.gcd n' c' = 1 := Int.gcd_div_gcd_div_gcd hg
  have hbez := Int.gcd_eq_gcd_ab n' c'
  rw [hcop, Nat.cast_one] at hbez
  have hα : n' • (Int.gcdA n' c' • α + Int.gcdB n' c' • x) = α := by
    rw [smul_add, smul_smul, smul_comm n' (Int.gcdB n' c') x, hc', smul_smul, ← add_smul,
      show n' * Int.gcdA n' c' + Int.gcdB n' c' * c' = 1 by rw [hbez]; ring, one_smul]
  rcases Int.isUnit_iff.mp (hprim n' _ hα) with h1 | h1
  · rw [h1, one_smul] at hc'
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨c', hc'.symm⟩
  · rw [h1, neg_one_smul] at hc'
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨-c', ?_⟩
    rw [neg_smul, ← hc', neg_neg]

variable {G : Type*} [Group G] [DistribMulAction G M]

omit [Module.IsTorsionFree ℤ M] in
lemma smul_zsmul_comm (w : G) (c : ℤ) (y : M) : w • (c • y) = c • (w • y) :=
  map_zsmul (DistribSMul.toAddMonoidHom M w) c y

/-- **`w α = -α` from `(1 - w)M ⊆ M ∩ ℚα`**: in a finite group acting faithfully on a
torsion-free `M`, a nontrivial `w` with `(1 - w)M ⊆ M ∩ ℚα` sends `α` to `-α`. -/
theorem smul_self_eq_neg_of_line [Finite G]
    (hfaith : ∀ w w' : G, (∀ x : M, w • x = w' • x) → w = w') {w : G} {α : M} (hα : α ≠ 0)
    (h : ∀ x, x - w • x ∈ lineMagnet α) (hw : w ≠ 1) : w • α = -α := by
  obtain ⟨m, hm, hwm⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite w)
  obtain ⟨n, c, hn, hc⟩ := h α
  set d := n - c
  have h1 : n • (w • α) = d • α := by
    rw [smul_sub] at hc
    rw [sub_smul, ← hc]
    abel
  have hpow : ∀ j : ℕ, (n ^ j) • ((w ^ j) • α) = (d ^ j) • α := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc (n ^ (j + 1)) • ((w ^ (j + 1)) • α) = n ^ j • (w ^ j • (n • (w • α))) := by
            rw [pow_succ, pow_succ, mul_smul, mul_smul, smul_zsmul_comm]
        _ = d ^ (j + 1) • α := by
            rw [h1, smul_zsmul_comm, smul_smul, mul_comm, ← smul_smul, ih, smul_smul,
              ← pow_succ']
  have hnd : n ^ m = d ^ m := by
    have h' := hpow m
    rw [hwm, one_smul] at h'
    have : (n ^ m - d ^ m) • α = 0 := by rw [sub_smul, h', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hα).mp this)
  have hab : n.natAbs = d.natAbs := by
    have := congrArg Int.natAbs hnd
    rw [Int.natAbs_pow, Int.natAbs_pow] at this
    exact Nat.pow_left_injective hm.ne' this
  rcases Int.natAbs_eq_natAbs_iff.mp hab with hd | hd
  · -- `w α = α`, hence `w = 1`
    exfalso
    have hwα : w • α = α := by
      have : n • (w • α - α) = 0 := by rw [smul_sub, h1, ← hd, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero_iff_right hn).mp this)
    refine hw (hfaith w 1 fun x => ?_)
    obtain ⟨n', c', hn', hc'⟩ := h x
    set y := x - w • x
    have hy : w • y = y := by
      have : n' • (w • y - y) = 0 := by
        rw [smul_sub, ← smul_zsmul_comm, hc', smul_zsmul_comm, hwα, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero_iff_right hn').mp this)
    have hwx : w • x = x - y := by simp [y]
    have hj : ∀ j : ℕ, (w ^ j) • x = x - (j : ℤ) • y := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', mul_smul, ih, smul_sub, hwx, smul_zsmul_comm, hy]
        push_cast
        rw [add_smul, one_smul]
        abel
    have h0 : (m : ℤ) • y = 0 := by
      have := hj m
      rw [hwm, one_smul] at this
      exact (sub_eq_self.mp this.symm)
    have hy0 : y = 0 := (smul_eq_zero_iff_right (by exact_mod_cast hm.ne')).mp h0
    rw [one_smul]
    exact (sub_eq_zero.mp hy0).symm
  · have : n • (w • α - -α) = 0 := by
      rw [smul_sub, h1, hd, smul_neg, neg_smul]
      abel
    exact sub_eq_zero.mp ((smul_eq_zero_iff_right hn).mp this)

end RankOne

open RankOne

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable {π : H →ₐc[k] MonoidAlgebra k X}

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- **`n ∈ G^{L_α}` gives `(1 - σ)M ⊆ L_α`** (and conversely): `G^{L_α}` centralizes
`(ker α)°`. -/
theorem mem_attractorSubgroup_lineMagnet_iff (hπ : Surjective π) {A : Type*} [CommRing A]
    [Algebra k A] [Nontrivial A] {g : WithConv (H →ₐ[k] A)} {σ : X ≃* X}
    (hg : IsNormalizingWith π A g σ) (α : Additive X) :
    g ∈ attractorSubgroup π (lineMagnet α) A ↔ ∀ x, x - actW σ x ∈ lineMagnet α := by
  rw [mem_attractorSubgroup_iff_joinIrredWeylMagnets π hπ hg]
  constructor
  · intro h x
    exact h ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h x

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] in
theorem sub_mem_lineMagnet (hπ : Surjective π) {A : Type*} [CommRing A] [Algebra k A]
    [Nontrivial A] {g : WithConv (H →ₐ[k] A)} {σ : X ≃* X} (hg : IsNormalizingWith π A g σ)
    {α : Additive X} (hgL : g ∈ attractorSubgroup π (lineMagnet α) A) (x : Additive X) :
    x - actW σ x ∈ lineMagnet α :=
  (mem_attractorSubgroup_lineMagnet_iff hπ hg α).1 hgL x

variable [Module.IsTorsionFree ℤ (Additive X)]

/-- **Rank one**: a `k̄`-point `n ∈ G^{L_α}` normalizing `T` with automorphism `σ ≠ 1` acts by a
reflection at `α`, provided `M ∩ ℚα = ℤα` (e.g. `α` primitive) or `(1 - σ)M ⊆ ℤα`. -/
theorem isReflectionOn_of_rankOne (D : SplitReductiveData π) {α : Additive X}
    (hα : α ∈ roots π) {g : WithConv (H →ₐ[k] AlgebraicClosure k)} {σ : X ≃* X}
    (hg : IsNormalizingWith π (AlgebraicClosure k) g σ)
    (hgL : g ∈ attractorSubgroup π (lineMagnet α) (AlgebraicClosure k)) (hσ : σ ≠ 1)
    (hint : (∀ x ∈ lineMagnet α, x ∈ AddSubgroup.zmultiples α) ∨
      ∀ x, x - actW σ x ∈ AddSubgroup.zmultiples α) :
    IsReflectionOn σ α := by
  obtain ⟨hσW, -⟩ := D.normalizer_cover g σ hg
  have : Finite D.W := D.finite
  set w : D.W := ⟨σ, hσW⟩
  have hne : w ≠ 1 := fun h1 => hσ (congrArg Subtype.val h1)
  have hL : ∀ x, x - actW σ x ∈ lineMagnet α := sub_mem_lineMagnet D.surjective hg hgL
  have hL' : ∀ x, x - w • x ∈ lineMagnet α := fun x => by
    rw [weyl_smul_def]
    exact hL x
  have hneg : w • α = -α := smul_self_eq_neg_of_line (G := D.W) (fun _ _ h => weyl_ext h)
    (ne_zero_of_mem_roots hα) hL' hne
  rw [weyl_smul_def] at hneg
  refine ⟨hneg, ?_⟩
  rcases hint with h | h
  · exact fun x => h _ (hL x)
  · exact h

/-- The primitive case of `isReflectionOn_of_rankOne`. -/
theorem isReflectionOn_of_rankOne_primitive (D : SplitReductiveData π) {α : Additive X}
    (hα : α ∈ roots π) (hprim : ∀ (n : ℤ) (β : Additive X), n • β = α → IsUnit n)
    {g : WithConv (H →ₐ[k] AlgebraicClosure k)} {σ : X ≃* X}
    (hg : IsNormalizingWith π (AlgebraicClosure k) g σ)
    (hgL : g ∈ attractorSubgroup π (lineMagnet α) (AlgebraicClosure k)) (hσ : σ ≠ 1) :
    IsReflectionOn σ α :=
  isReflectionOn_of_rankOne D hα hg hgL hσ
    (Or.inl fun _ hx => mem_zmultiples_of_mem_lineMagnet hprim hx)

/-- **`WithReflections` from rank one**: for each root `α`, a `k̄`-point of
`G^{L_α} ∩ N_G(T)` (`L_α = M ∩ ℚα`, `G^{L_α} = Z_G((ker α)°)`) with nontrivial automorphism
`σ`, and the integrality `(1 - σ)M ⊆ ℤα` when `M ∩ ℚα ≠ ℤα`. -/
def SplitReductiveData.WithReflections.ofRankOne (D : SplitReductiveData π)
    (h : ∀ α ∈ roots π, ∃ (g : WithConv (H →ₐ[k] AlgebraicClosure k)) (σ : X ≃* X),
      IsNormalizingWith π (AlgebraicClosure k) g σ ∧
        g ∈ attractorSubgroup π (lineMagnet α) (AlgebraicClosure k) ∧ σ ≠ 1 ∧
        ((∀ x ∈ lineMagnet α, x ∈ AddSubgroup.zmultiples α) ∨
          ∀ x, x - actW σ x ∈ AddSubgroup.zmultiples α)) :
    SplitReductiveData.WithReflections π where
  toSplitReductiveData := D
  exists_normalizing_refl α hα := by
    obtain ⟨g, σ, hg, hgL, hσ, hint⟩ := h α hα
    exact ⟨g, σ, hg, isReflectionOn_of_rankOne D hα hg hgL hσ hint⟩

end AlgMag.Reductive
