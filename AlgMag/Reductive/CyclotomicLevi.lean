/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TorsionPrimes
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Proposition `prop:weyl-levi` (ii): Weyl magnets are local to Levi subgroups

Setting of `AlgMag.Reductive.TorsionPrimes`: `W` acts on the lattice `M`, `Z w = (1 - w)M`.
`B` is a `W`-invariant bilinear form on `M`, positive on nonzero vectors (for a root datum,
`RootPairing.RootForm`, after restriction to the span of the roots).

* `fix w = {x | w • x = x}` is `M^w`; `levi w = {v | ∀ x ∈ M^w, v • x = x}` is the Weyl group
  `W_{L_w}` of the Levi subgroup `L_w` attached to the flat `V^w`.
* `fixed_of_Z_le`: if `Z_v ⊆ Z_w`, then `v` fixes `M^w` pointwise, i.e. `v ∈ W_{L_w}`.
* `orth_of_mem_Z`: every element of `Z_w` (in particular every root in `Z_w`) is orthogonal to
  `M^w`, i.e. is a root of `L_w`.
* `weylMagnetLower_levi`: the lower term defining redundancy of `Z_w` is the same whether computed
  with `W` or with `W_{L_w}`; hence `Z_w` is redundant for `G` iff it is redundant for `L_w`.
-/

namespace AlgMag.Reductive.Torsion

open Set

variable {M : Type*} [AddCommGroup M] {W : Type*} [Group W] [DistribMulAction W M]

section Form

variable (B : M →+ M →+ ℤ)
  (hinv : ∀ (g : W) (a b : M), B (g • a) (g • b) = B a b)
  (hpos : ∀ z : M, z ≠ 0 → 0 < B z z)

/-- `M^w`, the fixed lattice of `w`. -/
def fix (w : W) : Set M := {x | w • x = x}

/-- `W_{L_w}`: the elements of `W` fixing `M^w` pointwise. -/
def levi (w : W) : Subgroup W where
  carrier := {v | ∀ x ∈ fix (M := M) w, v • x = x}
  one_mem' := fun x _ => one_smul W x
  mul_mem' := fun ha hb x hx => by rw [mul_smul, hb x hx, ha x hx]
  inv_mem' := fun ha x hx => by
    have h := ha x hx
    rw [inv_smul_eq_iff, h]

include hinv in
/-- Elements of `Z_w` are orthogonal to `M^w`. -/
lemma orth_of_mem_Z {w : W} {x z : M} (hx : x ∈ fix w) (hz : z ∈ Z M w) : B x z = 0 := by
  obtain ⟨y, rfl⟩ := mem_Z.1 hz
  have h := hinv w x y
  rw [show w • x = x from hx] at h
  rw [map_sub, h, sub_self]

include hinv hpos in
/-- **Prop. `prop:weyl-levi` (ii).** If `Z_v ⊆ Z_w` then `v` fixes `M^w` pointwise, i.e.
`v ∈ W_{L_w}`. -/
theorem fixed_of_Z_le {v w : W} (hvw : Z M v ≤ Z M w) : v ∈ levi (M := M) w := by
  intro x hx
  -- `x ⊥ Z_w ⊇ Z_v`, so `B x y = B x (v • y)` for all `y`
  have horth : ∀ y : M, B x y = B x (v • y) := fun y => by
    have := orth_of_mem_Z B hinv hx (hvw (sub_mem_Z v y))
    rwa [map_sub, sub_eq_zero] at this
  -- hence `B (x - v⁻¹ • x) y = 0` for all `y`
  have hz : ∀ y : M, B (x - v⁻¹ • x) y = 0 := fun y => by
    have h1 := hinv v⁻¹ x (v • y)
    rw [inv_smul_smul] at h1
    rw [map_sub, AddMonoidHom.sub_apply, horth y, ← h1, sub_self]
  by_contra hne
  have hne' : x - v⁻¹ • x ≠ 0 := by
    intro h0
    apply hne
    rw [sub_eq_zero] at h0
    calc v • x = v • (v⁻¹ • x) := congrArg (v • ·) h0
      _ = x := smul_inv_smul v x
  exact absurd (hz _) (ne_of_gt (hpos _ hne'))

include hinv hpos in
/-- **Prop. `prop:weyl-levi` (ii), redundancy is local.** The lower term in the definition of
redundancy (`Rooted.weylMagnetLower`, the sum of the roots in `Z_w` and of the `Z_v ⊊ Z_w`) is the
same for `W` and for the Weyl group `W_{L_w}` of the Levi subgroup `L_w`. -/
theorem weylMagnetLower_levi (Φ : Set M) (w : W) :
    Rooted.weylMagnetLower Φ (fun v : levi (M := M) w => actOf M W v) ⟨w, fun _ hx => hx⟩ =
      Rooted.weylMagnetLower Φ (actOf M W) w := by
  unfold Rooted.weylMagnetLower
  congr 1
  apply le_antisymm
  · exact iSup₂_le fun v hv => le_iSup₂_of_le (v : W) hv le_rfl
  · refine iSup₂_le fun v hv => ?_
    exact le_iSup₂_of_le (⟨v, fixed_of_Z_le B hinv hpos (le_of_lt hv)⟩ : levi (M := M) w) hv le_rfl

end Form

end AlgMag.Reductive.Torsion



/-! ### Proposition `prop:weyl-levi` (i): fixed lattices are root-hyperplane intersections -/

namespace AlgMag.Reductive.Torsion

section Flats

variable {M : Type*} [AddCommGroup M] {W : Type*} [Group W] [DistribMulAction W M]
  (B : M →+ M →+ ℤ)
  (hinv : ∀ (g : W) (a b : M), B (g • a) (g • b) = B a b)
  (hpos : ∀ z : M, z ≠ 0 → 0 < B z z)

include hinv hpos in
/-- **Prop. `prop:weyl-levi` (i), first equality** (`(1-w)V = (V^w)^⊥`, lattice form):
`x` is fixed by `w` iff `x` is orthogonal to `Z_w`. -/
theorem mem_fix_iff_orth (w : W) (x : M) :
    x ∈ fix w ↔ ∀ z ∈ Z M w, B x z = 0 := by
  refine ⟨fun hx z hz => orth_of_mem_Z B hinv hx hz, fun h => ?_⟩
  have hz : ∀ y : M, B (x - w⁻¹ • x) y = 0 := fun y => by
    have h1 := h _ (sub_mem_Z w y)
    have h2 := hinv w⁻¹ x (w • y)
    rw [inv_smul_smul] at h2
    rw [map_sub, sub_eq_zero] at h1
    rw [map_sub, AddMonoidHom.sub_apply, h1, ← h2, sub_self]
  by_contra hne
  have hne' : x - w⁻¹ • x ≠ 0 := by
    intro h0
    apply hne
    rw [sub_eq_zero] at h0
    show w • x = x
    calc w • x = w • (w⁻¹ • x) := congrArg (w • ·) h0
      _ = x := smul_inv_smul w x
  exact absurd (hz _) (ne_of_gt (hpos _ hne'))

variable {Φ : Set M} {refl : M → W}
  (hreflfix : ∀ α ∈ Φ, ∀ x : M, refl α • x = x ↔ B α x = 0)

include hreflfix in
/-- **Prop. `prop:weyl-levi` (i), `V^w` is an intersection of root hyperplanes.** Input
(Steinberg 1975, p. 64, after Steinberg, *Endomorphisms of linear algebraic groups*, 1.20): the
pointwise stabilizer `W_{L_w}` of `M^w` is generated by the reflections it contains. Then `M^w`
is the set of `x` orthogonal to every root `α` with `s_α ∈ W_{L_w}`. -/
theorem fix_eq_hyperplanes (w : W)
    (hSt : levi (M := M) w ≤ Subgroup.closure (refl '' {α ∈ Φ | refl α ∈ levi (M := M) w})) :
    fix (M := M) w = {x | ∀ α ∈ Φ, refl α ∈ levi (M := M) w → B α x = 0} := by
  ext x
  refine ⟨fun hx α hα hl => (hreflfix α hα x).1 (hl x hx), fun hx => ?_⟩
  -- the stabilizer of `x` contains the generating reflections, hence `W_{L_w} ∋ w`
  let S : Subgroup W := MulAction.stabilizer W x
  have hgen : refl '' {α ∈ Φ | refl α ∈ levi (M := M) w} ⊆ S := by
    rintro _ ⟨α, ⟨hα, hl⟩, rfl⟩
    exact (hreflfix α hα x).2 (hx α hα hl)
  have hw : w ∈ levi (M := M) w := fun _ hy => hy
  exact (Subgroup.closure_le S).2 hgen (hSt hw)

end Flats

end AlgMag.Reductive.Torsion

/-! ### Proposition `prop:weyl-levi` (iii): the index formula -/

namespace AlgMag.Reductive.Torsion

section Index

variable {M : Type*} [AddCommGroup M] {W : Type*} [Group W] [DistribMulAction W M]

/-- `φ_w = 1 - w` on `M`. -/
def phi (w : W) : M →+ M where
  toFun x := x - w • x
  map_zero' := by simp
  map_add' x y := by rw [smul_add]; abel

lemma phi_apply (w : W) (x : M) : phi w x = x - w • x := rfl

lemma range_phi (w : W) : (phi (M := M) w).range = ZG M w := by
  ext z; rw [AddMonoidHom.mem_range, mem_ZG, mem_Z]; rfl

/-- `M_w = M ∩ (1 - w)V`, the saturation of `Z_w` in `M`. -/
def Msat (w : W) : AddSubgroup M where
  carrier := {x | ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ Z M w}
  zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add, mul_comm n m, mul_smul, mul_comm m n, mul_smul]
    exact add_mem (AddSubmonoid.nsmul_mem _ hx m) (AddSubmonoid.nsmul_mem _ hy n)
  neg_mem' := by
    rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [smul_neg]; exact neg_mem_Z hx⟩

lemma ZG_le_Msat (w : W) : ZG M w ≤ Msat w := fun z hz => ⟨1, one_ne_zero, by rwa [one_smul]⟩

lemma map_phi_Msat_le (w : W) : (Msat w).map (phi (M := M) w) ≤ ZG M w := by
  rintro _ ⟨x, -, rfl⟩; exact sub_mem_Z w x

/-- **Prop. `prop:weyl-levi` (iii), index part.** `[M_w : Z_w] · [M : M^w + M_w] = [M_w : (1-w)M_w]`,
where `M^w = ker (1 - w)`; the order of the torsion of `M/Z_w` is `[M_w : Z_w]`. -/
theorem index_formula (w : W) :
    (ZG M w).relIndex (Msat (M := M) w) * ((Msat (M := M) w) ⊔ (phi (M := M) w).ker).index =
      ((Msat (M := M) w).map (phi (M := M) w)).relIndex (Msat (M := M) w) := by
  have h1 : ((Msat (M := M) w).map (phi (M := M) w)).relIndex (ZG M w) = ((Msat (M := M) w) ⊔ (phi (M := M) w).ker).index := by
    rw [← AddSubgroup.comap_map_eq, AddSubgroup.index_comap, range_phi]
  rw [← h1, mul_comm]
  exact AddSubgroup.relIndex_mul_relIndex _ _ _ (map_phi_Msat_le w) (ZG_le_Msat w)


/-- `1 - w` restricted to `M_w`, as a `ℤ`-linear endomorphism. -/
def phiSat (w : W) : Msat (M := M) w →ₗ[ℤ] Msat (M := M) w :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => ⟨phi (M := M) w (x : M), ZG_le_Msat w (sub_mem_Z w (x : M))⟩
      map_zero' := by ext; simp [phi_apply]
      map_add' := fun x y => by ext; simp only [AddSubgroup.coe_add, map_add] }

lemma phiSat_injective [Finite W] [IsAddTorsionFree M] (w : W) :
    Function.Injective (phiSat (M := M) w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, n, hn, hx⟩ h0
  have hfix : w • x = x := by
    have := congrArg Subtype.val h0
    simpa [phiSat, phi_apply, sub_eq_zero, eq_comm] using this
  have hfix' : w • (n • x) = n • x := by rw [smul_comm, hfix]
  have := eq_zero_of_mem_Z_of_fixed (pow_orderOf_eq_one w) (orderOf_pos w).ne' hx hfix'
  ext
  exact (nsmul_eq_zero_iff_right hn).1 this

lemma map_phi_eq_range (w : W) :
    ((Msat (M := M) w).map (phi w)).addSubgroupOf (Msat w) =
      (LinearMap.range (phiSat (M := M) w)).toAddSubgroup := by
  ext ⟨x, hx⟩
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup,
    LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, h⟩; exact ⟨y, hy, congrArg Subtype.val h⟩

/-- **Prop. `prop:weyl-levi` (iii), determinant part.** `[M_w : (1-w)M_w] = |det((1-w)|_{M_w})|`,
the value at `1` of the characteristic polynomial of `w` on `M_w` up to sign. -/
theorem relIndex_eq_det [Finite W] [IsAddTorsionFree M] [Module.Finite ℤ M] (w : W) :
    ((Msat (M := M) w).map (phi w)).relIndex (Msat w) =
      Int.natAbs (LinearMap.det (phiSat (M := M) w)) := by
  have hinj := phiSat_injective (M := M) w
  haveI : Module.Finite ℤ (Msat (M := M) w) :=
    Module.Finite.of_injective (AddMonoidHom.toIntLinearMap (Msat (M := M) w).subtype)
      Subtype.val_injective
  haveI : Module.Free ℤ (Msat (M := M) w) := Module.free_of_finite_type_torsion_free'
  have key := Submodule.natAbs_det_equiv (LinearMap.range (phiSat (M := M) w))
    (LinearEquiv.ofInjective _ hinj)
  have hcomp : (LinearMap.range (phiSat (M := M) w)).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap
        ((LinearEquiv.ofInjective _ hinj : Msat (M := M) w ≃ₗ[ℤ] _) : Msat w →+ _) =
      phiSat w := by
    ext x; rfl
  rw [hcomp] at key
  rw [key, AddSubgroup.relIndex, map_phi_eq_range]
  rfl

/-- **Prop. `prop:weyl-levi` (iii), cyclotomic values.** `φ_d(1) = p` for `d = p^k`, `k ≥ 1`,
and `φ_d(1) = 1` if `d > 1` is not a prime power. -/
theorem cyclotomic_eval_one (p k : ℕ) [Fact p.Prime] :
    Polynomial.eval 1 (Polynomial.cyclotomic (p ^ (k + 1)) ℤ) = p :=
  Polynomial.eval_one_cyclotomic_prime_pow k

theorem cyclotomic_eval_one_not_prime_pow {d : ℕ} (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ d) :
    Polynomial.eval 1 (Polynomial.cyclotomic d ℤ) = 1 :=
  Polynomial.eval_one_cyclotomic_not_prime_pow h

end Index

end AlgMag.Reductive.Torsion

#print axioms AlgMag.Reductive.Torsion.fixed_of_Z_le
#print axioms AlgMag.Reductive.Torsion.weylMagnetLower_levi
#print axioms AlgMag.Reductive.Torsion.mem_fix_iff_orth
#print axioms AlgMag.Reductive.Torsion.fix_eq_hyperplanes
#print axioms AlgMag.Reductive.Torsion.index_formula
#print axioms AlgMag.Reductive.Torsion.relIndex_eq_det
