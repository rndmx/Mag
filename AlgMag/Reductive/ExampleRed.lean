/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ComponentsMeetNormalizerProof

/-!
# Example `ex:red`: attractors of Weyl magnet magnets containing no root

* `attractor_points_of_no_roots`: for `G` split reductive over an algebraically closed field,
  `X` a lattice, and a magnet `N` containing no root, `G^N(k) = ⋃_{w ∈ W_N} T(k) n_w`. This is
  Theorem `thm:red-attractors` (ii) (`red_attractors_ii_lattice`) with `K_∅ = T`
  (`compIdeal_eq_rootComp`, `hT_lattice`). Together with
  `Weyl.magnetHopfIdeal_weylMagnet_eq_centralizer` (`G^{(1-w)M} = Z_G(T^w)`), this is the general
  part of the example.
* The lattice computations of the example, on the character lattice `M` of the maximal torus:
  for `PGL₂`, `M = ℤα`, `s_α = -1`: `(1 - s_α)M = 2ℤα`, which contains no root, and `W_N = W`;
  for `PGL₃`, `M = ℤa ⊕ ℤb`, `c = s_a s_b`: `(1 - c)M = {xa + yb | x + y ≡ 0 mod 3}`, which
  contains no root, and `W_N = {1, c, c²} = ⟨c⟩`.
-/

suppress_compilation

set_option linter.unnecessarySeqFocus false

open Magnetism TauCeti WithConv

namespace AlgMag.Reductive

universe u

section General

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}
variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)] [Monoid.FG X] [IsMulTorsionFree X]

/-- **Example `ex:red`, general part.** If the magnet `N` contains no root, then
`G^N(k) = ⋃_{w ∈ W_N} T(k) n_w`: a point of `G^N(k)` is `h n` with `h ∈ T(k)` (`h` vanishes on
the ideal of `T`) and `n` normalizing `T` with automorphism `w ∈ W_N`, and conversely. -/
theorem attractor_points_of_no_roots (D : SplitReductiveData π) (N : Magnet (Additive X))
    (hN : ∀ α ∈ roots π, α ∉ N) (g : WithConv (H →ₐ[k] k)) :
    g ∈ attractorSubgroup π N k ↔ ∃ (h n : WithConv (H →ₐ[k] k)) (w : D.W),
      (∀ x, π x = 0 → h.ofConv x = 0) ∧ Weyl.IsNormalizingWith π k n (w : X ≃* X) ∧
      Weyl.weylMagnet (w : X ≃* X) ≤ N ∧ g = h * n := by
  have hR : ({α | α ∈ N} ∩ roots π : Set (Additive X)) = ∅ := by
    ext α
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun h hα => hN α hα h
  have hc : ∀ h : WithConv (H →ₐ[k] k),
      compIdeal π N ≤ RingHom.ker h.ofConv ↔ ∀ x, π x = 0 → h.ofConv x = 0 := by
    intro h
    rw [compIdeal_eq_rootComp, hR, rootComp, AddSubmonoid.closure_empty]
    exact ⟨fun H x hx => H ((hT_lattice D x).2 hx), fun H x hx => H x ((hT_lattice D x).1 hx)⟩
  rw [red_attractors_ii_lattice D N g]
  simp only [hc]

end General

namespace ExampleRed

/-! ### `PGL₂`: `M = ℤα`, `s_α = -1` -/

/-- The reflection `s_α = -1` on `M = ℤα`. -/
def sPGL2 : ℤ →+ ℤ := -AddMonoidHom.id ℤ

/-- `(1 - s_α)M = 2ℤα`. -/
theorem mem_weylMagnet_sPGL2 (m : ℤ) : m ∈ Rooted.weylMagnet sPGL2 ↔ 2 ∣ m := by
  rw [Rooted.weylMagnet, AddMonoidHom.mem_mrange]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, by simp [sPGL2]; ring⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by simp [sPGL2]; ring⟩

/-- `(1 - s_α)M = 2ℤα` contains no root `±α`. -/
theorem roots_not_mem_weylMagnet_sPGL2 :
    (1 : ℤ) ∉ Rooted.weylMagnet sPGL2 ∧ (-1 : ℤ) ∉ Rooted.weylMagnet sPGL2 := by
  simp only [mem_weylMagnet_sPGL2]
  omega

/-- `W_N = W = {1, s_α}` for `N = (1 - s_α)M`. -/
theorem weylPart_PGL2 :
    Rooted.weylMagnet (AddMonoidHom.id ℤ) ≤ Rooted.weylMagnet sPGL2 ∧
      Rooted.weylMagnet sPGL2 ≤ Rooted.weylMagnet sPGL2 := by
  refine ⟨fun m hm => ?_, le_rfl⟩
  obtain ⟨x, rfl⟩ := AddMonoidHom.mem_mrange.1 hm
  simp

/-! ### `PGL₃`: `M = ℤa ⊕ ℤb`, coordinates `xa + yb ↦ (x, y)`

`⟨a, b^∨⟩ = ⟨b, a^∨⟩ = -1`, `⟨a, (a+b)^∨⟩ = ⟨b, (a+b)^∨⟩ = 1`. -/

/-- `s_a(xa + yb) = (y - x)a + yb`. -/
def sa : ℤ × ℤ →+ ℤ × ℤ where
  toFun p := (p.2 - p.1, p.2)
  map_zero' := by simp
  map_add' p q := by ext <;> simp <;> ring

/-- `s_b(xa + yb) = xa + (x - y)b`. -/
def sb : ℤ × ℤ →+ ℤ × ℤ where
  toFun p := (p.1, p.1 - p.2)
  map_zero' := by simp
  map_add' p q := by ext <;> simp <;> ring

/-- `s_{a+b}(xa + yb) = -ya - xb`. -/
def sab : ℤ × ℤ →+ ℤ × ℤ where
  toFun p := (-p.2, -p.1)
  map_zero' := by simp
  map_add' p q := by ext <;> simp <;> ring

/-- The Coxeter element `c = s_a s_b`: `c(xa + yb) = -ya + (x - y)b`. -/
def cox : ℤ × ℤ →+ ℤ × ℤ where
  toFun p := (-p.2, p.1 - p.2)
  map_zero' := by simp
  map_add' p q := by ext <;> simp <;> ring

lemma sa_apply (p : ℤ × ℤ) : sa p = (p.2 - p.1, p.2) := rfl
lemma sb_apply (p : ℤ × ℤ) : sb p = (p.1, p.1 - p.2) := rfl
lemma sab_apply (p : ℤ × ℤ) : sab p = (-p.2, -p.1) := rfl
lemma cox_apply (p : ℤ × ℤ) : cox p = (-p.2, p.1 - p.2) := rfl

/-- `c = s_a s_b`. -/
theorem cox_eq : cox = sa.comp sb := by
  ext p <;> simp [cox_apply, sa_apply, sb_apply]

/-- `c³ = 1`, so `⟨c⟩ = {1, c, c²}`. -/
theorem cox_cube : cox.comp (cox.comp cox) = AddMonoidHom.id _ := by
  ext p <;> simp [cox_apply] <;> ring

/-- `(1 - c)M = {xa + yb | x + y ≡ 0 mod 3}`. -/
theorem mem_weylMagnet_cox (p : ℤ × ℤ) : p ∈ Rooted.weylMagnet cox ↔ 3 ∣ p.1 + p.2 := by
  rw [Rooted.weylMagnet, AddMonoidHom.mem_mrange]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.2, by simp [cox_apply]; ring⟩
  · rintro ⟨t, ht⟩
    refine ⟨(p.1 - t, t), ?_⟩
    ext <;> simp [cox_apply] <;> omega

/-- The roots `±a, ±b, ±(a + b)`. -/
def rootsPGL3 : Set (ℤ × ℤ) := {(1, 0), (0, 1), (1, 1), (-1, 0), (0, -1), (-1, -1)}

/-- `(1 - c)M` contains no root. -/
theorem roots_not_mem_weylMagnet_cox : ∀ β ∈ rootsPGL3, β ∉ Rooted.weylMagnet cox := by
  intro β hβ
  rw [mem_weylMagnet_cox]
  simp only [rootsPGL3, Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The Weyl group `W = S₃ = {1, c, c², s_a, s_b, s_{a+b}}` acting on `M`. -/
def weylPGL3 : Set (ℤ × ℤ →+ ℤ × ℤ) :=
  {AddMonoidHom.id _, cox, cox.comp cox, sa, sb, sab}

/-- **`W_N = ⟨c⟩` for `N = (1 - c)M`.** -/
theorem weylPart_PGL3 :
    {w | w ∈ weylPGL3 ∧ Rooted.weylMagnet w ≤ Rooted.weylMagnet cox} =
      {AddMonoidHom.id _, cox, cox.comp cox} := by
  have hmem : ∀ (w : ℤ × ℤ →+ ℤ × ℤ) (p : ℤ × ℤ), p - w p ∈ Rooted.weylMagnet w := fun w p =>
    AddMonoidHom.mem_mrange.2 ⟨p, rfl⟩
  have hid : Rooted.weylMagnet (AddMonoidHom.id (ℤ × ℤ)) ≤ Rooted.weylMagnet cox := by
    intro m hm
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_mrange.1 hm
    simp
  have hc2 : Rooted.weylMagnet (cox.comp cox) ≤ Rooted.weylMagnet cox := by
    intro m hm
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_mrange.1 hm
    rw [mem_weylMagnet_cox]
    exact ⟨x.1, by simp [cox_apply]; ring⟩
  have hsa : ¬ Rooted.weylMagnet sa ≤ Rooted.weylMagnet cox := fun h => by
    have := (mem_weylMagnet_cox _).1 (h (hmem sa (1, 1)))
    simp [sa_apply] at this
  have hsb : ¬ Rooted.weylMagnet sb ≤ Rooted.weylMagnet cox := fun h => by
    have := (mem_weylMagnet_cox _).1 (h (hmem sb (1, 1)))
    simp [sb_apply] at this
  have hsab : ¬ Rooted.weylMagnet sab ≤ Rooted.weylMagnet cox := fun h => by
    have := (mem_weylMagnet_cox _).1 (h (hmem sab (1, 0)))
    simp [sab_apply] at this
  ext w
  simp only [weylPGL3, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw | hw | hw | hw | hw | hw, h⟩
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr hw)
    · exact absurd (hw ▸ h) hsa
    · exact absurd (hw ▸ h) hsb
    · exact absurd (hw ▸ h) hsab
  · rintro (rfl | rfl | rfl)
    · exact ⟨Or.inl rfl, hid⟩
    · exact ⟨Or.inr (Or.inl rfl), le_rfl⟩
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hc2⟩

end ExampleRed

end AlgMag.Reductive
