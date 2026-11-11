/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic

/-!
# Double scalar action on the plane: the combinatorics of `Φ`

Mayeux, *Algebraic magnetism invariants of a double scalar action on the projective plane*,
arXiv:2509.04274v3, §§3, 4.

## Main results

* `AlgMag.DoubleScalar.Phi`: the set `Φ` of §3.
* `AlgMag.DoubleScalar.AddStable`: additively stable subsets of `Φ` (§4).
* `AlgMag.DoubleScalar.addStable_iff_closed`: a finite criterion for additive stability.
* `AlgMag.DoubleScalar.card_stable_eq`, `AlgMag.DoubleScalar.card_stable`: the classification of §4 by
  cardinality, `1 + 6 + 9 + 6 + 6 + 0 + 1 = 29`.
-/

namespace AlgMag.DoubleScalar

/-- The set `Φ ⊂ ℤ²` of §3: the weights of the double scalar action on the three charts. -/
def Phi : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (1, -1), (0, -1), (-1, 1), (-1, 0)}

/-- **§4.** A subset `E` of `Φ` is additively stable if `[E⟩ ∩ Φ = E`. -/
def AddStable (E : Set (ℤ × ℤ)) : Prop :=
  ((AddSubmonoid.closure E : AddSubmonoid (ℤ × ℤ)) : Set (ℤ × ℤ)) ∩ (Phi : Set (ℤ × ℤ)) = E

/-- A finite form of additive stability: the sum of two elements of `E` which is in `Φ` is in `E`. -/
def Closed (E : Finset (ℤ × ℤ)) : Prop := ∀ a ∈ E, ∀ b ∈ E, a + b ∈ Phi → a + b ∈ E

instance (E : Finset (ℤ × ℤ)) : Decidable (Closed E) := by unfold Closed; infer_instance

/-- The small range of slopes used for separating functionals. -/
def slopes : List ℤ := [-1, 0, 1]

set_option maxRecDepth 100000 in
/-- Every element of `Φ` outside a closed subset `E` is separated from `E` by a linear form. -/
theorem separate : ∀ E ∈ Phi.powerset, Closed E → ∀ w ∈ Phi, w ∉ E →
    ∃ p ∈ slopes, ∃ q ∈ slopes, (∀ e ∈ E, 0 ≤ p * e.1 + q * e.2) ∧ p * w.1 + q * w.2 < 0 := by
  decide

set_option maxRecDepth 100000 in
/-- **§4, classification by cardinality.** -/
theorem card_stable_eq :
    ((Phi.powerset.filter Closed).filter (fun E => E.card = 0)).card = 1 ∧
    ((Phi.powerset.filter Closed).filter (fun E => E.card = 1)).card = 6 ∧
    ((Phi.powerset.filter Closed).filter (fun E => E.card = 2)).card = 9 ∧
    ((Phi.powerset.filter Closed).filter (fun E => E.card = 3)).card = 6 ∧
    ((Phi.powerset.filter Closed).filter (fun E => E.card = 4)).card = 6 ∧
    ((Phi.powerset.filter Closed).filter (fun E => E.card = 5)).card = 0 ∧
    ((Phi.powerset.filter Closed).filter (fun E => E.card = 6)).card = 1 := by
  decide

set_option maxRecDepth 100000 in
/-- **§4.** There are `1 + 6 + 9 + 6 + 6 + 0 + 1 = 29` additively stable subsets. -/
theorem card_stable : (Phi.powerset.filter Closed).card = 29 := by decide


/-- `[E⟩ ∩ Φ` is contained in `E` if `E` is closed, by the separating linear forms. -/
theorem addStable_of_closed {E : Finset (ℤ × ℤ)} (hE : E ⊆ Phi) (hc : Closed E) :
    AddStable (E : Set (ℤ × ℤ)) := by
  refine Set.Subset.antisymm ?_ fun x hx => ⟨AddSubmonoid.subset_closure hx, hE hx⟩
  rintro w ⟨hw, hP⟩
  by_contra hn
  obtain ⟨p, -, q, -, h1, h2⟩ := separate E (Finset.mem_powerset.mpr hE) hc w hP hn
  have key : ∀ v ∈ AddSubmonoid.closure (E : Set (ℤ × ℤ)), 0 ≤ p * v.1 + q * v.2 := by
    intro v hv
    induction hv using AddSubmonoid.closure_induction with
    | mem x hx => exact h1 x hx
    | zero => simp
    | add x y _ _ hx hy =>
      have e : p * (x + y).1 + q * (x + y).2 = (p * x.1 + q * x.2) + (p * y.1 + q * y.2) := by
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      rw [e]
      exact add_nonneg hx hy
  exact absurd (key w hw) (not_le.mpr h2)

/-- **§4.** For a subset of `Φ`, additive stability is the finite condition `Closed`. -/
theorem addStable_iff_closed {E : Finset (ℤ × ℤ)} (hE : E ⊆ Phi) :
    AddStable (E : Set (ℤ × ℤ)) ↔ Closed E := by
  refine ⟨fun h a ha b hb hab => ?_, addStable_of_closed hE⟩
  have : a + b ∈ ((AddSubmonoid.closure (E : Set (ℤ × ℤ)) : AddSubmonoid (ℤ × ℤ)) : Set (ℤ × ℤ)) ∩
      (Phi : Set (ℤ × ℤ)) :=
    ⟨AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure ha) (AddSubmonoid.subset_closure hb), hab⟩
  rw [h] at this
  exact this

/-- The hexagon of §4, in its cyclic order. -/
def hexagon : Fin 6 → ℤ × ℤ
  | 0 => (1, 0) | 1 => (0, 1) | 2 => (-1, 1) | 3 => (-1, 0) | 4 => (0, -1) | 5 => (1, -1)

/-- `k` consecutive elements of the hexagon, starting at `i`. -/
def consecutive (k : ℕ) (i : Fin 6) : Finset (ℤ × ℤ) :=
  ((List.range k).map fun n => hexagon (i + (Fin.ofNat 6 n))).toFinset

set_option maxRecDepth 100000 in
/-- **§4, cardinality 3 and 4.** The additively stable subsets of cardinality 3 (resp. 4) are the sets of three
(resp. four) consecutive elements. -/
theorem stable_card_consecutive :
    (∀ E ∈ Phi.powerset, (Closed E ∧ E.card = 3) ↔ ∃ i, E = consecutive 3 i) ∧
    (∀ E ∈ Phi.powerset, (Closed E ∧ E.card = 4) ↔ ∃ i, E = consecutive 4 i) := by
  decide

set_option maxRecDepth 100000 in
/-- **§4, cardinality 2.** The additively stable subsets of cardinality 2 are the six pairs of adjacent elements
and the three pairs of opposite elements. -/
theorem stable_card_two :
    (∀ E ∈ Phi.powerset, (Closed E ∧ E.card = 2) ↔
      (∃ i, E = consecutive 2 i) ∨ ∃ a ∈ Phi, E = {a, -a}) ∧
    (((Phi.powerset.filter Closed).filter
      fun E => E.card = 2 ∧ ∃ a ∈ E, -a ∈ E).card = 3) := by
  decide

/-- **§4.** `{(0,1), (1,-1)}` is not additively stable, as `(0,1) + (1,-1)` belongs to `Φ`. -/
theorem not_stable_example : ¬ AddStable (({(0, 1), (1, -1)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  rw [addStable_iff_closed (by decide)]
  decide

set_option maxRecDepth 100000 in
/-- **Figure 1.** The poset of additively stable subsets, excluding `∅` and `Φ`: each singleton is below three
pairs, each adjacent pair below two triples, each opposite pair below no triple and two sets of cardinality four,
each triple below two sets of cardinality four. -/
theorem figure1_degrees :
    (∀ E ∈ Phi.powerset.filter Closed, E.card = 1 →
      ((Phi.powerset.filter Closed).filter fun F => E ⊆ F ∧ F.card = 2).card = 3) ∧
    (∀ E ∈ Phi.powerset.filter Closed, E.card = 2 → (∀ a ∈ E, -a ∉ E) →
      ((Phi.powerset.filter Closed).filter fun F => E ⊆ F ∧ F.card = 3).card = 2) ∧
    (∀ E ∈ Phi.powerset.filter Closed, E.card = 2 → (∃ a ∈ E, -a ∈ E) →
      ((Phi.powerset.filter Closed).filter fun F => E ⊆ F ∧ F.card = 3).card = 0 ∧
      ((Phi.powerset.filter Closed).filter fun F => E ⊆ F ∧ F.card = 4).card = 2) ∧
    (∀ E ∈ Phi.powerset.filter Closed, E.card = 3 →
      ((Phi.powerset.filter Closed).filter fun F => E ⊆ F ∧ F.card = 4).card = 2) := by
  decide

/-! ### Figures 1 and 2 -/

/-- The weights `w = ((1,0), (0,1), (0,0))` of the coordinates `x, y, z` of `ℙ²`: §3. -/
def wP : Fin 3 → ℤ × ℤ
  | 0 => (1, 0) | 1 => (0, 1) | 2 => (0, 0)

/-- `Φ` is the set of the differences of the weights. In particular it is the root system `A₂` of `SL₃`: this is
the combinatorial content of Remark 5.1 (ii). -/
theorem phi_eq_diff : (∀ i j, i ≠ j → wP i - wP j ∈ Phi) ∧ ∀ m ∈ Phi, ∃ i j, i ≠ j ∧ m = wP i - wP j := by
  decide

/-- **§3, the printed weights.** On the chart `z = 1` the weights are `(1,0), (0,1)`, on the chart `y = 1` they
are `(1,-1), (0,-1)` and on the chart `x = 1` they are `(-1,1), (-1,0)`. Here `w j - w s` is the weight of the
coordinate `j` on the chart `s`. -/
theorem chart_weights :
    (wP 0 - wP 2 = (1, 0) ∧ wP 1 - wP 2 = (0, 1)) ∧ (wP 0 - wP 1 = (1, -1) ∧ wP 2 - wP 1 = (0, -1)) ∧
    (wP 1 - wP 0 = (-1, 1) ∧ wP 2 - wP 0 = (-1, 0)) := by
  decide

/-- One step of the additive closure inside `Φ`. -/
def step (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S ∪ ((S ×ˢ S).image fun p => p.1 + p.2).filter (· ∈ Phi)

/-- `[E⟩ ∩ Φ`, computed. -/
def clo (g : List (ℤ × ℤ)) : Finset (ℤ × ℤ) := step (step g.toFinset)

/-- A row of Figures 1 and 2: the printed generators of the magnet; the coordinates `S x, S y, S z` of the three
charts in the attractor (e.g. `S z = {x}` is `𝔸¹` of weight `(1,0)` in the chart `z`, `S z = ∅` is the point
`{z}`); a label for the connected component of the fixed points `x, y, z`. -/
structure Row where
  gens : List (ℤ × ℤ)
  Sx : Finset (Fin 3)
  Sy : Finset (Fin 3)
  Sz : Finset (Fin 3)
  cx : ℕ
  cy : ℕ
  cz : ℕ
  deriving DecidableEq

/-- The charts of a row. -/
def Row.S (r : Row) : Fin 3 → Finset (Fin 3)
  | 0 => r.Sx | 1 => r.Sy | 2 => r.Sz

/-- The components of a row. -/
def Row.cl (r : Row) : Fin 3 → ℕ
  | 0 => r.cx | 1 => r.cy | 2 => r.cz

/-- The stable set of a row. -/
def Row.E (r : Row) : Finset (ℤ × ℤ) := clo r.gens

/-- The computation of a row by Lemma 4.2. -/
def Row.Good (r : Row) : Prop :=
  r.gens.toFinset ⊆ Phi ∧ Closed r.E ∧ (∀ s j, j ∈ r.S s ↔ j ≠ s ∧ wP j - wP s ∈ r.E) ∧
    ∀ i j, r.cl i = r.cl j ↔ i = j ∨ (wP i - wP j ∈ r.E ∧ wP j - wP i ∈ r.E)

instance (r : Row) : Decidable r.Good := by unfold Row.Good; infer_instance

/-- **Figures 1 and 2.** Coordinates `x = 0, y = 1, z = 2`. The rows are in the printed order, column by column,
preceded by the bottom magnet `0` and followed by the top magnet `ℤ²`, which the figures omit. -/
def fig2 : List Row := [
  -- `0`: `{x} ⊔ {y} ⊔ {z}`
  ⟨[], ∅, ∅, ∅, 0, 1, 2⟩,
  -- first column
  ⟨[(0, 1)], ∅, ∅, {1}, 0, 1, 2⟩,
  ⟨[(1, 0)], ∅, ∅, {0}, 0, 1, 2⟩,
  ⟨[(1, -1)], ∅, {0}, ∅, 0, 1, 2⟩,
  ⟨[(0, -1)], ∅, {2}, ∅, 0, 1, 2⟩,
  ⟨[(-1, 0)], {2}, ∅, ∅, 0, 1, 2⟩,
  ⟨[(-1, 1)], {1}, ∅, ∅, 0, 1, 2⟩,
  -- second column
  ⟨[(0, 1), (1, 0)], ∅, ∅, {0, 1}, 0, 1, 2⟩,
  ⟨[(0, 1), (0, -1)], ∅, {2}, {1}, 0, 1, 1⟩,
  ⟨[(1, 0), (1, -1)], ∅, {0}, {0}, 0, 1, 2⟩,
  ⟨[(1, -1), (0, -1)], ∅, {0, 2}, ∅, 0, 1, 2⟩,
  ⟨[(1, 0), (-1, 0)], {2}, ∅, {0}, 0, 1, 0⟩,
  ⟨[(0, -1), (-1, 0)], {2}, {2}, ∅, 0, 1, 2⟩,
  ⟨[(-1, 0), (-1, 1)], {1, 2}, ∅, ∅, 0, 1, 2⟩,
  ⟨[(1, -1), (-1, 1)], {1}, {0}, ∅, 0, 0, 1⟩,
  ⟨[(-1, 1), (0, 1)], {1}, ∅, {1}, 0, 1, 2⟩,
  -- third column
  ⟨[(0, 1), (1, 0), (1, -1)], ∅, {0}, {0, 1}, 0, 1, 2⟩,
  ⟨[(1, 0), (1, -1), (0, -1)], ∅, {0, 2}, {0}, 0, 1, 2⟩,
  ⟨[(1, -1), (0, -1), (-1, 0)], {2}, {0, 2}, ∅, 0, 1, 2⟩,
  ⟨[(0, -1), (-1, 0), (-1, 1)], {1, 2}, {2}, ∅, 0, 1, 2⟩,
  ⟨[(-1, 0), (-1, 1), (0, 1)], {1, 2}, ∅, {1}, 0, 1, 2⟩,
  ⟨[(-1, 1), (0, 1), (1, 0)], {1}, ∅, {0, 1}, 0, 1, 2⟩,
  -- fourth column
  ⟨[(0, 1), (0, -1), (1, 0)], ∅, {0, 2}, {0, 1}, 0, 1, 1⟩,
  ⟨[(0, 1), (0, -1), (-1, 0)], {1, 2}, {2}, {1}, 0, 1, 1⟩,
  ⟨[(1, 0), (-1, 0), (0, 1)], {1, 2}, ∅, {0, 1}, 0, 1, 0⟩,
  ⟨[(1, 0), (-1, 0), (0, -1)], {2}, {0, 2}, {0}, 0, 1, 0⟩,
  ⟨[(1, -1), (-1, 1), (1, 0)], {1}, {0}, {0, 1}, 0, 0, 1⟩,
  ⟨[(1, -1), (-1, 1), (-1, 0)], {1, 2}, {0, 2}, ∅, 0, 0, 1⟩,
  -- `ℤ²`: `ℙ²`
  ⟨[(1, 0), (0, 1), (-1, 0), (0, -1)], {1, 2}, {0, 2}, {0, 1}, 0, 0, 0⟩]

set_option maxRecDepth 200000 in
/-- All rows of Figures 1 and 2 are correct computations. -/
theorem fig2_good : ∀ r ∈ fig2, r.Good := by decide

set_option maxRecDepth 200000 in
/-- **Figures 1 and 2 are complete.** The rows enumerate the additively stable subsets, each once. -/
theorem fig2_complete :
    (fig2.map Row.E).Nodup ∧ (fig2.map Row.E).toFinset = Phi.powerset.filter Closed := by
  decide

lemma step_subset_closure {S : Finset (ℤ × ℤ)} {C : AddSubmonoid (ℤ × ℤ)} (h : ∀ x ∈ S, x ∈ C) :
    ∀ x ∈ step S, x ∈ C := by
  intro x hx
  simp only [step, Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_product] at hx
  obtain hx | ⟨⟨p, ⟨h1, h2⟩, rfl⟩, -⟩ := hx
  · exact h x hx
  · exact C.add_mem (h _ h1) (h _ h2)

lemma subset_step (S : Finset (ℤ × ℤ)) : S ⊆ step S := Finset.subset_union_left

lemma step_subset_phi {S : Finset (ℤ × ℤ)} (h : S ⊆ Phi) : step S ⊆ Phi := by
  intro x hx
  simp only [step, Finset.mem_union, Finset.mem_filter] at hx
  obtain hx | ⟨-, hx⟩ := hx
  · exact h hx
  · exact hx

/-- `[g⟩ ∩ Φ` is the stable set of a row. -/
theorem Row.closure_inter {r : Row} (h : r.Good) :
    ((AddSubmonoid.closure {x | x ∈ r.gens} : AddSubmonoid (ℤ × ℤ)) : Set (ℤ × ℤ)) ∩ (Phi : Set (ℤ × ℤ)) =
      (r.E : Set (ℤ × ℤ)) := by
  have hsub : r.E ⊆ Phi := step_subset_phi (step_subset_phi h.1)
  have hg : ∀ x ∈ r.gens.toFinset, x ∈ AddSubmonoid.closure {x | x ∈ r.gens} := fun x hx =>
    AddSubmonoid.subset_closure (List.mem_toFinset.mp hx)
  have hE : ∀ x ∈ r.E, x ∈ AddSubmonoid.closure {x | x ∈ r.gens} :=
    step_subset_closure (step_subset_closure hg)
  refine Set.Subset.antisymm ?_ fun x hx => ⟨hE x hx, hsub hx⟩
  rintro x ⟨hx, hP⟩
  have hst := addStable_of_closed hsub h.2.1
  have hle : AddSubmonoid.closure {x | x ∈ r.gens} ≤ AddSubmonoid.closure (r.E : Set (ℤ × ℤ)) := by
    refine AddSubmonoid.closure_le.mpr fun y hy => AddSubmonoid.subset_closure ?_
    exact subset_step _ (subset_step _ (List.mem_toFinset.mpr hy))
  have : x ∈ ((AddSubmonoid.closure (r.E : Set (ℤ × ℤ)) : AddSubmonoid (ℤ × ℤ)) : Set (ℤ × ℤ)) ∩
      (Phi : Set (ℤ × ℤ)) := ⟨hle hx, hP⟩
  rw [hst] at this
  exact this

end AlgMag.DoubleScalar
