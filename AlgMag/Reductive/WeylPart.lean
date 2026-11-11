/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Tactic.Abel

/-!
# The Weyl part of a magnet (Lemma `lem:weyl-part` (i), (ii))

`W` a finite group acting on the character group `M`; for a magnet `N ⊆ M`,
`W_N = {w | (1 - w)M ⊆ N}`. It is a subgroup of `W`, equal to `{w | (1 - w)M ⊆ N*}`, and it
stabilizes `N`, `N*` and `N ∩ Φ` for `Φ` a `W`-stable set. `N ∩ Φ` is additively stable.
-/

namespace AlgMag.Reductive

variable {M : Type*} [AddCommGroup M] {W : Type*} [Group W] [DistribMulAction W M]

/-- `(1 - w)M ⊆ N`. -/
def WeylIn (N : AddSubmonoid M) (w : W) : Prop := ∀ m : M, m - w • m ∈ N

/-- The units `N* = N ∩ -N`. -/
def unitsOf (N : AddSubmonoid M) : Set M := {x | x ∈ N ∧ -x ∈ N}

lemma weylIn_iff_units (N : AddSubmonoid M) (w : W) :
    WeylIn N w ↔ ∀ m : M, m - w • m ∈ unitsOf N := by
  refine ⟨fun h m => ⟨h m, ?_⟩, fun h m => (h m).1⟩
  have := h (-m)
  simpa [smul_neg, neg_sub, sub_eq_add_neg, add_comm] using this

lemma WeylIn.smul_mem {N : AddSubmonoid M} {w : W} (hw : WeylIn N w) {x : M} (hx : x ∈ N) :
    w • x ∈ N := by
  have h := hw (-x)
  have : w • x = x + (-x - w • -x) := by simp [smul_neg]
  rw [this]; exact N.add_mem hx h

lemma WeylIn.mul {N : AddSubmonoid M} {v w : W} (hv : WeylIn N v) (hw : WeylIn N w) :
    WeylIn N (v * w) := by
  intro m
  have : m - (v * w) • m = (m - v • m) + v • (m - w • m) := by
    rw [mul_smul, smul_sub]; abel
  rw [this]; exact N.add_mem (hv m) (hv.smul_mem (hw m))

lemma weylIn_one (N : AddSubmonoid M) : WeylIn N (1 : W) := fun m => by simp

variable [Finite W]

/-- **Lemma `lem:weyl-part` (i).** `W_N` is a subgroup of `W`. -/
def weylPart (N : AddSubmonoid M) : Subgroup W where
  carrier := {w | WeylIn N w}
  one_mem' := weylIn_one N
  mul_mem' := fun hv hw => WeylIn.mul hv hw
  inv_mem' := by
    intro w hw
    let S : Submonoid W := ⟨⟨{w | WeylIn N w}, fun hv hw => WeylIn.mul hv hw⟩, weylIn_one N⟩
    have h : w⁻¹ ∈ Submonoid.powers w :=
      (mem_powers_iff_mem_zpowers).2 (Subgroup.inv_mem _ (Subgroup.mem_zpowers w))
    have hS : Submonoid.powers w ≤ S := (Submonoid.powers_le).2 hw
    exact hS h

lemma mem_weylPart {N : AddSubmonoid M} {w : W} : w ∈ weylPart N ↔ WeylIn N w := Iff.rfl

/-- `W_N` stabilizes `N`. -/
lemma weylPart_smul_mem {N : AddSubmonoid M} {w : W} (hw : w ∈ weylPart N) {x : M}
    (hx : x ∈ N) : w • x ∈ N := WeylIn.smul_mem hw hx

/-- `W_N` stabilizes `N*`. -/
lemma weylPart_smul_units {N : AddSubmonoid M} {w : W} (hw : w ∈ weylPart N) {x : M}
    (hx : x ∈ unitsOf N) : w • x ∈ unitsOf N :=
  ⟨weylPart_smul_mem hw hx.1, by rw [← smul_neg]; exact weylPart_smul_mem hw hx.2⟩

/-- `W_N` stabilizes `R(N) = N ∩ Φ` for `Φ` stable under `W`. -/
lemma weylPart_smul_roots {N : AddSubmonoid M} {Φ : Set M} (hΦ : ∀ (v : W) x, x ∈ Φ → v • x ∈ Φ)
    {w : W} (hw : w ∈ weylPart N) {x : M} (hx : x ∈ (N : Set M) ∩ Φ) :
    w • x ∈ (N : Set M) ∩ Φ :=
  ⟨weylPart_smul_mem hw hx.1, hΦ w x hx.2⟩

/-- **Lemma `lem:weyl-part` (ii).** `R(N)` is additively stable, hence closed. -/
lemma roots_add_mem {N : AddSubmonoid M} {Φ : Set M} {α β : M}
    (hα : α ∈ (N : Set M) ∩ Φ) (hβ : β ∈ (N : Set M) ∩ Φ) (h : α + β ∈ Φ) :
    α + β ∈ (N : Set M) ∩ Φ := ⟨N.add_mem hα.1 hβ.1, h⟩

/-! ### Lemma `lem:weyl-part` (iii)

For `β ∈ R(N) ∩ -R(N)` the reflection `s_β` satisfies `(1 - s_β)M ⊆ ℤβ ⊆ N*`. Abstractly: let
`S ⊆ W` be a set of elements `s` with `(1 - s)M ⊆ Z` for an additive subgroup `Z ≤ N*`
(`Z = ℤ(R(N) ∩ -R(N))`). Then the subgroup `⟨S⟩` lies in `W_N`,
`(1 - w)M ⊆ Z` for every `w ∈ ⟨S⟩`, and `⟨S⟩` is normal in `W_N` when `S` is stable under
conjugation by `W_N` (`ws_βw⁻¹ = s_{wβ}`). -/

omit [Finite W] in
/-- `(1 - s_β)M ⊆ ℤβ` and `±β ∈ N` give `s_β ∈ W_N`. -/
lemma weylIn_of_sub_mem_zmultiples {N : AddSubmonoid M} {s : W} {β : M}
    (hs : ∀ m : M, m - s • m ∈ AddSubgroup.zmultiples β) (hβ : β ∈ N) (hβ' : -β ∈ N) :
    WeylIn N s := by
  intro m
  obtain ⟨n, hn⟩ := hs m
  rw [← hn]
  rcases Int.eq_nat_or_neg n with ⟨j, rfl | rfl⟩
  · simpa using N.nsmul_mem hβ j
  · simpa [neg_smul] using N.nsmul_mem hβ' j

omit [Finite W] in
/-- Elements of `⟨S⟩` move `M` inside `Z`. -/
lemma sub_mem_of_mem_closure {S : Set W} {Z : AddSubgroup M}
    (hS : ∀ s ∈ S, ∀ m : M, m - s • m ∈ Z)
    {w : W} (hw : w ∈ Subgroup.closure S) : ∀ m : M, m - w • m ∈ Z := by
  -- first: elements of `⟨S⟩` stabilize `Z` (for `s⁻¹`: `s⁻¹ z = z - (s⁻¹ z - s(s⁻¹ z))`)
  have hinv : ∀ s ∈ S, ∀ z ∈ Z, s⁻¹ • z ∈ Z := by
    intro s hs z hz
    have := hS s hs (s⁻¹ • z)
    rw [smul_inv_smul] at this
    have h2 : s⁻¹ • z = (s⁻¹ • z - z) + z := by abel
    rw [h2]; exact Z.add_mem (by simpa using this) hz
  induction hw using Subgroup.closure_induction'' with
  | mem s hs => exact hS s hs
  | inv_mem s hs =>
    intro m
    have := hS s hs (s⁻¹ • m)
    rw [smul_inv_smul] at this
    have h2 : m - s⁻¹ • m = -(s⁻¹ • m - m) := by abel
    rw [h2]; exact Z.neg_mem this
  | one => intro m; simp
  | mul v w hv hw ihv ihw =>
    intro m
    have : m - (v * w) • m = (m - v • m) + (v • m - v • (w • m)) := by rw [mul_smul]; abel
    rw [this]
    refine Z.add_mem (ihv m) ?_
    rw [← smul_sub]
    -- `v • Z ⊆ Z`: `v • z = z - (z - v • z)`
    have hz := ihw m
    have : v • (m - w • m) = (m - w • m) - ((m - w • m) - v • (m - w • m)) := by abel
    rw [this]; exact Z.sub_mem hz (ihv _)

/-- **Lemma `lem:weyl-part` (iii), inclusion.** If `Z ⊆ N*`, then `⟨S⟩ ≤ W_N`. -/
lemma closure_le_weylPart {N : AddSubmonoid M} {S : Set W} {Z : AddSubgroup M}
    (hZ : ∀ z ∈ Z, z ∈ N) (hS : ∀ s ∈ S, ∀ m : M, m - s • m ∈ Z) :
    Subgroup.closure S ≤ weylPart N :=
  fun _ hw m => hZ _ (sub_mem_of_mem_closure hS hw m)

/-- **Lemma `lem:weyl-part` (iii), normality.** If `S` is stable under conjugation by `W_N`,
`⟨S⟩` is normal in `W_N`. -/
lemma closure_normal_in_weylPart {N : AddSubmonoid M} {S : Set W}
    (hconj : ∀ v ∈ weylPart N, ∀ s ∈ S, v * s * v⁻¹ ∈ S) :
    ∀ v ∈ weylPart N, ∀ w ∈ Subgroup.closure S, v * w * v⁻¹ ∈ Subgroup.closure S := by
  intro v hv w hw
  have : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj v).toMonoidHom :=
    (Subgroup.closure_le _).2 fun s hs => Subgroup.subset_closure (hconj v hv s hs)
  exact this hw

end AlgMag.Reductive
