/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SelfActionsMain
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Data.ZMod.Basic

/-!
# Self-actions: the remark after Proposition 3.1 and the Examples of §5

Mayeux, *Algebraic magnetism invariants of self-actions of diagonalizable monoid schemes*,
Semigroup Forum 112 (2026) 532–540, doi:10.1007/s00233-025-10572-9 (the published version, read from
the publisher's PDF; numbering and quotations below are those of the journal).

Each example `ex_*` is stated for the monoid ideals, and over an arbitrary scheme `S ≠ ∅`
(`ex_*_scheme`), the two being related by `pureMagnets_scheme`; over a ring use `pureMagnets_ring`.

* `thm46_lifted`: Theorem 4.6 (ii) for `L ⊆ G`, in terms of generators in `L`, as used in the examples.
* `rem31_i`, `rem31_ii`: the conditions of Proposition 3.1 are necessary.
* `ex_i`, `ex_ii`, `ex_iii`, `ex_iv`, `ex_v_equiv`, `ex_v_card`, `ex_vi`, `ex_vi_multiple`, `ex_vi_direct`:
  the computations of `Π(a)` in Examples (i)-(vi) of §5.
* `ex_i_mem`, `ex_i_minimal`, `units_ZN`, `ex_ii_quot`, `ex_iv_units`, `ex_iv_units_equiv`, `ex_iv_quot`,
  `ex_iv_minimal`, `ex_v_notMem`, `ex_vi_singleton`, `ex_vi_direct_step`: the sentences of these examples.
-/

suppress_compilation

open CategoryTheory AlgebraicGeometry Magnetism Set

open scoped Classical

set_option linter.unusedSectionVars false

namespace AlgMag.SelfActions

open AlgMag.GB

section Height

variable {M : Type*} [AddCommMonoid M]

/-- The elements of `E` have height one, so an element of height one of `[A⟩`, `A ⊆ E`, lies in `A`. -/
lemma height_closure (ψ : M →+ ℤ) {A : Set M} (hA : ∀ e ∈ A, ψ e = 1) {x : M}
    (hx : x ∈ AddSubmonoid.closure A) :
    (ψ x = 0 ∧ x = 0) ∨ (1 ≤ ψ x ∧ (ψ x = 1 → x ∈ A)) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => exact Or.inr ⟨(hA x hx).ge, fun _ => hx⟩
  | zero => exact Or.inl ⟨map_zero ψ, rfl⟩
  | add x y _ _ hx hy =>
    rcases hx with ⟨hx, rfl⟩ | ⟨hx, hx'⟩
    · simpa using hy
    · rcases hy with ⟨hy, rfl⟩ | ⟨hy, -⟩
      · simpa using Or.inr ⟨hx, hx'⟩
      · refine Or.inr ⟨by rw [map_add]; omega, fun h => ?_⟩
        rw [map_add] at h
        omega

lemma isMinimalGen_of_height (ψ : M →+ ℤ) {E : Set M} (hE : ∀ e ∈ E, ψ e = 1) : IsMinimalGen E := by
  intro E' hE' e
  obtain ⟨b, hb, hbE'⟩ := exists_of_ssubset hE'
  have hmem : b ∈ AddSubmonoid.closure E' := e ▸ AddSubmonoid.subset_closure hb
  rcases height_closure ψ (fun x hx => hE x (hE'.1 hx)) hmem with ⟨h, -⟩ | ⟨-, h⟩
  · rw [hE b hb] at h
    exact absurd h one_ne_zero
  · exact hbE' (h (hE b hb))

lemma units_bot_of_height (ψ : M →+ ℤ) {E : Set M} (hE : ∀ e ∈ E, ψ e = 1) :
    unitsFace (AddSubmonoid.closure E) = ⊥ := by
  refine le_bot_iff.mp ?_
  rintro x ⟨hx, y, hy, e⟩
  have h0 : ψ x + ψ y = 0 := by rw [← map_add, e, map_zero]
  rcases height_closure ψ hE hx with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · rcases height_closure ψ hE hy with ⟨h', -⟩ | ⟨h', -⟩ <;> omega

lemma image_powerset_singleton (e : M) :
    AddSubmonoid.closure '' 𝒫 ({e} : Set M) = {⊥, AddSubmonoid.closure {e}} := by
  ext N
  constructor
  · rintro ⟨B, hB, rfl⟩
    rcases subset_singleton_iff_eq.1 hB with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨∅, by simp, AddSubmonoid.closure_empty⟩
    · exact ⟨_, mem_powerset (Subset.refl _), rfl⟩

end Height

section Lifted

variable {G : Type*} [AddCommMonoid G] [IsCancelAdd G] (L : AddSubmonoid G)

/-- The preimage in the type `L` of a subset of `G`. -/
abbrev inL (B : Set G) : Set L := {x | (x : G) ∈ B}

lemma map_closure_inL {B : Set G} (hB : B ⊆ L) :
    (AddSubmonoid.closure (inL L B)).map L.subtype = AddSubmonoid.closure B := by
  rw [AddMonoidHom.map_mclosure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hB hx⟩, hx, rfl⟩

lemma map_subtype_units : (unitsOf L).map L.subtype = unitsFace L := by
  ext x
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨-, ⟨v, hv⟩, -, e⟩, rfl⟩
    exact ⟨hu, v, hv, congrArg Subtype.val e⟩
  · rintro ⟨hx, y, hy, e⟩
    exact ⟨⟨x, hx⟩, ⟨trivial, ⟨y, hy⟩, trivial, Subtype.ext e⟩, rfl⟩

/-- `f⁻¹([f(B)⟩)`, read in `G`, is `L^× ⊔ [B⟩`. -/
lemma map_comap_closure_image {B : Set G} (hB : B ⊆ L) :
    ((AddSubmonoid.closure (proj L '' inL L B)).comap (proj L)).map L.subtype =
      unitsFace L ⊔ AddSubmonoid.closure B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change proj L x ∈ AddSubmonoid.closure (proj L '' inL L B) at hx
    rw [← AddMonoidHom.map_mclosure] at hx
    obtain ⟨y, hy, e⟩ := hx
    obtain ⟨u, hu, rfl⟩ := proj_eq_iff.1 e.symm
    have h1 : ((y : L) : G) ∈ AddSubmonoid.closure B := by
      rw [← map_closure_inL L hB]
      exact ⟨y, hy, rfl⟩
    have h2 : ((u : L) : G) ∈ unitsFace L := by
      rw [← map_subtype_units]
      exact ⟨u, hu, rfl⟩
    rw [AddSubmonoid.coe_subtype, AddSubmonoid.coe_add, add_comm]
    exact AddSubmonoid.add_mem_sup h2 h1
  · refine sup_le ?_ (AddSubmonoid.closure_le.mpr fun b hb => ?_)
    · rw [← map_subtype_units]
      exact (AddSubmonoid.gc_map_comap _).monotone_l (units_le_comap _)
    · exact ⟨⟨b, hB hb⟩, AddSubmonoid.subset_closure ⟨⟨b, hB hb⟩, hb, rfl⟩, rfl⟩

/-- **Theorem 4.6 (ii)** for `L ⊆ G`, with generators of `L/L^×` lifted to a subset `C` of `L`:
`Π(a) = {0} ⊔ {L^× ⊔ [B⟩ | B ⊆ C}`. -/
theorem thm46_lifted {C : Set G} (hC : C ⊆ L)
    (hgen : ∀ x ∈ L, ∃ y ∈ AddSubmonoid.closure C, ∃ u ∈ unitsFace L, x = y + u)
    (hmin : ∀ c ∈ C, c ∉ unitsFace L ⊔ AddSubmonoid.closure (C \ {c}))
    (hU : unitsFace L ≠ ⊥) :
    pureMagnets (monIdeal L) =
      {⊥} ∪ (fun B : Set G => unitsFace L ⊔ AddSubmonoid.closure B) '' 𝒫 C := by
  let E : Set (Sharp L) := proj L '' inL L C
  have hE : IsMinimalGen E := by
    intro E' hE' he
    obtain ⟨_, ⟨c, hc, rfl⟩, hcE'⟩ := exists_of_ssubset hE'
    have h1 : proj L c ∈ AddSubmonoid.closure E' := he ▸ AddSubmonoid.subset_closure ⟨c, hc, rfl⟩
    have hsub : E' ⊆ proj L '' inL L (C \ {(c : G)}) := by
      intro z hz
      obtain ⟨d, hd, rfl⟩ := hE'.1 hz
      refine ⟨d, ⟨hd, fun e => hcE' ?_⟩, rfl⟩
      have : d = c := Subtype.ext e
      exact this ▸ hz
    have h2 := AddSubmonoid.closure_mono hsub h1
    have hB : C \ {(c : G)} ⊆ L := fun x hx => hC hx.1
    have h3 : ((c : L) : G) ∈ unitsFace L ⊔ AddSubmonoid.closure (C \ {(c : G)}) := by
      rw [← map_comap_closure_image L hB]
      exact ⟨c, h2, rfl⟩
    exact hmin c hc h3
  have hgenE : AddSubmonoid.closure E = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨x, rfl⟩ := proj_surjective z
    obtain ⟨y, hy, u, hu, e⟩ := hgen x x.2
    rw [← map_closure_inL L hC] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_subtype_units] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have e' : x = y' + u' := Subtype.ext e
    rw [e', map_add, proj_unit hu', add_zero, ← AddMonoidHom.map_mclosure]
    exact ⟨y', hy', rfl⟩
  have hU' : unitsOf L ≠ ⊥ := by
    intro h
    apply hU
    rw [← map_subtype_units, h, AddSubmonoid.map_bot]
  rw [pureMagnets_subtype L, thm46_ii hE hgenE hU', image_union, image_singleton,
    AddSubmonoid.map_bot, image_image]
  congr 1
  ext K
  constructor
  · rintro ⟨B', hB', rfl⟩
    let B : Set G := Subtype.val '' {x : L | x ∈ inL L C ∧ proj L x ∈ B'}
    have hBC : B ⊆ C := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    have hBL : B ⊆ L := hBC.trans hC
    have e : proj L '' inL L B = B' := by
      ext z
      constructor
      · rintro ⟨x, ⟨y, hy, hyx⟩, rfl⟩
        have : y = x := Subtype.ext hyx
        exact this ▸ hy.2
      · intro hz
        obtain ⟨x, hx, rfl⟩ := hB' hz
        exact ⟨x, ⟨x, ⟨hx, hz⟩, rfl⟩, rfl⟩
    refine ⟨B, hBC, ?_⟩
    change unitsFace L ⊔ AddSubmonoid.closure B =
      ((AddSubmonoid.closure B').comap (proj L)).map L.subtype
    rw [← map_comap_closure_image L hBL, e]
  · rintro ⟨B, hB, rfl⟩
    have hBL : B ⊆ L := (show B ⊆ C from hB).trans hC
    refine ⟨proj L '' inL L B, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, (show B ⊆ C from hB) hx, rfl⟩
    · exact map_comap_closure_image L hBL

end Lifted

section Remark

/-- **Comment after Proposition 3.1** (journal p. 536): "The second is also necessary, indeed let
`M = ℤ` and `E = {-1, 1}`." Condition (i) holds and `Π(a) = {0, ℤ}` has two elements, not four. -/
theorem rem31_ii :
    IsMinimalGen ({-1, 1} : Set ℤ) ∧ AddSubmonoid.closure ({-1, 1} : Set ℤ) = ⊤ ∧
      pureMagnets (monIdeal (⊤ : AddSubmonoid ℤ)) = {⊥, ⊤} ∧
      AddSubmonoid.closure {(1 : ℤ)} ∉ pureMagnets (monIdeal (⊤ : AddSubmonoid ℤ)) := by
  have hpure := lemma41_pure (G := ℤ)
  have hnn : ∀ x ∈ AddSubmonoid.closure {(1 : ℤ)}, 0 ≤ x := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rw [mem_singleton_iff.mp hx]; exact zero_le_one
    | zero => exact le_rfl
    | add x y _ _ hx hy => exact add_nonneg hx hy
  have hnp : ∀ x ∈ AddSubmonoid.closure {(-1 : ℤ)}, x ≤ 0 := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rw [mem_singleton_iff.mp hx]; omega
    | zero => exact le_rfl
    | add x y _ _ hx hy => omega
  refine ⟨?_, ?_, hpure, ?_⟩
  · intro E' hE' e
    have hm1 : (-1 : ℤ) ∈ AddSubmonoid.closure E' := e ▸ AddSubmonoid.subset_closure (by simp)
    have hp1 : (1 : ℤ) ∈ AddSubmonoid.closure E' := e ▸ AddSubmonoid.subset_closure (by simp)
    obtain ⟨b, hb, hbE'⟩ := exists_of_ssubset hE'
    rcases hb with rfl | hb
    · have hle : AddSubmonoid.closure E' ≤ AddSubmonoid.closure {(1 : ℤ)} :=
        AddSubmonoid.closure_mono fun x hx => by
          rcases hE'.1 hx with rfl | h
          · exact absurd hx hbE'
          · exact h
      have := hnn _ (hle hm1)
      omega
    · rw [mem_singleton_iff.mp hb] at hbE'
      have hle : AddSubmonoid.closure E' ≤ AddSubmonoid.closure {(-1 : ℤ)} :=
        AddSubmonoid.closure_mono fun x hx => by
          rcases hE'.1 hx with h | h
          · exact h
          · rw [mem_singleton_iff.mp h] at hx
            exact absurd hx hbE'
      have := hnp _ (hle hp1)
      omega
  · refine top_le_iff.mp fun x _ => ?_
    have hm : (-1 : ℤ) ∈ AddSubmonoid.closure ({-1, 1} : Set ℤ) := AddSubmonoid.subset_closure (by simp)
    have hp : (1 : ℤ) ∈ AddSubmonoid.closure ({-1, 1} : Set ℤ) := AddSubmonoid.subset_closure (by simp)
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg x
    · simpa using nsmul_mem hp k
    · simpa using nsmul_mem hm k
  · rw [hpure]
    rintro (h | h)
    · have : (1 : ℤ) ∈ (⊥ : AddSubmonoid ℤ) := h ▸ AddSubmonoid.subset_closure rfl
      simp at this
    · have : (-1 : ℤ) ∈ AddSubmonoid.closure {(1 : ℤ)} := by
        rw [mem_singleton_iff.mp h]
        trivial
      have := hnn _ this
      omega

/-- **Comment after Proposition 3.1** (journal p. 536): "The first condition is of course necessary."
The journal gives no example; for `E = {1, 2} ⊆ ℕ`, condition (ii) holds, but `[{2}⟩` is not a pure
magnet and `Π(a) = {0, ℕ}`. -/
theorem rem31_i :
    unitsFace (AddSubmonoid.closure ({1, 2} : Set ℕ)) = ⊥ ∧
      AddSubmonoid.closure ({1, 2} : Set ℕ) = AddSubmonoid.closure {1} ∧
      pureMagnets (monIdeal (AddSubmonoid.closure ({1, 2} : Set ℕ))) =
        {⊥, AddSubmonoid.closure {1}} ∧
      AddSubmonoid.closure {2} ∉ pureMagnets (monIdeal (AddSubmonoid.closure ({1, 2} : Set ℕ))) := by
  have hcl : AddSubmonoid.closure ({1, 2} : Set ℕ) = AddSubmonoid.closure {1} := by
    refine le_antisymm (AddSubmonoid.closure_le.mpr ?_) (AddSubmonoid.closure_mono (by simp))
    rintro x (rfl | hx)
    · exact AddSubmonoid.subset_closure rfl
    · rw [mem_singleton_iff.mp hx]
      exact add_mem (AddSubmonoid.subset_closure rfl : (1 : ℕ) ∈ AddSubmonoid.closure {1})
        (AddSubmonoid.subset_closure rfl)
  have hsharp : ∀ L : AddSubmonoid ℕ, unitsFace L = ⊥ := fun L => by
    refine le_bot_iff.mp ?_
    rintro x ⟨-, y, -, e⟩
    exact Nat.eq_zero_of_add_eq_zero_right e
  have h1 : IsMinimalGen ({1} : Set ℕ) := isMinimalGen_of_height (Nat.castAddMonoidHom ℤ) (by simp)
  have hp : pureMagnets (monIdeal (AddSubmonoid.closure ({1, 2} : Set ℕ))) =
      {⊥, AddSubmonoid.closure {1}} := by
    rw [hcl, prop31 h1 (hsharp _), image_powerset_singleton]
  refine ⟨hsharp _, hcl, hp, ?_⟩
  rw [hp]
  have h2 : ∀ x ∈ AddSubmonoid.closure {(2 : ℕ)}, 2 ∣ x := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rw [mem_singleton_iff.mp hx]
    | zero => exact dvd_zero 2
    | add x y _ _ hx hy => exact dvd_add hx hy
  rintro (h | h)
  · have : (2 : ℕ) ∈ (⊥ : AddSubmonoid ℕ) := h ▸ AddSubmonoid.subset_closure rfl
    simp at this
  · have : (1 : ℕ) ∈ AddSubmonoid.closure {(2 : ℕ)} := h ▸ AddSubmonoid.subset_closure rfl
    have := h2 _ this
    omega

end Remark

/-- `f : M → M/M^×` is the quotient by the fibres of a surjective morphism `φ : M → Q` killing `M^×`,
whose fibres are the `M^×`-orbits. Used for the isomorphisms `N/N^* ≃ …` of Examples (ii), (iv). -/
def sharpEquivOfHom {M Q : Type*} [AddCommMonoid M] [AddCommMonoid Q] (φ : M →+ Q)
    (hs : Function.Surjective φ) (h0 : ∀ u ∈ unitsOf M, φ u = 0)
    (hf : ∀ x y, φ x = φ y → ∃ u ∈ unitsOf M, x = y + u) : Sharp M ≃+ Q :=
  let H : unitCon M ≤ AddCon.ker φ := by
    rintro x y ⟨u, hu, rfl⟩
    change φ _ = φ _
    rw [map_add, h0 u hu, add_zero]
  AddEquiv.ofBijective ((unitCon M).lift φ H) ⟨by
      intro a b e
      obtain ⟨x, rfl⟩ := proj_surjective a
      obtain ⟨y, rfl⟩ := proj_surjective b
      exact proj_eq_iff.2 (hf x y e), fun q => by
      obtain ⟨x, rfl⟩ := hs q
      exact ⟨proj M x, rfl⟩⟩

section Ex1

/-- **Example (i)**: `ℕ ⊂ ℤ` is `[1⟩`. -/
theorem ex_i_mem (x : ℤ) : x ∈ AddSubmonoid.closure ({1} : Set ℤ) ↔ 0 ≤ x := by
  constructor
  · intro hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rw [mem_singleton_iff.mp hx]; exact zero_le_one
    | zero => exact le_rfl
    | add x y _ _ hx hy => exact add_nonneg hx hy
  · intro hx
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    simpa using nsmul_mem (AddSubmonoid.subset_closure rfl :
      (1 : ℤ) ∈ AddSubmonoid.closure ({1} : Set ℤ)) k

/-- **Example (i)**: "`ℕ` is sharp and `{1}` is the minimal set generating `ℕ`". -/
theorem ex_i_minimal :
    unitsFace (AddSubmonoid.closure ({1} : Set ℤ)) = ⊥ ∧ IsMinimalGen ({1} : Set ℤ) := by
  have hE : ∀ e ∈ ({1} : Set ℤ), AddMonoidHom.id ℤ e = 1 := by simp
  exact ⟨units_bot_of_height _ hE, isMinimalGen_of_height _ hE⟩

/-- **Example (i)**: for `D(ℤ)` acting on `𝔸(ℕ)`, `ℕ = [1⟩ ⊆ ℤ`, one has `Π(a) = {0, ℕ}`. -/
theorem ex_i :
    pureMagnets (monIdeal (AddSubmonoid.closure ({1} : Set ℤ))) =
      {⊥, AddSubmonoid.closure {1}} := by
  have hE : ∀ e ∈ ({1} : Set ℤ), AddMonoidHom.id ℤ e = 1 := by simp
  rw [prop31 (isMinimalGen_of_height _ hE) (units_bot_of_height _ hE), image_powerset_singleton]

theorem ex_i_scheme {S : Scheme.{0}} [Nonempty S] :
    PiS (AddSubmonoid.closure ({1} : Set ℤ)) S = {⊥, AddSubmonoid.closure {1}} := by
  rw [PiS, pureMagnets_scheme, ex_i]

end Ex1

section Ex2

/-- `ℤ × ℕ ⊆ ℤ × ℤ`. -/
def ZN : AddSubmonoid (ℤ × ℤ) where
  carrier := {x | 0 ≤ x.2}
  zero_mem' := le_refl (0 : ℤ)
  add_mem' {a b} ha hb := show (0 : ℤ) ≤ a.2 + b.2 from add_nonneg ha hb

/-- `ℤ × 0 ⊆ ℤ × ℤ`. -/
def Z0 : AddSubmonoid (ℤ × ℤ) where
  carrier := {x | x.2 = 0}
  zero_mem' := rfl
  add_mem' {a b} ha hb := by
    change a.2 + b.2 = 0
    rw [show a.2 = 0 from ha, show b.2 = 0 from hb, add_zero]

/-- `0 × ℕ ⊆ ℤ × ℤ`. -/
def ZeroN : AddSubmonoid (ℤ × ℤ) where
  carrier := {x | x.1 = 0 ∧ 0 ≤ x.2}
  zero_mem' := ⟨rfl, le_rfl⟩
  add_mem' {a b} ha hb := ⟨by
    change a.1 + b.1 = 0
    rw [ha.1, hb.1, add_zero], show (0 : ℤ) ≤ a.2 + b.2 from add_nonneg ha.2 hb.2⟩

lemma units_ZN : unitsFace ZN = Z0 := by
  ext x
  constructor
  · rintro ⟨hx, y, hy, e⟩
    have h1 := congrArg Prod.snd e
    have h2 : (0 : ℤ) ≤ x.2 := hx
    have h3 : (0 : ℤ) ≤ y.2 := hy
    change x.2 = 0
    simp only [Prod.snd_add, Prod.snd_zero] at h1
    omega
  · intro hx
    have h2 : x.2 = 0 := hx
    refine ⟨h2.ge, -x, ?_, by simp⟩
    change (0 : ℤ) ≤ (-x).2
    simp [h2]

/-- **Example (ii)**: `(ℤ × ℕ)/(ℤ × ℕ)^* ≃ ℕ`. -/
def ex_ii_quot : Sharp ZN ≃+ ℕ :=
  sharpEquivOfHom
    { toFun := fun x => (x.1.2).toNat
      map_zero' := rfl
      map_add' := fun x y => Int.toNat_add x.2 y.2 }
    (fun n => ⟨⟨(0, (n : ℤ)), show (0 : ℤ) ≤ n from Int.natCast_nonneg n⟩, by simp⟩)
    (by
      rintro ⟨u, hu⟩ h
      have h1 : (u : ℤ × ℤ) ∈ unitsFace ZN := by
        rw [← map_subtype_units]
        exact ⟨⟨u, hu⟩, h, rfl⟩
      rw [units_ZN] at h1
      have h2 : u.2 = 0 := h1
      simp [h2])
    (by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ e
      have hx' : (0 : ℤ) ≤ x.2 := hx
      have hy' : (0 : ℤ) ≤ y.2 := hy
      have e' : x.2 = y.2 := by
        have : (x.2).toNat = (y.2).toNat := e
        omega
      have hz : ((x.1 - y.1, (0 : ℤ)) : ℤ × ℤ) ∈ unitsFace ZN := by
        rw [units_ZN]
        exact rfl
      rw [← map_subtype_units] at hz
      obtain ⟨u, hu, hue⟩ := hz
      refine ⟨u, hu, Subtype.ext ?_⟩
      rw [AddSubmonoid.coe_add]
      change _ = y + (u : ℤ × ℤ)
      have : (u : ℤ × ℤ) = (x.1 - y.1, 0) := hue
      rw [this]
      ext <;> simp [e'])

/-- **Example (ii)**: for `D(ℤ × ℤ)` acting on `𝔸(ℤ × ℕ)`, one has
`Π(a) = {0, ℤ × 0, ℤ × ℕ}` (printed: `{0, ℤ, ℤ × ℕ}`). -/
theorem ex_ii : pureMagnets (monIdeal ZN) = {⊥, Z0, ZN} := by
  have hC : ({((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ)) ⊆ ZN := by
    rintro _ rfl
    exact (zero_le_one : (0 : ℤ) ≤ 1)
  have hcl : ∀ b : ℕ, ((0 : ℤ), (b : ℤ)) ∈ AddSubmonoid.closure ({((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ)) := by
    intro b
    have := nsmul_mem (AddSubmonoid.subset_closure rfl :
      ((0 : ℤ), (1 : ℤ)) ∈ AddSubmonoid.closure ({((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ))) b
    simpa using this
  have htop : Z0 ⊔ AddSubmonoid.closure ({((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ)) = ZN := by
    apply le_antisymm
    · refine sup_le (fun x hx => ?_) (AddSubmonoid.closure_le.mpr hC)
      exact (show x.2 = 0 from hx).ge
    · intro x hx
      obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ x.2 from hx)
      have e : x = (x.1, 0) + (0, (b : ℤ)) := by
        ext <;> simp [hb]
      rw [e]
      exact AddSubmonoid.add_mem_sup (show ((x.1, 0) : ℤ × ℤ).2 = 0 from rfl) (hcl b)
  rw [thm46_lifted ZN hC ?_ ?_ ?_, units_ZN]
  · ext K
    simp only [mem_union, mem_singleton_iff, mem_image, mem_insert_iff]
    constructor
    · rintro (rfl | ⟨B, hB, rfl⟩)
      · exact Or.inl rfl
      · rcases subset_singleton_iff_eq.1 hB with rfl | rfl
        · exact Or.inr (Or.inl (by simp))
        · exact Or.inr (Or.inr htop)
    · rintro (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨∅, by simp, by simp⟩
      · exact Or.inr ⟨_, mem_powerset (Subset.refl _), htop⟩
  · intro x hx
    obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ x.2 from hx)
    refine ⟨(0, (b : ℤ)), hcl b, (x.1, 0), ?_, ?_⟩
    · rw [units_ZN]
      exact rfl
    · ext <;> simp [hb]
  · rintro c rfl hc
    rw [units_ZN, Set.sdiff_self, AddSubmonoid.closure_empty, sup_bot_eq] at hc
    exact one_ne_zero (show (1 : ℤ) = 0 from hc)
  · rw [units_ZN]
    intro h
    have : (((1 : ℤ), (0 : ℤ))) ∈ (⊥ : AddSubmonoid (ℤ × ℤ)) := h ▸ (rfl : ((1 : ℤ), (0 : ℤ)).2 = 0)
    simp at this

/-- **Example (ii)**: `𝔸(ℤ × ℕ)^{0 × ℕ} = ∅`, as `0 × ℕ` does not contain `(ℤ × ℕ)^×`: `J = 1`. -/
theorem ex_ii_zero_mem : ((0 : ℤ × ℤ)) ∈ monIdeal ZN ZeroN := by
  refine ⟨(1, 0), (le_refl (0 : ℤ)), fun h => one_ne_zero h.1, (-1, 0), (le_refl (0 : ℤ)), by ext <;> simp⟩

theorem ex_ii_empty {S : Scheme.{0}} : IsEmpty (Zatt (aAction ZN S) ZeroN).left :=
  isEmpty_Zatt_of_zero_mem _ ex_ii_zero_mem

/-- **Example (ii)**: `0 × ℕ` is not a pure magnet. -/
theorem ex_ii_not_pure : ZeroN ∉ pureMagnets (monIdeal ZN) := by
  rw [ex_ii]
  have h01 : ((0 : ℤ), (1 : ℤ)) ∈ ZeroN := ⟨rfl, zero_le_one⟩
  rintro (h | h | h)
  · rw [h] at h01
    simp at h01
  · rw [h] at h01
    exact one_ne_zero (show (1 : ℤ) = 0 from h01)
  · have : ((1 : ℤ), (0 : ℤ)) ∈ ZeroN := by
      rw [h]
      exact le_refl (0 : ℤ)
    exact one_ne_zero this.1

theorem ex_ii_scheme {S : Scheme.{0}} [Nonempty S] : PiS ZN S = {⊥, Z0, ZN} := by
  rw [PiS, pureMagnets_scheme, ex_ii]

end Ex2

section Ex3

/-- The set `{(1, -1), (1, 0), (1, 1)}`. -/
def E3 : Set (ℤ × ℤ) := {(1, -1), (1, 0), (1, 1)}

lemma E3_height : ∀ e ∈ E3, AddMonoidHom.fst ℤ ℤ e = 1 := by
  rintro e (rfl | rfl | rfl) <;> rfl

lemma E3_card : Cardinal.mk E3 = 3 := by
  let F : Finset (ℤ × ℤ) := {(1, -1), (1, 0), (1, 1)}
  have h : E3 = (F : Set (ℤ × ℤ)) := by
    simp [E3, F]
  have hc : F.card = 3 := by decide
  have hm : Cardinal.mk (F : Set (ℤ × ℤ)) = (F.card : Cardinal) := by
    simp
  rw [h, hm, hc]
  rfl

/-- **Example (iii)**: the "independence" of the printed sentence is the monoid-theoretic one, that no
element of `E` lies in the submonoid generated by the others; the vectors are `ℤ`-linearly dependent. -/
theorem ex_iii_independent :
    (∀ e ∈ E3, e ∉ AddSubmonoid.closure (E3 \ {e})) ∧
      ((1, -1) : ℤ × ℤ) + (1, 1) = 2 • ((1, 0) : ℤ × ℤ) :=
  ⟨fun _ he => (isMinimalGen_of_height _ E3_height).notMem_closure_diff he, by decide⟩

/-- **Example (iii)**: for `D(ℤ²)` acting on `𝔸([(1, -1), (1, 0), (1, 1)⟩)`, `#Π(a) = 2³`. -/
theorem ex_iii : Cardinal.mk (pureMagnets (monIdeal (AddSubmonoid.closure E3))) = 2 ^ 3 := by
  rw [prop31_card (isMinimalGen_of_height _ E3_height) (units_bot_of_height _ E3_height), E3_card]
  norm_cast

theorem ex_iii_scheme {S : Scheme.{0}} [Nonempty S] :
    Cardinal.mk (PiS (AddSubmonoid.closure E3) S) = 2 ^ 3 := by
  rw [PiS, pureMagnets_scheme, ex_iii]

end Ex3

section Ex4

/-- The submonoid `N = [(0, 1̄), (2, 0), (3, 1̄)⟩` of `ℤ × ℤ/2`. -/
def N4 : AddSubmonoid (ℤ × ZMod 2) := AddSubmonoid.closure {(0, 1), (2, 0), (3, 1)}

/-- The submonoid `[(0, 1̄)⟩ = {(0, 0), (0, 1̄)}`. -/
def U4 : AddSubmonoid (ℤ × ZMod 2) := AddSubmonoid.closure {(0, 1)}

lemma mem_U4 {x : ℤ × ZMod 2} (hx : x ∈ U4) : x.1 = 0 := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => rw [mem_singleton_iff.mp hx]
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]

lemma mem_U4_of {x : ℤ × ZMod 2} (hx : x.1 = 0) : x ∈ U4 := by
  obtain ⟨a, b⟩ := x
  change a = 0 at hx
  subst hx
  have h1 : ((0 : ℤ), (1 : ZMod 2)) ∈ U4 := AddSubmonoid.subset_closure rfl
  revert b
  have : ∀ b : ZMod 2, ((0 : ℤ), b) ∈ U4 := by
    intro b
    fin_cases b
    · exact zero_mem _
    · exact h1
  exact this

lemma N4_nonneg {x : ℤ × ZMod 2} (hx : x ∈ N4) : 0 ≤ x.1 ∧ x.1 ≠ 1 := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => rcases hx with rfl | rfl | rfl <;> simp
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Prod.fst_add]
    obtain ⟨h1, h2⟩ := hx
    obtain ⟨h3, h4⟩ := hy
    omega

lemma U4_le_N4 : U4 ≤ N4 := AddSubmonoid.closure_mono (by simp)

lemma units_N4 : unitsFace N4 = U4 := by
  ext x
  constructor
  · rintro ⟨hx, y, hy, e⟩
    have h1 := congrArg Prod.fst e
    simp only [Prod.fst_add, Prod.fst_zero] at h1
    have := (N4_nonneg hx).1
    have := (N4_nonneg hy).1
    exact mem_U4_of (by omega)
  · intro hx
    refine ⟨U4_le_N4 hx, x, U4_le_N4 hx, ?_⟩
    ext
    · simp [mem_U4 hx]
    · change x.2 + x.2 = 0
      exact CharTwo.add_self_eq_zero x.2

/-- **Example (iv)**: `N^* = {(0, 0), (0, 1̄)}`. -/
theorem ex_iv_units : (unitsFace N4 : Set (ℤ × ZMod 2)) = {(0, 0), (0, 1)} := by
  rw [units_N4]
  ext ⟨a, b⟩
  simp only [SetLike.mem_coe, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · intro h
    have h1 : a = 0 := mem_U4 h
    have h2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h2 b with h3 | h3
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr ⟨h1, h3⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact mem_U4_of h

/-- **Example (iv)**: `N^* ≅ ℤ/2ℤ`. -/
def ex_iv_units_equiv : unitsFace N4 ≃+ ZMod 2 where
  toFun x := (x : ℤ × ZMod 2).2
  invFun b := ⟨(0, b), by rw [units_N4]; exact mem_U4_of rfl⟩
  left_inv := by
    rintro ⟨x, hx⟩
    rw [units_N4] at hx
    exact Subtype.ext (Prod.ext (mem_U4 hx).symm rfl)
  right_inv _ := rfl
  map_add' _ _ := rfl

lemma N4_toNat {x : ℤ × ZMod 2} (hx : x ∈ N4) :
    (x.1).toNat ∈ AddSubmonoid.closure ({2, 3} : Set ℕ) := by
  have h2 : (2 : ℕ) ∈ AddSubmonoid.closure ({2, 3} : Set ℕ) :=
    AddSubmonoid.subset_closure (Or.inl rfl)
  have h3 : (3 : ℕ) ∈ AddSubmonoid.closure ({2, 3} : Set ℕ) :=
    AddSubmonoid.subset_closure (Or.inr rfl)
  have key : 0 ≤ x.1 ∧ (x.1).toNat ∈ AddSubmonoid.closure ({2, 3} : Set ℕ) := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact ⟨le_rfl, zero_mem _⟩
      · exact ⟨by simp, h2⟩
      · exact ⟨by simp, h3⟩
    | zero => exact ⟨le_rfl, zero_mem _⟩
    | add x y _ _ hx hy =>
      refine ⟨add_nonneg hx.1 hy.1, ?_⟩
      have : ((x + y).1).toNat = (x.1).toNat + (y.1).toNat := Int.toNat_add hx.1 hy.1
      rw [this]
      exact add_mem hx.2 hy.2
  exact key.2

/-- `N → [2, 3⟩`, `(a, b) ↦ a`. -/
def phi4 : N4 →+ AddSubmonoid.closure ({2, 3} : Set ℕ) where
  toFun x := ⟨(x.1.1).toNat, N4_toNat x.2⟩
  map_zero' := rfl
  map_add' x y := Subtype.ext (Int.toNat_add (N4_nonneg x.2).1 (N4_nonneg y.2).1)

/-- **Example (iv)**: `N/N^* ≃ [2, 3⟩ ⊂ ℕ`. -/
def ex_iv_quot : Sharp N4 ≃+ AddSubmonoid.closure ({2, 3} : Set ℕ) :=
  sharpEquivOfHom phi4
    (by
      rintro ⟨q, hq⟩
      have key : ∃ x ∈ N4, (x : ℤ × ZMod 2).1 = (q : ℤ) := by
        induction hq using AddSubmonoid.closure_induction with
        | mem q hq =>
          rcases hq with rfl | hq
          · exact ⟨(2, 0), AddSubmonoid.subset_closure (Or.inr (Or.inl rfl)), rfl⟩
          · rw [mem_singleton_iff.mp hq]
            exact ⟨(3, 1), AddSubmonoid.subset_closure (Or.inr (Or.inr rfl)), rfl⟩
        | zero => exact ⟨0, zero_mem _, rfl⟩
        | add p q _ _ hp hq =>
          obtain ⟨x, hx, ex⟩ := hp
          obtain ⟨y, hy, ey⟩ := hq
          exact ⟨x + y, add_mem hx hy, by simp [ex, ey]⟩
      obtain ⟨x, hx, ex⟩ := key
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      change (x.1).toNat = q
      rw [ex]
      simp)
    (by
      rintro ⟨u, hu⟩ h
      have h1 : (u : ℤ × ZMod 2) ∈ unitsFace N4 := by
        rw [← map_subtype_units]
        exact ⟨⟨u, hu⟩, h, rfl⟩
      rw [units_N4] at h1
      refine Subtype.ext ?_
      change (u.1).toNat = 0
      rw [mem_U4 h1]
      rfl)
    (by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ e
      have e1 : (x.1).toNat = (y.1).toNat := congrArg Subtype.val e
      have hx' := (N4_nonneg hx).1
      have hy' := (N4_nonneg hy).1
      have e2 : x.1 = y.1 := by omega
      have hz : ((0, x.2 - y.2) : ℤ × ZMod 2) ∈ unitsFace N4 := by
        rw [units_N4]
        exact mem_U4_of rfl
      rw [← map_subtype_units] at hz
      obtain ⟨u, hu, hue⟩ := hz
      refine ⟨u, hu, Subtype.ext ?_⟩
      rw [AddSubmonoid.coe_add]
      change x = y + (u : ℤ × ZMod 2)
      have : (u : ℤ × ZMod 2) = (0, x.2 - y.2) := hue
      rw [this]
      ext <;> simp [e2])

/-- **Example (iv)**: "The set `{2, 3}` is a minimal generating set of `N/N^* ≃ [2, 3⟩`". -/
theorem ex_iv_minimal : IsMinimalGen ({2, 3} : Set ℕ) := by
  have hmul : ∀ {d x : ℕ}, x ∈ AddSubmonoid.closure ({d} : Set ℕ) → d ∣ x := by
    intro d x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rw [mem_singleton_iff.mp hx]
    | zero => exact dvd_zero d
    | add x y _ _ hx hy => exact dvd_add hx hy
  refine isMinimalGen_of_notMem ?_
  rintro b (rfl | hb) h
  · have e : ({2, 3} : Set ℕ) \ {2} ⊆ {3} := by
      rintro x ⟨rfl | hx, hne⟩
      · exact absurd rfl hne
      · exact hx
    have := hmul (AddSubmonoid.closure_mono e h)
    omega
  · rw [mem_singleton_iff.mp hb] at h
    have e : ({2, 3} : Set ℕ) \ {3} ⊆ {2} := by
      rintro x ⟨rfl | hx, hne⟩
      · rfl
      · exact absurd hx hne
    have := hmul (AddSubmonoid.closure_mono e h)
    omega

/-- The lifts `(2, 0)`, `(3, 1̄)` of the generators `2, 3` of `N/N^× ≃ [2, 3⟩`. -/
def C4 : Set (ℤ × ZMod 2) := {(2, 0), (3, 1)}

lemma mem_mult {d : ℤ} {c : ZMod 2} {x : ℤ × ZMod 2}
    (hx : x ∈ U4 ⊔ AddSubmonoid.closure {(d, c)}) : d ∣ x.1 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := AddSubmonoid.mem_sup.mp hx
  simp only [Prod.fst_add, mem_U4 hu, zero_add]
  clear hx
  induction hv using AddSubmonoid.closure_induction with
  | mem x hx => rw [mem_singleton_iff.mp hx]
  | zero => exact dvd_zero d
  | add x y _ _ hx hy => exact dvd_add hx hy

lemma N4_eq_sup : ∀ x ∈ N4, ∃ y ∈ AddSubmonoid.closure C4, ∃ u ∈ U4, x = y + u := by
  intro x hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, zero_mem _, _, AddSubmonoid.subset_closure rfl, by simp⟩
    · exact ⟨_, AddSubmonoid.subset_closure (Or.inl rfl), 0, zero_mem _, by simp⟩
    · exact ⟨_, AddSubmonoid.subset_closure (Or.inr rfl), 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, u, hu, rfl⟩ := hx
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, u + v, add_mem hu hv, by abel⟩

lemma C4_sdiff_left : C4 \ {((2 : ℤ), (0 : ZMod 2))} = {((3 : ℤ), (1 : ZMod 2))} := by
  ext x
  constructor
  · rintro ⟨rfl | hx, hne⟩
    · exact absurd rfl hne
    · exact hx
  · rintro rfl
    refine ⟨Or.inr rfl, fun h => ?_⟩
    have := congrArg Prod.fst (mem_singleton_iff.mp h)
    simp at this

lemma C4_sdiff_right : C4 \ {((3 : ℤ), (1 : ZMod 2))} = {((2 : ℤ), (0 : ZMod 2))} := by
  ext x
  constructor
  · rintro ⟨rfl | hx, hne⟩
    · rfl
    · exact absurd hx hne
  · rintro rfl
    refine ⟨Or.inl rfl, fun h => ?_⟩
    have := congrArg Prod.fst (mem_singleton_iff.mp h)
    simp at this

/-- **Example (iv)**: for `D(ℤ × ℤ/2)` acting on `𝔸(N)`, `N = [(0, 1̄), (2, 0), (3, 1̄)⟩`, one has
`Π(a) = {0, [(0, 1̄)⟩, [(0, 1̄), (2, 0)⟩, [(0, 1̄), (3, 0)⟩, N}`. -/
theorem ex_iv : pureMagnets (monIdeal N4) =
    {⊥, AddSubmonoid.closure {(0, 1)}, AddSubmonoid.closure {(0, 1), (2, 0)},
      AddSubmonoid.closure {(0, 1), (3, 0)}, N4} := by
  have hC : C4 ⊆ N4 := by
    rintro _ (rfl | rfl)
    · exact AddSubmonoid.subset_closure (Or.inr (Or.inl rfl))
    · exact AddSubmonoid.subset_closure (Or.inr (Or.inr rfl))
  have hne : unitsFace N4 ≠ ⊥ := by
    rw [units_N4]
    intro h
    have h1 : ((0 : ℤ), (1 : ZMod 2)) ∈ (⊥ : AddSubmonoid (ℤ × ZMod 2)) :=
      h ▸ (AddSubmonoid.subset_closure rfl : ((0 : ℤ), (1 : ZMod 2)) ∈ U4)
    have := congrArg Prod.snd (AddSubmonoid.mem_bot.mp h1)
    simp at this
  have e0 : U4 ⊔ AddSubmonoid.closure (∅ : Set (ℤ × ZMod 2)) = AddSubmonoid.closure {(0, 1)} := by
    simp [U4]
  have e2 : U4 ⊔ AddSubmonoid.closure {((2 : ℤ), (0 : ZMod 2))} =
      AddSubmonoid.closure {(0, 1), (2, 0)} := by
    rw [U4, ← AddSubmonoid.closure_union]
    rfl
  have e3 : U4 ⊔ AddSubmonoid.closure {((3 : ℤ), (1 : ZMod 2))} =
      AddSubmonoid.closure {(0, 1), (3, 0)} := by
    have h01 : ((0 : ℤ), (1 : ZMod 2)) ∈ AddSubmonoid.closure {((0 : ℤ), (1 : ZMod 2)), (3, 0)} :=
      AddSubmonoid.subset_closure (Or.inl rfl)
    have h30 : ((3 : ℤ), (0 : ZMod 2)) ∈ AddSubmonoid.closure {((0 : ℤ), (1 : ZMod 2)), (3, 0)} :=
      AddSubmonoid.subset_closure (Or.inr rfl)
    apply le_antisymm
    · refine sup_le (AddSubmonoid.closure_mono (by simp)) (AddSubmonoid.closure_le.mpr ?_)
      rintro _ rfl
      have : ((3 : ℤ), (1 : ZMod 2)) = (0, 1) + (3, 0) := by ext <;> simp
      rw [this]
      exact add_mem h01 h30
    · refine AddSubmonoid.closure_le.mpr ?_
      rintro _ (rfl | hx)
      · exact AddSubmonoid.mem_sup_left (AddSubmonoid.subset_closure rfl)
      · rw [mem_singleton_iff.mp hx]
        have : ((3 : ℤ), (0 : ZMod 2)) = (0, 1) + (3, 1) := by
          ext
          · simp
          · exact (CharTwo.add_self_eq_zero (1 : ZMod 2)).symm
        rw [this]
        exact AddSubmonoid.add_mem_sup (AddSubmonoid.subset_closure rfl)
          (AddSubmonoid.subset_closure rfl)
  have e4 : U4 ⊔ AddSubmonoid.closure C4 = N4 := by
    apply le_antisymm
    · exact sup_le U4_le_N4 (AddSubmonoid.closure_le.mpr hC)
    · intro x hx
      obtain ⟨y, hy, u, hu, rfl⟩ := N4_eq_sup x hx
      rw [add_comm]
      exact AddSubmonoid.add_mem_sup hu hy
  rw [thm46_lifted N4 hC ?_ ?_ hne, units_N4]
  · ext K
    simp only [mem_union, mem_singleton_iff, mem_image, mem_insert_iff]
    constructor
    · rintro (rfl | ⟨B, hB, rfl⟩)
      · exact Or.inl rfl
      · rcases subset_pair_iff_eq.1 hB with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl e0)
        · exact Or.inr (Or.inr (Or.inl e2))
        · exact Or.inr (Or.inr (Or.inr (Or.inl e3)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr e4)))
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨∅, by simp, e0⟩
      · exact Or.inr ⟨{(2, 0)}, by simp [C4], e2⟩
      · exact Or.inr ⟨{(3, 1)}, by simp [C4], e3⟩
      · exact Or.inr ⟨C4, mem_powerset (Subset.refl _), e4⟩
  · intro x hx
    rw [units_N4]
    exact N4_eq_sup x hx
  · rw [units_N4]
    rintro c (rfl | hc)
    · rw [C4_sdiff_left]
      intro h
      have : (3 : ℤ) ∣ 2 := mem_mult h
      omega
    · rw [mem_singleton_iff.mp hc, C4_sdiff_right]
      intro h
      have : (2 : ℤ) ∣ 3 := mem_mult h
      omega

theorem ex_iv_scheme {S : Scheme.{0}} [Nonempty S] :
    PiS N4 S = {⊥, AddSubmonoid.closure {(0, 1)}, AddSubmonoid.closure {(0, 1), (2, 0)},
      AddSubmonoid.closure {(0, 1), (3, 0)}, N4} := by
  rw [PiS, pureMagnets_scheme, ex_iv]

end Ex4

section Ex5

/-- The height `(a, b) ↦ 2a - b`. -/
def psi5 : ℤ × ℤ →+ ℤ where
  toFun x := 2 * x.1 - x.2
  map_zero' := rfl
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add]
    ring

/-- The set `{(k, 2k - 1) | k ∈ ℕ}`. Since `0 ∈ ℕ` in the paper, it contains `(0, -1)`; the printed
parenthesis "(equality of integers in `ℕ_{≥1}`)" treats `k ≥ 1`, and the inequality covers `k = 0` as
well. See also `E5pos`. -/
def E5 : Set (ℤ × ℤ) := range fun k : ℕ => ((k : ℤ), 2 * (k : ℤ) - 1)

/-- The set `{(k, 2k - 1) | k ∈ ℕ_{≥ 1}}`. -/
def E5pos : Set (ℤ × ℤ) := range fun k : ℕ => (((k + 1 : ℕ) : ℤ), 2 * ((k + 1 : ℕ) : ℤ) - 1)

lemma E5_height : ∀ e ∈ E5, psi5 e = 1 := by
  rintro _ ⟨k, rfl⟩
  change 2 * (k : ℤ) - (2 * (k : ℤ) - 1) = 1
  ring

lemma E5pos_height : ∀ e ∈ E5pos, psi5 e = 1 := by
  rintro _ ⟨k, rfl⟩
  change 2 * ((k + 1 : ℕ) : ℤ) - (2 * ((k + 1 : ℕ) : ℤ) - 1) = 1
  ring

/-- The inequality of the printed proof of Example (v), for `s ≥ 2` (journal p. 538: "with `s > 2`",
which omits `s = 2`): if `n₁ + … + n_s = n`, then `(2n₁ - 1) + … + (2n_s - 1) = 2n - s < 2n - 1`. -/
theorem ex_v_inequality (l : List ℕ) (hl : 2 ≤ l.length) :
    (l.map fun n : ℕ => 2 * (n : ℤ) - 1).sum < 2 * ((l.sum : ℕ) : ℤ) - 1 := by
  have h : ∀ t : List ℕ,
      (t.map fun n : ℕ => 2 * (n : ℤ) - 1).sum = 2 * ((t.sum : ℕ) : ℤ) - t.length := by
    intro t
    induction t with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      push_cast
      ring
  rw [h]
  have : (2 : ℤ) ≤ l.length := by exact_mod_cast hl
  omega

/-- A sum of elements of `{(k, 2k - 1)}`, in coordinates. -/
lemma sum_E5 (l : List ℕ) :
    (l.map fun k : ℕ => (((k : ℤ), 2 * (k : ℤ) - 1) : ℤ × ℤ)).sum =
      (((l.sum : ℕ) : ℤ), (l.map fun n : ℕ => 2 * (n : ℤ) - 1).sum) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ext <;> simp

/-- The printed argument of Example (v): "if `n₁ + … + n_s = n` with `s > 2` (equality of integers in
`ℕ_{≥1}`), then `(2n₁ - 1 + … + 2n_s - 1) < 2n - 1`". So `(n, 2n - 1)` is not in the submonoid generated
by the other elements: a sum of `s ≥ 2` of them fails the inequality, for `s = 1` it would be one of
them, and for `s = 0` the second coordinate would be `-1 ≠ 0` or the first `n ≠ 0`. -/
theorem ex_v_notMem : ∀ b ∈ E5, b ∉ AddSubmonoid.closure (E5 \ {b}) := by
  rintro _ ⟨n, rfl⟩ h
  obtain ⟨l, hl, e⟩ := AddSubmonoid.exists_list_of_mem_closure h
  have hks : ∃ ks : List ℕ, l = ks.map fun k : ℕ => (((k : ℤ), 2 * (k : ℤ) - 1) : ℤ × ℤ) := by
    clear e
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons a t ih =>
      obtain ⟨hr, -⟩ := hl a (by simp)
      obtain ⟨k, rfl⟩ := hr
      obtain ⟨ks, rfl⟩ := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
      exact ⟨k :: ks, rfl⟩
  obtain ⟨ks, rfl⟩ := hks
  rw [sum_E5] at e
  have e1 : ((ks.sum : ℕ) : ℤ) = n := congrArg Prod.fst e
  have e2 : (ks.map fun m : ℕ => 2 * (m : ℤ) - 1).sum = 2 * (n : ℤ) - 1 := congrArg Prod.snd e
  match ks, hl, e1, e2 with
  | [], _, e1, e2 =>
    simp only [List.sum_nil, Nat.cast_zero, List.map_nil] at e1 e2
    omega
  | [k], hl, e1, _ =>
    have hk := (hl ((k : ℤ), 2 * (k : ℤ) - 1) (by simp)).2
    have hkn : k = n := by simpa using e1
    subst hkn
    exact hk rfl
  | k :: k' :: t, _, e1, e2 =>
    have := ex_v_inequality (k :: k' :: t) (by simp)
    rw [e1, e2] at this
    exact lt_irrefl _ this

/-- **Example (v)**: `{(k, 2k - 1) | k ∈ ℕ}` is a minimal generating set of a monoid "(which is
sharp)". Minimality is the printed inequality (`ex_v_notMem`). -/
theorem ex_v_minimal : IsMinimalGen E5 ∧ unitsFace (AddSubmonoid.closure E5) = ⊥ :=
  ⟨isMinimalGen_of_notMem ex_v_notMem, units_bot_of_height psi5 E5_height⟩

/-- **Example (v)**: "Theorem 4.6 implies that `Π(a)` is in bijection with `𝒫({(k, 2k - 1) | k ∈ ℕ})`". -/
def ex_v_equiv : pureMagnets (monIdeal (AddSubmonoid.closure E5)) ≃ 𝒫 E5 :=
  prop31Equiv ex_v_minimal.1 ex_v_minimal.2

/-- **Example (v)**: "in particular `#Π(a) > ℵ₀`". -/
theorem ex_v_card : Cardinal.aleph0 < Cardinal.mk (pureMagnets (monIdeal (AddSubmonoid.closure E5))) := by
  rw [prop31_card ex_v_minimal.1 ex_v_minimal.2]
  have hinj : Function.Injective fun k : ℕ => ((k : ℤ), 2 * (k : ℤ) - 1) := fun a b h => by
    have : (a : ℤ) = b := congrArg Prod.fst h
    omega
  have h1 : Cardinal.mk E5 = Cardinal.aleph0 := by
    rw [E5, Cardinal.mk_range_eq _ hinj, Cardinal.mk_nat]
  rw [h1]
  exact Cardinal.cantor _

lemma E5pos_subset : E5pos ⊆ E5 := by
  rintro _ ⟨k, rfl⟩
  rw [E5]
  exact ⟨k + 1, rfl⟩

/-- **Example (v)**, with `k ≥ 1` as in the parenthesis of the printed proof. -/
theorem ex_v_card_pos :
    Cardinal.aleph0 < Cardinal.mk (pureMagnets (monIdeal (AddSubmonoid.closure E5pos))) := by
  have hmin : IsMinimalGen E5pos := isMinimalGen_of_notMem fun b hb h => by
    have hsub : E5pos \ {b} ⊆ E5 \ {b} := fun _ hx => ⟨E5pos_subset hx.1, hx.2⟩
    exact ex_v_notMem b (E5pos_subset hb) (AddSubmonoid.closure_mono hsub h)
  rw [prop31_card hmin (units_bot_of_height psi5 E5pos_height)]
  have hinj : Function.Injective fun k : ℕ => (((k + 1 : ℕ) : ℤ), 2 * ((k + 1 : ℕ) : ℤ) - 1) :=
    fun a b h => by
      have : ((a + 1 : ℕ) : ℤ) = ((b + 1 : ℕ) : ℤ) := congrArg Prod.fst h
      omega
  have h1 : Cardinal.mk E5pos = Cardinal.aleph0 := by
    rw [E5pos, Cardinal.mk_range_eq _ hinj, Cardinal.mk_nat]
  rw [h1]
  exact Cardinal.cantor _

theorem ex_v_card_scheme {S : Scheme.{0}} [Nonempty S] :
    Cardinal.aleph0 < Cardinal.mk (PiS (AddSubmonoid.closure E5) S) := by
  rw [PiS, pureMagnets_scheme]
  exact ex_v_card

end Ex5

section Ex6

lemma sharp_nat (L : AddSubmonoid ℕ) : unitsFace L = ⊥ := by
  refine le_bot_iff.mp ?_
  rintro x ⟨-, y, -, e⟩
  exact Nat.eq_zero_of_add_eq_zero_right e

/-- A finite generating set contains a minimal generating set. -/
lemma exists_minimalGen {M : Type*} [AddCommMonoid M] (s : Finset M) :
    ∃ E : Finset M, AddSubmonoid.closure (E : Set M) = AddSubmonoid.closure (s : Set M) ∧
      IsMinimalGen (E : Set M) := by
  let P : Finset (Finset M) := s.powerset.filter fun t =>
    AddSubmonoid.closure (t : Set M) = AddSubmonoid.closure (s : Set M)
  have hP : P.Nonempty := ⟨s, by simp [P]⟩
  obtain ⟨E, hE⟩ := P.exists_minimal hP
  have hE' := Finset.mem_filter.mp hE.1
  refine ⟨E, hE'.2, fun E' hss e => ?_⟩
  have hfin : E'.Finite := E.finite_toSet.subset hss.1
  have hsub : hfin.toFinset ⊆ E := by
    intro x hx
    exact hss.1 (hfin.mem_toFinset.mp hx)
  have hmem : hfin.toFinset ∈ P := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hsub.trans
      (Finset.mem_powerset.mp hE'.1)), ?_⟩
    rw [hfin.coe_toFinset, e, hE'.2]
  have := hE.2 hmem hsub
  obtain ⟨b, hb, hbE'⟩ := exists_of_ssubset hss
  exact hbE' (hfin.mem_toFinset.mp (this hb))

/-- **Example (vi)**: for `A(ℕ)` acting on `𝔸(N)`, `N ⊆ ℕ`, the set `Π(a)` is finite, since "any
numerical monoid (a submonoid of `ℕ`) is finitely generated". -/
theorem ex_vi (N : AddSubmonoid ℕ) : (pureMagnets (monIdeal N)).Finite := by
  obtain ⟨s, hs⟩ := Nat.addSubmonoid_fg N
  obtain ⟨E, hE, hmin⟩ := exists_minimalGen s
  rw [hs] at hE
  rw [← hE, prop31 hmin (sharp_nat _)]
  exact E.finite_toSet.finite_subsets.image _

theorem ex_vi_scheme {S : Scheme.{0}} (N : AddSubmonoid ℕ) : (PiS N S).Finite := by
  rcases isEmpty_or_nonempty S with hS | hS
  · rw [PiS, pureMagnets_empty_base]
    exact Set.finite_singleton _
  rw [PiS, pureMagnets_scheme]
  exact ex_vi N

/-- **Example (vi)**: if `N = dℕ`, `d ≠ 0`, then `{d}` is a minimal set of generators and
`Π(a) = {0, N}` by Theorem 4.6. (For `d = 0`, `{d}` is not minimal, and `Π(a) = {0}`.) -/
theorem ex_vi_multiple {d : ℕ} (hd : d ≠ 0) :
    pureMagnets (monIdeal (AddSubmonoid.closure {d})) = {⊥, AddSubmonoid.closure {d}} := by
  have hmin : IsMinimalGen ({d} : Set ℕ) := by
    intro E' hE' e
    have h0 : E' = ∅ := by
      rcases subset_singleton_iff_eq.1 hE'.1 with h | h
      · exact h
      · exact absurd h hE'.ne
    rw [h0, AddSubmonoid.closure_empty] at e
    have : d ∈ (⊥ : AddSubmonoid ℕ) := e ▸ AddSubmonoid.subset_closure rfl
    exact hd (by simpa using this)
  rw [prop31 hmin (sharp_nat _), image_powerset_singleton]

/-- An element of `dℕ` is a multiple of `d`. -/
lemma exists_nsmul_of_mem {d x : ℕ} (hx : x ∈ AddSubmonoid.closure {d}) : ∃ k : ℕ, x = k • d := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => exact ⟨1, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by rw [add_smul]⟩

/-- The first step of the direct proof of Example (vi): if `P ⊊ dℕ` is a strict submonoid, "then `d` is
outside `P`". -/
lemma ex_vi_notMem {d : ℕ} {P : AddSubmonoid ℕ} (hP : P < AddSubmonoid.closure {d}) : d ∉ P :=
  fun h => (not_le_of_gt hP) (AddSubmonoid.closure_le.mpr (by simpa using h))

/-- A monoid map on `dℕ` killing `d` is the indicator of `0`. -/
lemma char_eq_indicator {d : ℕ} {R : Type*} [CommRing R]
    (χ : Multiplicative (AddSubmonoid.closure ({d} : Set ℕ)) →* R)
    (h : χ (Multiplicative.ofAdd ⟨d, AddSubmonoid.subset_closure rfl⟩) = 0)
    (l : AddSubmonoid.closure ({d} : Set ℕ)) :
    χ (Multiplicative.ofAdd l) = if (l : ℕ) = 0 then 1 else 0 := by
  obtain ⟨k, hk⟩ := exists_nsmul_of_mem l.2
  split_ifs with h0
  · have : l = 0 := Subtype.ext h0
    rw [this, ofAdd_zero, map_one]
  · have hdL : d ∈ AddSubmonoid.closure ({d} : Set ℕ) := AddSubmonoid.subset_closure rfl
    rcases k with _ | j
    · exact absurd (by simpa using hk) h0
    · have hl : l = (⟨d, hdL⟩ : AddSubmonoid.closure ({d} : Set ℕ)) +
          ⟨j • d, nsmul_mem hdL j⟩ := Subtype.ext (by
        rw [hk, succ_nsmul, add_comm]
        rfl)
      rw [hl, ofAdd_add, map_mul, h, zero_mul]

/-- The indicator of `0`, on `dℕ`. -/
def indicatorChar (d : ℕ) (R : Type*) [CommRing R] :
    Multiplicative (AddSubmonoid.closure ({d} : Set ℕ)) →* R where
  toFun l := if ((Multiplicative.toAdd l : AddSubmonoid.closure ({d} : Set ℕ)) : ℕ) = 0 then 1 else 0
  map_one' := if_pos rfl
  map_mul' a b := by
    have e : ((Multiplicative.toAdd (a * b) : AddSubmonoid.closure ({d} : Set ℕ)) : ℕ) =
        ((Multiplicative.toAdd a : AddSubmonoid.closure ({d} : Set ℕ)) : ℕ) +
          ((Multiplicative.toAdd b : AddSubmonoid.closure ({d} : Set ℕ)) : ℕ) := rfl
    rw [e]
    by_cases ha : ((Multiplicative.toAdd a : AddSubmonoid.closure ({d} : Set ℕ)) : ℕ) = 0 <;>
      by_cases hb : ((Multiplicative.toAdd b : AddSubmonoid.closure ({d} : Set ℕ)) : ℕ) = 0 <;>
        simp [ha, hb]

/-- The direct proof of Example (vi): `Hom^{ℕ-graded}_{R-alg}(R[N], R[P])` is a singleton, for
`P ⊊ dℕ` and any ring `R`. -/
theorem ex_vi_singleton {d : ℕ} {P : AddSubmonoid ℕ} (hP : P < AddSubmonoid.closure {d})
    (R : Type*) [CommRing R] :
    Nonempty (Unique (Attractor (magnetGrading (AddSubmonoid.closure ({d} : Set ℕ)) R) P R)) := by
  have hdP := ex_vi_notMem hP
  let χ₀ : {φ : Multiplicative (AddSubmonoid.closure ({d} : Set ℕ)) →* R //
      ∀ m : AddSubmonoid.closure ({d} : Set ℕ), (m : ℕ) ∉ P → φ (Multiplicative.ofAdd m) = 0} :=
    ⟨indicatorChar d R, fun m hm => by
      change (if (m : ℕ) = 0 then (1 : R) else 0) = 0
      exact if_neg fun h => hm (by rw [h]; exact P.zero_mem)⟩
  have huniq : ∀ χ : {φ : Multiplicative (AddSubmonoid.closure ({d} : Set ℕ)) →* R //
      ∀ m : AddSubmonoid.closure ({d} : Set ℕ), (m : ℕ) ∉ P → φ (Multiplicative.ofAdd m) = 0},
      χ = χ₀ := fun χ => Subtype.ext (MonoidHom.ext fun l => by
    obtain ⟨l, rfl⟩ := Multiplicative.ofAdd.surjective l
    exact char_eq_indicator χ.1 (χ.2 _ hdP) l)
  let e := attractorSelfEquiv (R := R) (L := AddSubmonoid.closure ({d} : Set ℕ)) (N := P) R
  exact ⟨{ default := e.symm χ₀
           uniq := fun a => e.injective ((huniq (e a)).trans (e.apply_symm_apply χ₀).symm) }⟩

/-- The step "So `X^P = X^0`" of the direct proof of Example (vi), from the singleton: the tautological
point of `X^P` over `ℤ[N]/J_P` is the unique one (`char_eq_indicator`), so `X^m ∈ J_P` for all `m ≠ 0`. -/
theorem ex_vi_direct_step {d : ℕ} {P : AddSubmonoid ℕ} (hP : P < AddSubmonoid.closure {d}) :
    d ∉ P ∧ monIdeal (AddSubmonoid.closure {d}) P = monIdeal (AddSubmonoid.closure {d}) ⊥ := by
  have hdP := ex_vi_notMem hP
  refine ⟨hdP, Subset.antisymm (monIdeal_anti bot_le) ?_⟩
  let L : AddSubmonoid ℕ := AddSubmonoid.closure {d}
  let J := magnetIdeal (magnetGrading L ℤ) P
  let χ : Multiplicative L →* (AddMonoidAlgebra ℤ L ⧸ J) :=
    (Ideal.Quotient.mk J : _ →+* _).toMonoidHom.comp (AddMonoidAlgebra.of ℤ L)
  have hχ : ∀ l : L, χ (Multiplicative.ofAdd l) = Ideal.Quotient.mk J (mono ℤ L l) := fun _ => rfl
  have hd : χ (Multiplicative.ofAdd ⟨d, AddSubmonoid.subset_closure rfl⟩) = 0 := by
    rw [hχ]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (mem_magnetIdeal_of_notMem hdP (single_mem_magnetGrading _ _))
  have hmem : ∀ l : L, (l : ℕ) ≠ 0 → (l : ℕ) ∈ monIdeal L P := by
    intro l hl
    have h1 := char_eq_indicator χ hd l
    rw [if_neg hl, hχ] at h1
    exact (mono_mem_magnetIdeal_iff ℤ L l).1 (Ideal.Quotient.eq_zero_iff_mem.mp h1)
  rintro x ⟨m, hm, hm0, t, ht, rfl⟩
  have hne : m + t ≠ 0 := fun h => hm0 (by simpa using (Nat.add_eq_zero_iff.mp h).1)
  exact hmem ⟨m + t, add_mem hm ht⟩ hne

/-- The direct proof of Example (vi): `𝔸(N)^N = 𝔸(N) ≠ 𝔸(N)^0`, so `0` and `N = dℕ` are the only pure
magnets. -/
theorem ex_vi_direct {d : ℕ} (hd : d ≠ 0) :
    pureMagnets (monIdeal (AddSubmonoid.closure {d})) = {⊥, AddSubmonoid.closure {d}} := by
  have hne : monIdeal (AddSubmonoid.closure {d}) (AddSubmonoid.closure {d}) ≠
      monIdeal (AddSubmonoid.closure {d}) (⊥ : AddSubmonoid ℕ) := by
    rw [monIdeal_self]
    intro h
    have : d ∈ monIdeal (AddSubmonoid.closure {d}) (⊥ : AddSubmonoid ℕ) :=
      mem_monIdeal_of_notMem (AddSubmonoid.subset_closure rfl) (by simpa using hd)
    rw [← h] at this
    exact this
  ext K
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hK
    have hle := IsPure.le_self hK
    by_cases hK' : K = AddSubmonoid.closure {d}
    · exact Or.inr hK'
    · exact Or.inl (le_bot_iff.mp (hK ⊥ (ex_vi_direct_step (lt_of_le_of_ne hle hK')).2))
  · rintro (rfl | rfl)
    · exact isPure_bot
    · intro K' e
      by_contra hc
      have hlt : (AddSubmonoid.closure {d}) ⊓ K' < AddSubmonoid.closure {d} :=
        lt_of_le_of_ne inf_le_left fun e' => hc (inf_eq_left.mp e')
      have h1 := (ex_vi_direct_step hlt).2
      rw [monIdeal_inf, ← e, Set.union_self] at h1
      exact hne h1

end Ex6

end AlgMag.SelfActions

#print axioms AlgMag.SelfActions.thm46_lifted
#print axioms AlgMag.SelfActions.rem31_ii
#print axioms AlgMag.SelfActions.rem31_i
#print axioms AlgMag.SelfActions.ex_i_scheme
#print axioms AlgMag.SelfActions.ex_ii_scheme
#print axioms AlgMag.SelfActions.ex_ii_empty
#print axioms AlgMag.SelfActions.ex_ii_not_pure
#print axioms AlgMag.SelfActions.ex_iii_independent
#print axioms AlgMag.SelfActions.ex_iii_scheme
#print axioms AlgMag.SelfActions.ex_iv_scheme
#print axioms AlgMag.SelfActions.ex_i_mem
#print axioms AlgMag.SelfActions.ex_i_minimal
#print axioms AlgMag.SelfActions.ex_ii_quot
#print axioms AlgMag.SelfActions.ex_iv_units
#print axioms AlgMag.SelfActions.ex_iv_units_equiv
#print axioms AlgMag.SelfActions.ex_iv_quot
#print axioms AlgMag.SelfActions.ex_iv_minimal
#print axioms AlgMag.SelfActions.ex_v_inequality
#print axioms AlgMag.SelfActions.ex_v_notMem
#print axioms AlgMag.SelfActions.ex_v_minimal
#print axioms AlgMag.SelfActions.ex_v_equiv
#print axioms AlgMag.SelfActions.ex_v_card_scheme
#print axioms AlgMag.SelfActions.ex_v_card_pos
#print axioms AlgMag.SelfActions.ex_vi_scheme
#print axioms AlgMag.SelfActions.ex_vi_multiple
#print axioms AlgMag.SelfActions.ex_vi_singleton
#print axioms AlgMag.SelfActions.ex_vi_direct_step
#print axioms AlgMag.SelfActions.ex_vi_direct
