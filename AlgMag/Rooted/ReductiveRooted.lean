/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Rooted.RootedBasic

/-!
# Split reductive groups are rooted (statement, from an abstract input)

`algmag-notes/reductive/reductive-rooted.md`, Theorem R. `G` split reductive, `T = D(M)` acting by
conjugation, roots `Φ ⊆ M`, Weyl group `W`, `Z_w = (1 - w)M`. Then `G` is rooted by
`Φ_G = {[α⟩ : α ∈ Φ} ∪ {Z_w : w ∈ W}`.

The geometric input is Theorem 2 of the classification note: for every magnet `N`,
`E(G^N) = [N ∩ Φ⟩ + Σ_{Z_w ⊆ N} Z_w`, this is pure, and `N` is pure iff `N = E(G^N)`.
It is recorded as `ReductiveInput`; Theorem R follows with no further geometry. To connect, build
`ReductiveInput` from the `AlgMag.Reductive` layer once Theorem A is in Lean.
-/

namespace AlgMag.Rooted

variable {M : Type*} [AddCommGroup M]

/-- `Z_w = (1 - w)M`, as a submonoid. -/
def weylMagnet (w : M →+ M) : AddSubmonoid M := AddMonoidHom.mrange (AddMonoidHom.id M - w)

/-- `Φ_G = {[α⟩ : α ∈ Φ} ∪ {Z_w : w ∈ W}`. -/
def reductiveRoot (Φ : Set M) {W : Type*} (act : W → M →+ M) : Set (AddSubmonoid M) :=
  mono '' Φ ∪ Set.range (fun w => weylMagnet (act w))

/-- `E(G^N) = [N ∩ Φ⟩ + Σ_{w ∈ W_N} Z_w`, `W_N = {w : Z_w ⊆ N}`. -/
def reductiveHull (Φ : Set M) {W : Type*} (act : W → M →+ M) (N : AddSubmonoid M) :
    AddSubmonoid M :=
  AddSubmonoid.closure ((N : Set M) ∩ Φ) ⊔
    ⨆ w ∈ {w | weylMagnet (act w) ≤ N}, weylMagnet (act w)

/-- Abstract input (Theorem 2 / Theorem A of the classification note) for the pure-magnet
predicate `P` of the conjugation action of `T = D(M)` on `G`. -/
structure ReductiveInput (P : AddSubmonoid M → Prop) (Φ : Set M) {W : Type*}
    (act : W → M →+ M) : Prop where
  pure_iff : ∀ N, P N ↔ N = reductiveHull Φ act N
  hull_pure : ∀ N, P (reductiveHull Φ act N)

/-- Key lemma: `[tr_{Φ_G}(N)⟩ = E(G^N)`. -/
theorem gen_trace_reductiveRoot (Φ : Set M) {W : Type*} (act : W → M →+ M)
    (N : AddSubmonoid M) : gen (trace (reductiveRoot Φ act) N) = reductiveHull Φ act N := by
  have h1 : trace (reductiveRoot Φ act) N =
      trace (mono '' Φ) N ∪ trace (Set.range fun w => weylMagnet (act w)) N := by
    ext I
    constructor
    · rintro ⟨hI | hI, hle⟩
      · exact Or.inl ⟨hI, hle⟩
      · exact Or.inr ⟨hI, hle⟩
    · rintro (⟨hI, hle⟩ | ⟨hI, hle⟩)
      · exact ⟨Or.inl hI, hle⟩
      · exact ⟨Or.inr hI, hle⟩
  have h2 : trace (Set.range fun w => weylMagnet (act w)) N =
      (fun w => weylMagnet (act w)) '' {w | weylMagnet (act w) ≤ N} := by
    ext I
    constructor
    · rintro ⟨⟨w, rfl⟩, hle⟩
      exact ⟨w, hle, rfl⟩
    · rintro ⟨w, hle, rfl⟩
      exact ⟨⟨w, rfl⟩, hle⟩
  have h3 : sSup (trace (mono '' Φ) N) = AddSubmonoid.closure ((N : Set M) ∩ Φ) := by
    rw [trace_mono_image]
    exact gen_mono_image _
  unfold reductiveHull
  show sSup (trace (reductiveRoot Φ act) N) = _
  rw [h1, sSup_union, h2, sSup_image, h3]

/-- **Theorem R.** Under the abstract input, the action is rooted by `Φ_G`. -/
theorem reductive_joinDense {P : AddSubmonoid M → Prop} {Φ : Set M} {W : Type*}
    {act : W → M →+ M} (H : ReductiveInput P Φ act) : IsJoinDense P (reductiveRoot Φ act) := by
  refine isJoinDense_of_hull (fun N hN => ?_) (fun N => ?_)
  · rw [gen_trace_reductiveRoot]
    exact ((H.pure_iff N).1 hN).symm
  · rw [gen_trace_reductiveRoot]
    exact H.hull_pure N

end AlgMag.Rooted
