/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumRing
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.FiniteType

/-!
# The generic stabilizer for quasi-separated `X`: the ring part

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.
This file gives the ring part of the generic stabilizer statement (over a nonempty open of the base, the stabilizer is `D(M/Z)`), for quasi-separated `X`.

`f k` and `G k` describe a locally closed part `E` of `D(M)_R`: `D(f k)` cover an open `A` and `E ∩ D(f k)`
is cut out by `G k`. `FixP ρ χ` says that `χ` is a point of `E`. If `E` is a subgroup functor, then over a
nonempty open of `Spec R` it is `D(M/Z)`.

Over the fraction field `K`: the ideal of the closure of `E_K` is the ideal of `D(M/Z)`, by
`exists_stab_subgroup`, after the product law on the closure (`hmul_Ik`). Then `E_K` is open and
schematically dense in `D(M/Z)_K`, so the ideal `J` of its complement holds a nonzerodivisor, and the
translate argument gives `J = ⊤` (`J_eq_top`).
-/

open TensorProduct

universe u

namespace AlgMag.ChartQSStabGen

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M]

/-- A ring morphism as a morphism of monoids. -/
abbrev rm {A B : Type u} [CommRing A] [CommRing B] (θ : A →+* B) : A →* B := θ

/-- Evaluation of `R[M]` at a character. -/
noncomputable def ev {A : Type u} [CommRing A] (ρ : R →+* A) (χ : Multiplicative M →* A) :
    AddMonoidAlgebra R M →+* A :=
  AddMonoidAlgebra.liftNCRingHom ρ χ (fun _ _ => mul_comm _ _)

lemma ev_single {A : Type u} [CommRing A] (ρ : R →+* A) (χ : Multiplicative M →* A) (m : M) (r : R) :
    ev ρ χ (AddMonoidAlgebra.single m r) = ρ r * χ (Multiplicative.ofAdd m) := by
  simp [ev, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

lemma ringHom_ext' {A : Type u} [CommRing A] {a b : AddMonoidAlgebra R M →+* A}
    (h : ∀ m r, a (AddMonoidAlgebra.single m r) = b (AddMonoidAlgebra.single m r)) : a = b := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r => exact h m r

lemma map_ev {A B : Type u} [CommRing A] [CommRing B] (θ : A →+* B) (ρ : R →+* A)
    (χ : Multiplicative M →* A) (x : AddMonoidAlgebra R M) :
    θ (ev ρ χ x) = ev (θ.comp ρ) ((rm θ).comp χ) x := by
  have : θ.comp (ev ρ χ) = ev (θ.comp ρ) ((rm θ).comp χ) :=
    ringHom_ext' fun m r => by simp [ev_single]
  exact congrArg (fun k => k x) this

section Fix

variable {ι : Type u} (f : ι → AddMonoidAlgebra R M) (G : ι → Finset (AddMonoidAlgebra R M))

/-- `χ` is a point of the locally closed part described by `f` and `G`. -/
def FixP {A : Type u} [CommRing A] (ρ : R →+* A) (χ : Multiplicative M →* A) : Prop :=
  Ideal.span (Set.range fun k => ev ρ χ (f k)) = ⊤ ∧
    ∀ k, ∀ x ∈ G k, ∃ n : ℕ, ev ρ χ (f k) ^ n * ev ρ χ x = 0

variable {f G}

lemma FixP.map {A B : Type u} [CommRing A] [CommRing B] (θ : A →+* B) {ρ : R →+* A}
    {χ : Multiplicative M →* A} (h : FixP f G ρ χ) : FixP f G (θ.comp ρ) ((rm θ).comp χ) := by
  refine ⟨?_, fun k x hx => ?_⟩
  · have := congrArg (Ideal.map θ) h.1
    rw [Ideal.map_span, Ideal.map_top] at this
    rw [← this]
    congr 1
    ext y
    simp [map_ev]
  · obtain ⟨n, hn⟩ := h.2 k x hx
    refine ⟨n, ?_⟩
    have := congrArg θ hn
    simpa [map_ev] using this

end Fix

/-- The ring of a locally closed part of `Spec S`. -/
abbrev Lc {S : Type u} [CommRing S] (a : Ideal S) (b : S) : Type u :=
  Localization.Away (Ideal.Quotient.mk a b)

/-- `S → (S/a)_b`. -/
noncomputable def lcMap {S : Type u} [CommRing S] (a : Ideal S) (b : S) : S →+* Lc a b :=
  (algebraMap (S ⧸ a) (Lc a b)).comp (Ideal.Quotient.mk a)

lemma lcMap_b_isUnit {S : Type u} [CommRing S] (a : Ideal S) (b : S) : IsUnit (lcMap a b b) :=
  show IsUnit (algebraMap _ _ (Ideal.Quotient.mk a b)) from IsLocalization.Away.algebraMap_isUnit _

lemma lcMap_eq_zero {S : Type u} [CommRing S] {a : Ideal S} (b : S) {x : S} (h : x ∈ a) :
    lcMap a b x = 0 := by
  simp [lcMap, Ideal.Quotient.eq_zero_iff_mem.mpr h]

/-- `(S/a)_b → T`, if `S → T` kills `a` and inverts `b`. -/
noncomputable def lcLift {S T : Type u} [CommRing S] [CommRing T] {a : Ideal S} {b : S} (θ : S →+* T)
    (ha : ∀ x ∈ a, θ x = 0) (hb : IsUnit (θ b)) : Lc a b →+* T :=
  IsLocalization.Away.lift (Ideal.Quotient.mk a b) (g := Ideal.Quotient.lift a θ ha) (by simpa using hb)

lemma lcLift_comp {S T : Type u} [CommRing S] [CommRing T] {a : Ideal S} {b : S} (θ : S →+* T)
    (ha : ∀ x ∈ a, θ x = 0) (hb : IsUnit (θ b)) : (lcLift θ ha hb).comp (lcMap a b) = θ := by
  refine RingHom.ext fun x => ?_
  simp [lcLift, lcMap]

section Tests

variable {ι : Type u}

/-- The ring of `D(M) × D(M)` over `R`. -/
abbrev SS (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] : Type u :=
  AddMonoidAlgebra R (M × M)

/-- `R → R[M × M]`. -/
noncomputable abbrev cS : R →+* SS R M := algebraMap R (SS R M)

/-- The test hypotheses: `E` is a subgroup functor. `Lc a b` are the locally closed subschemes of
`D(M) × D(M)`, which lie in the site. -/
structure Tests (f : ι → AddMonoidAlgebra R M) (G : ι → Finset (AddMonoidAlgebra R M)) : Prop where
  hone : FixP f G (RingHom.id R) (1 : Multiplicative M →* R)
  hs : ∀ (a : Ideal (SS R M)) (b : SS R M) (χ : Multiplicative M →* SS R M) (i : ι),
    IsUnit (ev ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ) (f i)) →
    (∀ x ∈ G i, ev ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ) x = 0) →
    FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ)
  hmul : ∀ (a : Ideal (SS R M)) (b : SS R M) (χ₁ χ₂ : Multiplicative M →* SS R M),
    FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ₁) →
    FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ₂) →
    FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp (χ₁ * χ₂))
  hdiv : ∀ (a : Ideal (SS R M)) (b : SS R M) (χ₁ χ₂ : Multiplicative M →* SS R M),
    FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ₂) →
    FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp (χ₁ * χ₂)) →
    FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ₁)

/-- The first universal character on `M × M`. -/
noncomputable def g₀ : Multiplicative M →* SS R M :=
  (AddMonoidAlgebra.of R (M × M)).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M M))

/-- The second universal character on `M × M`. -/
noncomputable def h₀ : Multiplicative M →* SS R M :=
  (AddMonoidAlgebra.of R (M × M)).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M M))

/-- The character of `M × M` from a pair of characters. -/
noncomputable def pairChar {T : Type u} [CommRing T] (χ₁ χ₂ : Multiplicative M →* T) :
    Multiplicative (M × M) →* T where
  toFun := fun x => χ₁ (Multiplicative.ofAdd (Multiplicative.toAdd x).1) *
        χ₂ (Multiplicative.ofAdd (Multiplicative.toAdd x).2)
  map_one' := by simp
  map_mul' := fun x y => by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul]
    ring

/-- `R[M × M] → T` from a pair of characters. -/
noncomputable def pairMap {T : Type u} [CommRing T] (ρ : R →+* T) (χ₁ χ₂ : Multiplicative M →* T) :
    SS R M →+* T :=
  ev (M := M × M) ρ (pairChar χ₁ χ₂)

lemma pairMap_cS {T : Type u} [CommRing T] (ρ : R →+* T) (χ₁ χ₂ : Multiplicative M →* T) :
    (pairMap ρ χ₁ χ₂).comp (cS (R := R) (M := M)) = ρ := by
  refine RingHom.ext fun r => ?_
  change pairMap ρ χ₁ χ₂ (AddMonoidAlgebra.single 0 r) = _
  simp [pairMap, ev_single, pairChar]

lemma pairMap_g₀ {T : Type u} [CommRing T] (ρ : R →+* T) (χ₁ χ₂ : Multiplicative M →* T) :
    (rm (pairMap ρ χ₁ χ₂)).comp (g₀ (R := R) (M := M)) = χ₁ := by
  refine MonoidHom.ext fun m => ?_
  simp [pairMap, g₀, AddMonoidAlgebra.of_apply, ev_single, pairChar]

lemma pairMap_h₀ {T : Type u} [CommRing T] (ρ : R →+* T) (χ₁ χ₂ : Multiplicative M →* T) :
    (rm (pairMap ρ χ₁ χ₂)).comp (h₀ (R := R) (M := M)) = χ₂ := by
  refine MonoidHom.ext fun m => ?_
  simp [pairMap, h₀, AddMonoidAlgebra.of_apply, ev_single, pairChar]

/-- Transport from a locally closed test ring. -/
lemma fix_of_lc {T : Type u} [CommRing T] {f : ι → AddMonoidAlgebra R M}
    {G : ι → Finset (AddMonoidAlgebra R M)} {a : Ideal (SS R M)} {b : SS R M}
    (θ : SS R M →+* T) (ha : ∀ x ∈ a, θ x = 0) (hb : IsUnit (θ b))
    {χ : Multiplicative M →* SS R M}
    (h : FixP f G ((lcMap a b).comp cS) ((rm (lcMap a b)).comp χ)) :
    FixP f G (θ.comp cS) ((rm θ).comp χ) := by
  have := h.map (lcLift θ ha hb)
  have e := lcLift_comp θ ha hb
  have e1 : (lcLift θ ha hb).comp ((lcMap a b).comp cS) = θ.comp (cS (R := R) (M := M)) := by
    rw [← RingHom.comp_assoc, e]
  have e2 : (rm (lcLift θ ha hb)).comp
      ((rm (lcMap a b)).comp χ) = (rm θ).comp χ := by
    refine MonoidHom.ext fun m => ?_
    exact congrArg (fun k => k (χ m)) e
  rwa [e1, e2] at this

end Tests

end AlgMag.ChartQSStabGen
