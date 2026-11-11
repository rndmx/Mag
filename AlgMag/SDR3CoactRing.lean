/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3SchemeQuotient

/-!
# Lemma D, Steps 2, 3: the coaction from the action, the saturated open

Step 3. With `Y = D(Λ) × Z`, `Y₂ = D(Λ) × D(Λ) × Z`:

* `SDR3Coact_ofRing`: the action `a : Y → Z` gives a coaction on `Γ(Z)`, its counit and coassociativity being read on
  `Γ(Y)`, `Γ(Y₂)`. Only the ring maps are used.
* `SDR3Coact_saturated`: the image `V` of `π⁻¹ U₀` under `a` is stable: `a y ∈ V ↔ π y ∈ V`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgMag.SD

open AlgMag.SQ

section Ring

variable {A C C₂ Λ : Type u} [CommRing A] [CommRing C] [CommRing C₂] [AddCommGroup Λ]

/-- `Σ a_d t^d ↦ Σ f(a_d) g(d)`. -/
noncomputable abbrev SDR3Coact_lift {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (g : Multiplicative Λ →* S) : AddMonoidAlgebra R Λ →+* S :=
  AddMonoidAlgebra.liftNCRingHom f g (fun _ _ => mul_comm _ _)

lemma SDR3Coact_lift_single {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (g : Multiplicative Λ →* S) (d : Λ) (r : R) :
    SDR3Coact_lift f g (AddMonoidAlgebra.single d r) = f r * g (Multiplicative.ofAdd d) := by
  simp [SDR3Coact_lift, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

/-- The coaction on `Γ(Z)` given by an action. -/
theorem SDR3Coact_ofRing (πs as : A →+* C) (es : C →+* A) (ps ms acts : C →+* C₂)
    (χ : Multiplicative Λ →* C) (τ : Multiplicative Λ →* C₂)
    (hφ : Function.Bijective (SDR3Coact_lift πs χ)) (hψ : Function.Injective (SDR3Coact_lift ps τ))
    (heπ : ∀ y, es (πs y) = y) (hea : ∀ y, es (as y) = y) (heχ : ∀ d, es (χ d) = 1)
    (hmπ : ∀ y, ms (πs y) = ps (πs y)) (hmχ : ∀ d, ms (χ d) = ps (χ d) * τ d)
    (hactπ : ∀ y, acts (πs y) = ps (as y)) (hactχ : ∀ d, acts (χ d) = τ d)
    (hma : ∀ y, ms (as y) = acts (as y)) :
    ∃ c : Coact A Λ, ∀ y, SDR3Coact_lift πs χ (c.σ y) = as y := by
  classical
  let E := RingEquiv.ofBijective _ hφ
  let σ : A →+* AddMonoidAlgebra A Λ := (E.symm : C →+* _).comp as
  have hσ : ∀ y, SDR3Coact_lift πs χ (σ y) = as y := fun y => E.apply_symm_apply (as y)
  -- the counit
  have hcounit : ∀ w : AddMonoidAlgebra A Λ, es (SDR3Coact_lift πs χ w) = w.coeff.sum fun _ a => a := by
    intro w
    induction w using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index' (by simp) (by simp)]
    | single d r =>
      rw [SDR3Coact_lift_single, map_mul, heπ, heχ, mul_one, AddMonoidAlgebra.coeff_single,
        Finsupp.sum_single_index rfl]
  -- the two expansions of `Γ(Y₂)`
  let Θ₁ : AddMonoidAlgebra A Λ →+* AddMonoidAlgebra C Λ :=
    SDR3Coact_lift (AddMonoidAlgebra.singleZeroRingHom.comp πs)
      { toFun := fun d => AddMonoidAlgebra.single (Multiplicative.toAdd d) (χ d)
        map_one' := by simp [AddMonoidAlgebra.one_def]
        map_mul' := fun x y => by simp [AddMonoidAlgebra.single_mul_single] }
  let Θ₂ : AddMonoidAlgebra A Λ →+* AddMonoidAlgebra C Λ := AddMonoidAlgebra.mapRingHom Λ as
  have h1 : ∀ w, SDR3Coact_lift ps τ (Θ₁ w) = ms (SDR3Coact_lift πs χ w) := by
    intro w
    induction w using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single d r =>
      have : Θ₁ (AddMonoidAlgebra.single d r) = AddMonoidAlgebra.single d (πs r * χ (Multiplicative.ofAdd d)) := by
        simp [Θ₁, SDR3Coact_lift_single, AddMonoidAlgebra.single_mul_single]
      rw [this, SDR3Coact_lift_single, SDR3Coact_lift_single, map_mul, map_mul, hmπ, hmχ, mul_assoc]
  have h2 : ∀ w, SDR3Coact_lift ps τ (Θ₂ w) = acts (SDR3Coact_lift πs χ w) := by
    intro w
    induction w using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single d r =>
      have : Θ₂ (AddMonoidAlgebra.single d r) = AddMonoidAlgebra.single d (as r) := by simp [Θ₂]
      rw [this, SDR3Coact_lift_single, SDR3Coact_lift_single, map_mul, hactπ, hactχ]
  have hΘ₁ : ∀ (w : AddMonoidAlgebra A Λ) d, (Θ₁ w).coeff d = πs (w.coeff d) * χ (Multiplicative.ofAdd d) := by
    intro w d
    induction w using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [map_add, ha, hb, add_mul]
    | single e r =>
      have : Θ₁ (AddMonoidAlgebra.single e r) = AddMonoidAlgebra.single e (πs r * χ (Multiplicative.ofAdd e)) := by
        simp [Θ₁, SDR3Coact_lift_single, AddMonoidAlgebra.single_mul_single]
      rw [this]
      by_cases h : e = d
      · subst h; simp
      · simp [h]
  have hΘ₂ : ∀ (w : AddMonoidAlgebra A Λ) d, (Θ₂ w).coeff d = as (w.coeff d) := by
    intro w d
    simp [Θ₂]
  refine ⟨⟨σ, ?_, ?_⟩, hσ⟩
  · intro y
    rw [← hcounit, hσ, hea]
  · intro y d
    have hΘ : Θ₁ (σ y) = Θ₂ (σ y) := by
      apply hψ
      rw [h1, h2, hσ, hma]
    have hc := congrArg (fun z => z.coeff d) hΘ
    simp only [hΘ₁, hΘ₂] at hc
    apply hφ.1
    rw [hσ, SDR3Coact_lift_single]
    exact hc.symm

end Ring

section Saturated

variable {Y Y₂ Z : Scheme.{u}}

/-- `V = a(π⁻¹ U₀)` is saturated. In coordinates `p (t,s,z) = (s,z)`, `act (t,s,z) = (t,sz)`, `m (t,s,z) = (ts,z)`, and
`ι (t,z) = (t⁻¹,tz)`. -/
theorem SDR3Coact_saturated {π a : Y ⟶ Z} {p m act : Y₂ ⟶ Y} {ι : Y ⟶ Y}
    (hpb : IsPullback p act a π) (hmπ : m ≫ π = p ≫ π) (hma : m ≫ a = act ≫ a)
    (hιπ : ι ≫ π = a) (hιa : ι ≫ a = π) (U₀ : Set Z) (y : Y) :
    a y ∈ a '' (π ⁻¹' U₀) ↔ π y ∈ a '' (π ⁻¹' U₀) := by
  have key : ∀ y : Y, π y ∈ a '' (π ⁻¹' U₀) → a y ∈ a '' (π ⁻¹' U₀) := by
    rintro y ⟨z, hz, hzy⟩
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := π) z y hzy
    let w' : Y₂ := hpb.isoPullback.inv w
    have e1 : p w' = z := by
      have : hpb.isoPullback.inv ≫ p = pullback.fst a π := hpb.isoPullback_inv_fst
      rw [← hw1, ← this]; rfl
    have e2 : act w' = y := by
      have : hpb.isoPullback.inv ≫ act = pullback.snd a π := hpb.isoPullback_inv_snd
      rw [← hw2, ← this]; rfl
    refine ⟨m w', ?_, ?_⟩
    · have : π (m w') = π (p w') := congrArg (fun k : Y₂ ⟶ Z => k w') hmπ
      change π (m w') ∈ U₀
      rw [this, e1]; exact hz
    · have : a (m w') = a (act w') := congrArg (fun k : Y₂ ⟶ Z => k w') hma
      rw [this, e2]
  refine ⟨fun h => ?_, key y⟩
  have h1 : π (ι y) = a y := congrArg (fun k : Y ⟶ Z => k y) hιπ
  have h2 : a (ι y) = π y := congrArg (fun k : Y ⟶ Z => k y) hιa
  rw [← h2]
  exact key (ι y) (h1 ▸ h)

end Saturated

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Coact_ofRing
#print axioms AlgMag.SD.SDR3Coact_saturated
