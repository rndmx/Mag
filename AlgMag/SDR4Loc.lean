/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Z

/-!
# Lemma D, final bridge: `(B / I')_{P'} ≅ κ'[L]`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Steps 1-2: item 1 of the bridge. `G` plays the part of `κ'[L]`, embedded in `κ'[Γ]` by `ω`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ

variable {R A R' κ G Γ' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Field κ] [CommRing G] [AddCommGroup Γ']
  [UniqueSums Γ'] [Algebra R A] [Algebra R R']

/-- **`(B / I')_{P'} ≅ κ'[L]`**. `B = R' ⊗ A`, `θ` from `SDR3Orbit_bcOrbit`, `G` embedded in `κ'[Γ]` with degrees in `L`, the
degrees of `L` being realized by homogeneous `a` with `φ a ≠ 0`, `κ'` the fraction field of `R' / P'`. -/
theorem SDR4_orbit_loc (cA : Coact A Γ') (hcA : ∀ r : R, cA.σ (algebraMap R A r) = AddMonoidAlgebra.single 0 (algebraMap R A r))
    (φ : A →+* κ) (τ : R' →+* κ) (θ : R' ⊗[R] A →+* κ) (hθ : ∀ r b, θ (r ⊗ₜ b) = τ r * φ b) (I' : Ideal (R' ⊗[R] A))
    (hI' : ∀ y, y ∈ I' ↔ ∀ d, θ ((SDExist_bc R' cA hcA).comp d y) = 0)
    (P' : Ideal R') [P'.IsPrime] (hτ : ∀ a, τ a = 0 ↔ a ∈ P') (hτs : ∀ k, ∃ r s, s ∉ P' ∧ k * τ s = τ r)
    (ω : G →+* AddMonoidAlgebra κ Γ') (hω : Function.Injective ω) (ΘL : R' →+* G) (ΘA : A →+* G)
    (hΘL : ∀ r, ω (ΘL r) = AddMonoidAlgebra.single 0 (τ r))
    (hΘA : ∀ a, ω (ΘA a) = AddMonoidAlgebra.mapRingHom Γ' φ (cA.σ a))
    (Θ : R' ⊗[R] A →+* G) (hΘ : ∀ r a, Θ (r ⊗ₜ a) = ΘL r * ΘA a)
    (L : Set Γ') (hL : ∀ d ∈ L, ∃ a, cA.IsHom d a ∧ φ a ≠ 0)
    (hgen : ∀ Q : G → Prop, Q 0 → (∀ a b, Q a → Q b → Q (a + b)) →
      (∀ d ∈ L, ∀ (k : κ) (g : G), ω g = AddMonoidAlgebra.single d k → Q g) → ∀ g, Q g)
    (hone : ∀ k : κ, ∃ g : G, ω g = AddMonoidAlgebra.single 0 k)
    (T : Submonoid ((R' ⊗[R] A) ⧸ I'))
    (hT : T = P'.primeCompl.map ((Ideal.Quotient.mk I').comp (algebraMap R' (R' ⊗[R] A)))) :
    I'.IsPrime ∧ ∃ e : Localization T ≃+* G, ∀ b, e (algebraMap _ (Localization T) (Ideal.Quotient.mk I' b)) = Θ b := by
  classical
  let cT := SDExist_bc R' cA hcA
  let Ω : R' ⊗[R] A →+* AddMonoidAlgebra κ Γ' := (AddMonoidAlgebra.mapRingHom Γ' θ).comp cT.σ
  have hΩco : ∀ y d, (Ω y).coeff d = θ (cT.comp d y) := fun y d => AddMonoidAlgebra.coeff_mapRingHom ..
  have hΩ : ∀ r a, Ω (r ⊗ₜ a) = AddMonoidAlgebra.single 0 (τ r) * AddMonoidAlgebra.mapRingHom Γ' φ (cA.σ a) := by
    intro r a
    ext d
    rw [hΩco, SDExist_bc_comp, hθ]
    have := AddMonoidAlgebra.coeff_single_mul_add (AddMonoidAlgebra.mapRingHom Γ' φ (cA.σ a)) (τ r) 0 d
    rw [zero_add] at this
    rw [this, AddMonoidAlgebra.coeff_mapRingHom]
    rfl
  have hωΘ : ∀ y, ω (Θ y) = Ω y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
    | tmul r a => rw [hΘ, map_mul, hΘL, hΘA, hΩ]
  have hkerΩ : ∀ y, y ∈ I' ↔ Ω y = 0 := by
    intro y
    rw [hI']
    constructor
    · intro h
      ext d
      rw [hΩco, h d]
      rfl
    · intro h d
      rw [← hΩco, h]
      rfl
  have hprime : I'.IsPrime := by
    have : I' = RingHom.ker Ω := by
      ext y
      exact hkerΩ y
    rw [this]
    exact RingHom.ker_isPrime _
  refine ⟨hprime, ?_⟩
  have hker : ∀ y, y ∈ I' ↔ Θ y = 0 := fun y => by
    rw [hkerΩ, ← hωΘ]
    exact ⟨fun h => hω (h.trans (map_zero ω).symm), fun h => by rw [h, map_zero]⟩
  have hΘs : ∀ s : R', Θ (algebraMap R' (R' ⊗[R] A) s) = ΘL s := fun s => by
    apply hω
    rw [hωΘ, hΘL]
    change Ω (s ⊗ₜ[R] (1 : A)) = _
    rw [hΩ, map_one, map_one, mul_one]
  have hu : ∀ s, s ∉ P' → IsUnit (Θ (algebraMap R' (R' ⊗[R] A) s)) := by
    intro s hs
    have h0 : τ s ≠ 0 := fun h => hs ((hτ s).1 h)
    obtain ⟨g, hg⟩ := hone (τ s)⁻¹
    refine IsUnit.of_mul_eq_one g (hω ?_)
    rw [hΘs, map_mul, hΘL, hg, AddMonoidAlgebra.single_mul_single, add_zero, mul_inv_cancel₀ h0, map_one]
    rfl
  have hs : ∀ g, ∃ b s, s ∉ P' ∧ g * Θ (algebraMap R' (R' ⊗[R] A) s) = Θ b := by
    refine hgen _ ⟨0, 1, ?_, ?_⟩ ?_ ?_
    · exact fun h => (Ideal.ne_top_iff_one P').1 (Ideal.IsPrime.ne_top ‹_›) h
    · rw [zero_mul, map_zero]
    · rintro a b ⟨b₁, s₁, hs₁, h₁⟩ ⟨b₂, s₂, hs₂, h₂⟩
      refine ⟨b₁ * algebraMap R' _ s₂ + b₂ * algebraMap R' _ s₁, s₁ * s₂, ?_, ?_⟩
      · intro h
        obtain h | h := Ideal.IsPrime.mem_or_mem ‹_› h
        · exact hs₁ h
        · exact hs₂ h
      · rw [map_mul, map_mul, map_add, map_mul, map_mul, ← h₁, ← h₂]
        ring
    · intro d hd k g hg
      obtain ⟨a, ha, ha0⟩ := hL d hd
      obtain ⟨r, s, hs', he⟩ := hτs (k * (φ a)⁻¹)
      refine ⟨r ⊗ₜ a, s, hs', hω ?_⟩
      have hσ : cA.σ a = AddMonoidAlgebra.single d a := ha
      rw [map_mul, hg, hΘs, hΘL, hωΘ, hΩ, hσ, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.single_mul_single,
        AddMonoidAlgebra.single_mul_single, add_zero, zero_add, ← he]
      congr 1
      field_simp
  exact SDR4_loc (algebraMap R' (R' ⊗[R] A)) P' I' Θ hker hu hs T hT

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_orbit_loc
