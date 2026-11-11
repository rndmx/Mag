/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmMain

/-!
# Lemma D, Step 4-5: the idempotent `ε` of G3, lifted to `C`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`. `T = E ⊗_B C` with `E` the localized closed orbit. The peer's
`SDR3Orbit_clopen` gives `ε`; a common denominator gives `d''`, and `d' = comp 0 d''` has the property needed in
`SDR3Asm_alg`. No grading on `T` is used: the homogeneous parts are taken in `C`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

variable {R B C Γ : Type u} [CommRing R] [CommRing B] [CommRing C] [AddCommGroup Γ]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

/-- The extended ideal of a homogeneous ideal is homogeneous. -/
theorem SDR3Asm_map_hom {cB : Coact B Γ} {cC : Coact C Γ} (hg : SDExist_IsGraded cB cC) {I : Ideal B}
    (hI : cB.IsHomIdeal I) : cC.IsHomIdeal (I.map (algebraMap B C)) := by
  classical
  have hhom : ∀ g b, cC.IsHom g (algebraMap B C (cB.comp g b)) := fun g b => by
    have h2 := hg g (cB.comp g b)
    rw [cB.comp_self_of_isHom (cB.comp_isHom g b)] at h2
    rw [← h2]
    exact cC.comp_isHom g _
  have hsum : ∀ (s : Finset Γ) (f : Γ → C) (d : Γ), (∀ g ∈ s, cC.comp d (f g) ∈ I.map (algebraMap B C)) →
      cC.comp d (∑ g ∈ s, f g) ∈ I.map (algebraMap B C) := by
    intro s f d
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp [Coact.comp]
    | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha, cC.comp_add]
      exact Ideal.add_mem _ (h a (Finset.mem_insert_self _ _))
        (ih fun g hg => h g (Finset.mem_insert_of_mem hg))
  have key : ∀ (i : B) (c : C), i ∈ I → ∀ d, cC.comp d (algebraMap B C i * c) ∈ I.map (algebraMap B C) := by
    intro i c hi d
    have e : algebraMap B C i * c = ∑ g ∈ (cB.σ i).coeff.support, algebraMap B C (cB.comp g i) * c := by
      rw [← Finset.sum_mul, ← map_sum]
      congr 2
      exact (cB.sum_eq i).symm
    rw [e]
    refine hsum _ _ d fun g _ => ?_
    rw [cC.comp_mul_of_isHom (hhom g i)]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hI i hi g))
  intro y hy d
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    simpa using key i 1 hi d
  | zero => simp [Coact.comp]
  | add x z _ _ hx hz =>
    rw [cC.comp_add]
    exact Ideal.add_mem _ hx hz
  | smul c x hx' _ =>
    have h : ∀ c' x', x' ∈ I.map (algebraMap B C) → cC.comp d (c' * x') ∈ I.map (algebraMap B C) := by
      intro c' x' hx''
      induction hx'' using Submodule.span_induction generalizing c' with
      | mem x₁ hx₁ =>
        obtain ⟨i, hi, rfl⟩ := hx₁
        rw [mul_comm]
        exact key i c' hi d
      | zero => simp [Coact.comp]
      | add x₁ z₁ _ _ hx₁ hz₁ =>
        rw [mul_add, cC.comp_add]
        exact Ideal.add_mem _ (hx₁ c') (hz₁ c')
      | smul c₁ x₁ _ hx₁ =>
        rw [smul_eq_mul, ← mul_assoc]
        exact hx₁ _
    exact h c x hx'

/-- From a homogeneous `d''`, which kills `𝔫` modulo `I C` up to `R ∖ P`, to its degree `0` part. -/
theorem SDR3Asm_deg0 {cB : Coact B Γ} {cC : Coact C Γ} (hg : SDExist_IsGraded cB cC) {I : Ideal B}
    (hI : cB.IsHomIdeal I) (hcC : ∀ r : R, cC.σ (algebraMap R C r) = AddMonoidAlgebra.single 0 (algebraMap R C r))
    (P : Ideal R) [P.IsPrime] (𝔫 : Ideal C) (h𝔫 : cC.IsHomIdeal 𝔫) {d'' : C}
    (hk : ∀ j ∈ 𝔫, ∃ t, t ∉ P ∧ algebraMap R C t * j * d'' ∈ I.map (algebraMap B C)) :
    ∀ j ∈ 𝔫, ∃ t, t ∉ P ∧ algebraMap R C t * cC.comp 0 d'' * j ∈ I.map (algebraMap B C) := by
  classical
  have hmap := SDR3Asm_map_hom hg hI
  have hone : ∀ g, ∀ j ∈ 𝔫, ∃ t, t ∉ P ∧ algebraMap R C t * cC.comp 0 d'' * cC.comp g j ∈ I.map (algebraMap B C) := by
    intro g j hj
    obtain ⟨t, ht, hm⟩ := hk _ (h𝔫 j hj g)
    refine ⟨t, ht, ?_⟩
    have h1 := hmap _ hm g
    have ht0 : cC.IsHom 0 (algebraMap R C t) := hcC t
    have hm0 : cC.IsHom g (algebraMap R C t * cC.comp g j) := by
      simpa using ht0.mul (cC.comp_isHom g j)
    rw [cC.comp_mul_of_isHom hm0, sub_self] at h1
    convert h1 using 1
    ring
  have hfin : ∀ (s : Finset Γ) (j : C), j ∈ 𝔫 → ∃ t, t ∉ P ∧
      algebraMap R C t * cC.comp 0 d'' * (∑ g ∈ s, cC.comp g j) ∈ I.map (algebraMap B C) := by
    intro s j hj
    induction s using Finset.induction_on with
    | empty => exact ⟨1, (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›), by simp⟩
    | insert a s ha ih =>
      obtain ⟨t, ht, hm⟩ := ih
      obtain ⟨t', ht', hm'⟩ := hone a j hj
      refine ⟨t * t', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht ht', ?_⟩
      rw [Finset.sum_insert ha, map_mul]
      have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R C t) hm')
        (Ideal.mul_mem_left _ (algebraMap R C t') hm)
      convert this using 1
      ring
  intro j hj
  obtain ⟨t, ht, hm⟩ := hfin (cC.σ j).coeff.support j hj
  refine ⟨t, ht, ?_⟩
  have e : ∑ g ∈ (cC.σ j).coeff.support, cC.comp g j = j := cC.sum_eq j
  rwa [e] at hm

/-- The kernel of `C → E ⊗_B C`, for `E` the localization of `B/I` at the image of `R ∖ P`. -/
theorem SDR3Asm_tensor_ker (P : Ideal R) [P.IsPrime] (I : Ideal B)
    (S : Submonoid (B ⧸ I)) (hS : S = P.primeCompl.map ((Ideal.Quotient.mk I).comp (algebraMap R B))) {c : C}
    (hc : (1 : Localization S) ⊗ₜ[B] c = 0) : ∃ t, t ∉ P ∧ algebraMap R C t * c ∈ I.map (algebraMap B C) := by
  let J := I.map (algebraMap B C)
  let qm : (B ⧸ I) →+* (C ⧸ J) := Ideal.quotientMap J (algebraMap B C) Ideal.le_comap_map
  let S₂ : Submonoid (C ⧸ J) := S.map qm
  let Tl := Localization S₂
  have hu : ∀ s : S, IsUnit ((algebraMap (C ⧸ J) Tl).comp qm s) := fun s =>
    IsLocalization.map_units Tl (⟨qm s, s, s.2, rfl⟩ : S₂)
  let lif : Localization S →+* Tl := IsLocalization.lift hu
  have hlif : ∀ b : B, lif (algebraMap B _ b) = algebraMap (C ⧸ J) Tl (Ideal.Quotient.mk J (algebraMap B C b)) := by
    intro b
    have : algebraMap B (Localization S) b = algebraMap (B ⧸ I) (Localization S) (Ideal.Quotient.mk I b) := rfl
    rw [this, IsLocalization.lift_eq]
    rfl
  letI : Algebra B Tl := (lif.comp (algebraMap B _)).toAlgebra
  let F₁ : Localization S →ₐ[B] Tl := { lif with commutes' := fun _ => rfl }
  let F₂ : C →ₐ[B] Tl :=
    { ((algebraMap (C ⧸ J) Tl).comp (Ideal.Quotient.mk J)) with
      commutes' := fun b => (hlif b).symm }
  have h1 := congrArg (Algebra.TensorProduct.productMap F₁ F₂) hc
  rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul, map_zero] at h1
  obtain ⟨⟨_, s, hs, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff S₂ Tl _).1 h1
  rw [hS] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨t, ht, ?_⟩
  have h2 : Ideal.Quotient.mk J (algebraMap R C t * c) = 0 := by
    rw [map_mul, IsScalarTower.algebraMap_apply R B C]
    exact hm
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2

/-- **G3, lifted to `C`.** `π : C → E` under `B`, with `π a` a unit, `C_a` étale over `B`. The idempotent `ε` of `E ⊗_B C`
gives `d'`, of degree `0`, with `d' ≡ s'` modulo `𝔫 = ker π`, killing `𝔫` modulo `I C` up to `R ∖ P`. -/
theorem SDR3Asm_G3 {cB : Coact B Γ} {cC : Coact C Γ} (hg : SDExist_IsGraded cB cC) {I : Ideal B}
    (hI : cB.IsHomIdeal I) (hcC : ∀ r : R, cC.σ (algebraMap R C r) = AddMonoidAlgebra.single 0 (algebraMap R C r))
    (P : Ideal R) [P.IsPrime] (S : Submonoid (B ⧸ I))
    (hS : S = P.primeCompl.map ((Ideal.Quotient.mk I).comp (algebraMap R B)))
    (π : C →ₐ[B] Localization S) (h𝔫 : cC.IsHomIdeal (RingHom.ker π.toRingHom))
    (a : C) (hau : IsUnit (π a)) [Algebra.Etale B (Localization.Away a)] :
    ∃ (d' : C) (s' : R), cC.IsHom 0 d' ∧ s' ∉ P ∧ d' - algebraMap R C s' ∈ RingHom.ker π.toRingHom ∧
      ∀ j ∈ RingHom.ker π.toRingHom, ∃ t, t ∉ P ∧ algebraMap R C t * d' * j ∈ I.map (algebraMap B C) := by
  let E := Localization S
  let T := E ⊗[B] C
  let πT : T →ₐ[E] E := Algebra.TensorProduct.lift (AlgHom.id E E) π (fun _ _ => Commute.all _ _)
  have hπT : ∀ (k : E) (c : C), πT (k ⊗ₜ[B] c) = k * π c := fun k c =>
    Algebra.TensorProduct.lift_tmul _ _ _ k c
  let dd : T := (1 : E) ⊗ₜ[B] a
  have hdd : IsUnit (πT dd) := by
    rw [hπT, one_mul]
    exact hau
  haveI hEt : Algebra.Etale E (Localization.Away dd) := by
    let Ca := Localization.Away a
    letI iT : Algebra T (E ⊗[B] Ca) := SDLocA_alg B C Ca E
    have hT2 : IsScalarTower E T (E ⊗[B] Ca) := .of_algebraMap_eq fun r => by
      change r ⊗ₜ[B] (1 : Ca) = r ⊗ₜ[B] algebraMap C Ca (1 : C)
      rw [map_one]
    have hLoc : IsLocalization.Away dd (E ⊗[B] Ca) := by
      have h0 := IsLocalization.tensorProduct_tensorProduct_right B E (Submonoid.powers a) Ca
        (A := C) (by ext; simp [RingHom.algebraMap_toAlgebra])
      rw [Submonoid.map_powers] at h0
      exact h0
    exact Algebra.Etale.of_equiv
      ((IsLocalization.algEquiv (Submonoid.powers dd) (E ⊗[B] Ca) (Localization.Away dd)).restrictScalars E)
  obtain ⟨ε, -, hε1, hεJ⟩ := SDR3Orbit_clopen πT dd hdd
  -- the denominator
  let σ : R → E := fun s => algebraMap B E (algebraMap R B s)
  have hσm : ∀ s s₂, σ (s * s₂) = σ s * σ s₂ := fun s s₂ => by simp [σ]
  have hσ : ∀ (s : R) (c : C), σ s • ((1 : E) ⊗ₜ[B] c) = (1 : E) ⊗ₜ[B] (algebraMap R C s * c) := by
    intro s c
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change algebraMap B E (algebraMap R B s) ⊗ₜ[B] c = _
    rw [Algebra.algebraMap_eq_smul_one (algebraMap R B s),
      TensorProduct.smul_tmul, IsScalarTower.algebraMap_apply R B C s, Algebra.smul_def]
  have hE : ∀ k : E, ∃ s, s ∉ P ∧ ∃ β : B, σ s * k = algebraMap B E β := by
    intro k
    obtain ⟨⟨q, s₁⟩, hq⟩ := IsLocalization.surj S k
    obtain ⟨β, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hs₂ : (s₁ : B ⧸ I) ∈ P.primeCompl.map ((Ideal.Quotient.mk I).comp (algebraMap R B)) := hS ▸ s₁.2
    obtain ⟨s, hs, hse⟩ := hs₂
    refine ⟨s, hs, β, ?_⟩
    have e : σ s = algebraMap (B ⧸ I) E (s₁ : B ⧸ I) := by
      rw [← hse]
      rfl
    rw [mul_comm, e]
    exact hq
  have hden : ∀ τ : T, ∃ s, s ∉ P ∧ ∃ c : C, σ s • τ = (1 : E) ⊗ₜ[B] c := by
    intro τ
    induction τ using TensorProduct.induction_on with
    | zero => exact ⟨1, (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›), 0, by simp⟩
    | add x y hx hy =>
      obtain ⟨s, hs, c, hc⟩ := hx
      obtain ⟨s₂, hs₂, c₂, hc₂⟩ := hy
      refine ⟨s * s₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs₂,
        algebraMap R C s₂ * c + algebraMap R C s * c₂, ?_⟩
      rw [TensorProduct.tmul_add, ← hσ, ← hσ, ← hc, ← hc₂, smul_add, hσm, mul_smul, mul_comm (σ s), mul_smul]
      simp only [smul_comm (σ s₂) (σ s)]
    | tmul k c =>
      obtain ⟨s, hs, β, hβ⟩ := hE k
      refine ⟨s, hs, algebraMap B C β * c, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, hβ, Algebra.algebraMap_eq_smul_one β,
        TensorProduct.smul_tmul, Algebra.smul_def]
  obtain ⟨s', hs', d'', hd''⟩ := hden ε
  have hπR : ∀ s : R, π (algebraMap R C s) = σ s := fun s => by
    rw [IsScalarTower.algebraMap_apply R B C]
    exact π.commutes _
  have hd''𝔫 : π d'' = σ s' := by
    have h1 := congrArg πT hd''
    rw [map_smul, hε1, hπT, one_mul, smul_eq_mul, mul_one] at h1
    exact h1.symm
  have hkill : ∀ j ∈ RingHom.ker π.toRingHom, ∃ t, t ∉ P ∧ algebraMap R C t * j * d'' ∈ I.map (algebraMap B C) := by
    intro j hj
    have hj0 : π j = 0 := hj
    have h1 := hεJ ((1 : E) ⊗ₜ[B] j) (by rw [hπT, hj0, mul_zero])
    have h2 : (1 : E) ⊗ₜ[B] (j * d'') = 0 := by
      have e : (1 : E) ⊗ₜ[B] (j * d'') = ((1 : E) ⊗ₜ[B] j) * ((1 : E) ⊗ₜ[B] d'') := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [e, ← hd'', mul_smul_comm, h1, smul_zero]
    obtain ⟨t, ht, hm⟩ := SDR3Asm_tensor_ker P I S hS h2
    exact ⟨t, ht, by rwa [mul_assoc]⟩
  refine ⟨cC.comp 0 d'', s', cC.comp_isHom 0 d'', hs', ?_, SDR3Asm_deg0 hg hI hcC P _ h𝔫 hkill⟩
  have h3 : d'' - algebraMap R C s' ∈ RingHom.ker π.toRingHom := by
    change π _ = 0
    rw [map_sub, hd''𝔫, hπR, sub_self]
  have h4 := h𝔫 _ h3 0
  have h5 : cC.comp 0 (d'' - algebraMap R C s') = cC.comp 0 d'' - algebraMap R C s' := by
    have h6 : cC.comp 0 (algebraMap R C s') = algebraMap R C s' := cC.comp_self_of_isHom (hcC s')
    have h7 : cC.comp 0 (d'' - algebraMap R C s') + cC.comp 0 (algebraMap R C s') = cC.comp 0 d'' := by
      rw [← cC.comp_add, sub_add_cancel]
    rw [← h7, h6, add_sub_cancel_right]
  rwa [h5] at h4

end AlgMag.SD
