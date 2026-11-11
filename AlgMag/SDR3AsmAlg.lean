/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDLocAMain
import AlgMag.SDExistIntegral

/-!
# Lemma D, Steps 4-5: the graded integral closure and the element `d`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`:
`d` is built from a homogeneous `a ∉ 𝔫`, and `d - c ∈ 𝔫` with `c ∉ P`, so that no inversion
is needed before `SDExist_isolate`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

section Closure

variable {Γ B C : Type u} [AddCommGroup Γ] [CommRing B] [CommRing C] [Algebra B C]

/-- An element of `C[Γ]` with coefficients in a subring comes from that subring. -/
lemma SDR3Asm_mem_range (S : Subring C) (z : AddMonoidAlgebra C Γ) (hz : ∀ d, z.coeff d ∈ S) :
    z ∈ (AddMonoidAlgebra.mapRingHom Γ S.subtype).range := by
  classical
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.onFinset z.coeff.support (fun d => ⟨z.coeff d, hz d⟩) fun d hd => ?_), ?_⟩
  · rw [Finsupp.mem_support_iff]
    intro h0
    exact hd (Subtype.ext h0)
  · ext d
    rw [AddMonoidAlgebra.coeff_mapRingHom]
    rfl

lemma SDR3Asm_map_injective (S : Subring C) :
    Function.Injective (AddMonoidAlgebra.mapRingHom Γ S.subtype) := by
  intro x y h
  ext d
  have := congrArg (fun z => z.coeff d) h
  simp only [AddMonoidAlgebra.coeff_mapRingHom] at this
  exact congrArg Subtype.val (Subtype.ext this)

/-- The grading of a subring stable under all homogeneous components. -/
noncomputable def SDR3Asm_subσ (c : Coact C Γ) (S : Subring C) (hS : ∀ y ∈ S, ∀ d, c.comp d y ∈ S) :
    S →+* AddMonoidAlgebra S Γ :=
  (RingEquiv.ofBijective (AddMonoidAlgebra.mapRingHom Γ S.subtype).rangeRestrict
      ⟨fun _ _ h => SDR3Asm_map_injective S (congrArg Subtype.val h),
        (AddMonoidAlgebra.mapRingHom Γ S.subtype).rangeRestrict_surjective⟩).symm.toRingHom.comp
    ((c.σ.comp S.subtype).codRestrict _ fun y => SDR3Asm_mem_range S _ fun d => hS y y.2 d)

lemma SDR3Asm_subσ_map (c : Coact C Γ) (S : Subring C) (hS : ∀ y ∈ S, ∀ d, c.comp d y ∈ S) (y : S) :
    AddMonoidAlgebra.mapRingHom Γ S.subtype (SDR3Asm_subσ c S hS y) = c.σ y := by
  let E := RingEquiv.ofBijective (AddMonoidAlgebra.mapRingHom Γ S.subtype).rangeRestrict
      ⟨fun _ _ h => SDR3Asm_map_injective S (congrArg Subtype.val h),
        (AddMonoidAlgebra.mapRingHom Γ S.subtype).rangeRestrict_surjective⟩
  have := E.apply_symm_apply (((c.σ.comp S.subtype).codRestrict _ fun y => SDR3Asm_mem_range S _ fun d => hS y y.2 d) y)
  exact congrArg Subtype.val this

lemma SDR3Asm_subσ_coeff (c : Coact C Γ) (S : Subring C) (hS : ∀ y ∈ S, ∀ d, c.comp d y ∈ S) (y : S) (d : Γ) :
    (((SDR3Asm_subσ c S hS y).coeff d : S) : C) = c.comp d y := by
  have := congrArg (fun z => z.coeff d) (SDR3Asm_subσ_map c S hS y)
  simp only [AddMonoidAlgebra.coeff_mapRingHom] at this
  exact this

/-- The grading of a subring stable under all homogeneous components. -/
noncomputable def SDR3Asm_subCoact (c : Coact C Γ) (S : Subring C) (hS : ∀ y ∈ S, ∀ d, c.comp d y ∈ S) :
    Coact S Γ where
  σ := SDR3Asm_subσ c S hS
  sum_eq := fun y => by
    classical
    apply Subtype.ext
    have hsum : (((SDR3Asm_subσ c S hS y).coeff.sum fun _ a => a : S) : C) =
        ∑ d ∈ (SDR3Asm_subσ c S hS y).coeff.support, c.comp d y := by
      rw [Finsupp.sum, AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl fun d _ => SDR3Asm_subσ_coeff c S hS y d
    rw [hsum]
    conv_rhs => rw [← c.sum_eq (y : C)]
    rw [Finsupp.sum]
    refine Finset.sum_subset (fun d hd => ?_) (fun d _ hd => ?_)
    · rw [Finsupp.mem_support_iff] at hd ⊢
      intro h0
      apply hd
      apply Subtype.ext
      rw [SDR3Asm_subσ_coeff]
      exact h0
    · rw [Finsupp.notMem_support_iff] at hd
      have := SDR3Asm_subσ_coeff c S hS y d
      rw [hd] at this
      exact this.symm
  hom := fun y d => by
    apply SDR3Asm_map_injective S
    rw [SDR3Asm_subσ_map, AddMonoidAlgebra.mapRingHom_single]
    have e : (((SDR3Asm_subσ c S hS y).coeff d : S) : C) = c.comp d y := SDR3Asm_subσ_coeff c S hS y d
    change c.σ (((SDR3Asm_subσ c S hS y).coeff d : S) : C) =
      AddMonoidAlgebra.single d (((SDR3Asm_subσ c S hS y).coeff d : S) : C)
    rw [e]
    exact c.hom y d

lemma SDR3Asm_subCoact_comp (c : Coact C Γ) (S : Subring C) (hS : ∀ y ∈ S, ∀ d, c.comp d y ∈ S) (y : S) (d : Γ) :
    (((SDR3Asm_subCoact c S hS).comp d y : S) : C) = c.comp d y := SDR3Asm_subσ_coeff c S hS y d

/-- **Step 4**: the integral closure `C'` of `B` in the graded ring `C` is a graded subring, for `Γ ≅ ℤ^r`. -/
noncomputable def SDR3Asm_closureCoact {r : ℕ} (e : Γ ≃+ (Fin r → ℤ)) (cB : Coact B Γ) (cC : Coact C Γ)
    (hf : cC.σ.comp (algebraMap B C) = (AddMonoidAlgebra.mapRingHom Γ (algebraMap B C)).comp cB.σ) :
    Coact (integralClosure B C) Γ :=
  SDR3Asm_subCoact cC (integralClosure B C).toSubring fun _ hy d =>
    SDExist_comp_integral_free e cB cC (algebraMap B C) hf hy d

end Closure

section Elements

variable {Γ R B C : Type u} [AddCommGroup Γ] [CommRing R] [CommRing B] [CommRing C] [Algebra B C]
  {cB : Coact B Γ} {cC : Coact C Γ} {ι : R →+* B}

/-- A homogeneous `a ∉ 𝔫` gives `x` of degree `0`, multiple of `a`, with `x - h ∈ 𝔫`, `h ∉ P`. -/
theorem SDR3Asm_d₀ (hg : SDExist_IsGraded cB cC) (hι : cB.IsInv ι) {P : Ideal R} [P.IsPrime] {I : Ideal B}
    (hI : cB.IsHomIdeal I) (hIq : ∀ a, ι a ∈ I → a ∈ P)
    (hmax : ∀ J, cB.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ P)
    (𝔫 : Ideal C) [𝔫.IsPrime] (h𝔫 : cC.IsHomIdeal 𝔫) (h𝔫I : ∀ b, b ∈ I → algebraMap B C b ∈ 𝔫)
    (hR : ∀ s, algebraMap B C (ι s) ∈ 𝔫 → s ∈ P)
    (hfib : ∀ y : C, ∃ s, s ∉ P ∧ ∃ β, algebraMap B C (ι s) * y - algebraMap B C β ∈ 𝔫)
    {e : Γ} {a : C} (ha : cC.IsHom e a) (ha𝔫 : a ∉ 𝔫) :
    ∃ x b, x = a * b ∧ cC.IsHom 0 x ∧ ∃ h, h ∉ P ∧ x - algebraMap B C (ι h) ∈ 𝔫 := by
  obtain ⟨s, hs, β, hβ⟩ := hfib a
  have hsh : cC.IsHom 0 (algebraMap B C (ι s)) := by
    have h0 : cB.IsHom 0 (ι s) := (hι.range _).2 ⟨s, rfl⟩
    have h1 := hg 0 (ι s)
    rw [cB.comp_self_of_isHom h0] at h1
    rw [← h1]
    exact cC.comp_isHom 0 _
  have hsa : cC.IsHom e (algebraMap B C (ι s) * a) := by
    simpa using hsh.mul ha
  let β' := cB.comp e β
  have h1 : algebraMap B C (ι s) * a - algebraMap B C β' ∈ 𝔫 := by
    have := h𝔫 _ hβ e
    have e1 : cC.comp e (algebraMap B C (ι s) * a - algebraMap B C β) =
        cC.comp e (algebraMap B C (ι s) * a) - cC.comp e (algebraMap B C β) := by
      simp [Coact.comp]
    rw [e1, cC.comp_self_of_isHom hsa, hg] at this
    exact this
  have hsn : algebraMap B C (ι s) ∉ 𝔫 := fun h => hs (hR s h)
  have hβI : β' ∉ I := by
    intro hm
    have h2 := 𝔫.add_mem h1 (h𝔫I _ hm)
    rw [sub_add_cancel] at h2
    exact (Ideal.IsPrime.mem_or_mem ‹_› h2).elim hsn ha𝔫
  obtain ⟨h, hh, b', hb'⟩ := exists_inv_of_homog hι hI hIq hmax (cB.comp_isHom e β) hβI
  let b'' := cB.comp (0 - e) b'
  have hb'' : ι h = β' * b'' := by
    have h0 : cB.IsHom 0 (ι h) := (hι.range _).2 ⟨h, rfl⟩
    rw [← cB.comp_self_of_isHom h0, hb', cB.comp_mul_of_isHom (cB.comp_isHom e β)]
  have hbh : cC.IsHom (0 - e) (algebraMap B C b'') := by
    have h2 := hg (0 - e) b''
    rw [cB.comp_self_of_isHom (cB.comp_isHom _ _)] at h2
    rw [← h2]
    exact cC.comp_isHom _ _
  refine ⟨algebraMap B C (ι s) * a * algebraMap B C b'', algebraMap B C (ι s) * algebraMap B C b'', by ring, ?_, h, hh, ?_⟩
  · simpa using hsa.mul hbh
  · rw [hb'', map_mul, ← sub_mul]
    exact Ideal.mul_mem_right _ _ h1

end Elements

end AlgMag.SD
