/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDLocAFinite
import AlgMag.SDExistBaseChange

/-!
# Lemma D, Step 3 (iv)-(v), purely algebraic form

Step 3 (iv)-(v) of the proof of Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`:
the grading of `D = (R'' ⊗ C)/(1-e)`, and the section `D → (R'' ⊗ B)_h` for an invariant `h ∉ q`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

open AlgMag.SQ

section Quot

variable {T Γ : Type u} [CommRing T] [AddCommGroup Γ] (c : Coact T Γ) (J : Ideal T) (hJ : c.IsHomIdeal J)

include hJ in
lemma SDLocA_map_σ_eq_zero {y : T} (hy : y ∈ J) :
    AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J) (c.σ y) = 0 := by
  ext d
  rw [AddMonoidAlgebra.coeff_mapRingHom]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hJ y hy d)

/-- The grading of a quotient by a homogeneous ideal. -/
noncomputable def SDLocA_quot : Coact (T ⧸ J) Γ where
  σ := Ideal.Quotient.lift J ((AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J)).comp c.σ)
    fun _ hy => SDLocA_map_σ_eq_zero c J hJ hy
  sum_eq := fun z => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.Quotient.lift_mk]
    conv_rhs => rw [← c.sum_eq y]
    have e : ∀ d, (((AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J)).comp c.σ) y).coeff d =
        Ideal.Quotient.mk J ((c.σ y).coeff d) := fun d => by
      change (AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J) (c.σ y)).coeff d = _
      rw [AddMonoidAlgebra.coeff_mapRingHom]
    have hsub : (((AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J)).comp c.σ) y).coeff.support ⊆
        (c.σ y).coeff.support := fun d hd => by
      rw [Finsupp.mem_support_iff] at hd ⊢
      intro h0
      apply hd
      rw [e, h0, map_zero]
    simp only [Finsupp.sum, map_sum]
    exact (Finset.sum_subset hsub fun d _ hd => Finsupp.notMem_support_iff.1 hd).trans
      (Finset.sum_congr rfl fun d _ => e d)
  hom := fun z d => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    have e0 : ((AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J)).comp c.σ y).coeff d =
        Ideal.Quotient.mk J (c.comp d y) := by
      change (AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J) (c.σ y)).coeff d = _
      rw [AddMonoidAlgebra.coeff_mapRingHom]
      rfl
    rw [Ideal.Quotient.lift_mk, e0, Ideal.Quotient.lift_mk]
    change AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J) (c.σ (c.comp d y)) = _
    have h := c.hom y d
    change c.σ (c.comp d y) = AddMonoidAlgebra.single d (c.comp d y) at h
    rw [h, AddMonoidAlgebra.mapRingHom_single]

lemma SDLocA_quot_comp (d : Γ) (y : T) :
    (SDLocA_quot c J hJ).comp d (Ideal.Quotient.mk J y) = Ideal.Quotient.mk J (c.comp d y) := by
  change ((Ideal.Quotient.lift J ((AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J)).comp c.σ)
    (fun _ hy => SDLocA_map_σ_eq_zero c J hJ hy)) (Ideal.Quotient.mk J y)).coeff d = _
  rw [Ideal.Quotient.lift_mk]
  change (AddMonoidAlgebra.mapRingHom Γ (Ideal.Quotient.mk J) (c.σ y)).coeff d = _
  rw [AddMonoidAlgebra.coeff_mapRingHom]
  rfl

/-- The ideal `(1-e)`, for `e` of degree zero, is homogeneous. -/
lemma SDLocA_span_hom {e : T} (he : c.IsHom 0 e) : c.IsHomIdeal (Ideal.span {1 - e}) := by
  have h1 : c.IsHom 0 (1 - e) := by
    change c.σ (1 - e) = AddMonoidAlgebra.single 0 (1 - e)
    have he' : c.σ e = AddMonoidAlgebra.single 0 e := he
    rw [map_sub, map_one, he', AddMonoidAlgebra.one_def, ← AddMonoidAlgebra.single_sub]
  intro y hy d
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have := c.comp_mul_of_isHom h1 a d
  rw [sub_zero] at this
  rw [mul_comm a, this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end Quot

variable {R B C Γ : Type u} (R'' : Type u) [CommRing R] [CommRing B] [CommRing C] [CommRing R''] [AddCommGroup Γ]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] [Algebra R R'']
  (cB : Coact B Γ) (cC : Coact C Γ)
  (hcB : ∀ r : R, cB.σ (algebraMap R B r) = AddMonoidAlgebra.single 0 (algebraMap R B r))
  (hcC : ∀ r : R, cC.σ (algebraMap R C r) = AddMonoidAlgebra.single 0 (algebraMap R C r))

/-- **Step 3 (iv)-(v), the form used on the scheme side.** `B → C` graded, `C` integral over `B`, `C_d` étale over `B`, and
`e` an idempotent of degree zero of `R'' ⊗ C`, with `1 ⊗ d` a unit on its corner. Put `D = (R'' ⊗ C)/(1-e)`. If `D` is onto
modulo the closed orbit `I` and has a prime `𝔯` over `q`, one invariant `h ∉ q` gives the section `D → (R'' ⊗ B)_h`,
together with the bijection `(R'' ⊗ B)_h → D_h`. -/
theorem SDLocA_main (hBC : ∀ (d : Γ) (b : B), cC.comp d (algebraMap B C b) = algebraMap B C (cB.comp d b))
    (hιB : cB.IsInv (algebraMap R B)) [Algebra.IsIntegral B C] (x : C) [Algebra.Etale B (Localization.Away x)]
    {e : R'' ⊗[R] C} (he : IsIdempotentElem e) (hu : ∃ u, e = u * ((1 : R'') ⊗ₜ[R] x) * e)
    (he0 : (SDExist_bc R'' cC hcC).IsHom 0 e)
    {q : Ideal R''} [q.IsPrime] {I : Ideal (R'' ⊗[R] B)}
    (hI : (SDExist_bc R'' cB hcB).IsHomIdeal I)
    (hIq : ∀ a : R'', a ⊗ₜ[R] (1 : B) ∈ I → a ∈ q)
    (hmax : ∀ J, (SDExist_bc R'' cB hcB).IsHomIdeal J → I < J → ∃ a : R'', a ⊗ₜ[R] (1 : B) ∈ J ∧ a ∉ q) :
    letI := SDLocA_alg R B C R''
    ∀ (H1 : ∀ y : (R'' ⊗[R] C) ⧸ Ideal.span {1 - e}, ∃ b,
        y - algebraMap (R'' ⊗[R] B) _ b ∈ I.map (algebraMap (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e})))
      (𝔯 : Ideal ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e})) (_ : 𝔯.IsPrime)
      (_ : ∀ a : R'', algebraMap (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e}) (a ⊗ₜ[R] (1 : B)) ∈ 𝔯 → a ∈ q),
      ∃ h : R'', h ∉ q ∧
        (∀ y : (R'' ⊗[R] C) ⧸ Ideal.span {1 - e}, ∃ b,
          algebraMap (R'' ⊗[R] B) _ (h ⊗ₜ[R] (1 : B)) * y = algebraMap (R'' ⊗[R] B) _ b) ∧
        (∀ b : R'' ⊗[R] B, algebraMap (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e}) b = 0 →
          ∃ n : ℕ, (h ⊗ₜ[R] (1 : B)) ^ n * b = 0) ∧
        ∃ s : (R'' ⊗[R] C) ⧸ Ideal.span {1 - e} →+* Localization.Away (h ⊗ₜ[R] (1 : B) : R'' ⊗[R] B),
          ∀ b : R'' ⊗[R] B, s (algebraMap (R'' ⊗[R] B) _ b) = algebraMap (R'' ⊗[R] B) _ b := by
  letI := SDLocA_alg R B C R''
  intro H1 𝔯 h𝔯P h𝔯
  obtain ⟨hE, hF, hFl, hP⟩ := SDLocA_finite R B R'' C x he hu
  let cT := SDExist_bc R'' cC hcC
  let cD := SDLocA_quot cT (Ideal.span {1 - e}) (SDLocA_span_hom cT he0)
  have hg : SDExist_IsGraded (SDExist_bc R'' cB hcB) cD := by
    intro d b
    induction b using TensorProduct.induction_on with
    | zero => simp [Coact.comp]
    | add a c ha hc => rw [map_add, Coact.comp_add, ha, hc, Coact.comp_add, map_add]
    | tmul r b =>
      change cD.comp d (Ideal.Quotient.mk _ (r ⊗ₜ[R] algebraMap B C b)) =
        Ideal.Quotient.mk _ _
      rw [SDLocA_quot_comp, SDExist_bc_comp, SDExist_bc_comp, hBC]
      rfl
  have hι := SDExist_bc_isInv R'' cB hcB hιB
  obtain ⟨h, hh, hs, hi⟩ := SDLocA_uniform (ι := Algebra.TensorProduct.includeLeftRingHom) hg hι hI hIq hmax H1 𝔯 h𝔯
  exact ⟨h, hh, hs, hi, SDLocA_section hs hi⟩

end AlgMag.SD

#print axioms AlgMag.SD.SDLocA_main
