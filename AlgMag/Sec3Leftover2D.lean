/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover2C

/-!
# Algebraic Magnetism: Example 3.33 as closed subschemes, Fact 2.6 via `GB.mul`, §16.4 (ii) base change

* `AlgMag.GB.faceIota`, `faceIota_closed`, `repFace_toPoint`: for `L ∩ N` a face of `L`, the attractor
  `𝔸(L)^N`, represented by `𝔸(L ∩ N)_S`, is a closed subscheme of `𝔸(L)_S` (Example 3.21).
* `AlgMag.GB.ex333_closed`, `ex333_zero_closed`: Example 3.33: both attractors are closed in `𝔸²_S`.
* `AlgMag.GB.fact26_mul`: Fact 2.6: on charts, the dual of the comultiplication is `GB.mul`.
* `AlgMag.S16R.stageTopEquiv_baseChange`, `stagesChain_baseChange`: §16.4 (ii) is natural in `T`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped TensorProduct

noncomputable section

namespace AlgMag.S16R

variable {C : Type*} [Category.{u} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M₁ M₂ : Type u} [AddCommMonoid M₁] [AddCommMonoid M₂] {F : Cᵒᵖ ⥤ Type u}
  (act : AAction 𝒪 (M₁ × M₂) F) (N₁ : AddSubmonoid M₁) (N₂ : AddSubmonoid M₂)

/-- **§16.4 (ii)**: `stageTopEquiv` commutes with base change. -/
lemma stageTopEquiv_baseChange {T T' : C} (s : T' ⟶ T)
    (ψ : BigPt (attractorAction act (N₁.prod (⊤ : AddSubmonoid M₂)))
      ((⊤ : AddSubmonoid M₁).prod N₂) T) :
    stageTopEquiv act N₁ N₂ T' (ψ.baseChange s) = (stageTopEquiv act N₁ N₂ T ψ).baseChange s := rfl

/-- **§16.4 (ii)**: `stagesChain` commutes with base change, so it is an isomorphism of functors. -/
lemma stagesChain_baseChange {T T' : C} (s : T' ⟶ T) (φ : AttractorPt act (N₁.prod N₂) T) :
    stagesChain act N₁ N₂ T' (φ.baseChange s) = (stagesChain act N₁ N₂ T φ).baseChange s := by
  apply (stageTopEquiv act N₁ N₂ T').injective
  rw [stageTopEquiv_baseChange]
  change stageTopEquiv act N₁ N₂ T' ((stageTopEquiv act N₁ N₂ T').symm
      (stagesEquiv act N₁ N₂ T' (φ.baseChange s))) =
    (stageTopEquiv act N₁ N₂ T ((stageTopEquiv act N₁ N₂ T).symm
      (stagesEquiv act N₁ N₂ T φ))).baseChange s
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, stagesEquiv_baseChange]

end AlgMag.S16R

namespace AlgMag.GB

section Face

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M] (L N : AddSubmonoid M)
  (hf : ∀ a b : L, ((a + b : L) : M) ∈ N → (a : M) ∈ N ∧ (b : M) ∈ N)

open Classical in
/-- `X^n ↦ X^n` if `n ∈ N`, else `0`. -/
def faceMon : Multiplicative L →* zRing (L ⊓ N : AddSubmonoid M) where
  toFun n := if h : ((Multiplicative.toAdd n : L) : M) ∈ N then
    AddMonoidAlgebra.single ⟨_, AddSubmonoid.mem_inf.mpr ⟨(Multiplicative.toAdd n).2, h⟩⟩ 1 else 0
  map_one' := (dif_pos N.zero_mem).trans rfl
  map_mul' a b := by
    by_cases hab : ((Multiplicative.toAdd (a * b) : L) : M) ∈ N
    · obtain ⟨ha, hb⟩ := hf _ _ hab
      refine (dif_pos hab).trans (Eq.trans ?_
        (congrArg₂ (· * ·) (dif_pos ha).symm (dif_pos hb).symm))
      refine Eq.trans ?_ (AddMonoidAlgebra.single_mul_single ..).symm
      rw [mul_one]
      rfl
    · refine (dif_neg hab).trans ?_
      by_cases ha : ((Multiplicative.toAdd a : L) : M) ∈ N
      · have hb : ((Multiplicative.toAdd b : L) : M) ∉ N := fun hb => hab (N.add_mem ha hb)
        exact ((congrArg (_ * ·) (dif_neg hb)).trans (mul_zero _)).symm
      · exact ((congrArg (· * _) (dif_neg ha)).trans (zero_mul _)).symm

/-- `ℤ[L] → ℤ[L ∩ N]`, killing the monomials outside `N`. -/
def faceRing : zRing L ⟶ zRing (L ⊓ N : AddSubmonoid M) := liftZ (faceMon L N hf)

lemma faceRing_surjective : Function.Surjective (faceRing L N hf).hom := by
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | single n c =>
    have hn := AddSubmonoid.mem_inf.mp n.2
    refine ⟨c • AddMonoidAlgebra.single (⟨n.1, hn.1⟩ : L) 1, ?_⟩
    rw [map_zsmul, faceRing, liftZ_X]
    refine (congrArg (c • ·) (dif_pos hn.2)).trans ?_
    simp [AddMonoidAlgebra.smul_single]

/-- **Example 3.21**: the morphism `𝔸(L ∩ N)_S → 𝔸(L)_S`, extension by zero. -/
def faceIota : A (L ⊓ N : AddSubmonoid M) S ⟶ A L S :=
  (pts _).symm (extOff L N hf (pts _ (𝟙 _)))

lemma extOff_res {T T' : Over S} (g : T' ⟶ T) (y : APt (overO S) (L ⊓ N : AddSubmonoid M) (op T)) :
    extOff L N hf (APt.res g.op y) = APt.res g.op (extOff L N hf y) := by
  refine MonoidHom.ext fun n => ?_
  by_cases hn : ((Multiplicative.toAdd n : L) : M) ∈ N
  · have e : extOff L N hf y n = _ := dif_pos hn
    exact (dif_pos hn).trans (congrArg (fun v => ((overO S).map g.op).hom v) e.symm)
  · have e : extOff L N hf y n = 0 := dif_neg hn
    exact (dif_neg hn).trans
      ((congrArg (fun v => ((overO S).map g.op).hom v) e).trans
        (map_zero ((overO S).map g.op).hom)).symm

lemma pts_comp_faceIota {T : Over S} (z : T ⟶ A (L ⊓ N : AddSubmonoid M) S) :
    pts T (z ≫ faceIota L N hf) = extOff L N hf (pts T z) := by
  rw [pts_comp, faceIota, Equiv.apply_symm_apply, ← extOff_res, ← pts_comp, Category.comp_id]

/-- `𝔸(L)^N → 𝔸(L)` on the scheme `𝔸(L ∩ N)_S` is `faceIota`. -/
theorem repFace_toPoint {T : Over S} (z : T ⟶ A (L ⊓ N : AddSubmonoid M) S) :
    (repFace L N hf T z).toPoint = z ≫ faceIota L N hf :=
  (pts T).injective ((pts_attPt_toPoint L N _ fun n hn => dif_neg hn).trans
    (pts_comp_faceIota L N hf z).symm)

lemma toAZ_faceIota : (faceIota (S := S) L N hf).left ≫ toAZ L S =
    toAZ (L ⊓ N : AddSubmonoid M) S ≫ Spec.map (faceRing L N hf) := by
  refine (ptsZ _).injective (MonoidHom.ext fun n => ?_)
  have h1 : ptsZ _ ((faceIota (S := S) L N hf).left ≫ toAZ L S) =
      extOff L N hf (pts _ (𝟙 (A (L ⊓ N : AddSubmonoid M) S))) :=
    (pts _).apply_symm_apply _
  rw [h1]
  change _ = (homSpecEquiv _ _ (toAZ (L ⊓ N : AddSubmonoid M) S ≫ Spec.map (faceRing L N hf))).hom
    (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  rw [homSpecEquiv_map]
  change _ = (homSpecEquiv _ _ (toAZ (L ⊓ N : AddSubmonoid M) S)).hom
    ((faceRing L N hf).hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1))
  rw [faceRing, liftZ_X]
  by_cases hn : ((Multiplicative.toAdd n : L) : M) ∈ N
  · have e : faceMon L N hf (Multiplicative.ofAdd (Multiplicative.toAdd n)) =
        AddMonoidAlgebra.single ⟨_, AddSubmonoid.mem_inf.mpr ⟨(Multiplicative.toAdd n).2, hn⟩⟩ 1 :=
      dif_pos hn
    rw [e]
    exact dif_pos hn
  · have e : faceMon L N hf (Multiplicative.ofAdd (Multiplicative.toAdd n)) = 0 := dif_neg hn
    rw [e, map_zero]
    exact dif_neg hn

/-- The square exhibiting `faceIota` as a base change of `Spec ℤ[L ∩ N] → Spec ℤ[L]`. -/
theorem isPullback_faceIota : IsPullback (faceIota (S := S) L N hf).left
    (toAZ (L ⊓ N : AddSubmonoid M) S) (toAZ L S) (Spec.map (faceRing L N hf)) := by
  refine IsPullback.of_right (h₁₂ := (A L S).hom) (h₂₂ := terminal.from (AZ L))
    (v₁₃ := terminal.from S) ?_ (toAZ_faceIota L N hf) (IsPullback.of_hasPullback _ _)
  have h1 : (faceIota (S := S) L N hf).left ≫ (A L S).hom = (A (L ⊓ N : AddSubmonoid M) S).hom :=
    Over.w _
  have h2 : Spec.map (faceRing L N hf) ≫ terminal.from (AZ L) =
      terminal.from (AZ (L ⊓ N : AddSubmonoid M)) := terminal.hom_ext _ _
  rw [h1, h2]
  exact IsPullback.of_hasPullback _ _

/-- **Example 3.21**: `𝔸(L)^N`, represented by `𝔸(L ∩ N)_S`, is a closed subscheme of `𝔸(L)_S`. -/
theorem faceIota_closed : IsClosedImmersion (faceIota (S := S) L N hf).left := by
  have : IsClosedImmersion (Spec.map (faceRing L N hf)) :=
    IsClosedImmersion.spec_of_surjective _ (faceRing_surjective L N hf)
  exact MorphismProperty.of_isPullback (isPullback_faceIota L N hf).flip this

end Face

section Ex333

variable (S : Scheme.{u})

lemma X2_face (a b : Q2.{u}) (h : ((a + b : Q2.{u}) : Z2.{u}) ∈ X2.{u}) :
    (a : Z2.{u}) ∈ X2.{u} ∧ (b : Z2.{u}) ∈ X2.{u} := by
  have h2 : (a.1.down.2 + b.1.down.2 : ℤ) = 0 := h.2
  have pa : (0 : ℤ) ≤ a.1.down.2 := a.2.2
  have pb : (0 : ℤ) ≤ b.1.down.2 := b.2.2
  have qa : (0 : ℤ) ≤ a.1.down.1 := a.2.1
  have qb : (0 : ℤ) ≤ b.1.down.1 := b.2.1
  exact ⟨⟨qa, by change a.1.down.2 = 0; omega⟩, ⟨qb, by change b.1.down.2 = 0; omega⟩⟩

lemma bot_face (a b : Q2.{u}) (h : ((a + b : Q2.{u}) : Z2.{u}) ∈ (⊥ : AddSubmonoid Z2.{u})) :
    (a : Z2.{u}) ∈ (⊥ : AddSubmonoid Z2.{u}) ∧ (b : Z2.{u}) ∈ (⊥ : AddSubmonoid Z2.{u}) := by
  have h0 := AddSubmonoid.mem_bot.mp h
  have h1 : (a.1.down.1 + b.1.down.1 : ℤ) = 0 := congrArg (fun z : Z2.{u} => z.down.1) h0
  have h2 : (a.1.down.2 + b.1.down.2 : ℤ) = 0 := congrArg (fun z : Z2.{u} => z.down.2) h0
  have pa : (0 : ℤ) ≤ a.1.down.2 := a.2.2
  have pb : (0 : ℤ) ≤ b.1.down.2 := b.2.2
  have qa : (0 : ℤ) ≤ a.1.down.1 := a.2.1
  have qb : (0 : ℤ) ≤ b.1.down.1 := b.2.1
  refine ⟨AddSubmonoid.mem_bot.mpr (ULift.ext _ _ (Prod.ext ?_ ?_)),
    AddSubmonoid.mem_bot.mpr (ULift.ext _ _ (Prod.ext ?_ ?_))⟩ <;>
  · change (_ : ℤ) = 0
    omega

/-- **Example 3.33**: `X^{ℕ×0} = 𝔸¹_S ×_S 0` is a closed subscheme of `𝔸²_S = 𝔸(ℕ²)_S`. -/
theorem ex333_closed :
    IsClosedImmersion (faceIota (S := S) Q2.{u} X2.{u} X2_face).left :=
  faceIota_closed _ _ _

/-- **Example 3.33**: `X^{(ℕ×0)∩(0×ℕ)} = X^{0} = 0_{𝔸²_S}` is a closed subscheme of `𝔸²_S`. -/
theorem ex333_zero_closed :
    IsClosedImmersion (faceIota (S := S) Q2.{u} ⊥ bot_face).left :=
  faceIota_closed _ _ _

end Ex333

section Comul

variable (N : Type u) [AddCommMonoid N] (R : CommRingCat.{u}) {S : Scheme.{u}} (s : Spec R ⟶ S)

lemma specComul_piR : specComul N R ≫ piR N R = specFst N R ≫ piR N R := by
  simp only [specComul, specFst, piR, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  exact ((Bialgebra.comulAlgHom R (AddMonoidAlgebra R N)).commutes r).trans
    ((Algebra.TensorProduct.includeLeft :
      AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R N ⊗[R] AddMonoidAlgebra R N).commutes r).symm

lemma specSnd_piR : specSnd N R ≫ piR N R = specFst N R ≫ piR N R := by
  simp only [specSnd, specFst, piR, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  exact ((Algebra.TensorProduct.includeRight :
      AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R N ⊗[R] AddMonoidAlgebra R N).commutes r).trans
    ((Algebra.TensorProduct.includeLeft :
      AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R N ⊗[R] AddMonoidAlgebra R N).commutes r).symm

/-- `Spec (R[N] ⊗_R R[N])` over `S`. -/
abbrev T2 : Over S := Over.mk (specFst N R ≫ piR N R ≫ s)

/-- The chart composed with the first projection. -/
def j₁ : T2 N R s ⟶ A N S := Over.homMk (specFst N R ≫ (jS N R s).left) (by
  have := Over.w (jS N R s)
  simp only [Category.assoc, Over.mk_hom]
  exact congrArg (specFst N R ≫ ·) this)

/-- The chart composed with the second projection. -/
def j₂ : T2 N R s ⟶ A N S := Over.homMk (specSnd N R ≫ (jS N R s).left) (by
  have := Over.w (jS N R s)
  simp only [Category.assoc, Over.mk_hom]
  refine (congrArg (specSnd N R ≫ ·) this).trans ?_
  simpa [Category.assoc] using congrArg (· ≫ s) (specSnd_piR N R))

/-- The chart composed with the dual of the comultiplication. -/
def jc : T2 N R s ⟶ A N S := Over.homMk (specComul N R ≫ (jS N R s).left) (by
  have := Over.w (jS N R s)
  simp only [Category.assoc, Over.mk_hom]
  refine (congrArg (specComul N R ≫ ·) this).trans ?_
  simpa [Category.assoc] using congrArg (· ≫ s) (specComul_piR N R))

/-- **Fact 2.6**: on the chart `Spec R[N] → 𝔸(N)_S`, the dual of the comultiplication of `R[N]` is the
multiplication morphism `GB.mul` of `𝔸(N)_S`. -/
theorem fact26_mul : jc N R s = CartesianMonoidalCategory.lift (j₁ N R s) (j₂ N R s) ≫ mul N S := by
  refine (pts _).injective ?_
  rw [pts_mul]
  exact fact26_comul N R s

end Comul

end AlgMag.GB

#print axioms AlgMag.S16R.stageTopEquiv_baseChange
#print axioms AlgMag.S16R.stagesChain_baseChange
#print axioms AlgMag.GB.repFace_toPoint
#print axioms AlgMag.GB.faceIota_closed
#print axioms AlgMag.GB.ex333_closed
#print axioms AlgMag.GB.ex333_zero_closed
#print axioms AlgMag.GB.fact26_mul
