/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover2A
import AlgMag.Sec3Leftover2F
import AlgMag.Sec3Final

/-!
# Algebraic Magnetism: Fact 2.6 (comultiplication), Example 3.33 (representability), §16.4 (ii) (middle term)

* `AlgMag.GB.fact26_comul`, `fact26_counit`: the comultiplication of `𝒪[N]` is that of `𝔸(N)`.
* `AlgMag.GB.repFace`, `ex333_rep`: Example 3.33: `X^{ℕ×0}` is represented by the scheme `𝔸(ℕ² ∩ (ℕ×0))_S`.
* `AlgMag.S16R.stageTopEquiv`, `stagesChain`: §16.4 (ii), `(X^{N₁×M₂})^{M₁×N₂} = (X^{N₁})^{N₂}`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open scoped TensorProduct

noncomputable section

namespace AlgMag.S16R

variable {C : Type*} [Category.{u} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M₁ M₂ : Type u} [AddCommMonoid M₁] [AddCommMonoid M₂] {F : Cᵒᵖ ⥤ Type u}
  (act : AAction 𝒪 (M₁ × M₂) F) (N₁ : AddSubmonoid M₁) (N₂ : AddSubmonoid M₂)

/-- The first coordinate of a point of `𝔸(M₁ × N₂)`. -/
def top₁ {U : Cᵒᵖ} (c : APt 𝒪 ((⊤ : AddSubmonoid M₁).prod N₂) U) : APt 𝒪 M₁ U :=
  c.comp (AddMonoidHom.toMultiplicative
    { toFun := fun m => ⟨(m, 0), trivial, N₂.zero_mem⟩, map_zero' := rfl
      map_add' := fun a b => Subtype.ext (Prod.ext rfl (add_zero 0).symm) })

/-- `prodTopEquiv` on the functors of points. -/
def pTop (T : C) : (attractor act (N₁.prod (⊤ : AddSubmonoid M₂))).obj (op T) ≃
    (attractor (actFst act) N₁).obj (op T) := prodTopEquiv act N₁ T

lemma pTop_smul_inr {T : C} (h : APt 𝒪 M₂ (op T))
    (φ : (attractor act (N₁.prod (⊤ : AddSubmonoid M₂))).obj (op T)) :
    pTop act N₁ T ((attractorAction act _).smul (inrPt h) φ) =
      (actSnd act N₁).smul h (pTop act N₁ T φ) := rfl

lemma pTop_symm_smul_inr {T : C} (h : APt 𝒪 M₂ (op T))
    (x : (attractor (actFst act) N₁).obj (op T)) :
    (pTop act N₁ T).symm ((actSnd act N₁).smul h x) =
      (attractorAction act _).smul (inrPt h) ((pTop act N₁ T).symm x) := by
  apply (pTop act N₁ T).injective
  rw [Equiv.apply_symm_apply, pTop_smul_inr, Equiv.apply_symm_apply]

lemma pTop_symm_map {T T' : C} (s : T' ⟶ T) (x : (attractor (actFst act) N₁).obj (op T)) :
    (pTop act N₁ T').symm ((attractor (actFst act) N₁).map s.op x) =
      (attractor act _).map s.op ((pTop act N₁ T).symm x) := by
  apply (pTop act N₁ T').injective
  have e : pTop act N₁ T' ((attractor act _).map s.op ((pTop act N₁ T).symm x)) =
      (attractor (actFst act) N₁).map s.op (pTop act N₁ T ((pTop act N₁ T).symm x)) := rfl
  rw [e, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **§16.4 (ii)**, the middle equality, any site and any `X`:
`(X^{N₁ × M₂}_{M₁ × M₂})^{M₁ × N₂}_{M₁ × M₂} = (X^{N₁ × 0}_{M₁ × 0})^{0 × N₂}_{0 × M₂}`. -/
def stageTopEquiv (T : C) :
    BigPt (attractorAction act (N₁.prod (⊤ : AddSubmonoid M₂)))
        ((⊤ : AddSubmonoid M₁).prod N₂) T ≃ BigPt (actSnd act N₁) N₂ T where
  toFun ψ :=
    { app := fun {T'} t b => pTop act N₁ T' (ψ.app t (glue ⊤ N₂ 1 b))
      naturality := fun {T' T''} s t b => by
        have e : glue (⊤ : AddSubmonoid M₁) N₂ 1 (APt.res s.op b) =
            APt.res s.op (glue ⊤ N₂ 1 b) := by
          rw [← glue_res]
          congr 1
          exact MonoidHom.ext fun _ => (map_one (𝒪.map s.op).hom).symm
        rw [e, ψ.naturality]
        rfl
      equivariant := fun {T'} t h b => by
        rw [glue_mul', ψ.equivariant]
        rfl }
  invFun χ :=
    { app := fun {T'} t c => (attractorAction act _).smul (inlPt (top₁ N₂ c))
        ((pTop act N₁ T').symm (χ.app t (cut₂ ⊤ N₂ c)))
      naturality := fun {T' T''} s t c => by
        refine Eq.trans ?_ ((attractorAction act _).map_smul s.op _ _).symm
        congr 1
        have e : cut₂ (⊤ : AddSubmonoid M₁) N₂ (APt.res s.op c) =
            APt.res s.op (cut₂ ⊤ N₂ c) := rfl
        rw [e, χ.naturality]
        exact pTop_symm_map act N₁ s _
      equivariant := fun {T'} t k c => by
        have hc₂ : cut₂ (⊤ : AddSubmonoid M₁) N₂ (APt.toMagnet _ k * c) =
            APt.toMagnet N₂ (k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M₁ M₂))) *
              cut₂ ⊤ N₂ c := rfl
        rw [hc₂, χ.equivariant, pTop_symm_smul_inr]
        refine (((attractorAction act _).mul_smul _ _ _).symm).trans
          (Eq.trans ?_ ((attractorAction act _).mul_smul _ _ _))
        congr 1
        have h2 : inlPt (M₂ := M₂) (top₁ N₂ (APt.toMagnet _ k * c)) =
            inlPt (M₂ := M₂) (k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M₁ M₂))) *
              inlPt (M₂ := M₂) (top₁ N₂ c) := MonoidHom.ext fun _ => rfl
        rw [h2]
        conv_rhs => rw [← split_pt k]
        ac_rfl }
  left_inv ψ := by
    refine BigPt.ext ?_
    funext T' t c
    change (attractorAction act _).smul _ ((pTop act N₁ T').symm
      (pTop act N₁ T' (ψ.app t _))) = _
    rw [Equiv.symm_apply_apply, ← ψ.equivariant]
    have e : APt.toMagnet ((⊤ : AddSubmonoid M₁).prod N₂) (inlPt (top₁ N₂ c)) *
        glue ⊤ N₂ 1 (cut₂ ⊤ N₂ c) = c := by
      rw [← glue_mul, mul_one]
      exact glue_cut ⊤ N₂ c
    rw [e]
  right_inv χ := by
    refine BigPt.ext ?_
    funext T' t b
    change pTop act N₁ T' ((attractorAction act _).smul (inlPt (top₁ N₂ (glue ⊤ N₂ 1 b)))
      ((pTop act N₁ T').symm (χ.app t (cut₂ ⊤ N₂ (glue ⊤ N₂ 1 b))))) = _
    rw [cut₂_glue]
    have h1 : inlPt (M₂ := M₂) (top₁ N₂ (glue (⊤ : AddSubmonoid M₁) N₂ 1 b)) = 1 := by
      refine MonoidHom.ext fun n => ?_
      have hb : b (Multiplicative.ofAdd (⟨0, N₂.zero_mem⟩ : N₂)) = 1 := b.map_one
      exact (congrArg (_ * ·) hb).trans (mul_one _)
    rw [h1, (attractorAction act _).one_smul, Equiv.apply_symm_apply]

/-- **§16.4 (ii)** whole: `X^{N₁ × N₂} = (X^{N₁ × M₂})^{M₁ × N₂} = (X^{N₁})^{N₂}`, as a bijection on
points composed from `stagesEquiv` and `stageTopEquiv`. -/
def stagesChain (T : C) : AttractorPt act (N₁.prod N₂) T ≃
    BigPt (attractorAction act (N₁.prod (⊤ : AddSubmonoid M₂)))
      ((⊤ : AddSubmonoid M₁).prod N₂) T :=
  (stagesEquiv act N₁ N₂ T).trans (stageTopEquiv act N₁ N₂ T).symm

end AlgMag.S16R

namespace AlgMag.GB

section Comul

variable (N : Type u) [AddCommMonoid N] (R : CommRingCat.{u})

/-- `R[N]`. -/
local notation "RN" => AddMonoidAlgebra R N

/-- `Spec (R[N] ⊗_R R[N])`. -/
abbrev PR2 : Scheme.{u} := Spec (CommRingCat.of (RN ⊗[R] RN))

/-- The comultiplication on spectra. -/
def specComul : PR2 N R ⟶ PR N R :=
  Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R RN).toRingHom)
/-- First projection. -/
def specFst : PR2 N R ⟶ PR N R :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : RN →ₐ[R] RN ⊗[R] RN).toRingHom)
/-- Second projection. -/
def specSnd : PR2 N R ⟶ PR N R :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : RN →ₐ[R] RN ⊗[R] RN).toRingHom)
/-- The counit on spectra. -/
def specCounit : Spec R ⟶ PR N R :=
  Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R RN).toRingHom)

lemma comul_single_one (R : Type u) [CommRing R] (n : N) :
    Coalgebra.comul (R := R) (AddMonoidAlgebra.single n (1 : R)) =
      (Algebra.TensorProduct.includeLeft :
          AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R N ⊗[R] AddMonoidAlgebra R N)
        (AddMonoidAlgebra.single n 1) *
      (Algebra.TensorProduct.includeRight :
          AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R N ⊗[R] AddMonoidAlgebra R N)
        (AddMonoidAlgebra.single n 1) := by
  simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.tmul_mul_tmul]

variable {S : Scheme.{u}} (s : Spec R ⟶ S)

/-- The coordinate `X^n` pulled back along the spectrum of a ring map. -/
lemma coord_spec {B : CommRingCat.{u}} (f : CommRingCat.of RN ⟶ B) (n : N) :
    ptsZ (Spec B) (Spec.map f ≫ (jS N R s).left ≫ toAZ N S) (Multiplicative.ofAdd n) =
      (Scheme.ΓSpecIso B).inv.hom (f.hom (AddMonoidAlgebra.single n 1)) := by
  rw [ptsZ_comp, ptsZ_jS]
  exact (congrArg (fun k => k.hom (AddMonoidAlgebra.single n (1 : R)))
    (Scheme.ΓSpecIso_inv_naturality f)).symm

/-- **Fact 2.6**, the comultiplication: on the chart `Spec R[N] → 𝔸(N)_S`, the map dual to the
comultiplication of `R[N]` is the multiplication of `𝔸(N)`: `Δ(X^n) = X^n ⊗ X^n`. -/
theorem fact26_comul : ptsZ (PR2 N R) (specComul N R ≫ (jS N R s).left ≫ toAZ N S) =
    ptsZ (PR2 N R) (specFst N R ≫ (jS N R s).left ≫ toAZ N S) *
      ptsZ (PR2 N R) (specSnd N R ≫ (jS N R s).left ≫ toAZ N S) := by
  refine MonoidHom.ext fun n => ?_
  refine (coord_spec N R s _ (Multiplicative.toAdd n)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (coord_spec N R s _ (Multiplicative.toAdd n)).symm
    (coord_spec N R s _ (Multiplicative.toAdd n)).symm)
  refine Eq.trans (congrArg _ ?_) (map_mul (Scheme.ΓSpecIso _).inv.hom _ _)
  exact comul_single_one N R _

/-- **Fact 2.6**, the counit: `ε(X^n) = 1`, the unit point of `𝔸(N)`. -/
theorem fact26_counit : ptsZ (Spec R) (specCounit N R ≫ (jS N R s).left ≫ toAZ N S) = 1 := by
  refine MonoidHom.ext fun n => ?_
  refine (coord_spec N R s _ (Multiplicative.toAdd n)).trans ?_
  refine (congrArg _ ?_).trans (map_one (Scheme.ΓSpecIso R).inv.hom)
  exact AddMonoidAlgebra.counit_single _ _ |>.trans (by simp)

end Comul

section Rep

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M] (L N : AddSubmonoid M)

open Classical in
/-- Extension by zero. -/
def extOff (hf : ∀ a b : L, ((a + b : L) : M) ∈ N → (a : M) ∈ N ∧ (b : M) ∈ N) {T : Over S}
    (y : APt (overO S) (L ⊓ N : AddSubmonoid M) (op T)) : APt (overO S) L (op T) where
  toFun n := if h : ((Multiplicative.toAdd n : L) : M) ∈ N then
    y (Multiplicative.ofAdd ⟨_, AddSubmonoid.mem_inf.mpr ⟨(Multiplicative.toAdd n).2, h⟩⟩) else 0
  map_one' := (dif_pos N.zero_mem).trans (map_one y)
  map_mul' a b := by
    by_cases hab : ((Multiplicative.toAdd (a * b) : L) : M) ∈ N
    · obtain ⟨ha, hb⟩ := hf _ _ hab
      refine (dif_pos hab).trans (Eq.trans ?_
        (congrArg₂ (· * ·) (dif_pos ha).symm (dif_pos hb).symm))
      exact map_mul y
        (Multiplicative.ofAdd ⟨_, AddSubmonoid.mem_inf.mpr ⟨(Multiplicative.toAdd a).2, ha⟩⟩)
        (Multiplicative.ofAdd ⟨_, AddSubmonoid.mem_inf.mpr ⟨(Multiplicative.toAdd b).2, hb⟩⟩)
    · refine (dif_neg hab).trans ?_
      by_cases ha : ((Multiplicative.toAdd a : L) : M) ∈ N
      · have hb : ((Multiplicative.toAdd b : L) : M) ∉ N := fun hb => hab (N.add_mem ha hb)
        exact ((congrArg (_ * ·) (dif_neg hb)).trans (mul_zero _)).symm
      · exact ((congrArg (· * _) (dif_neg ha)).trans (zero_mul _)).symm

/-- Restriction `𝔸(L) → 𝔸(L ∩ N)`. -/
def resInf {T : Over S} (x : APt (overO S) L (op T)) :
    APt (overO S) (L ⊓ N : AddSubmonoid M) (op T) :=
  x.comp (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion inf_le_left))

lemma resInf_extOff (hf : ∀ a b : L, ((a + b : L) : M) ∈ N → (a : M) ∈ N ∧ (b : M) ∈ N) {T : Over S}
    (y : APt (overO S) (L ⊓ N : AddSubmonoid M) (op T)) : resInf L N (extOff L N hf y) = y :=
  MonoidHom.ext fun n => dif_pos (AddSubmonoid.mem_inf.mp (Multiplicative.toAdd n).2).2

lemma extOff_resInf (hf : ∀ a b : L, ((a + b : L) : M) ∈ N → (a : M) ∈ N ∧ (b : M) ∈ N) {T : Over S}
    (x : APt (overO S) L (op T))
    (hx : ∀ n : L, (n : M) ∉ N → x (Multiplicative.ofAdd n) = 0) :
    extOff L N hf (resInf L N x) = x := by
  refine MonoidHom.ext fun n => ?_
  by_cases hn : ((Multiplicative.toAdd n : L) : M) ∈ N
  · exact dif_pos hn
  · exact (dif_neg hn).trans (hx _ hn).symm

/-- **Example 3.21 / 3.33**, representability: if `L ∩ N` is a face of `L`, then `𝔸(L)^N` is represented by
the scheme `𝔸(L ∩ N)_S`. -/
def repFace (hf : ∀ a b : L, ((a + b : L) : M) ∈ N → (a : M) ∈ N ∧ (b : M) ∈ N) (T : Over S) :
    (T ⟶ A (L ⊓ N : AddSubmonoid M) S) ≃ AttractorPt (aAction L S) N T where
  toFun z := attPt L N (extOff L N hf (pts T z)) fun n hn => dif_neg hn
  invFun φ := (pts T).symm (resInf L N (pts T φ.toPoint))
  left_inv z := by
    apply (pts T).injective
    refine ((pts T).apply_symm_apply _).trans ?_
    refine (congrArg (resInf L N) (pts_attPt_toPoint L N _ _)).trans ?_
    exact resInf_extOff L N hf _
  right_inv φ := by
    refine toPoint_injective_global ((pts T).injective ?_)
    refine (pts_attPt_toPoint L N _ _).trans ?_
    refine (congrArg (extOff L N hf) ((pts T).apply_symm_apply _)).trans ?_
    exact extOff_resInf L N hf _ ((exists_att_A_iff L N φ.toPoint).mp ⟨φ, rfl⟩)

/-- `repFace` commutes with base change: the bijection is natural in `T`, so `𝔸(L ∩ N)_S` represents
the functor `𝔸(L)^N`. -/
lemma repFace_baseChange (hf : ∀ a b : L, ((a + b : L) : M) ∈ N → (a : M) ∈ N ∧ (b : M) ∈ N)
    {T T' : Over S} (s : T' ⟶ T) (z : T ⟶ A (L ⊓ N : AddSubmonoid M) S) :
    repFace L N hf T' (s ≫ z) = (repFace L N hf T z).baseChange s := by
  have key : ∀ {T₀ : Over S} (z₀ : T₀ ⟶ A (L ⊓ N : AddSubmonoid M) S),
      pts T₀ (repFace L N hf T₀ z₀).toPoint = extOff L N hf (pts T₀ z₀) := fun z₀ =>
    pts_attPt_toPoint L N _ fun n hn => dif_neg hn
  refine toPoint_injective_global ((pts T').injective ?_)
  rw [toPoint_baseChange, pts_comp, key, key, pts_comp]
  refine MonoidHom.ext fun n => ?_
  by_cases hn : ((Multiplicative.toAdd n : L) : M) ∈ N
  · have e : extOff L N hf (pts T z) n = _ := dif_pos hn
    exact (dif_pos hn).trans (congrArg (fun v => ((overO S).map s.op).hom v) e.symm)
  · have e : extOff L N hf (pts T z) n = 0 := dif_neg hn
    exact (dif_neg hn).trans
      ((congrArg (fun v => ((overO S).map s.op).hom v) e).trans
        (map_zero ((overO S).map s.op).hom)).symm

/-- **Example 3.33**: the first equality as a representability statement: `X^{ℕ×0}` is represented by
`𝔸(ℕ² ∩ (ℕ×0))_S`, the line `𝔸¹_S ×_S 0`. -/
def ex333_rep (T : Over S) :
    (T ⟶ A (Q2.{u} ⊓ X2.{u} : AddSubmonoid Z2.{u}) S) ≃ AttractorPt (aAction Q2.{u} S) X2.{u} T :=
  repFace Q2 X2 (fun a b h => by
    have h2 : (a.1.down.2 + b.1.down.2 : ℤ) = 0 := h.2
    have pa : (0 : ℤ) ≤ a.1.down.2 := a.2.2
    have pb : (0 : ℤ) ≤ b.1.down.2 := b.2.2
    have qa : (0 : ℤ) ≤ a.1.down.1 := a.2.1
    have qb : (0 : ℤ) ≤ b.1.down.1 := b.2.1
    exact ⟨⟨qa, by change a.1.down.2 = 0; omega⟩, ⟨qb, by change b.1.down.2 = 0; omega⟩⟩) T

end Rep

end AlgMag.GB

#print axioms AlgMag.S16R.stageTopEquiv
#print axioms AlgMag.S16R.stagesChain
#print axioms AlgMag.GB.fact26_comul
#print axioms AlgMag.GB.fact26_counit
#print axioms AlgMag.GB.repFace
#print axioms AlgMag.GB.repFace_baseChange
#print axioms AlgMag.GB.ex333_rep
