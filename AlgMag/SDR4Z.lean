/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Move

/-!
# Lemma D, final bridge: the chart `Z = W' ×_R R'` over `Spec (R' ⊗ A)`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Steps 2, 3, 9: items 2-5 of the bridge. `Z → Spec (R' ⊗ A)` is étale and separated, an open `Vo` of `Z` with a coaction satisfies the
fields of `SDR3Asm_Data` other than the section `s₀`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Fs

variable {R₀ R₁ A₁ : Type u} [CommRing R₀] [CommRing R₁] [CommRing A₁] [Algebra R₀ R₁] [Algebra R₀ A₁]

/-- The pullback square of `Spec (R' ⊗ A)`. -/
lemma SDR4_pb₀ : IsPullback (sp (Algebra.TensorProduct.includeLeftRingHom : R₁ →+* R₁ ⊗[R₀] A₁))
    (sp ((Algebra.TensorProduct.includeRight : A₁ →ₐ[R₀] R₁ ⊗[R₀] A₁) : A₁ →+* R₁ ⊗[R₀] A₁))
    (sp (algebraMap R₀ R₁)) (sp (algebraMap R₀ A₁)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R₀ R₁ A₁)

lemma SDR4_fs_comp {𝒱 : Scheme.{u}} {B₀ B₁ : Type u} [CommRing B₀] [CommRing B₁] (f : 𝒱 ⟶ Spec (.of B₁)) (ψ : B₀ →+* B₁)
    (x : B₀) : SDR3Asm_fs (f ≫ sp ψ) x = SDR3Asm_fs f (ψ x) := by
  change (f ≫ sp ψ).appTop.hom _ = f.appTop.hom _
  rw [Scheme.Hom.comp_appTop]
  exact congrArg f.appTop.hom (appTop_sp_inv ψ x)

lemma SDR4_fs_tmul {𝒱 : Scheme.{u}} (f : 𝒱 ⟶ Spec (.of (R₁ ⊗[R₀] A₁))) (r : R₁) (a : A₁) :
    SDR3Asm_fs f (r ⊗ₜ a) =
      SDR3Asm_fs (f ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R₁ →+* R₁ ⊗[R₀] A₁)) r *
        SDR3Asm_fs (f ≫ sp ((Algebra.TensorProduct.includeRight : A₁ →ₐ[R₀] R₁ ⊗[R₀] A₁) : A₁ →+* R₁ ⊗[R₀] A₁)) a := by
  rw [SDR4_fs_comp, SDR4_fs_comp, ← map_mul]
  congr 1
  change _ = (r ⊗ₜ[R₀] (1 : A₁)) * ((1 : R₁) ⊗ₜ[R₀] a)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Fs

section Z

variable {P P₀ Λ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀] [AddCommGroup Λ] [Countable Λ]
  [AddGroup.FG Λ] (δ : P →+ Λ) (j : P₀ →+ P) (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [Algebra (gRing P₀ T) (gRing P T)] {R' : Type u} [CommRing R'] [Algebra (gRing P₀ T) R']

/-- `Spec R'` over `𝔸(P₀)_T`. -/
noncomputable def SDR4_Qr (hC : B.Contains (Spec (.of R'))) : BigFppfOver B S hS :=
  siteObject B S hS hC (sp (algebraMap (gRing P₀ T) R') ≫ (specObj P₀ T).hom.hom)

/-- `Spec R' → 𝔸(P₀)_T`. -/
noncomputable def SDR4_e (hC : B.Contains (Spec (.of R'))) : SDR4_Qr (P₀ := P₀) T hC ⟶ specObj P₀ T :=
  overHom (sp (algebraMap (gRing P₀ T) R')) rfl

variable {T} {W' : BigFppfOver B S hS} (p : W' ⟶ specObj P T) (hC : B.Contains (Spec (.of R')))

/-- `Z = W' ×_R R'`. -/
noncomputable abbrev SDR4_Z : BigFppfOver B S hS := Limits.pullback (p ≫ specAlong T j) (SDR4_e (P₀ := P₀) T hC)

/-- `Z → Spec (R' ⊗ A)`. -/
noncomputable def SDR4_f₀ (halg : algebraMap (gRing P₀ T) (gRing P T) = monι j _) :
    (SCH).obj (SDR4_Z j p hC) ⟶ Spec (.of (R' ⊗[gRing P₀ T] gRing P T)) :=
  (SDR4_pb₀ (R₀ := gRing P₀ T) (R₁ := R') (A₁ := gRing P T)).lift ((SCH).map (pullback.snd _ _))
    ((SCH).map (pullback.fst _ _) ≫ (SCH).map p) (by
      have h := congrArg (SCH).map (pullback.condition (f := p ≫ specAlong T j) (g := SDR4_e (P₀ := P₀) T hC))
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp] at h
      have e1 : (SCH).map (specAlong T j) = sp (algebraMap (gRing P₀ T) (gRing P T)) := by
        rw [halg]; rfl
      rw [e1] at h
      exact h.symm.trans (Category.assoc _ _ _).symm)

variable (halg : algebraMap (gRing P₀ T) (gRing P T) = monι j _)

lemma SDR4_f₀_L : SDR4_f₀ j p hC halg ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[gRing P₀ T] gRing P T) =
    (SCH).map (pullback.snd _ _) := IsPullback.lift_fst _ _ _ _

lemma SDR4_f₀_R : SDR4_f₀ j p hC halg ≫
    sp ((Algebra.TensorProduct.includeRight : gRing P T →ₐ[gRing P₀ T] R' ⊗[gRing P₀ T] gRing P T) :
      gRing P T →+* R' ⊗[gRing P₀ T] gRing P T) =
    (SCH).map (pullback.fst _ _) ≫ (SCH).map p := IsPullback.lift_snd _ _ _ _

/-- `Z` is the base change of `W'` along `Spec (R' ⊗ A) → Spec A`. -/
theorem SDR4_f₀_pb : IsPullback ((SCH).map (pullback.fst (p ≫ specAlong T j) (SDR4_e (P₀ := P₀) T hC))) (SDR4_f₀ j p hC halg)
    ((SCH).map p)
    (sp ((Algebra.TensorProduct.includeRight : gRing P T →ₐ[gRing P₀ T] R' ⊗[gRing P₀ T] gRing P T) :
      gRing P T →+* R' ⊗[gRing P₀ T] gRing P T)) := by
  have hs := ((IsPullback.of_hasPullback (p ≫ specAlong T j) (SDR4_e (P₀ := P₀) T hC)).map (SCH)).flip
  have e1 : (SCH).map (specAlong T j) = sp (algebraMap (gRing P₀ T) (gRing P T)) := by
    rw [halg]; rfl
  have hs' : IsPullback (SDR4_f₀ j p hC halg ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[gRing P₀ T] gRing P T))
      ((SCH).map (pullback.fst (p ≫ specAlong T j) (SDR4_e (P₀ := P₀) T hC))) (sp (algebraMap (gRing P₀ T) R'))
      ((SCH).map p ≫ sp (algebraMap (gRing P₀ T) (gRing P T))) := by
    have e2 : (SCH).map (p ≫ specAlong T j) = (SCH).map p ≫ sp (algebraMap (gRing P₀ T) (gRing P T)) := by
      rw [Functor.map_comp, e1]
      rfl
    rw [e2] at hs
    rw [SDR4_f₀_L]
    exact hs
  exact (IsPullback.of_right hs' (SDR4_f₀_R j p hC halg) SDR4_pb₀).flip

end Z

section Formula

variable {P Λ : Type u} [AddCommMonoid P] [Countable P] [AddCommGroup Λ] (δ : P →+ Λ) {T T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

lemma SDR4_specLift_app (t : T' ⟶ T) (a : APt (fppfO B S hS) P (op T')) (m : gRing P T) :
    ((SCH).map (specLift t a)).appTop.hom (SDR4_ofG P T m) = specRing t a m :=
  appTop_toSpec_comp (specRing t a) m

/-- `(g • w)^* m = w^* m · g(δ n)` for a monomial `m` of degree `n`. -/
lemma SDR4_smulW_app (g : APt (fppfO B S hS) Λ (op T')) (w : T' ⟶ specObj P T) (n : P) (x : Γ((SCH).obj T, ⊤)) :
    ((SCH).map (SDR3Coact_smulW δ g w)).appTop.hom (SDR4_ofG P T (AddMonoidAlgebra.single n x)) =
      ((SCH).map w).appTop.hom (SDR4_ofG P T (AddMonoidAlgebra.single n x)) *
        SDR4_cast g (Multiplicative.ofAdd (δ n)) := by
  have e1 : ((SCH).map w).appTop.hom (SDR4_ofG P T (AddMonoidAlgebra.single n x)) =
      specRing (w ≫ specPr P T) (APt.res w.op (specPt P T)) (AddMonoidAlgebra.single n x) := by
    conv_lhs => rw [← SDR3Coact_eta w]
    exact SDR4_specLift_app _ _ _
  rw [e1, SDR3Coact_smulW, SDR4_specLift_app, specRing_single, specRing_single]
  change _ * (SDR4_cast g (Multiplicative.ofAdd (δ n)) * SDR4_cast (APt.res w.op (specPt P T)) (Multiplicative.ofAdd n)) =
    _ * SDR4_cast (APt.res w.op (specPt P T)) (Multiplicative.ofAdd n) * _
  ring

end Formula

section Fields

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {P P₀ Λ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀]
  [Countable P₀] [AddCommGroup Λ] [Countable Λ] [AddGroup.FG Λ] (δ : P →+ Λ) (j : P₀ →+ P) {T : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] [Algebra (gRing P₀ T) (gRing P T)] {R' : Type u} [CommRing R']
  [Algebra (gRing P₀ T) R'] {W' : BigFppfOver B S hS} (p : W' ⟶ specObj P T) (hC : B.Contains (Spec (.of R')))
  (halg : algebraMap (gRing P₀ T) (gRing P T) = monι j _)

/-- The action on `Z`. -/
noncomputable def SDR4_actZ (hk0 : ∀ k, δ (j k) = 0) (act : AAction (fppfO B S hS) Λ (yoneda.obj W'))
    (hact : ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T')) (l : T' ⟶ W'),
      act.smul (U := op T') g l ≫ p = SDR3Coact_smulW δ g (l ≫ p)) :
    AAction (fppfO B S hS) Λ (yoneda.obj (SDR4_Z j p hC)) :=
  SDR4_pbAct act (p ≫ specAlong T j) _ (fun {T'} g l => by
    rw [← Category.assoc, hact, SDR4_smulW_along j δ hk0, Category.assoc])

include halg in
/-- `B → Γ(Vo)` is graded (bridge item 3). -/
theorem SDR4_hV (hcInv : ∀ r : gRing P₀ T, (monCoact (R := Γ((SCH).obj T, ⊤)) δ).σ (algebraMap _ (gRing P T) r) =
      AddMonoidAlgebra.single 0 (algebraMap _ (gRing P T) r))
    {Vo : BigFppfOver B S hS} (k : Vo ⟶ SDR4_Z j p hC) (actV : AAction (fppfO B S hS) Λ (yoneda.obj Vo))
    (hLeft : ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T')) (t : T' ⟶ Vo),
      actV.smul (U := op T') g t ≫ k ≫ pullback.snd _ _ = t ≫ k ≫ pullback.snd _ _)
    (hRight : ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T')) (t : T' ⟶ Vo),
      actV.smul (U := op T') g t ≫ k ≫ pullback.fst _ _ ≫ p = SDR3Coact_smulW δ g (t ≫ k ≫ pullback.fst _ _ ≫ p))
    {c : Coact Γ((SCH).obj Vo, ⊤) Λ}
    (hc : ∀ y, SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ (k ≫ pullback.fst _ _ ≫ p))).appTop.hom
        (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) (k ≫ pullback.fst _ _ ≫ p))) (c.σ y) =
      ((SCH).map (SDR3Coact_a actV (k ≫ pullback.fst _ _ ≫ p))).appTop.hom y)
    (d : Λ) (b : R' ⊗[gRing P₀ T] gRing P T) :
    c.comp d (SDR3Asm_fs ((SCH).map k ≫ SDR4_f₀ j p hC halg) b) =
      SDR3Asm_fs ((SCH).map k ≫ SDR4_f₀ j p hC halg) ((SDExist_bc R' (monCoact δ) hcInv).comp d b) := by
  classical
  let r₀ : Vo ⟶ specObj P T := k ≫ pullback.fst _ _ ≫ p
  let f := (SCH).map k ≫ SDR4_f₀ j p hC halg
  let π := SDR3Coact_π Λ r₀
  let a := SDR3Coact_a actV r₀
  let χ := SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r₀)
  let ℓL : Vo ⟶ SDR4_Qr (P₀ := P₀) T hC := k ≫ pullback.snd _ _
  let οL : R' →+* Γ((SCH).obj (SDR4_Qr (P₀ := P₀) T hC), ⊤) := (Scheme.ΓSpecIso (.of R')).inv.hom
  have hfL : ∀ u, SDR3Asm_fs (f ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[gRing P₀ T] gRing P T)) u =
      ((SCH).map ℓL).appTop.hom (οL u) := by
    intro u
    have : f ≫ sp (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[gRing P₀ T] gRing P T) = (SCH).map ℓL := by
      simp only [f, ℓL, Category.assoc, Functor.map_comp]
      rw [SDR4_f₀_L]
      rfl
    rw [this]
    rfl
  have hfR : ∀ m, SDR3Asm_fs (f ≫ sp ((Algebra.TensorProduct.includeRight :
      gRing P T →ₐ[gRing P₀ T] R' ⊗[gRing P₀ T] gRing P T) : gRing P T →+* R' ⊗[gRing P₀ T] gRing P T)) m =
      ((SCH).map r₀).appTop.hom (SDR4_ofG P T m) := by
    intro m
    have : f ≫ sp ((Algebra.TensorProduct.includeRight :
        gRing P T →ₐ[gRing P₀ T] R' ⊗[gRing P₀ T] gRing P T) : gRing P T →+* R' ⊗[gRing P₀ T] gRing P T) = (SCH).map r₀ := by
      simp only [f, r₀, Category.assoc, Functor.map_comp]
      rw [SDR4_f₀_R]
      rfl
    rw [this]
    rfl
  have haL : a ≫ ℓL = π ≫ ℓL := hLeft _ _
  have haR : a ≫ r₀ = SDR3Coact_smulW δ (SDR3Coact_χ Λ r₀) (π ≫ r₀) := hRight _ _
  have hσ : ∀ (r : R') (n : P) (x : Γ((SCH).obj T, ⊤)),
      (SDExist_bc R' (monCoact δ) hcInv).σ (r ⊗ₜ AddMonoidAlgebra.single n x) =
        AddMonoidAlgebra.single (δ n) (r ⊗ₜ AddMonoidAlgebra.single n x) := by
    intro r n x
    have hm : (monCoact (R := Γ((SCH).obj T, ⊤)) δ).σ (AddMonoidAlgebra.single n x) =
        AddMonoidAlgebra.single (δ n) (AddMonoidAlgebra.single n x) := monσ_single _ _ _
    ext e
    change (SDExist_bc R' (monCoact δ) hcInv).comp e _ = _
    rw [SDExist_bc_comp, Coact.comp, hm]
    by_cases he : δ n = e
    · subst he; simp
    · simp [he]
  let cT := SDExist_bc R' (monCoact δ) hcInv
  let Ψ₁ : (R' ⊗[gRing P₀ T] gRing P T) →+* Γ((SCH).obj (SDR3Coact_Y Λ r₀), ⊤) :=
    ((SCH).map a).appTop.hom.comp (SDR3Asm_fs f)
  let Ψ₂ : (R' ⊗[gRing P₀ T] gRing P T) →+* Γ((SCH).obj (SDR3Coact_Y Λ r₀), ⊤) :=
    (SDR3Coact_lift ((SCH).map π).appTop.hom χ).comp ((AddMonoidAlgebra.mapRingHom Λ (SDR3Asm_fs f)).comp cT.σ)
  have key : ∀ b, Ψ₁ b = Ψ₂ b := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add y z hy hz => rw [map_add, map_add, hy, hz]
    | tmul r m =>
      induction m using AddMonoidAlgebra.induction_linear with
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add y z hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
      | single n x =>
        change ((SCH).map a).appTop.hom (SDR3Asm_fs f _) =
          SDR3Coact_lift ((SCH).map π).appTop.hom χ (AddMonoidAlgebra.mapRingHom Λ (SDR3Asm_fs f) (cT.σ _))
        rw [hσ, AddMonoidAlgebra.mapRingHom_single, SDR3Coact_lift_single, SDR4_fs_tmul, hfL, hfR, map_mul, map_mul,
          ← SDR4_app_comp a ℓL, ← SDR4_app_comp a r₀, ← SDR4_app_comp π ℓL, ← SDR4_app_comp π r₀, haL, haR, SDR4_smulW_app]
        change _ * (_ * SDR4_cast (SDR3Coact_χ Λ r₀) (Multiplicative.ofAdd (δ n))) =
          _ * _ * SDR4_cast (SDR3Coact_χ Λ r₀) (Multiplicative.ofAdd (δ n))
        ring
  exact SDR4_graded actV r₀ hc cT (SDR3Asm_fs f) key d b

end Fields

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_f₀_pb
#print axioms AlgMag.SD.SDR4_hV
