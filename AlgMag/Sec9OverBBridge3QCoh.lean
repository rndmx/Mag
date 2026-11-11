/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge3Sheaf

/-!
# A quasi-coherent module of `Space.Modules` gives a `PrintedQCoh` module

Base change for `famPMod 𝓜` between affines is proved in three steps: over a chart (`fam_cart_chart`),
along flat morphisms (`fam_cart_flat`, Stacks `isIso_restrictionBaseChange_of_cover`), and in general
(`isBC_of_cover`, faithfully flat descent of bijectivity).
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace AlgMag.B3

open AlgMag.S9B AlgMag.S9 AlgebraicGeometry.Space

section Alg

theorem bij_of_pi {R' E₁ E₂ : Type u} [CommRing R'] [AddCommGroup E₁] [AddCommGroup E₂]
    [Module R' E₁] [Module R' E₂] {ι : Type*} [Finite ι] (Si : ι → Type u) [∀ i, CommRing (Si i)]
    [∀ i, Algebra R' (Si i)] [Module.FaithfullyFlat R' (∀ i, Si i)] (Φ : E₁ →ₗ[R'] E₂)
    (h : ∀ i, Function.Bijective (Φ.lTensor (Si i))) : Function.Bijective Φ := by
  classical
  haveI := Fintype.ofFinite ι
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective R' (∀ i, Si i)]
  let e₁ : (∀ i, Si i) ⊗[R'] E₁ ≃ₗ[R'] ∀ i, Si i ⊗[R'] E₁ := TensorProduct.piLeft ..
  let e₂ : (∀ i, Si i) ⊗[R'] E₂ ≃ₗ[R'] ∀ i, Si i ⊗[R'] E₂ := TensorProduct.piLeft ..
  let g : (∀ i, Si i ⊗[R'] E₁) → ∀ i, Si i ⊗[R'] E₂ := fun x i => Φ.lTensor (Si i) (x i)
  have hg : Function.Bijective g := Function.Bijective.piMap h
  have key : ∀ z, e₂ (Φ.lTensor (∀ i, Si i) z) = g (e₁ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [g]; rfl
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb, map_add]
      funext i
      simp [g]
    | tmul a y =>
      funext i
      simp [g, e₁, e₂]
  have e : (fun z => Φ.lTensor (∀ i, Si i) z) = e₂.symm ∘ g ∘ e₁ := by
    funext z
    simp only [Function.comp, ← key, LinearEquiv.symm_apply_apply]
  change Function.Bijective (fun z => Φ.lTensor (∀ i, Si i) z)
  rw [e]
  exact e₂.symm.bijective.comp (hg.comp e₁.bijective)

/-- Base change descends along a faithfully flat family of the target ring. -/
theorem isBC_of_cover {R R' E E' : Type u} [CommRing R] [CommRing R'] [AddCommGroup E]
    [AddCommGroup E'] [Module R E] [Module R' E'] {ι : Type*} [Finite ι] (Si : ι → Type u)
    [∀ i, CommRing (Si i)] (Di : ι → Type u) [∀ i, AddCommGroup (Di i)] [∀ i, Module (Si i) (Di i)]
    (h : R →+* R') (φ : E →+ E') (hφ : ∀ r x, φ (r • x) = h r • φ x)
    (k : ∀ i, R' →+* Si i) (q : ∀ i, E' →+ Di i) (hq : ∀ i r x, q i (r • x) = k i r • q i x)
    (H1 : ∀ i, IsBC (k i) (q i) (hq i))
    (H2 : ∀ i, IsBC ((k i).comp h) ((q i).comp φ) (fun r x => by
      simp only [AddMonoidHom.comp_apply, hφ, hq, RingHom.comp_apply]))
    (hff : (RingHom.pi k).FaithfullyFlat) : IsBC h φ hφ := by
  letI := h.toAlgebra
  letI mE : Module R E' := Module.compHom E' h
  haveI : IsScalarTower R R' E' := ⟨fun r s x => by
    change (h r * s) • x = h r • s • x
    rw [mul_smul]⟩
  let L : E →ₗ[R] E' := { toFun := φ, map_add' := φ.map_add, map_smul' := hφ }
  let Φ : R' ⊗[R] E →ₗ[R'] E' := LinearMap.liftBaseChange R' L
  letI : ∀ i, Algebra R' (Si i) := fun i => (k i).toAlgebra
  haveI : Module.FaithfullyFlat R' (∀ i, Si i) :=
    (RingHom.faithfullyFlat_algebraMap_iff).1 hff
  have hb : Function.Bijective Φ := by
    refine bij_of_pi Si Φ fun i => ?_
    letI : Module R' (Di i) := Module.compHom _ (k i)
    haveI : IsScalarTower R' (Si i) (Di i) := ⟨fun r s x => by
      change (k i r * s) • x = k i r • s • x
      rw [mul_smul]⟩
    letI : Algebra R (Si i) := ((k i).comp h).toAlgebra
    letI : Module R (Di i) := Module.compHom _ ((k i).comp h)
    haveI : IsScalarTower R (Si i) (Di i) := ⟨fun r s x => by
      change ((k i).comp h r * s) • x = (k i).comp h r • s • x
      rw [mul_smul]⟩
    haveI : IsScalarTower R R' (Si i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let L1 : E' →ₗ[R'] Di i := { toFun := q i, map_add' := (q i).map_add, map_smul' := hq i }
    let L2 : E →ₗ[R] Di i := ⟨⟨(q i).comp φ, ((q i).comp φ).map_add⟩, fun r x => by
      change q i (φ (r • x)) = k i (h r) • q i (φ x)
      rw [hφ, hq]⟩
    have h1 : IsBaseChange (Si i) L1 := H1 i
    have h2 : IsBaseChange (Si i) L2 := H2 i
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange R R' (Si i) (Si i) E
    have key : ∀ z, h1.equiv (Φ.lTensor (Si i) z) = h2.equiv (c z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add u v hu hv =>
          simp only [TensorProduct.tmul_add, map_add, hu, hv]
        | tmul r x =>
          simp only [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul]
          simp only [c, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            IsBaseChange.equiv_tmul]
          simp only [Φ, LinearMap.liftBaseChange_tmul]
          change a • q i (r • φ x) = (r • a) • q i (φ x)
          rw [hq, Algebra.smul_def, mul_comm, mul_smul]
          rfl
    have e : (fun z => Φ.lTensor (Si i) z) = h1.equiv.symm ∘ h2.equiv ∘ c := by
      funext z
      simp only [Function.comp, ← key, LinearEquiv.symm_apply_apply]
    change Function.Bijective (fun z => Φ.lTensor (Si i) z)
    rw [e]
    exact h1.equiv.symm.bijective.comp (h2.equiv.bijective.comp c.bijective)
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ hb) fun x => ?_
  change Φ (1 ⊗ₜ x) = L x
  simp [Φ]

theorem isBC_comp {R R' R'' E E' E'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    [AddCommGroup E] [AddCommGroup E'] [AddCommGroup E''] [Module R E] [Module R' E'] [Module R'' E'']
    (h : R →+* R') (φ : E →+ E') (hφ : ∀ r x, φ (r • x) = h r • φ x)
    (h' : R' →+* R'') (φ' : E' →+ E'') (hφ' : ∀ r x, φ' (r • x) = h' r • φ' x)
    (H : IsBC h φ hφ) (H' : IsBC h' φ' hφ') :
    IsBC (h'.comp h) (φ'.comp φ) (fun r x => (congrArg φ' (hφ r x)).trans (hφ' _ _)) := by
  letI := h.toAlgebra
  letI := h'.toAlgebra
  letI := (h'.comp h).toAlgebra
  letI : Module R E' := Module.compHom E' h
  haveI : IsScalarTower R R' E' := ⟨fun r s x => by
    change (h r * s) • x = h r • s • x
    rw [mul_smul]⟩
  letI : Module R' E'' := Module.compHom E'' h'
  haveI : IsScalarTower R' R'' E'' := ⟨fun r s x => by
    change (h' r * s) • x = h' r • s • x
    rw [mul_smul]⟩
  letI : Module R E'' := Module.compHom E'' (h'.comp h)
  haveI : IsScalarTower R R'' E'' := ⟨fun r s x => by
    change ((h'.comp h) r * s) • x = (h'.comp h) r • s • x
    rw [mul_smul]⟩
  haveI : IsScalarTower R R' R'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R R' E'' := ⟨fun r s x => by
    change h' (r • s) • x = (h'.comp h) r • h' s • x
    rw [← mul_smul, Algebra.smul_def, map_mul]
    rfl⟩
  have h1 : IsBaseChange R' (⟨⟨φ, φ.map_add⟩, hφ⟩ : E →ₗ[R] E') := H
  have h2 : IsBaseChange R'' (⟨⟨φ', φ'.map_add⟩, hφ'⟩ : E' →ₗ[R'] E'') := H'
  have h3 := h1.comp h2
  refine IsBaseChange.of_equiv h3.equiv fun x => ?_
  exact (IsBaseChange.equiv_tmul h3 1 x).trans (one_smul _ _)

theorem isBC_congr {R R' E E' : Type u} [CommRing R] [CommRing R'] [AddCommGroup E] [AddCommGroup E']
    [Module R E] [Module R' E'] {h h₂ : R →+* R'} {φ φ₂ : E →+ E'} {hφ : ∀ r x, φ (r • x) = h r • φ x}
    (hφ₂ : ∀ r x, φ₂ (r • x) = h₂ r • φ₂ x) (e : h = h₂) (e' : φ = φ₂) (H : IsBC h φ hφ) :
    IsBC h₂ φ₂ hφ₂ := by
  subst e e'
  exact H

end Alg

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace Bs S hS Bsp}
  (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB)

/-- The evaluation at a chart, as an isomorphism. -/
def evalE (h𝓜 : 𝓜.IsQuasicoherentOnSite) {T : SB Bsp} (hT : IsAffine T.left)
    {V₀ : AffineEtale Bs S hS Bsp} (τ : T ⟶ cB V₀) : (famPMod 𝓜).obj (op T) ≃+ Dv 𝓜 τ :=
  (famE 𝓜 T).trans (AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun x : Fam 𝓜 T => x.val hT (𝟙 T) τ) (fun _ _ => rfl))
    (eval_bijective' 𝓜 h𝓜 hT τ))

/-- **Base change over a chart.** -/
theorem fam_cart_chart (h𝓜 : 𝓜.IsQuasicoherentOnSite) {X Y : SB Bsp} (hX : IsAffine X.left)
    (hY : IsAffine Y.left) (a : Y ⟶ X) {V₀ : AffineEtale Bs S hS Bsp} (τ : X ⟶ cB V₀) :
    IsBC ((OB Bsp).map a.op).hom ((famPMod 𝓜).map a.op) ((famPMod 𝓜).map_smul a.op) := by
  refine AlgMag.S9BF.isBC_transport ((OB Bsp).map a.op).hom ((famPMod 𝓜).map a.op)
    ((famPMod 𝓜).map_smul a.op) (ρ 𝓜 a (𝟙 V₀) (sq1 a τ)) (ρ_smul 𝓜 a (𝟙 V₀) (sq1 a τ))
    (evalE 𝓜 h𝓜 hX τ) ?_ (evalE 𝓜 h𝓜 hY (a ≫ τ)) ?_ ?_ (ρ_isBC 𝓜 a (sq1 a τ))
  · intro r x
    have e : evalE 𝓜 h𝓜 hX τ x = (famE 𝓜 X x).val hX (𝟙 X) τ := rfl
    have e2 : evalE 𝓜 h𝓜 hX τ (r • x) = (famE 𝓜 X (r • x)).val hX (𝟙 X) τ := rfl
    rw [e, e2, famE_smul, Fam.smul_val, op_id, (OB Bsp).map_id]
    rfl
  · intro r x
    have e : evalE 𝓜 h𝓜 hY (a ≫ τ) x = (famE 𝓜 Y x).val hY (𝟙 Y) (a ≫ τ) := rfl
    have e2 : evalE 𝓜 h𝓜 hY (a ≫ τ) (r • x) = (famE 𝓜 Y (r • x)).val hY (𝟙 Y) (a ≫ τ) := rfl
    rw [e, e2, famE_smul, Fam.smul_val, op_id, (OB Bsp).map_id]
    rfl
  · intro x
    change (famE 𝓜 Y ((famPMod 𝓜).map a.op x)).val hY (𝟙 Y) (a ≫ τ) =
      ρ 𝓜 a (𝟙 V₀) (sq1 a τ) ((famE 𝓜 X x).val hX (𝟙 X) τ)
    rw [famE_map, (famE 𝓜 X x).compat hY hX (𝟙 X) τ (a ≫ τ) a (𝟙 V₀) (sq1 a τ)]
    change (famE 𝓜 X x).val hY (𝟙 Y ≫ a) (a ≫ τ) = (famE 𝓜 X x).val hY (a ≫ 𝟙 X) (a ≫ τ)
    rw [Category.id_comp, Category.comp_id]

variable {𝓜}

/-- A family over an affine object: `Cov` for the sieve it generates. -/
theorem cov_of_family {T : SB Bsp} (hT : IsAffine T.left) {I : Type (u + 1)} [Finite I] (W : I → SB Bsp)
    (g : ∀ i, W i ⟶ T) (hW : ∀ i, IsAffine (W i).left) (hfl : ∀ i, Flat (SB.Hom.left (g i)))
    (hsu : ∀ x : T.left, ∃ i, x ∈ Set.range (SB.Hom.left (g i))) :
    Cov (Sieve.generate (Presieve.ofArrows W g)) := by
  intro A hA a
  have hw := fun i => sb_isPullback a (g i)
  refine ⟨I, inferInstance, fun i => sbPb a (g i), fun i => sbFst a (g i),
    fun i => isAffine_of_isPullback (hw i) hA (hW i) hT,
    fun i => flat_of_isPullback (hw i) (hfl i), fun x => ?_, fun i => ?_⟩
  · obtain ⟨i, y, hy⟩ := hsu (SB.Hom.left a x)
    obtain ⟨z, h1, -⟩ := exists_pt_of_isPullback (hw i) x y hy.symm
    exact ⟨i, z, h1⟩
  · exact ⟨W i, sbSnd a (g i), g i, Presieve.ofArrows.mk i, (hw i).w.symm⟩

/-- Open covers: the Zariski part of `IsQCoh`. -/
theorem cov_open (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (R : Sieve T) (hR : coverSieve T 𝒰 ≤ R) :
    Cov R := by
  intro A hA a
  classical
  have hch : ∀ x : A.left, ∃ (A' : SB Bsp) (t : A' ⟶ A), IsAffine A'.left ∧
      IsOpenImmersion (SB.Hom.left t) ∧ x ∈ Set.range (SB.Hom.left t) ∧ R.arrows (t ≫ a) := by
    intro x
    obtain ⟨y, hy⟩ := 𝒰.covers (SB.Hom.left a x)
    obtain ⟨A', t, l, hA', hop, hx, he⟩ := geo_opn a (coverHom T 𝒰 _)
      (inferInstanceAs (IsOpenImmersion (𝒰.f _))) x ⟨y, hy⟩
    refine ⟨A', t, hA', hop, hx, hR _ ⟨_, SB.Hom.left l, ?_⟩⟩
    rw [← he, SB.comp_left]
    rfl
  choose Ai t hAi hop hx hin using hch
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x => Set.range (SB.Hom.left (t x))) (fun x => (hop x).base_open.isOpen_range)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨ULift.{u + 1} F, inferInstance, fun i => Ai i.down, fun i => t i.down, fun i => hAi _,
    fun i => by haveI := hop i.down.1; infer_instance, fun x => ?_, fun i => hin _⟩
  have := hF (Set.mem_univ x)
  simp only [Set.mem_iUnion] at this
  obtain ⟨i, hi, h⟩ := this
  exact ⟨⟨⟨i, hi⟩⟩, h⟩

/-- An affine object over `B` has a finite flat surjective family of affines mapping to charts. -/
theorem exists_chart_family {T : SB Bsp} (hB : IsAlgebraicSpace Bs S hS Bsp) (hT : IsAffine T.left) :
    ∃ (J : Type (u + 1)) (_ : Finite J) (W : J → SB Bsp) (g : ∀ j, W j ⟶ T),
      (∀ j, IsAffine (W j).left) ∧ (∀ j, Flat (SB.Hom.left (g j))) ∧
      (∀ x : T.left, ∃ j, x ∈ Set.range (SB.Hom.left (g j))) ∧
      ∀ j, ∃ V : AffineEtale Bs S hS Bsp, Nonempty (W j ⟶ cB V) := by
  classical
  obtain ⟨U, f, hfS, hfE⟩ := hB.exists_atlas
  let gT : yoneda.obj T.obj ⟶ Bsp := yonedaEquiv.symm T.pt
  let P : BigFppfOver Bs S hS := hfE.rep.pullback gT
  let a : P ⟶ U := hfE.rep.fst' gT
  let b : P ⟶ T.obj := hfE.rep.snd gT
  have hsq : yoneda.map a ≫ f = yoneda.map b ≫ gT := (hfE.rep.isPullback' gT).w
  have hbs : Surjective ((BigFppfOver.toScheme Bs S hS).map b) :=
    hfS.property gT (hfE.rep.fst gT) (hfE.rep.snd gT) (hfE.rep.isPullback gT)
  have hbe : Etale ((BigFppfOver.toScheme Bs S hS).map b) :=
    hfE.property gT (hfE.rep.fst gT) (hfE.rep.snd gT) (hfE.rep.isPullback gT)
  let Q : SmallEtale Bs S hS Bsp := ⟨CostructuredArrow.mk f, hfE⟩
  let Ps : SB Bsp := ⟨P, Bsp.map b.op T.pt⟩
  let bs : Ps ⟶ T := ⟨b, rfl⟩
  have hpt : Bsp.map a.op (yonedaEquiv f) = Bsp.map b.op T.pt := by
    refine (yonedaEquiv_naturality _ _).trans ((congrArg yonedaEquiv hsq).trans ?_)
    refine (yonedaEquiv_naturality _ _).symm.trans ?_
    rw [Equiv.apply_symm_apply]
  let c : Ps ⟶ cBs Q := ⟨a, hpt⟩
  have hbl : SB.Hom.left bs = (BigFppfOver.toScheme Bs S hS).map b := rfl
  have hopenb : IsOpenMap (SB.Hom.left bs) := by
    rw [hbl]
    haveI : UniversallyOpen ((BigFppfOver.toScheme Bs S hS).map b) := inferInstance
    exact ((BigFppfOver.toScheme Bs S hS).map b).isOpenMap
  have hch : ∀ x : T.left, ∃ (A' : SB Bsp) (t : A' ⟶ Ps) (W : AffineEtale Bs S hS Bsp) (i : W.obj ⟶ Q)
      (w : A' ⟶ cB W), IsAffine A'.left ∧ IsOpenImmersion (SB.Hom.left t) ∧
        x ∈ Set.range (SB.Hom.left (t ≫ bs)) := by
    intro x
    obtain ⟨y, hy⟩ := hbs.surj x
    obtain ⟨A', t, W, i, w, hA', hop, ⟨z, hz⟩, -⟩ := exists_affine_chart c y
    refine ⟨A', t, W, i, w, hA', hop, z, ?_⟩
    rw [SB.comp_left]
    change SB.Hom.left bs (SB.Hom.left t z) = x
    rw [hz]
    exact hy
  choose Ai t Wc ic wc hAi hop hx using hch
  haveI := hT
  have hopen : ∀ x, IsOpen (Set.range (SB.Hom.left (t x ≫ bs))) := fun x => by
    rw [SB.comp_left]
    haveI := hop x
    change IsOpen (Set.range ((SB.Hom.left bs) ∘ (SB.Hom.left (t x))))
    rw [Set.range_comp]
    exact hopenb _ (hop x).base_open.isOpen_range
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x => Set.range (SB.Hom.left (t x ≫ bs))) hopen (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨ULift.{u + 1} F, inferInstance, fun i => Ai i.down, fun i => t i.down ≫ bs, fun i => hAi _,
    fun i => ?_, fun x => ?_, fun i => ⟨Wc i.down, ⟨wc i.down⟩⟩⟩
  · rw [SB.comp_left, hbl]
    haveI := hop i.down.1
    infer_instance
  · have := hF (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨⟨i, hi⟩⟩, h⟩

variable (𝓜)

/-- The additive presheaf of `famPMod`. -/
def Fab : (SB Bsp)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := AddCommGrpCat.of ((famPMod 𝓜).obj T)
  map f := AddCommGrpCat.ofHom ((famPMod 𝓜).map f)
  map_id T := by ext x; exact (famPMod 𝓜).map_id T x
  map_comp f g := by ext x; exact (famPMod 𝓜).map_comp f g x

instance (X : (SB Bsp)ᵒᵖ) : Module ((OB Bsp ⋙ forget₂ CommRingCat RingCat).obj X) ((Fab 𝓜).obj X) :=
  inferInstanceAs (Module ((OB Bsp).obj X) ((famPMod 𝓜).obj X))

/-- `famPMod` as a presheaf of modules. -/
def MF : PresheafOfModules.{u} (OB Bsp ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.ofPresheaf (Fab 𝓜) (fun {X Y} f r z => (famPMod 𝓜).map_smul f r z)

lemma MF_cart (h𝓜 : 𝓜.IsQuasicoherentOnSite) {X Y : SB Bsp} (hX : IsAffine X.left)
    (hY : IsAffine Y.left) (a : Y ⟶ X) {V₀ : AffineEtale Bs S hS Bsp} (τ : X ⟶ cB V₀) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange (R := OB Bsp) (MF 𝓜) a.op) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (AlgMag.B2.cart_of_isBC (R := OB Bsp) (MF 𝓜) a.op
    (fam_cart_chart 𝓜 h𝓜 hX hY a τ))

lemma MF_sheaf {T : SB Bsp} (hT : IsAffine T.left) {I : Type (u + 1)} [Finite I] (W : I → SB Bsp)
    (g : ∀ i, W i ⟶ T) (hW : ∀ i, IsAffine (W i).left) (hfl : ∀ i, Flat (SB.Hom.left (g i)))
    (hsu : ∀ x : T.left, ∃ i, x ∈ Set.range (SB.Hom.left (g i))) :
    Presieve.IsSheafFor ((MF 𝓜).presheaf ⋙ forget AddCommGrpCat) (Presieve.ofArrows W g) :=
  (Presieve.isSheafFor_iff_generate _).mpr (fam_isSheafFor 𝓜 (cov_of_family hT W g hW hfl hsu))

/-- **Base change along a flat morphism of affines.** -/
theorem fam_cart_flat (h𝓜 : 𝓜.IsQuasicoherentOnSite) {U V : SB Bsp} (hU : IsAffine U.left)
    (hV : IsAffine V.left) (f : U ⟶ V) (hf : Flat (SB.Hom.left f)) :
    IsBC ((OB Bsp).map f.op).hom ((famPMod 𝓜).map f.op) ((famPMod 𝓜).map_smul f.op) := by
  classical
  obtain ⟨I, hI, W, g, hW, hfl, hsu, hch⟩ := exists_chart_family hB hV
  choose Vc hτ using hch
  let τ := fun i => (hτ i).some
  have hflat' : ((OB Bsp).map f.op).hom.Flat := HasRingHomProperty.appTop (P := @Flat) _ hf
  have hP := fun i => IsPullback.of_hasPullback f (g i)
  have hsuU : ∀ x : U.left, ∃ i, x ∈ Set.range (SB.Hom.left (pullback.fst f (g i))) := fun x => by
    obtain ⟨i, y, hy⟩ := hsu (SB.Hom.left f x)
    obtain ⟨z, h1, -⟩ := exists_pt_of_isPullback (hP i) x y hy.symm
    exact ⟨i, z, h1⟩
  have hPa := fun i => isAffine_of_isPullback (hP i) hU (hW i) hV
  have hQ := fun c : I × I => IsPullback.of_hasPullback (g c.1) (g c.2)
  have hQa := fun c => isAffine_of_isPullback (hQ c) (hW c.1) (hW c.2) hV
  have hR := fun c : I × I => IsPullback.of_hasPullback f (pullback.fst (g c.1) (g c.2) ≫ g c.1)
  have hRa := fun c => isAffine_of_isPullback (hR c) hU (hQa c) hV
  have hiso := Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover (R := OB Bsp) (MF 𝓜) f W g
    hflat' (MF_sheaf 𝓜 hV W g hW hfl hsu)
    (MF_sheaf 𝓜 hU _ _ hPa (fun i => flat_of_isPullback (hP i) (hfl i)) hsuU)
    (fun i => isPushout_OB (hP i) hU (hW i) hV)
    (fun c => isPushout_OB (hR c) hU (hQa c) hV)
    (fun i => MF_cart 𝓜 h𝓜 (hW i) (hPa i) _ (τ i))
    (fun c => MF_cart 𝓜 h𝓜 (hQa c) (hRa c) _ (pullback.fst (g c.1) (g c.2) ≫ τ c.1))
  exact AlgMag.B2.isBC_of_cart (R := OB Bsp) (MF 𝓜) f.op ((ConcreteCategory.isIso_iff_bijective _).1 hiso)

/-- **Base change between affines.** -/
theorem fam_cart (h𝓜 : 𝓜.IsQuasicoherentOnSite) {T T' : SB Bsp} (hT : IsAffine T.left)
    (hT' : IsAffine T'.left) (s : T' ⟶ T) :
    IsBC ((OB Bsp).map s.op).hom ((famPMod 𝓜).map s.op) ((famPMod 𝓜).map_smul s.op) := by
  classical
  obtain ⟨I, hI, W, g, hW, hfl, hsu, hch⟩ := exists_chart_family hB hT
  choose Vc hτ using hch
  let τ := fun i => (hτ i).some
  have hP := fun i => sb_isPullback s (g i)
  have hPa := fun i => isAffine_of_isPullback (hP i) hT' (hW i) hT
  have hflU := fun i => flat_of_isPullback (hP i) (hfl i)
  refine isBC_of_cover (fun i => (OB Bsp).obj (op (sbPb s (g i))))
    (fun i => (famPMod 𝓜).obj (op (sbPb s (g i)))) ((OB Bsp).map s.op).hom ((famPMod 𝓜).map s.op)
    ((famPMod 𝓜).map_smul s.op) (fun i => ((OB Bsp).map (sbFst s (g i)).op).hom)
    (fun i => (famPMod 𝓜).map (sbFst s (g i)).op) (fun i => (famPMod 𝓜).map_smul _)
    (fun i => fam_cart_flat 𝓜 h𝓜 (hPa i) hT' _ (hflU i)) (fun i => ?_) ?_
  · have h1 := fam_cart_flat 𝓜 h𝓜 (hW i) hT (g i) (hfl i)
    have h2 := fam_cart_chart 𝓜 h𝓜 (hW i) (hPa i) (sbSnd s (g i)) (τ i)
    have h3 := isBC_comp _ _ _ _ _ _ h1 h2
    refine isBC_congr _ ?_ ?_ h3
    · have e := (hP i).w
      have : (OB Bsp).map (g i).op ≫ (OB Bsp).map (sbSnd s (g i)).op =
          (OB Bsp).map s.op ≫ (OB Bsp).map (sbFst s (g i)).op := by
        rw [← (OB Bsp).map_comp, ← (OB Bsp).map_comp, ← op_comp, ← op_comp, e]
      exact congrArg CommRingCat.Hom.hom this
    · ext x
      change (famPMod 𝓜).map (sbSnd s (g i)).op ((famPMod 𝓜).map (g i).op x) =
        (famPMod 𝓜).map (sbFst s (g i)).op ((famPMod 𝓜).map s.op x)
      rw [← (famPMod 𝓜).map_comp, ← (famPMod 𝓜).map_comp, ← op_comp, ← op_comp, (hP i).w]
  · haveI := hT'
    haveI := hPa
    haveI := hflU
    exact Scheme.faithfullyFlat_pi_appTop (fun i => (sbPb s (g i)).left)
      (fun i => SB.Hom.left (sbFst s (g i))) (fun x => by
        obtain ⟨i, y, hy⟩ := hsu (SB.Hom.left s x)
        obtain ⟨z, h1, -⟩ := exists_pt_of_isPullback (hP i) x y hy.symm
        exact ⟨i, z, h1⟩)

/-- **`famPMod 𝓜` is quasi-coherent.** -/
theorem fam_isQCoh (h𝓜 : 𝓜.IsQuasicoherentOnSite) : IsQCoh (famPMod 𝓜) where
  sheaf T 𝒰 R hR := fam_isSheafFor 𝓜 (cov_open T 𝒰 R hR)
  base_change {T T'} s hT hT' := fam_cart 𝓜 h𝓜 hT hT' s

/-- **The bridge.** A quasi-coherent module `𝓜` of `Space.Modules` on the algebraic space `B` gives a
quasi-coherent `𝒪_B`-module, in the printed sense. -/
theorem fam_printed (h𝓜 : 𝓜.IsQuasicoherentOnSite) : AlgMag.B2.PrintedQCoh (famPMod 𝓜) :=
  (AlgMag.B2.isQCoh_iff_printed _).1 (fam_isQCoh 𝓜 h𝓜)

open AlgMag.S9BF AlgMag.S9BS AlgMag.S9BR AlgMag.S9BP AlgMag.B2
open AlgMag.S9 (PMod HModule)

variable {F : PMod (OB Bsp)}
variable {Y : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

/-- **Proposition 9.9** for `𝓜`, `F` an `𝒪_B`-module, `p` an affine morphism of algebraic spaces. -/
def prop99_modules (h𝓜 : 𝓜.IsQuasicoherentOnSite) (p : Y ⟶ Bsp) (hp : Space.IsAffineHom Bs S hS p) :
    HomAt F (famPMod 𝓜) (Vp p) ≃ HomPush F (famPMod 𝓜) (affOverOfIsAffineHom p hp) :=
  prop99_space p hp (fam_isQCoh 𝓜 h𝓜)

/-- **Proposition 9.10** for `𝓜`. -/
def prop910_modules (h𝓜 : 𝓜.IsQuasicoherentOnSite) (p : Y ⟶ Bsp) (hp : Space.IsAffineHom Bs S hS p) {H : (SB Bsp)ᵒᵖ ⥤ MonCat.{u}}
    (e : Vp p ≅ H ⋙ forget MonCat) :
    HModule H (famPMod 𝓜) ≃ CoactionAff (famPMod 𝓜) (affOverOfIso (affOverOfIsAffineHom p hp) e) :=
  prop910_space p hp e (fam_isQCoh 𝓜 h𝓜)

variable {M : Type u} [AddCommMonoid M] [Countable M]

/-- **Propositions 9.10 and 9.11** for `𝓜`, for `𝔸(M)_B`. -/
def prop911_modules (h𝓜 : 𝓜.IsQuasicoherentOnSite) :
    CoactionAff (famPMod 𝓜) (affOverHm (M := M) (Bsp := Bsp)) ≃ Decomp (famPMod 𝓜) M :=
  coactionEquivDecomp (fam_isQCoh 𝓜 h𝓜)

/-- **Proposition 9.12** for `𝓜`, over a quasi-compact algebraic space. -/
theorem prop912_modules (h𝓜 : 𝓜.IsQuasicoherentOnSite) {n : ℕ} (p : Y ⟶ Bsp) (hY : IsAlgebraicSpace Bs S hS Y)
    (hq : Space.IsQuasiCompactSpace Bs S hS Y) :
    Nonempty (CochainV (famPMod 𝓜) M (Vp p) n ≃ ((Fin n → M) →₀ SecF (famPMod 𝓜) (Vp p))) :=
  prop912_space (fam_isQCoh 𝓜 h𝓜) p hY hq

/-- **Proposition 9.13 and Remark 9.14** for `𝓜`. -/
theorem prop913_modules (h𝓜 : 𝓜.IsQuasicoherentOnSite) {n : ℕ} (R : CoactionAff (famPMod 𝓜) (affOverHm (M := M) (Bsp := Bsp)))
    {V : (SB Bsp)ᵒᵖ ⥤ Type u} (c : CochainV (famPMod 𝓜) M V (n + 1))
    (hc : ∀ {T : SB Bsp} (t : V.obj (op T)) g,
      (deltaV ((hModuleEquivCoaction _ (fam_isQCoh 𝓜 h𝓜)).symm R) c).app t g = 0) :
    ∃ e : CochainV (famPMod 𝓜) M V n,
      deltaV ((hModuleEquivCoaction _ (fam_isQCoh 𝓜 h𝓜)).symm R) e = c :=
  prop913_of_coaction (fam_isQCoh 𝓜 h𝓜) R c hc

end AlgMag.B3

#print axioms AlgMag.B3.fam_isQCoh
#print axioms AlgMag.B3.fam_printed
#print axioms AlgMag.B3.prop99_modules
#print axioms AlgMag.B3.prop910_modules
#print axioms AlgMag.B3.prop911_modules
#print axioms AlgMag.B3.prop912_modules
#print axioms AlgMag.B3.prop913_modules
