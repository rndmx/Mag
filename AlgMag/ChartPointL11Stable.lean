/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointL11Image

/-!
# The image of the orbit is stable (Lemma 1.1 of the chart-lemma proof, step A)
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

lemma hom_nat {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : BigFppfOver B S hS}
    (f : yoneda.obj A ⟶ F) {V V' : BigFppfOver B S hS} (r : V' ⟶ V) (v : V ⟶ A) :
    f.app (op V') (r ≫ v) = F.map r.op (f.app (op V) v) :=
  hom_naturality_apply f r.op v

variable [IsAffine S] {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]
  {o : yoneda.obj (Ob P N) ⟶ X}

/-- **Lemma 1.1, step A, on charts.** `g₁, g₂` étale charts, `V → T₁, V → T₂` with
`g₂ v₂ = h · g₁ v₁` and `g₁ v₁` in the image. Then `g₂ v₂` is in the image: `T₁[M] ×_X T₂` is flat
over `T₁`, so the kernel of `Γ(T₁) → Γ(O_{T₁})` generates the kernel of the base change, in which
functions coming from the kernel for `T₂` die by equivariance. -/
theorem image_stable_chart (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o)
    {T₁ T₂ W₁ W₂ : BigFppfOver B S hS} [IsAffine ((SCH).obj T₁)] [IsAffine ((SCH).obj T₂)]
    [IsAffine ((SCH).obj W₁)]
    {g₁ : yoneda.obj T₁ ⟶ X} {g₂ : yoneda.obj T₂ ⟶ X}
    (hg₁ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g₁)
    (hg₂ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g₂)
    {p₁ : W₁ ⟶ Ob P N} {w₁ : W₁ ⟶ T₁} (sq₁ : IsPullback (yoneda.map p₁) (yoneda.map w₁) o g₁)
    {p₂ : W₂ ⟶ Ob P N} {w₂ : W₂ ⟶ T₂} (sq₂ : IsPullback (yoneda.map p₂) (yoneda.map w₂) o g₂)
    {V : BigFppfOver B S hS} (v₁ : V ⟶ T₁) (v₂ : V ⟶ T₂)
    (h : Multiplicative M →* Γ((SCH).obj V, ⊤))
    (hv : g₂.app (op V) v₂ = actX.smul (U := op V) h (g₁.app (op V) v₁))
    (hm : g₁.app (op V) v₁ ∈ (imS o).obj (op V)) :
    g₂.app (op V) v₂ ∈ (imS o).obj (op V) := by
  classical
  refine chart_mem hX hsep hg₂ sq₂ v₂ fun a₂ ha₂ => ?_
  -- `E = T₁[M] ×_X T₂`
  let μ := orbMap actX g₁
  obtain ⟨E, e₂, e₁, he₁, sqE⟩ := exists_pull hsep g₂ μ
  haveI hEa : IsAffine ((SCH).obj E) := isAffine_of_isAffineHom ((SCH).map e₁)
  have hEet : Etale ((SCH).map e₁) := hg₂.property _ _ _ sqE
  -- the point `V → T₁[M]`
  have hψ : (evalAt ((SCH).map v₁).appTop.hom h).comp (ι1 T₁ (M := M)) =
      ((SCH).map v₁).appTop.hom := RingHom.ext fun b => evalAt_ι _ _ b
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_spLift (R' := R1 T₁ M) (ι1 T₁) contains1 v₁ _ hψ
  have hres : secPt ((SCH).map τ).appTop.hom (univPt1 (U := T₁)) = h := MonoidHom.ext fun m => by
    refine (hτ₂ _).trans ?_
    refine (evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
    rw [map_one, one_mul]
    rfl
  have hμτ : μ.app (op V) τ = g₂.app (op V) v₂ := by
    have := orbMap_app actX g₁ τ
    rw [hres, hτ₁] at this
    exact this.trans hv.symm
  obtain ⟨l, hl₂, hl₁⟩ := pb_lift sqE v₂ τ hμτ.symm
  -- the algebra structures
  let e0 : E ⟶ T₁ := e₁ ≫ Gπ M T₁
  let α : RT T₁ →+* RT E := ((SCH).map e0).appTop.hom
  let β : RT T₁ →+* RT W₁ := ((SCH).map w₁).appTop.hom
  letI : Algebra (RT T₁) (RT E) := α.toAlgebra
  letI : Algebra (RT T₁) (RT W₁) := β.toAlgebra
  have hβft : β.FiniteType := by
    have : LocallyOfFinitePresentation ((SCH).map w₁) := hlfp.property _ _ _ sq₁
    have h2 : LocallyOfFiniteType ((SCH).map w₁) := inferInstance
    exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 h2
  haveI : Algebra.FiniteType (RT T₁) (RT W₁) := (RingHom.finiteType_algebraMap).1 hβft
  have hαfl : Module.Flat (RT T₁) (RT E) := by
    have f1 : (ι1 T₁ (M := M)).Flat :=
      (RingHom.flat_algebraMap_iff (R := RT T₁) (S := AddMonoidAlgebra (RT T₁) M)).2 inferInstance
    have f2 := RingHom.Flat.of_bijective (spSec_bijective T₁ (ι1 T₁ (M := M)) contains1)
    have f3 : ((SCH).map e₁).appTop.hom.Flat := Scheme.Hom.flat_appTop _
    have e : α = ((SCH).map e₁).appTop.hom.comp ((spSec T₁ (ι1 T₁ (M := M)) contains1).comp
        (ι1 T₁ (M := M))) := by
      refine RingHom.ext fun b => ?_
      change ((SCH).map (e₁ ≫ Gπ M T₁)).appTop.hom b = ((SCH).map e₁).appTop.hom _
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]
      change ((SCH).map e₁).appTop.hom (((SCH).map (Gπ M T₁)).appTop.hom b) = _
      rw [spToT_appTop]
      rfl
    change α.Flat
    rw [e]
    exact RingHom.Flat.comp (RingHom.Flat.comp f1 f2) f3
  -- the key: `a₂` restricted to `E` lies in `ker β · Γ(E)`
  have hkey : ((SCH).map e₂).appTop.hom a₂ ∈
      (RingHom.ker (algebraMap (RT T₁) (RT W₁))).map (algebraMap (RT T₁) (RT E)) := by
    refine mem_map_ker_of_tmul_eq_zero (B₀ := RT W₁) _ ?_
    let Ra := RT E ⊗[RT T₁] RT W₁
    haveI : Algebra.FiniteType (RT E) Ra := inferInstance
    have hC : B.Contains (Spec (.of Ra)) := contains_ft (RT E) Ra (contains_RT E)
    let Ef : BigFppfOver B S hS := spObj E (algebraMap (RT E) Ra) hC
    let s : Ef ⟶ E := spToT E _ hC
    let inr : RT W₁ →+* Ra := (Algebra.TensorProduct.includeRight : RT W₁ →ₐ[RT T₁] Ra).toRingHom
    let j : RT W₁ →+* Γ((SCH).obj Ef, ⊤) := (spSec E (algebraMap (RT E) Ra) hC).comp inr
    have hjc : j.comp β = ((SCH).map (s ≫ e0)).appTop.hom := by
      refine RingHom.ext fun x => ?_
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]
      change spSec E (algebraMap (RT E) Ra) hC (inr (β x)) =
        ((SCH).map s).appTop.hom (α x)
      rw [spToT_appTop]
      congr 1
      change (1 : RT E) ⊗ₜ[RT T₁] (β x) = (α x) ⊗ₜ[RT T₁] (1 : RT W₁)
      have e1 : β x = x • (1 : RT W₁) := by rw [Algebra.smul_def, mul_one]; rfl
      have e2 : α x = x • (1 : RT E) := by rw [Algebra.smul_def, mul_one]; rfl
      rw [e1, e2, TensorProduct.smul_tmul]
    let tw : (SCH).obj Ef ⟶ (SCH).obj W₁ := toAffine (T := (SCH).obj Ef) (U := (SCH).obj W₁) j
    have htw : tw ≫ (SCH).map w₁ = (SCH).map (s ≫ e0) := by
      haveI : IsAffine ((SCH).obj Ef) := inferInstance
      refine toAffine_ext ?_
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, toAffine_appTop]
      exact hjc
    let toW : Ef ⟶ W₁ := siteHom tw (by
      rw [← site_w w₁, ← Category.assoc, htw, site_w])
    have h2 : toW ≫ w₁ = s ≫ e0 := site_hom_ext (by rw [Functor.map_comp]; exact htw)
    let ζ : Ef ⟶ Gk M T₁ := s ≫ e₁
    let hE : Multiplicative M →* Γ((SCH).obj Ef, ⊤) :=
      secPt ((SCH).map ζ).appTop.hom (univPt1 (U := T₁))
    let x : Ef ⟶ Ob P N := oSmul N hE (toW ≫ p₁)
    have hx : o.app (op Ef) x = g₂.app (op Ef) (s ≫ e₂) := by
      have a1 : o.app (op Ef) x = actX.smul (U := op Ef) hE (o.app (op Ef) (toW ≫ p₁)) :=
        hoe (T := op Ef) hE (toW ≫ p₁)
      have a2 : o.app (op Ef) (toW ≫ p₁) = g₁.app (op Ef) (toW ≫ w₁) := by
        rw [hom_nat, hom_nat, pb_comm sq₁]
      have a3 : μ.app (op Ef) ζ = actX.smul (U := op Ef) hE (g₁.app (op Ef) (ζ ≫ Gπ M T₁)) :=
        orbMap_app actX g₁ ζ
      have a4 : g₂.app (op Ef) (s ≫ e₂) = μ.app (op Ef) ζ := by
        rw [hom_nat, hom_nat, pb_comm sqE]
      have a5 : toW ≫ w₁ = ζ ≫ Gπ M T₁ := by
        rw [h2]; simp [ζ, e0]
      rw [a1, a2, a4, a3, a5]
    obtain ⟨l2, -, hl2⟩ := pb_lift sq₂ x (s ≫ e₂) hx
    have hz : ((SCH).map (s ≫ e₂)).appTop.hom a₂ = 0 := by
      rw [← hl2, Functor.map_comp, Scheme.Hom.comp_appTop]
      change ((SCH).map l2).appTop.hom (((SCH).map w₂).appTop.hom a₂) = 0
      rw [ha₂, map_zero]
    rw [Functor.map_comp, Scheme.Hom.comp_appTop] at hz
    change ((SCH).map s).appTop.hom (((SCH).map e₂).appTop.hom a₂) = 0 at hz
    rw [spToT_appTop] at hz
    exact (spSec_bijective E _ hC).1 (hz.trans (map_zero _).symm)
  -- conclusion
  have hl0 : l ≫ e0 = v₁ := by
    change l ≫ e₁ ≫ Gπ M T₁ = v₁
    rw [← Category.assoc, hl₁, hτ₁]
  have hfin : ((SCH).map l).appTop.hom.comp (algebraMap (RT T₁) (RT E)) =
      ((SCH).map v₁).appTop.hom := by
    rw [← hl0, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  have hker : (RingHom.ker (algebraMap (RT T₁) (RT W₁))).map (algebraMap (RT T₁) (RT E)) ≤
      RingHom.ker ((SCH).map l).appTop.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hfin]
    exact chart_kills hX hsep hg₁ sq₁ v₁ hm x hx
  have := hker hkey
  rw [RingHom.mem_ker] at this
  rw [← hl₂, Functor.map_comp, Scheme.Hom.comp_appTop]
  exact this

end AlgMag.ChartPoint
