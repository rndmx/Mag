/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge2Printed
import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# From a quasi-coherent module on the small étale site of `B` to the big site: compatible families

`𝓜` a module of `Space.Modules` on the algebraic space `B`. `Fam 𝓜 T`, for `T` over `B`: the families
of values in `Γ(A) ⊗_{Γ(V)} 𝓜(V)`, over the affine `A ⟶ T` with a chart `A ⟶ V`, compatible with
morphisms of such data. Functoriality in `T` is reindexing, so `map_comp` is automatic.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace AlgMag.B3

/-! ### Base change along ring maps given as data -/

section BC

variable {R S R' S' R'' S'' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [CommRing R''] [CommRing S'']

/-- `S ⊗_R M`, with `S` an `R`-algebra through `f`. -/
def BCv (f : R →+* S) (M : Type u) [AddCommGroup M] [Module R M] : Type u :=
  letI := f.toAlgebra
  S ⊗[R] M

variable (f : R →+* S) (f' : R' →+* S') (f'' : R'' →+* S'')
  (M M' M'' : Type u) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']
  [AddCommGroup M''] [Module R'' M'']

instance : AddCommGroup (BCv f M) :=
  (fun (_ : Algebra R S) => (inferInstance : AddCommGroup (S ⊗[R] M))) f.toAlgebra

instance : Module S (BCv f M) :=
  (fun (_ : Algebra R S) => (inferInstance : Module S (S ⊗[R] M))) f.toAlgebra

variable {M M' M''}

/-- `s ⊗ m`. -/
def BCv.tm (s : S) (m : M) : BCv f M :=
  letI := f.toAlgebra
  (s ⊗ₜ[R] m : S ⊗[R] M)

variable {f f' f''}

/-- The map `s ⊗ m ↦ g s ⊗ φ m` of a morphism of the data. -/
def bcMap (h : R →+* R') (g : S →+* S') (c : g.comp f = f'.comp h) (φ : M →+ M')
    (hφ : ∀ r m, φ (r • m) = h r • φ m) : BCv f M →+ BCv f' M' :=
  letI := f.toAlgebra
  letI := f'.toAlgebra
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun m => (g s ⊗ₜ[R'] φ m : S' ⊗[R'] M'))
        (fun a b => by rw [map_add, TensorProduct.tmul_add]; rfl))
      (fun a b => by ext m; simp only [map_add, TensorProduct.add_tmul]; rfl))
    (fun r s m => by
      have e : g (r • s) = (h r) • g s := by
        have := congrArg (fun k => k r) c
        simp only [RingHom.comp_apply] at this
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        change g (f r) * g s = f' (h r) * g s
        rw [this]
      change g (r • s) ⊗ₜ[R'] φ m = g s ⊗ₜ[R'] φ (r • m)
      rw [e, hφ, TensorProduct.smul_tmul])

@[simp] lemma bcMap_tm (h : R →+* R') (g : S →+* S') (c : g.comp f = f'.comp h) (φ : M →+ M')
    (hφ : ∀ r m, φ (r • m) = h r • φ m) (s : S) (m : M) :
    bcMap h g c φ hφ (BCv.tm f s m) = BCv.tm f' (g s) (φ m) := by
  letI := f.toAlgebra
  letI := f'.toAlgebra
  exact TensorProduct.liftAddHom_tmul _ _ _ _

variable (f) in
/-- Additive maps out of `BCv` are determined on pure tensors. -/
theorem BCv.induction {P : BCv f M → Prop} (h0 : P 0) (ht : ∀ s m, P (BCv.tm f s m))
    (ha : ∀ x y, P x → P y → P (x + y)) (z : BCv f M) : P z := by
  letI := f.toAlgebra
  exact TensorProduct.induction_on (motive := P) z h0 ht ha

lemma bcMap_smul (h : R →+* R') (g : S →+* S') (c : g.comp f = f'.comp h) (φ : M →+ M')
    (hφ : ∀ r m, φ (r • m) = h r • φ m) (a : S) (z : BCv f M) :
    bcMap h g c φ hφ (a • z) = g a • bcMap h g c φ hφ z := by
  letI := f.toAlgebra
  letI := f'.toAlgebra
  refine BCv.induction f (P := fun z => bcMap h g c φ hφ (a • z) = g a • bcMap h g c φ hφ z) ?_ (fun s m => ?_) (fun x y hx hy => ?_) z
  · simp
  · have e : ∀ {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
        (f : R →+* S) (a s : S) (m : M), a • BCv.tm f s m = BCv.tm f (a * s) m := by
      intro R S M _ _ _ _ f a s m
      letI := f.toAlgebra
      exact TensorProduct.smul_tmul' a s m
    rw [e, bcMap_tm, bcMap_tm, map_mul, e]
  · rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The comparison is bijective when `S' = S` and `M'` is the base change of `M`. -/
theorem bcMap_bijective (h : R →+* R') (f' : R' →+* S) (c : (RingHom.id S).comp f = f'.comp h)
    (φ : M →+ M') (hφ : ∀ r m, φ (r • m) = h r • φ m)
    (hBC : AlgMag.S9.IsBC h φ hφ) :
    Function.Bijective (bcMap h (RingHom.id S) c φ hφ) := by
  letI := h.toAlgebra
  letI := f.toAlgebra
  letI := f'.toAlgebra
  letI : Module R M' := Module.compHom M' h
  haveI : IsScalarTower R R' M' := ⟨fun r s x => by
    change (h r * s) • x = h r • s • x
    rw [mul_smul]⟩
  have hfe : ∀ r, f r = f' (h r) := fun r => congrArg (fun k => k r) c
  haveI : IsScalarTower R R' S := IsScalarTower.of_algebraMap_eq hfe
  have h1 : IsBaseChange R' ({ toFun := φ, map_add' := φ.map_add, map_smul' := hφ } : M →ₗ[R] M') :=
    hBC
  have h2 := h1.comp (TensorProduct.isBaseChange R' M' S)
  have key : ∀ z : S ⊗[R] M, bcMap h (RingHom.id S) c φ hφ z = h2.equiv z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add a b ha hb => exact (map_add _ a b).trans ((congrArg₂ _ ha hb).trans (map_add _ a b).symm)
    | tmul s m =>
      refine (bcMap_tm h (RingHom.id S) c φ hφ s m).trans ?_
      refine Eq.trans ?_ (IsBaseChange.equiv_tmul h2 s m).symm
      change s ⊗ₜ[R'] φ m = s • ((1 : S) ⊗ₜ[R'] φ m)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have e : (fun z => bcMap h (RingHom.id S) c φ hφ z) = h2.equiv := funext key
  exact (e ▸ h2.equiv.bijective :)

end BC

/-! ### Charts as objects over `B` -/

open AlgMag.S9B AlgMag.S9
open AlgebraicGeometry.Space

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

/-- An affine étale chart of `B`, as an object over `B`. -/
def cB (V : AffineEtale Bs S hS Bsp) : SB Bsp :=
  ⟨(AffineEtale.toOver Bs S hS Bsp).obj V, yonedaEquiv V.obj.obj.hom⟩

/-- A morphism of charts, as a morphism over `B`. -/
def cBm {V' V : AffineEtale Bs S hS Bsp} (φ : V' ⟶ V) : cB V' ⟶ cB V :=
  ⟨(AffineEtale.toOver Bs S hS Bsp).map φ, by
    have := CostructuredArrow.w ((AffineEtale.inclusion Bs S hS Bsp).map φ).hom
    exact (yonedaEquiv_naturality _ _).trans (congrArg yonedaEquiv this)⟩

lemma cBm_comp {V'' V' V : AffineEtale Bs S hS Bsp} (φ : V'' ⟶ V') (ψ : V' ⟶ V) :
    cBm (φ ≫ ψ) = cBm φ ≫ cBm ψ :=
  SB.Hom.ext ((AffineEtale.toOver Bs S hS Bsp).map_comp _ _)

variable {hB : IsAlgebraicSpace Bs S hS Bsp}

/-- The presheaf of modules underlying `𝓜`. -/
abbrev Pm (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB) :
    PresheafOfModules.{u} (structurePresheaf Bs S hS Bsp ⋙ forget₂ CommRingCat RingCat) :=
  𝓜.val

/-- The ring of a chart. -/
abbrev rc (V : AffineEtale Bs S hS Bsp) : CommRingCat.{u} := (OB Bsp).obj (op (cB V))

/-- The sections of `𝓜` over a chart. -/
abbrev Mv (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB) (V : AffineEtale Bs S hS Bsp) : Type u :=
  (Pm 𝓜).obj (op V.obj)

instance (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB) (V : AffineEtale Bs S hS Bsp) :
    Module (rc V) (Mv 𝓜 V) :=
  inferInstanceAs (Module ((structurePresheaf Bs S hS Bsp).obj (op V.obj)) ((Pm 𝓜).obj (op V.obj)))

/-- Restriction of `𝓜` along a morphism of charts. -/
def Mres (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB) {V' V : AffineEtale Bs S hS Bsp} (φ : V' ⟶ V) :
    Mv 𝓜 V →+ Mv 𝓜 V' :=
  AddMonoidHom.mk' (fun x => (Pm 𝓜).map ((AffineEtale.inclusion Bs S hS Bsp).map φ).op x)
    (fun a b => map_add ((Pm 𝓜).map ((AffineEtale.inclusion Bs S hS Bsp).map φ).op).hom a b)

lemma Mres_smul (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB) {V' V : AffineEtale Bs S hS Bsp}
    (φ : V' ⟶ V) (r : rc V) (x : Mv 𝓜 V) :
    Mres 𝓜 φ (r • x) = ((OB Bsp).map (cBm φ).op).hom r • Mres 𝓜 φ x :=
  ((Pm 𝓜).map ((AffineEtale.inclusion Bs S hS Bsp).map φ).op).hom.map_smul r x

end AlgMag.B3
