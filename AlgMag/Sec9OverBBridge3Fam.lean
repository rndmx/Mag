/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge3Core

/-!
# The compatible families `Fam 𝓜 T`
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace AlgMag.B3

open AlgMag.S9B AlgMag.S9 AlgebraicGeometry.Space

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace Bs S hS Bsp}
  (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB)

/-- The value `Γ(A) ⊗_{Γ(V)} 𝓜(V)` at a chart `v : A ⟶ V`. -/
abbrev Dv {A : SB Bsp} {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) : Type u :=
  BCv ((OB Bsp).map v.op).hom (Mv 𝓜 V)

lemma square_ring {A' A : SB Bsp} {V' V : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v' : A' ⟶ cB V'}
    (s : A' ⟶ A) (φ : V' ⟶ V) (hc : v' ≫ cBm φ = s ≫ v) :
    ((OB Bsp).map s.op).hom.comp ((OB Bsp).map v.op).hom =
      ((OB Bsp).map v'.op).hom.comp ((OB Bsp).map (cBm φ).op).hom := by
  have : (OB Bsp).map v.op ≫ (OB Bsp).map s.op = (OB Bsp).map (cBm φ).op ≫ (OB Bsp).map v'.op := by
    rw [← (OB Bsp).map_comp, ← (OB Bsp).map_comp, ← op_comp, ← op_comp, hc]
  exact congrArg CommRingCat.Hom.hom this

/-- Restriction of values along a morphism of the data. -/
def ρ {A' A : SB Bsp} {V' V : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v' : A' ⟶ cB V'}
    (s : A' ⟶ A) (φ : V' ⟶ V) (hc : v' ≫ cBm φ = s ≫ v) : Dv 𝓜 v →+ Dv 𝓜 v' :=
  bcMap ((OB Bsp).map (cBm φ).op).hom ((OB Bsp).map s.op).hom (square_ring s φ hc) (Mres 𝓜 φ)
    (Mres_smul 𝓜 φ)

/-- A compatible family over `T`. -/
structure Fam (T : SB Bsp) where
  /-- the values -/
  val : ∀ {A : SB Bsp} (_ : IsAffine A.left) (_ : A ⟶ T) {V : AffineEtale Bs S hS Bsp}
    (v : A ⟶ cB V), Dv 𝓜 v
  compat : ∀ {A' A : SB Bsp} (hA' : IsAffine A'.left) (hA : IsAffine A.left) (a : A ⟶ T)
    {V' V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) (v' : A' ⟶ cB V') (s : A' ⟶ A) (φ : V' ⟶ V)
    (hc : v' ≫ cBm φ = s ≫ v), ρ 𝓜 s φ hc (val hA a v) = val hA' (s ≫ a) v'

variable {𝓜}

@[ext] lemma Fam.ext {T : SB Bsp} {x y : Fam 𝓜 T}
    (h : ∀ {A : SB Bsp} (hA : IsAffine A.left) (a : A ⟶ T) {V : AffineEtale Bs S hS Bsp}
      (v : A ⟶ cB V), x.val hA a v = y.val hA a v) : x = y := by
  cases x; cases y; congr; funext A hA a V v; exact h hA a v

instance (T : SB Bsp) : Add (Fam 𝓜 T) where
  add x y := ⟨fun hA a _ v => x.val hA a v + y.val hA a v, fun hA' hA a _ _ v v' s φ hc => by
    rw [map_add, x.compat, y.compat]⟩

instance (T : SB Bsp) : Zero (Fam 𝓜 T) where
  zero := ⟨fun _ _ _ _ => 0, fun _ _ _ _ _ _ _ s φ hc => map_zero _⟩

instance (T : SB Bsp) : Neg (Fam 𝓜 T) where
  neg x := ⟨fun hA a _ v => - x.val hA a v, fun hA' hA a _ _ v v' s φ hc => by
    rw [map_neg, x.compat]⟩

instance (T : SB Bsp) : AddCommGroup (Fam 𝓜 T) where
  add_assoc x y z := Fam.ext fun _ _ _ _ => add_assoc _ _ _
  zero_add x := Fam.ext fun _ _ _ _ => zero_add _
  add_zero x := Fam.ext fun _ _ _ _ => add_zero _
  add_comm x y := Fam.ext fun _ _ _ _ => add_comm _ _
  neg_add_cancel x := Fam.ext fun _ _ _ _ => neg_add_cancel _
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] lemma Fam.add_val {T : SB Bsp} (x y : Fam 𝓜 T) {A : SB Bsp} (hA : IsAffine A.left) (a : A ⟶ T)
    {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) :
    (x + y).val hA a v = x.val hA a v + y.val hA a v := rfl

@[simp] lemma Fam.zero_val {T : SB Bsp} {A : SB Bsp} (hA : IsAffine A.left) (a : A ⟶ T)
    {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) : (0 : Fam 𝓜 T).val hA a v = 0 := rfl

/-- Reindexing along `t : T' ⟶ T`. -/
def Fam.res {T' T : SB Bsp} (t : T' ⟶ T) (x : Fam 𝓜 T) : Fam 𝓜 T' where
  val hA a _ v := x.val hA (a ≫ t) v
  compat hA' hA a _ _ v v' s φ hc := by
    rw [x.compat hA' hA (a ≫ t) v v' s φ hc, Category.assoc]

instance (T : SB Bsp) : Module ((OB Bsp).obj (op T)) (Fam 𝓜 T) where
  smul r x := ⟨fun hA a _ v => ((OB Bsp).map a.op).hom r • x.val hA a v,
    fun hA' hA a _ _ v v' s φ hc => by
      refine (bcMap_smul _ _ _ _ _ _ _).trans ?_
      refine congrArg₂ (· • ·) ?_ (x.compat hA' hA a v v' s φ hc)
      rw [op_comp, (OB Bsp).map_comp]
      rfl⟩
  one_smul x := Fam.ext fun hA a _ v => by
    change ((OB Bsp).map a.op).hom 1 • _ = _
    rw [map_one, one_smul]
  mul_smul r r' x := Fam.ext fun hA a _ v => by
    change ((OB Bsp).map a.op).hom (r * r') • _ = _ • (_ • _)
    rw [map_mul, mul_smul]
  smul_zero r := Fam.ext fun _ _ _ _ => smul_zero _
  smul_add r x y := Fam.ext fun _ _ _ _ => smul_add _ _ _
  add_smul r r' x := Fam.ext fun hA a _ v => by
    change ((OB Bsp).map a.op).hom (r + r') • _ = _ + _
    rw [map_add, add_smul]
    rfl
  zero_smul x := Fam.ext fun hA a _ v => by
    change ((OB Bsp).map a.op).hom 0 • _ = _
    rw [map_zero, zero_smul]
    rfl

@[simp] lemma Fam.smul_val {T : SB Bsp} (r : (OB Bsp).obj (op T)) (x : Fam 𝓜 T) {A : SB Bsp}
    (hA : IsAffine A.left) (a : A ⟶ T) {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) :
    (r • x).val hA a v = ((OB Bsp).map a.op).hom r • x.val hA a v := rfl

/-- `Fam` is small: values over a small set of representatives determine a family. -/
instance small_fam (T : SB Bsp) : Small.{u} (Fam 𝓜 T) := by
  haveI : EssentiallySmall.{u} (BigFppfOver Bs S hS) :=
    inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 Bs.Schemes) (Bs.obj hS)))
  haveI : EssentiallySmall.{u} (AffineEtale Bs S hS Bsp) :=
    essentiallySmall_of_fully_faithful (AffineEtale.inclusion Bs S hS Bsp)
  let J₁ := SmallModel.{u} (BigFppfOver Bs S hS)
  let e₁ := equivSmallModel.{u} (BigFppfOver Bs S hS)
  let J₂ := SmallModel.{u} (AffineEtale Bs S hS Bsp)
  let e₂ := equivSmallModel.{u} (AffineEtale Bs S hS Bsp)
  -- the object of `SB` of a representative
  let rep : ∀ (j : J₁), Bsp.obj (op (e₁.inverse.obj j)) → SB Bsp := fun j p => ⟨e₁.inverse.obj j, p⟩
  let J := Σ (j : J₁) (p : Bsp.obj (op (e₁.inverse.obj j))) (_ : PLift (IsAffine (rep j p).left))
    (_ : rep j p ⟶ T) (k : J₂), (rep j p ⟶ cB (e₂.inverse.obj k))
  let Φ : Fam 𝓜 T → ∀ i : J, Dv 𝓜 i.2.2.2.2.2 := fun x i => x.val i.2.2.1.down i.2.2.2.1 i.2.2.2.2.2
  refine small_of_injective (f := Φ) fun x y hxy => Fam.ext fun {A} hA a {V} v => ?_
  -- an isomorphism from `A` to a representative
  let i₀ : A.obj ≅ e₁.inverse.obj (e₁.functor.obj A.obj) := e₁.unitIso.app A.obj
  let A₀ : SB Bsp := rep (e₁.functor.obj A.obj) (Bsp.map i₀.inv.op A.pt)
  let i : A ⟶ A₀ := ⟨i₀.hom, by
    change Bsp.map i₀.hom.op (Bsp.map i₀.inv.op A.pt) = A.pt
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, i₀.hom_inv_id, op_id, FunctorToTypes.map_id_apply]⟩
  let i' : A₀ ⟶ A := ⟨i₀.inv, rfl⟩
  have hii : i' ≫ i = 𝟙 _ := SB.Hom.ext i₀.inv_hom_id
  have hii' : i ≫ i' = 𝟙 _ := SB.Hom.ext i₀.hom_inv_id
  have hA₀ : IsAffine A₀.left := by
    haveI := hA
    have : IsIso (SB.Hom.left i') := ⟨SB.Hom.left i, by rw [← SB.comp_left, hii, SB.id_left],
      by rw [← SB.comp_left, hii', SB.id_left]⟩
    exact .of_isIso (SB.Hom.left i')
  let k₀ : V ≅ e₂.inverse.obj (e₂.functor.obj V) := e₂.unitIso.app V
  let v₀ : A₀ ⟶ cB (e₂.inverse.obj (e₂.functor.obj V)) := i' ≫ v ≫ cBm k₀.hom
  have hvv : v ≫ cBm k₀.hom ≫ cBm k₀.inv = v := by
    have hid : cBm (𝟙 V) = 𝟙 (cB V) := SB.Hom.ext (AffineEtale.toOver Bs S hS Bsp |>.map_id V)
    rw [← cBm_comp, k₀.hom_inv_id, hid, Category.comp_id]
  have hc : v ≫ cBm k₀.hom = i ≫ v₀ := by
    change _ = i ≫ i' ≫ v ≫ cBm k₀.hom
    rw [← Category.assoc i, hii', Category.id_comp]
  have hc' : v ≫ cBm (𝟙 V ≫ k₀.hom) = i ≫ v₀ := by rw [Category.id_comp]; exact hc
  have hx := x.compat hA hA₀ (i' ≫ a) v₀ v i k₀.hom hc
  have hy := y.compat hA hA₀ (i' ≫ a) v₀ v i k₀.hom hc
  have hval := congrFun hxy
    ⟨e₁.functor.obj A.obj, Bsp.map i₀.inv.op A.pt, ⟨hA₀⟩, i' ≫ a, e₂.functor.obj V, v₀⟩
  have ha : i ≫ i' ≫ a = a := by rw [← Category.assoc, hii', Category.id_comp]
  rw [ha] at hx hy
  rw [← hx, ← hy]
  exact congrArg _ hval

lemma Fam.res_add {T' T : SB Bsp} (t : T' ⟶ T) (x y : Fam 𝓜 T) :
    Fam.res t (x + y) = Fam.res t x + Fam.res t y := rfl

lemma Fam.res_smul {T' T : SB Bsp} (t : T' ⟶ T) (r : (OB Bsp).obj (op T)) (x : Fam 𝓜 T) :
    Fam.res t (r • x) = ((OB Bsp).map t.op).hom r • Fam.res t x :=
  Fam.ext fun hA a _ v => by
    change ((OB Bsp).map (a ≫ t).op).hom r • _ = ((OB Bsp).map a.op).hom _ • _
    rw [op_comp, (OB Bsp).map_comp]
    rfl

lemma Fam.res_id {T : SB Bsp} (x : Fam 𝓜 T) : Fam.res (𝟙 T) x = x :=
  Fam.ext fun hA a _ v => by
    change x.val hA (a ≫ 𝟙 T) v = _
    rw [Category.comp_id]

lemma Fam.res_comp {T'' T' T : SB Bsp} (t' : T'' ⟶ T') (t : T' ⟶ T) (x : Fam 𝓜 T) :
    Fam.res (t' ≫ t) x = Fam.res t' (Fam.res t x) :=
  Fam.ext fun hA a _ v => by
    change x.val hA (a ≫ t' ≫ t) v = x.val hA ((a ≫ t') ≫ t) v
    rw [Category.assoc]

/-- The group of values. -/
@[reducible] def shG (T : SB Bsp) : AddCommGroup (Shrink.{u} (Fam 𝓜 T)) :=
  (equivShrink _).symm.addCommGroup

attribute [local instance] shG

/-- The module of values. -/
@[reducible] def shM (T : SB Bsp) : Module ((OB Bsp).obj (op T)) (Shrink.{u} (Fam 𝓜 T)) :=
  Equiv.module _ (equivShrink (Fam 𝓜 T)).symm.addEquiv

attribute [local instance] shM

lemma sh_add {T : SB Bsp} (x y : Shrink.{u} (Fam 𝓜 T)) :
    (equivShrink (Fam 𝓜 T)).symm (x + y) = (equivShrink _).symm x + (equivShrink _).symm y :=
  Equiv.symm_apply_apply (equivShrink (Fam 𝓜 T)) ((equivShrink _).symm x + (equivShrink _).symm y)

lemma sh_smul {T : SB Bsp} (r : (OB Bsp).obj (op T)) (x : Shrink.{u} (Fam 𝓜 T)) :
    (equivShrink (Fam 𝓜 T)).symm (r • x) = r • (equivShrink _).symm x :=
  Equiv.symm_apply_apply (equivShrink (Fam 𝓜 T)) (r • (equivShrink _).symm x)

/-- The `𝒪_B`-module of compatible families. -/
def famPMod (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB) : PMod (OB Bsp) where
  obj T := Shrink.{u} (Fam 𝓜 T.unop)
  grp T := shG T.unop
  mod T := shM T.unop
  map f := AddMonoidHom.mk' (fun x => equivShrink _ (Fam.res f.unop ((equivShrink _).symm x)))
    (fun a b => (equivShrink _).symm.injective (by
      simp only [sh_add, Equiv.symm_apply_apply]
      exact Fam.res_add _ _ _))
  map_smul {U V} f r x := by
    refine (equivShrink (Fam 𝓜 V.unop)).symm.injective ?_
    refine (Equiv.symm_apply_apply _ _).trans ?_
    refine (congrArg (Fam.res f.unop) (sh_smul (T := U.unop) r x)).trans ?_
    refine (Fam.res_smul f.unop r _).trans ?_
    refine Eq.trans ?_ (sh_smul (T := V.unop) _ _).symm
    exact congrArg (_ • ·) (Equiv.symm_apply_apply _ _).symm
  map_id U x := by
    change equivShrink _ (Fam.res (𝟙 _) _) = x
    rw [Fam.res_id, Equiv.apply_symm_apply]
  map_comp f g x := by
    change equivShrink _ (Fam.res (g.unop ≫ f.unop) _) =
      equivShrink _ (Fam.res g.unop ((equivShrink _).symm (equivShrink _ _)))
    rw [Fam.res_comp, Equiv.symm_apply_apply]

/-- The identification of the values of `famPMod`. -/
def famE (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB) (T : SB Bsp) :
    (famPMod 𝓜).obj (op T) ≃+ Fam 𝓜 T where
  __ := (equivShrink _).symm
  map_add' x y := sh_add x y

lemma famE_map {T' T : SB Bsp} (t : T' ⟶ T) (x : (famPMod 𝓜).obj (op T)) :
    famE 𝓜 T' ((famPMod 𝓜).map t.op x) = Fam.res t (famE 𝓜 T x) :=
  Equiv.symm_apply_apply (equivShrink _) _

lemma famE_smul (T : SB Bsp) (r : (OB Bsp).obj (op T)) (x : (famPMod 𝓜).obj (op T)) :
    famE 𝓜 T (r • x) = r • famE 𝓜 T x := sh_smul r x

end AlgMag.B3
