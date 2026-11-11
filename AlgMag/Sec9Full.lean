/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalMiscProp91Sheaf

/-!
# Propositions 9.9, 9.10, 9.11 of *Algebraic Magnetism* on the whole site of `B`

The earlier forms (`homAtEquivHomPush`, `hModuleEquivCoaction`, `coactionEquivDecomp`) describe a
morphism `F → G ⊗ 𝒜` by its values on the affine objects of the site of `B`, glued back by hand.
Here the target is the module `f_* f^* G` on the whole site (`PushSec X G`, with the module structure of
`AlgMag.FinalMisc`), which is `G ⊗_𝒪 𝒜` as a sheaf by Proposition 9.1 (`AlgMag.FinalMisc.prop91_sheaf`).

* `HomTo F G X`: morphisms of `𝒪_B`-modules `F → f_* f^* G`, on every object of the site.
* `homAtEquivHomTo`: Proposition 9.9, first assertion; `homAtEquivHomTo_pull`: second assertion.
* `Coaction F H`: comodule structures `ρ : F → f_* f^* F = F ⊗ 𝒜`, coassociative and counital.
* `hModuleEquivCoactionFull`: Proposition 9.10.
* `prop911_full`: Propositions 9.10 and 9.11 for `𝔸(M)_B`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace AlgMag.S9Full

open AlgMag.S9B AlgMag.S9BF AlgMag.S9BS AlgMag.S9BR AlgMag.B2 AlgMag.Final AlgMag.FinalMisc
open AlgMag.S9 (PMod HModule)

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}
  {F G : PMod (OB Bsp)} {X X' : (SB Bsp)ᵒᵖ ⥤ Type u}

variable (F G X) in
/-- `Hom_{𝒪_B}(F, f_* f^* G)`: `𝒪(T)`-linear maps `F(T) → (f_* f^* G)(T)` for every object `T` of the
site of `B`, compatible with all restrictions. -/
structure HomTo where
  /-- the value on `T` -/
  app : ∀ T : SB Bsp, F.obj (op T) →ₗ[(OB Bsp).obj (op T)] PushSec X G T
  naturality : ∀ {T T' : SB Bsp} (s : T' ⟶ T) (v : F.obj (op T)),
    app T' (F.map s.op v) = pushRes s (app T v)

lemma HomTo.ext' {a b : HomTo F G X}
    (h : ∀ (T : SB Bsp) (v : F.obj (op T)) {W : SB Bsp} (t : W ⟶ T) (x : X.obj (op W)),
      (a.app T v).val t x = (b.app T v).val t x) : a = b := by
  cases a with
  | mk a na =>
    cases b with
    | mk b nb =>
      have : a = b := by
        funext T
        refine LinearMap.ext fun v => ?_
        exact pushSec_val_injective G T fun t x => h T v t x
      subst this
      rfl

/-- **Proposition 9.9**, first assertion, on the whole site: `Hom_𝒪(F, G)(X) = Hom_𝒪(F, f_* f^* G)`.
No hypothesis on `F`, `G`, `X`. For `X → B` affine and `G` quasi-coherent, `f_* f^* G = G ⊗_𝒪 𝒜` by
Proposition 9.1 (`prop99_full_tensor`). -/
def homAtEquivHomTo : HomAt F G X ≃ HomTo F G X where
  toFun φ :=
    { app := fun T =>
        { toFun := fun v =>
            ⟨fun t x => φ.app x (F.map t.op v), fun s t x => by
              rw [op_comp, F.map_comp, φ.naturality]⟩
          map_add' := fun v w => pushSec_val_injective G T fun t x => by
            change φ.app x (F.map t.op (v + w)) = φ.app x (F.map t.op v) + φ.app x (F.map t.op w)
            rw [map_add, map_add]
          map_smul' := fun c v => pushSec_val_injective G T fun t x => by
            change φ.app x (F.map t.op (c • v)) = ((OB Bsp).map t.op).hom c • φ.app x (F.map t.op v)
            rw [F.map_smul, LinearMap.map_smul] }
      naturality := fun s v => pushSec_val_injective G _ fun t x => by
        change φ.app x (F.map t.op (F.map s.op v)) = φ.app x (F.map (t ≫ s).op v)
        rw [op_comp, F.map_comp] }
  invFun ψ :=
    { app := fun {T} x =>
        { toFun := fun v => (ψ.app T v).val (𝟙 T) x
          map_add' := fun v w => by rw [map_add]; rfl
          map_smul' := fun c v => by
            rw [LinearMap.map_smul]
            change ((OB Bsp).map (𝟙 T).op).hom c • _ = _
            rw [op_id, (OB Bsp).map_id]
            rfl }
      naturality := fun {T T'} s x v => by
        change (ψ.app T' (F.map s.op v)).val (𝟙 T') (X.map s.op x) = G.map s.op ((ψ.app T v).val (𝟙 T) x)
        rw [ψ.naturality, ← (ψ.app T v).naturality]
        change (ψ.app T v).val (𝟙 T' ≫ s) _ = (ψ.app T v).val (s ≫ 𝟙 T) _
        rw [Category.id_comp, Category.comp_id] }
  left_inv φ := by
    ext T x v
    change φ.app x (F.map (𝟙 T).op v) = φ.app x v
    rw [op_id, F.map_id]
  right_inv ψ := HomTo.ext' fun T v W t x => by
    change (ψ.app W (F.map t.op v)).val (𝟙 W) x = (ψ.app T v).val t x
    rw [ψ.naturality]
    change (ψ.app T v).val (𝟙 W ≫ t) x = _
    rw [Category.id_comp]

/-- `m^♯ : f_* f^* G → f'_* f'^* G` for `m : X' ⟶ X`. -/
def pushSecMap (m : X' ⟶ X) {T : SB Bsp} (σ : PushSec X G T) : PushSec X' G T where
  val t x := σ.val t (m.app _ x)
  naturality s t x := by
    rw [← σ.naturality, nat_apply]

/-- The map `(Id_G ⊗ m^♯)` of Proposition 9.9, on the whole site. -/
def HomTo.push (m : X' ⟶ X) (ψ : HomTo F G X) : HomTo F G X' where
  app T :=
    { toFun := fun v => pushSecMap m (ψ.app T v)
      map_add' := fun v w => by rw [map_add]; rfl
      map_smul' := fun c v => by rw [LinearMap.map_smul]; rfl }
  naturality s v := by
    change pushSecMap m (ψ.app _ (F.map s.op v)) = _
    rw [ψ.naturality]
    rfl

/-- **Proposition 9.9**, second assertion: the map `Hom_𝒪(F, G)(X) → Hom_𝒪(F, G)(X')` induced by
`m : X' ⟶ X` corresponds to composition with `Id_G ⊗ m^♯`. -/
theorem homAtEquivHomTo_pull (m : X' ⟶ X) (φ : HomAt F G X) :
    homAtEquivHomTo (φ.pull m) = (homAtEquivHomTo φ).push m :=
  HomTo.ext' fun _ _ _ _ _ => rfl

/-- The whole-site form agrees with the affine form `HomPush` (values on affine objects). -/
def homToEquivHomPush (r : AffOver X) (hG : IsQCoh G) : HomTo F G X ≃ HomPush F G r :=
  homAtEquivHomTo.symm.trans (homAtEquivHomPush r hG)

/-- **Proposition 9.9** for an affine morphism of algebraic spaces `p : Y → B`, on the whole site. -/
def prop99_full {Y : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ Bsp) :
    HomAt F G (Vp p) ≃ HomTo F G (Vp p) :=
  homAtEquivHomTo

/-- **Proposition 9.9**: the target `f_* f^* G` of `prop99_full` is `G ⊗_𝒪 𝒜`, the sheafification of the
presheaf tensor product, for `G` quasi-coherent in the printed sense and `p` affine (Proposition 9.1). -/
theorem prop99_full_tensor {Y : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ Bsp)
    (hp : Space.IsAffineHom Bs S hS p) (hG : PrintedQCoh G) (J : GrothendieckTopology (SB Bsp))
    (hJ : ∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left), coverSieve T 𝒰 ∈ J T)
    (hGJ : Presieve.IsSheaf J G.toPresheaf) :
    Presheaf.IsLocallyInjective J (canon G (Vp p)) ∧ Presheaf.IsLocallySurjective J (canon G (Vp p)) ∧
      Presieve.IsSheaf J (pushF G (Vp p)) ∧
      ∀ (Q : (SB Bsp)ᵒᵖ ⥤ Type (u + 1)), Presieve.IsSheaf J Q → ∀ h : preTen G (Vp p) ⟶ Q,
        ∃! k : pushF G (Vp p) ⟶ Q, canon G (Vp p) ≫ k = h :=
  prop91_sheaf (affOverOfIsAffineHom p hp) hG J hJ hGJ

/-! ### Proposition 9.10 -/

section Comodule

variable {H : (SB Bsp)ᵒᵖ ⥤ MonCat.{u}}

variable (H F) in
/-- **Proposition 9.10**, comodule side, on the whole site: `ρ : F → f_* f^* F = F ⊗ 𝒜` with
`(ρ ⊗ Id_𝒜) ρ = (Id_F ⊗ Δ) ρ` and `(Id_F ⊗ ε) ρ = Id_F`, read at the points `(t, g, h)` of `T ×_B H ×_B H`
and `(Id, 1)` of `T`. -/
structure Coaction where
  /-- `ρ` -/
  ρ : HomTo F F (H ⋙ forget MonCat)
  coassoc : ∀ (T : SB Bsp) (v : F.obj (op T)) {W : SB Bsp} (t : W ⟶ T) (g h : H.obj (op W)),
    (ρ.app W ((ρ.app T v).val t h)).val (𝟙 W) g = (ρ.app T v).val t (g * h)
  counit : ∀ (T : SB Bsp) (v : F.obj (op T)), (ρ.app T v).val (𝟙 T) (1 : H.obj (op T)) = v

lemma Coaction.ext' {A B : Coaction F H} (h : A.ρ = B.ρ) : A = B := by
  cases A; cases B; cases h; rfl

/-- **Proposition 9.10**, on the whole site: `H`-`𝒪`-module structures on `F` are comodule structures
`F → F ⊗ 𝒜 = f_* f^* F`. No hypothesis on `F` or `H`; for `H → B` affine and `F` quasi-coherent the
target is `F ⊗_𝒪 𝒜` by Proposition 9.1. -/
def hModuleEquivCoactionFull : HModule H F ≃ Coaction F H where
  toFun A :=
    { ρ :=
      { app := fun T =>
          { toFun := fun v =>
              ⟨fun t g => A.smul g (F.map t.op v), fun s t g => by
                rw [op_comp, F.map_comp, A.map_smul]
                rfl⟩
            map_add' := fun v w => pushSec_val_injective (X := H ⋙ forget MonCat) F T fun t g => by
              change A.smul g (F.map t.op (v + w)) = A.smul g (F.map t.op v) + A.smul g (F.map t.op w)
              rw [map_add, A.smul_add]
            map_smul' := fun c v => pushSec_val_injective (X := H ⋙ forget MonCat) F T fun t g => by
              change A.smul g (F.map t.op (c • v)) = ((OB Bsp).map t.op).hom c • A.smul g (F.map t.op v)
              rw [F.map_smul, A.smul_smul] }
        naturality := fun s v => pushSec_val_injective (X := H ⋙ forget MonCat) F _ fun t g => by
          change A.smul g (F.map t.op (F.map s.op v)) = A.smul g (F.map (t ≫ s).op v)
          rw [op_comp, F.map_comp] }
      coassoc := fun T v W t g h => by
        change A.smul g (F.map (𝟙 W).op (A.smul h (F.map t.op v))) = A.smul (g * h) (F.map t.op v)
        rw [op_id, F.map_id, A.mul_smul]
      counit := fun T v => by
        change A.smul 1 (F.map (𝟙 T).op v) = v
        rw [op_id, F.map_id, A.one_smul] }
  invFun R :=
    { smul := fun {U} g x => (R.ρ.app U.unop x).val (𝟙 U.unop) g
      one_smul := fun {U} x => R.counit U.unop x
      mul_smul := fun {U} g h x => (R.coassoc U.unop x (𝟙 U.unop) g h).symm
      smul_add := fun {U} g x y => by rw [map_add]; rfl
      smul_smul := fun {U} g a x => by
        rw [LinearMap.map_smul]
        change ((OB Bsp).map (𝟙 U.unop).op).hom a • _ = _
        rw [op_id, (OB Bsp).map_id]
        rfl
      map_smul := fun {U V} f g x => by
        change F.map f.unop.op ((R.ρ.app U.unop x).val (𝟙 U.unop) g) =
          (R.ρ.app V.unop (F.map f.unop.op x)).val (𝟙 V.unop) ((H.map f.unop.op).hom g)
        rw [R.ρ.naturality, ← (R.ρ.app U.unop x).naturality]
        change (R.ρ.app U.unop x).val (f.unop ≫ 𝟙 U.unop) _ = (R.ρ.app U.unop x).val (𝟙 V.unop ≫ f.unop) _
        rw [Category.id_comp, Category.comp_id]
        rfl }
  left_inv A := by
    refine HModule.ext'' fun U g x => ?_
    change A.smul g (F.map (𝟙 U.unop).op x) = A.smul g x
    rw [op_id, F.map_id]
  right_inv R := Coaction.ext' <| HomTo.ext' fun T v W t g => by
    change (R.ρ.app W (F.map t.op v)).val (𝟙 W) g = (R.ρ.app T v).val t g
    rw [R.ρ.naturality]
    change (R.ρ.app T v).val (𝟙 W ≫ t) g = _
    rw [Category.id_comp]

/-- The whole-site comodules agree with the affine form `CoactionAff`. -/
def coactionEquivAff (r : AffOver (H ⋙ forget MonCat)) (hF : IsQCoh F) :
    Coaction F H ≃ CoactionAff F r :=
  hModuleEquivCoactionFull.symm.trans (hModuleEquivCoaction r hF)

/-- **Proposition 9.10** for an affine monoid algebraic space over `B`, on the whole site. -/
def prop910_full : HModule H F ≃ Coaction F H := hModuleEquivCoactionFull

end Comodule

/-! ### Proposition 9.11 -/

variable {M : Type u} [AddCommMonoid M] [Countable M]

/-- **Propositions 9.10 and 9.11** for `𝔸(M)_B`, on the whole site: comodule structures
`F → F ⊗ 𝒪_B[M]` on a quasi-coherent `F` are the families `(ρ_m)` of the corrected wording
(`AlgMag.S9B.Decomp`). -/
def prop911_full (hF : IsQCoh F) : Coaction F (Hm M Bsp) ≃ Decomp F M :=
  (coactionEquivAff affOverHm hF).trans (coactionEquivDecomp hF)

/-- **Propositions 9.10 and 9.11** for `𝔸(M)_B`, from module structures, for the printed notion. -/
def prop911_full_printed (hF : PrintedQCoh F) : HModule (Hm M Bsp) F ≃ Decomp F M :=
  prop910_full.trans (prop911_full hF.isQCoh)

end AlgMag.S9Full

#print axioms AlgMag.S9Full.homAtEquivHomTo
#print axioms AlgMag.S9Full.homAtEquivHomTo_pull
#print axioms AlgMag.S9Full.prop99_full_tensor
#print axioms AlgMag.S9Full.hModuleEquivCoactionFull
#print axioms AlgMag.S9Full.prop911_full
#print axioms AlgMag.S9Full.prop911_full_printed
