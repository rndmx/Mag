/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverB
import AlgMag.SecLeftoverQCoh
import AlgMag.SecLeftoverQCohB

/-!
# §9 of *Algebraic Magnetism* over an algebraic space `B`: Propositions 9.1, 9.9, 9.10, 9.12

Objects over `B` are presheaves on `SB Bsp`. An affine morphism `X → B` is given by `AffOver X`: for
each affine `T` over `B`, the affine scheme `T ×_B X` (`P T`) with its universal property.

* `AlgMag.S9BF.prop91`: Proposition 9.1.
* `AlgMag.S9BF.homAtEquivHomPush`, `AlgMag.S9BF.homAtEquivHomPush_pull`: Proposition 9.9.
* `AlgMag.S9BF.hModuleEquivCoaction`: Proposition 9.10.
* `AlgMag.S9BF.cochainVEquivFinsupp`: Proposition 9.12, quasi-compact `V` (`QCCover`), literal `⨁`.
* `AlgMag.S9BF.isQCoh_of_local`: quasi-coherence on the big site from the local datum of Tag 03DX (1).
* `AlgMag.S9BF.isQCoh_of_scheme`: the case of a module pulled back from a scheme.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.checkUnivs false
set_option linter.deprecated false

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Classical

noncomputable section

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

namespace AlgMag.S9BF

open AlgMag.S9 AlgMag.S9B

/-- An affine morphism `X → B`: for `T` affine over `B`, the affine scheme `T ×_B X`. -/
structure AffOver (X : (SB Bsp)ᵒᵖ ⥤ Type u) where
  /-- `T ×_B X` -/
  P : ∀ (T : SB Bsp) [IsAffine T.left], SB Bsp
  aff : ∀ (T : SB Bsp) [IsAffine T.left], IsAffine (P T).left
  /-- the projection to `T` -/
  pr : ∀ (T : SB Bsp) [IsAffine T.left], P T ⟶ T
  /-- the projection to `X` -/
  univ : ∀ (T : SB Bsp) [IsAffine T.left], X.obj (op (P T))
  /-- the universal property -/
  lift : ∀ {T W : SB Bsp} [IsAffine T.left], (W ⟶ T) → X.obj (op W) → (W ⟶ P T)
  lift_pr : ∀ {T W : SB Bsp} [IsAffine T.left] (t : W ⟶ T) (x : X.obj (op W)),
    lift t x ≫ pr T = t
  lift_univ : ∀ {T W : SB Bsp} [IsAffine T.left] (t : W ⟶ T) (x : X.obj (op W)),
    X.map (lift t x).op (univ T) = x
  uniq : ∀ {T W : SB Bsp} [IsAffine T.left] (g g' : W ⟶ P T), g ≫ pr T = g' ≫ pr T →
    X.map g.op (univ T) = X.map g'.op (univ T) → g = g'

attribute [local instance] AffOver.aff

variable {X X' : (SB Bsp)ᵒᵖ ⥤ Type u} (r : AffOver X) (r' : AffOver X')

namespace AffOver

lemma comp_lift {T W W' : SB Bsp} [IsAffine T.left] (q : W' ⟶ W) (t : W ⟶ T) (x : X.obj (op W)) :
    q ≫ r.lift t x = r.lift (q ≫ t) (X.map q.op x) := by
  refine r.uniq _ _ ?_ ?_
  · rw [Category.assoc, r.lift_pr, r.lift_pr]
  · rw [r.lift_univ, op_comp, X.map_comp]
    simp only [types_comp_apply]
    rw [r.lift_univ]

/-- `s ×_B X : T' ×_B X → T ×_B X`. -/
def Pmap {T T' : SB Bsp} [IsAffine T.left] [IsAffine T'.left] (s : T' ⟶ T) : r.P T' ⟶ r.P T :=
  r.lift (r.pr T' ≫ s) (r.univ T')

lemma lift_Pmap {T T' W : SB Bsp} [IsAffine T.left] [IsAffine T'.left] (s : T' ⟶ T) (t : W ⟶ T')
    (x : X.obj (op W)) : r.lift t x ≫ r.Pmap s = r.lift (t ≫ s) x := by
  unfold Pmap
  rw [comp_lift, r.lift_univ, ← Category.assoc, r.lift_pr]

lemma lift_pr_univ {T : SB Bsp} [IsAffine T.left] : r.lift (r.pr T) (r.univ T) = 𝟙 _ := by
  refine r.uniq _ _ ?_ ?_
  · rw [r.lift_pr, Category.id_comp]
  · rw [r.lift_univ, op_id, X.map_id]
    rfl

end AffOver

variable {F G : PMod (OB Bsp)}

/-- **Proposition 9.1**: for `T` affine over `B`, the restriction `G(T) → (f_* f^* G)(T) = G(T ×_B X)`
is the base change along `Γ(T) → Γ(T ×_B X) = 𝒜(T)`: `f_* f^* G = G ⊗_𝒪 𝒜`. -/
theorem prop91 (hG : IsQCoh G) (T : SB Bsp) [IsAffine T.left] :
    IsBC ((OB Bsp).map (r.pr T).op).hom (G.map (r.pr T).op) (G.map_smul (r.pr T).op) :=
  hG.base_change (r.pr T)

omit r r' in
lemma nat_apply (m : X' ⟶ X) {U V : (SB Bsp)ᵒᵖ} (g : U ⟶ V) (y : X'.obj U) :
    X.map g (m.app U y) = m.app V (X'.map g y) :=
  (ConcreteCategory.congr_hom (m.naturality g) y).symm

variable (F) in
/-- `Hom_𝒪(F, G)(X)`: morphisms of `𝒪`-modules `F|_X → G|_X`. -/
@[ext]
structure HomAt (G : PMod (OB Bsp)) (X : (SB Bsp)ᵒᵖ ⥤ Type u) where
  /-- the value at `x ∈ X(T)` -/
  app : ∀ {T : SB Bsp} (_ : X.obj (op T)), F.obj (op T) →ₗ[(OB Bsp).obj (op T)] G.obj (op T)
  naturality : ∀ {T T' : SB Bsp} (s : T' ⟶ T) (x : X.obj (op T)) (v : F.obj (op T)),
    app (X.map s.op x) (F.map s.op v) = G.map s.op (app x v)

/-- The pull-back `Hom_𝒪(F, G)(X) → Hom_𝒪(F, G)(X')` along `m : X' ⟶ X`. -/
def HomAt.pull (m : X' ⟶ X) (φ : HomAt F G X) : HomAt F G X' where
  app x := φ.app (m.app _ x)
  naturality s x v := by
    rw [← φ.naturality]
    congr 2
    exact (nat_apply m s.op x).symm

variable (F G) in
/-- `Hom_𝒪(F, f_* f^* G)`, `f_* f^* G = G ⊗ 𝒜` by Proposition 9.1, on the affine objects (which
determine a morphism to a quasi-coherent module). -/
@[ext]
structure HomPush (r : AffOver X) where
  /-- the value at `T` -/
  app : ∀ (T : SB Bsp) [IsAffine T.left], F.obj (op T) →+ G.obj (op (r.P T))
  map_smul : ∀ (T : SB Bsp) [IsAffine T.left] (a : (OB Bsp).obj (op T)) (v : F.obj (op T)),
    app T (a • v) = ((OB Bsp).map (r.pr T).op).hom a • app T v
  naturality : ∀ {T T' : SB Bsp} [IsAffine T.left] [IsAffine T'.left] (s : T' ⟶ T)
    (v : F.obj (op T)), app T' (F.map s.op v) = G.map (r.Pmap s).op (app T v)

/-- `m` over `T`: `T ×_B X' → T ×_B X`. -/
def Pm (m : X' ⟶ X) (T : SB Bsp) [IsAffine T.left] : r'.P T ⟶ r.P T :=
  r.lift (r'.pr T) (m.app _ (r'.univ T))

/-- The map `(Id_G ⊗ m^♯)` of Proposition 9.9. -/
def HomPush.push (m : X' ⟶ X) (ψ : HomPush F G r) : HomPush F G r' where
  app T _ := (G.map (Pm r r' m T).op).comp (ψ.app T)
  map_smul T _ a v := by
    simp only [AddMonoidHom.comp_apply]
    rw [ψ.map_smul, G.map_smul, ← CommRingCat.comp_apply, ← (OB Bsp).map_comp, ← op_comp]
    unfold Pm
    rw [r.lift_pr]
  naturality {T T'} _ _ s v := by
    simp only [AddMonoidHom.comp_apply]
    rw [ψ.naturality, ← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp]
    congr 2
    unfold Pm
    rw [r.lift_Pmap, AffOver.Pmap, AffOver.comp_lift, r'.lift_pr, nat_apply, r'.lift_univ]

/-- The value of the inverse of Proposition 9.9, over an affine `A → T`. -/
def pushVal (ψ : HomPush F G r) {A : SB Bsp} [IsAffine A.left] (x : X.obj (op A)) (v : F.obj (op A)) :
    G.obj (op A) :=
  G.map (r.lift (𝟙 A) x).op (ψ.app A v)

lemma pushVal_res (ψ : HomPush F G r) {A A' : SB Bsp} [IsAffine A.left] [IsAffine A'.left]
    (s : A' ⟶ A) (x : X.obj (op A)) (v : F.obj (op A)) :
    pushVal r ψ (X.map s.op x) (F.map s.op v) = G.map s.op (pushVal r ψ x v) := by
  unfold pushVal
  rw [ψ.naturality, ← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp]
  congr 2
  rw [r.lift_Pmap, AffOver.comp_lift, Category.id_comp, Category.comp_id]

lemma pushVal_smul (ψ : HomPush F G r) {A : SB Bsp} [IsAffine A.left] (x : X.obj (op A))
    (a : (OB Bsp).obj (op A)) (v : F.obj (op A)) :
    pushVal r ψ x (a • v) = a • pushVal r ψ x v := by
  unfold pushVal
  rw [ψ.map_smul, G.map_smul, ← CommRingCat.comp_apply, ← (OB Bsp).map_comp, ← op_comp, r.lift_pr]
  simp

variable (hG : IsQCoh G)

include hG

/-- The glued value of the inverse of Proposition 9.9. -/
def pushGlue (ψ : HomPush F G r) {T : SB Bsp} (x : X.obj (op T)) (v : F.obj (op T)) : G.obj (op T) :=
  glueV hG T (fun A a _ => pushVal r ψ (X.map a.op x) (F.map a.op v)) (fun A A' s a _ _ => by
    rw [← pushVal_res, op_comp, X.map_comp, F.map_comp]
    rfl)

lemma pushGlue_spec (ψ : HomPush F G r) {T A : SB Bsp} (a : A ⟶ T) [IsAffine A.left]
    (x : X.obj (op T)) (v : F.obj (op T)) :
    G.map a.op (pushGlue r hG ψ x v) = pushVal r ψ (X.map a.op x) (F.map a.op v) :=
  glueV_spec hG T _ _ A a

lemma pushGlue_affine (ψ : HomPush F G r) {A : SB Bsp} [IsAffine A.left]
    (x : X.obj (op A)) (v : F.obj (op A)) : pushGlue r hG ψ x v = pushVal r ψ x v := by
  have h := pushGlue_spec r hG ψ (𝟙 A) x v
  rw [op_id, G.map_id, X.map_id, F.map_id] at h
  exact h

/-- **Proposition 9.9**: `Hom_𝒪(F, G)(X) = Hom_𝒪(F, G ⊗ 𝒜)`, for `G` quasi-coherent and `X → B`
affine (flatness and finite presentation are not needed). -/
def homAtEquivHomPush : HomAt F G X ≃ HomPush F G r where
  toFun φ :=
    { app := fun T _ => (φ.app (r.univ T)).toAddMonoidHom.comp (F.map (r.pr T).op)
      map_smul := fun T _ a v => by
        simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
        rw [F.map_smul, _root_.map_smul]
      naturality := fun {T T'} _ _ s v => by
        simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
        rw [← φ.naturality, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
        unfold AffOver.Pmap
        rw [r.lift_pr, r.lift_univ] }
  invFun ψ :=
    { app := fun {T} x =>
        { toFun := fun v => pushGlue r hG ψ x v
          map_add' := fun v w => by
            refine sep_affine hG T fun A a _ => ?_
            rw [map_add, pushGlue_spec, pushGlue_spec, pushGlue_spec, map_add]
            unfold pushVal
            rw [map_add, map_add]
          map_smul' := fun c v => by
            refine sep_affine hG T fun A a _ => ?_
            rw [RingHom.id_apply, G.map_smul, pushGlue_spec, pushGlue_spec, F.map_smul,
              pushVal_smul] }
      naturality := fun {T T'} s x v => by
        refine sep_affine hG T' fun A a _ => ?_
        change G.map a.op (pushGlue r hG ψ _ _) = G.map a.op (G.map s.op (pushGlue r hG ψ x v))
        rw [← G.map_comp, ← op_comp, pushGlue_spec, pushGlue_spec, op_comp, X.map_comp, F.map_comp]
        rfl }
  left_inv φ := by
    ext T x v
    change pushGlue r hG _ x v = _
    refine sep_affine hG T fun A a _ => ?_
    rw [pushGlue_spec]
    change G.map _ (φ.app (r.univ A) (F.map _ (F.map a.op v))) = _
    rw [← φ.naturality, ← F.map_comp, ← op_comp, r.lift_pr, r.lift_univ, op_id, F.map_id,
      φ.naturality]
  right_inv ψ := by
    ext T _ v
    change pushGlue r hG ψ _ _ = _
    rw [pushGlue_affine]
    unfold pushVal
    rw [ψ.naturality, ← G.map_comp, ← op_comp, r.lift_Pmap, Category.id_comp, r.lift_pr_univ,
      op_id, G.map_id]

/-- **Proposition 9.9**, second assertion: the map induced by `m : X' ⟶ X` is `(Id_G ⊗ m^♯)`. -/
theorem homAtEquivHomPush_pull (m : X' ⟶ X) (φ : HomAt F G X) :
    homAtEquivHomPush r' hG (φ.pull m) = (homAtEquivHomPush r hG φ).push r r' m := by
  ext T _ v
  change φ.app (m.app _ (r'.univ T)) (F.map (r'.pr T).op v) =
    G.map (Pm r r' m T).op (φ.app (r.univ T) (F.map (r.pr T).op v))
  rw [← φ.naturality, ← F.map_comp, ← op_comp]
  unfold Pm
  rw [r.lift_pr, r.lift_univ]

omit hG

/-! ### Proposition 9.10 -/

section Comodule

variable {H : (SB Bsp)ᵒᵖ ⥤ MonCat.{u}} (r : AffOver (H ⋙ forget MonCat))

/-- The universal point of `H` on `T ×_B H`. -/
abbrev Hu (T : SB Bsp) [IsAffine T.left] : H.obj (op (r.P T)) := r.univ T

/-- The morphism to `T ×_B H` given by `t` and a point of `H`. -/
abbrev lg {T W : SB Bsp} [IsAffine T.left] (t : W ⟶ T) (g : H.obj (op W)) : W ⟶ r.P T := r.lift t g

lemma res_lg {T W : SB Bsp} [IsAffine T.left] (t : W ⟶ T) (g : H.obj (op W)) :
    (H.map (lg r t g).op).hom (Hu r T) = g := r.lift_univ t g

variable (F) in
/-- **Proposition 9.10**, comodule side: `ρ : F → F ⊗ 𝒜` with `(ρ ⊗ Id) ρ = (Id ⊗ Δ) ρ` and
`(Id ⊗ ε) ρ = Id`, on the affine objects. -/
structure CoactionAff where
  /-- `ρ` -/
  ρ : HomPush F F r
  coassoc : ∀ (T : SB Bsp) [IsAffine T.left] (v : F.obj (op T)),
    ρ.app (r.P T) (ρ.app T v) =
      F.map (lg r (r.pr (r.P T) ≫ r.pr T)
        (Hu r (r.P T) * (H.map (r.pr (r.P T)).op).hom (Hu r T))).op (ρ.app T v)
  counit : ∀ (T : SB Bsp) [IsAffine T.left] (v : F.obj (op T)),
    F.map (lg r (𝟙 T) (1 : H.obj (op T))).op (ρ.app T v) = v

lemma pushVal_one (R : CoactionAff F r) {A : SB Bsp} [IsAffine A.left] (v : F.obj (op A)) :
    pushVal r R.ρ (X := H ⋙ forget MonCat) (1 : H.obj (op A)) v = v := R.counit A v

lemma pushVal_mul (R : CoactionAff F r) {A : SB Bsp} [IsAffine A.left] (g h : H.obj (op A))
    (v : F.obj (op A)) :
    pushVal r R.ρ (X := H ⋙ forget MonCat) (g * h) v =
      pushVal r R.ρ (X := H ⋙ forget MonCat) g (pushVal r R.ρ (X := H ⋙ forget MonCat) h v) := by
  unfold pushVal
  rw [R.ρ.naturality, R.coassoc, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
  congr 2
  rw [r.lift_Pmap, Category.id_comp, AffOver.comp_lift]
  refine congrArg Quiver.Hom.op ?_
  congr 1
  · rw [← Category.assoc, r.lift_pr, r.lift_pr]
  · change g * h = (H.map _).hom (_ * _)
    rw [map_mul]
    congr 1
    · exact (r.lift_univ _ _).symm
    · change h = (H.map _).hom ((H.map (r.pr (r.P A)).op).hom (Hu r A))
      rw [← MonCat.comp_apply, ← H.map_comp, ← op_comp, r.lift_pr]
      exact (r.lift_univ _ _).symm

lemma CoactionAff.ext' {A B : CoactionAff F r} (h : A.ρ = B.ρ) : A = B := by
  cases A; cases B; cases h; rfl

lemma HModule.ext'' {A B : HModule H F}
    (h : ∀ (U : (SB Bsp)ᵒᵖ) (g : H.obj U) (x : F.obj U), A.smul g x = B.smul g x) : A = B := by
  cases A with
  | mk a _ _ _ _ _ =>
    cases B with
    | mk b _ _ _ _ _ =>
      have : @a = @b := by
        funext U g x
        exact h U g x
      subst this
      rfl

/-- **Proposition 9.10**: for `F` quasi-coherent and `H → B` affine, `H`-`𝒪`-module structures on `F`
correspond to comodule structures `F → F ⊗ 𝒜`; the action is `g • v = (id, g)^* ρ(v)`. -/
def hModuleEquivCoaction (hF : IsQCoh F) : HModule H F ≃ CoactionAff F r where
  toFun A :=
    { ρ :=
      { app := fun T _ =>
          { toFun := fun v => A.smul (Hu r T) (F.map (r.pr T).op v)
            map_zero' := by rw [map_zero, A.smul_zero]
            map_add' := fun a b => by rw [map_add, A.smul_add] }
        map_smul := fun T _ a v => by
          change A.smul _ (F.map _ _) = _ • A.smul _ (F.map _ _)
          rw [F.map_smul, A.smul_smul]
        naturality := fun {T T'} _ _ s v => by
          change A.smul _ (F.map _ (F.map _ v)) = F.map _ (A.smul _ (F.map _ v))
          rw [A.map_smul, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
          unfold AffOver.Pmap
          rw [r.lift_pr]
          congr 1
          exact (r.lift_univ _ _).symm }
      coassoc := fun T _ v => by
        change A.smul (Hu r (r.P T)) (F.map (r.pr (r.P T)).op
          (A.smul (Hu r T) (F.map (r.pr T).op v))) =
          F.map _ (A.smul (Hu r T) (F.map (r.pr T).op v))
        rw [A.map_smul, A.map_smul, ← A.mul_smul, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp,
          r.lift_pr, res_lg]
      counit := fun T _ v => by
        change F.map _ (A.smul (Hu r T) (F.map (r.pr T).op v)) = v
        rw [A.map_smul, res_lg, ← F.map_comp, ← op_comp, r.lift_pr, op_id, F.map_id, A.one_smul] }
  invFun R :=
    { smul := fun {U} g x => pushGlue r hF R.ρ (X := H ⋙ forget MonCat) g x
      one_smul := fun {U} x => by
        refine sep_affine hF (unop U) fun A a _ => ?_
        rw [pushGlue_spec]
        have e : (H ⋙ forget MonCat).map a.op (1 : H.obj U) = (1 : H.obj (op A)) :=
          map_one (H.map a.op).hom
        rw [e]
        exact pushVal_one r R _
      mul_smul := fun {U} g h x => by
        refine sep_affine hF (unop U) fun A a _ => ?_
        rw [pushGlue_spec, pushGlue_spec, pushGlue_spec]
        have e : (H ⋙ forget MonCat).map a.op (g * h) =
            ((H.map a.op).hom g * (H.map a.op).hom h : H.obj (op A)) :=
          map_mul (H.map a.op).hom g h
        rw [e]
        exact pushVal_mul r R _ _ _
      smul_add := fun {U} g x y => by
        refine sep_affine hF (unop U) fun A a _ => ?_
        rw [map_add, pushGlue_spec, pushGlue_spec, pushGlue_spec, map_add]
        unfold pushVal
        rw [map_add, map_add]
      smul_smul := fun {U} g c x => by
        refine sep_affine hF (unop U) fun A a _ => ?_
        rw [F.map_smul, pushGlue_spec, pushGlue_spec, F.map_smul, pushVal_smul]
      map_smul := fun {U V} f g x => by
        refine sep_affine hF (unop V) fun A a _ => ?_
        have e := pushGlue_spec r hF R.ρ (X := H ⋙ forget MonCat) (a ≫ f.unop) g x
        rw [pushGlue_spec]
        rw [op_comp, Quiver.Hom.op_unop, F.map_comp] at e
        refine e.trans ?_
        rw [(H ⋙ forget MonCat).map_comp, F.map_comp]
        rfl }
  left_inv A := by
    refine HModule.ext'' fun U g x => ?_
    refine sep_affine hF (unop U) fun B a _ => ?_
    change F.map a.op (pushGlue r hF _ (X := H ⋙ forget MonCat) g x) = _
    rw [pushGlue_spec]
    change F.map _ (A.smul (Hu r B) (F.map (r.pr B).op (F.map a.op x))) = _
    rw [A.map_smul, res_lg, ← F.map_comp, ← op_comp, r.lift_pr, op_id, F.map_id]
    exact (A.map_smul a.op g x).symm
  right_inv R := by
    refine CoactionAff.ext' r ?_
    ext T _ v
    change pushGlue r hF R.ρ (X := H ⋙ forget MonCat) _ _ = _
    rw [pushGlue_affine]
    unfold pushVal
    rw [R.ρ.naturality, ← F.map_comp, ← op_comp, r.lift_Pmap, Category.id_comp, r.lift_pr_univ,
      op_id, F.map_id]

end Comodule

/-! ### Proposition 9.12: the literal direct sum over a quasi-compact space -/

section DirectSum

variable {F : PMod (OB Bsp)}

/-- **fppf separation**: for `e : E' → E` of affine schemes with `Γ(E) → Γ(E')` faithfully flat,
`F(E) → F(E')` is injective. -/
lemma map_injective_of_faithfullyFlat (hF : IsQCoh F) {E E' : SB Bsp} [IsAffine E.left]
    [IsAffine E'.left] (e : E' ⟶ E) (hff : ((OB Bsp).map e.op).hom.FaithfullyFlat) :
    Function.Injective (F.map e.op) := by
  letI := ((OB Bsp).map e.op).hom.toAlgebra
  letI : Module ((OB Bsp).obj (op E)) (F.obj (op E')) :=
    Module.compHom _ ((OB Bsp).map e.op).hom
  haveI : IsScalarTower ((OB Bsp).obj (op E)) ((OB Bsp).obj (op E')) (F.obj (op E')) :=
    ⟨fun r s x => by
      change (((OB Bsp).map e.op).hom r * s) • x = ((OB Bsp).map e.op).hom r • s • x
      rw [mul_smul]⟩
  have hb : IsBaseChange ((OB Bsp).obj (op E'))
      ({ toFun := F.map e.op, map_add' := (F.map e.op).map_add, map_smul' := F.map_smul e.op } :
        F.obj (op E) →ₗ[(OB Bsp).obj (op E)] F.obj (op E')) := hF.base_change e
  haveI : Module.FaithfullyFlat ((OB Bsp).obj (op E)) ((OB Bsp).obj (op E')) := hff
  have h1 := Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := (OB Bsp).obj (op E)) (B := (OB Bsp).obj (op E')) (F.obj (op E))
  intro x y hxy
  apply h1
  apply hb.equiv.injective
  change hb.equiv ((1 : (OB Bsp).obj (op E')) ⊗ₜ x) = hb.equiv ((1 : (OB Bsp).obj (op E')) ⊗ₜ y)
  rw [IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
  exact congrArg _ hxy

/-- A quasi-compact object `V` over `B`: a quasi-compact scheme point `w` of `V` such that every
affine point of `V` lifts to it, fppf locally (for `V` an algebraic space: a quasi-compact étale
atlas). -/
structure QCCover (V : (SB Bsp)ᵒᵖ ⥤ Type u) where
  /-- the atlas -/
  W : SB Bsp
  compact : CompactSpace W.left
  /-- the point of `V` -/
  w : V.obj (op W)
  cover : ∀ (E : SB Bsp) [IsAffine E.left] (t : V.obj (op E)),
    ∃ (E' : SB Bsp) (_ : IsAffine E'.left) (e : E' ⟶ E) (g : E' ⟶ W),
      ((OB Bsp).map e.op).hom.FaithfullyFlat ∧ V.map g.op w = V.map e.op t

variable (F) in
/-- `F(V)`, for `V` over `B`: compatible families of sections over the points of `V`. -/
@[ext]
structure SecF (V : (SB Bsp)ᵒᵖ ⥤ Type u) where
  /-- the value at a point -/
  val : ∀ {T : SB Bsp}, V.obj (op T) → F.obj (op T)
  naturality : ∀ {T T' : SB Bsp} (s : T' ⟶ T) (t : V.obj (op T)),
    val (V.map s.op t) = F.map s.op (val t)

instance (V : (SB Bsp)ᵒᵖ ⥤ Type u) : Zero (SecF F V) :=
  ⟨⟨fun _ => 0, fun _ _ => (map_zero _).symm⟩⟩

variable {M : Type u} [AddCommMonoid M] [Countable M] {V : (SB Bsp)ᵒᵖ ⥤ Type u} {n : ℕ}

/-- The `m`-coefficient of a section over `V`, an element of `F_m(V)`. -/
def coefV (hF : IsQCoh F) (σ : SecV F M V n) (m : Fin n → M) : SecF F V where
  val t := coef hF (σ.at t) m
  naturality {T T'} s t := by
    refine sep_affine hF T' fun A a _ => ?_
    rw [S9B.coef_spec, ← F.map_comp, ← op_comp, S9B.coef_spec]
    change σ.val A (V.map a.op (V.map s.op t)) m = σ.val A (V.map (a ≫ s).op t) m
    rw [op_comp, V.map_comp]
    rfl

lemma coefV_finite (hF : IsQCoh F) (C : QCCover V) (σ : SecV F M V n) :
    (Function.support (coefV hF σ)).Finite := by
  haveI := C.compact
  refine (coef_finite hF (σ.at C.w)).subset fun m hm => ?_
  by_contra hc
  apply hm
  have h0 : coef hF (σ.at C.w) m = 0 := by simpa using hc
  refine SecF.ext ?_
  funext T t
  refine sep_affine hF T fun E a _ => ?_
  obtain ⟨E', _, e, g, hff, hg⟩ := C.cover E (V.map a.op t)
  refine map_injective_of_faithfullyFlat hF e hff ?_
  change F.map e.op (F.map a.op (coef hF (σ.at t) m)) = F.map e.op (F.map a.op 0)
  rw [map_zero, map_zero, ← F.map_comp, ← op_comp, S9B.coef_spec]
  have h1 : σ.val E' (V.map (e ≫ a).op t) = σ.val E' (V.map g.op C.w) := by
    rw [hg, op_comp, V.map_comp]
    rfl
  change σ.val E' (V.map (e ≫ a).op t) m = 0
  rw [h1]
  change (σ.at C.w).val E' g m = 0
  rw [← S9B.coef_spec hF, h0, map_zero]

/-- **Proposition 9.12**, sections of `⨁ F_m` over a quasi-compact `V` are the literal direct sum. -/
def secVEquivFinsupp (hF : IsQCoh F) (C : QCCover V) :
    SecV F M V n ≃ ((Fin n → M) →₀ SecF F V) where
  toFun σ := Finsupp.ofSupportFinite (coefV hF σ) (coefV_finite hF C σ)
  invFun x :=
    { val := fun E _ t => x.mapRange (fun s => s.val t) rfl
      compat := fun E E' _ _ s t => by
        ext m
        exact (x m).naturality s t }
  left_inv σ := by
    refine SecV.ext ?_
    funext E _ t
    ext m
    change coef hF (σ.at t) m = _
    have h := S9B.coef_spec hF (σ.at t) m (𝟙 E)
    rw [op_id, F.map_id] at h
    refine h.trans ?_
    change σ.val E (V.map (𝟙 E).op t) m = _
    rw [op_id, V.map_id]
    rfl
  right_inv x := by
    ext m T t
    change coef hF (SecV.at _ t) m = (x m).val t
    refine sep_affine hF T fun A a _ => ?_
    rw [S9B.coef_spec]
    exact ((x m).naturality a t)

/-- **Proposition 9.12, literal form over a quasi-compact `V`**:
`Cⁿ(𝔸(M)_V, F_V) = ⨁_{m ∈ Mⁿ} F_m(V)`. -/
def cochainVEquivFinsupp (hF : IsQCoh F) (C : QCCover V) :
    CochainV F M V n ≃ ((Fin n → M) →₀ SecF F V) :=
  (cochainVEquivSec hF).trans (secVEquivFinsupp hF C)

end DirectSum

/-! ### The bridge to Stacks quasi-coherent modules -/

section Bridge

open AlgMag.Leftover

/-- Transport of `IsBC` along semilinear bijections. -/
lemma isBC_transport {R R' E E' D D' : Type u} [CommRing R] [CommRing R']
    [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E']
    [AddCommGroup D] [Module R D] [AddCommGroup D'] [Module R' D']
    (φ : R →+* R') (f : E →+ E') (hf : ∀ (r : R) (x : E), f (r • x) = φ r • f x)
    (g : D →+ D') (hg : ∀ (r : R) (x : D), g (r • x) = φ r • g x)
    (e : E ≃+ D) (he : ∀ (r : R) (x : E), e (r • x) = r • e x)
    (e' : E' ≃+ D') (he' : ∀ (r : R') (x : E'), e' (r • x) = r • e' x)
    (hc : ∀ x, e' (f x) = g (e x)) (h : IsBC φ g hg) : IsBC φ f hf := by
  letI := φ.toAlgebra
  letI : Module R D' := Module.compHom D' φ
  haveI : IsScalarTower R R' D' := ⟨fun r s x => by
    change (φ r * s) • x = φ r • s • x
    rw [mul_smul]⟩
  have h' : IsBaseChange R' ({ toFun := g, map_add' := g.map_add, map_smul' := hg } : D →ₗ[R] D') := h
  let eL : E ≃ₗ[R] D := { e with map_smul' := he }
  let T : R' ⊗[R] E ≃ₗ[R'] R' ⊗[R] D :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') eL
  let Ψ : R' ⊗[R] E →+ E' :=
    (e'.symm : D' →+ E').comp
      ((h'.equiv.toLinearMap.toAddMonoidHom).comp T.toLinearMap.toAddMonoidHom)
  refine AlgMag.Leftover.isBC_of φ f hf Ψ ?_ ?_
  · exact e'.symm.bijective.comp (h'.equiv.bijective.comp T.bijective)
  · intro c m
    apply e'.injective
    change e' (e'.symm (h'.equiv (T (c ⊗ₜ m)))) = _
    rw [e'.apply_symm_apply, he', hc]
    change h'.equiv (c ⊗ₜ eL m) = _
    rw [IsBaseChange.equiv_tmul]
    rfl

/-- The local datum of Tag 03DX (1) (`BigFppfOver.HasLocalAssociatedModule` of Stacks), for a module
on the big site of `B`: over each `T`, `F` is the associated module of a quasi-coherent `𝒪_T`-module. -/
structure LocalAssoc (F : PMod (OB Bsp)) (T : SB Bsp) where
  /-- the module on `T` -/
  G : T.left.Modules
  qc : G.IsQuasicoherent
  /-- the identification of values over `u : U → T` -/
  ι : ∀ {U : SB Bsp} (u : U ⟶ T), F.obj (op U) ≃+ (assocPMod G).obj (op (Over.mk (SB.Hom.left u)))
  smul : ∀ {U : SB Bsp} (u : U ⟶ T) (a : (OB Bsp).obj (op U)) (x : F.obj (op U)),
    ι u (a • x) = (show (GB.overO T.left).obj (op (Over.mk (SB.Hom.left u))) from a) • ι u x
  nat : ∀ {U U' : SB Bsp} (s : U' ⟶ U) (u : U ⟶ T) (x : F.obj (op U)),
    ι (s ≫ u) (F.map s.op x) =
      (assocPMod G).map (Over.homMk (V := Over.mk (SB.Hom.left u))
        (U := Over.mk (SB.Hom.left (s ≫ u))) (SB.Hom.left s) (SB.comp_left s u).symm).op (ι u x)

/-- **Bridge.** An `𝒪_B`-module (a sheaf on the big site of `B`) which is, over every `T`, associated
with a Stacks quasi-coherent module on `T` is an `AlgMag.S9B.IsQCoh` module. Base change is Tag 03DX
through `AlgMag.Leftover.isQCoh_assocPMod`. -/
theorem isQCoh_of_local (F : PMod (OB Bsp))
    (hsheaf : ∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (R : Sieve T),
      coverSieve T 𝒰 ≤ R → Presieve.IsSheafFor F.toPresheaf R.arrows)
    (L : ∀ T : SB Bsp, LocalAssoc F T) : IsQCoh F where
  sheaf := hsheaf
  base_change {T T'} s _ _ := by
    let D := L T
    haveI := D.qc
    let c : Over.mk (SB.Hom.left (s ≫ 𝟙 T)) ⟶ Over.mk (SB.Hom.left (𝟙 T)) :=
      Over.homMk (SB.Hom.left s) (SB.comp_left s (𝟙 T)).symm
    haveI : IsAffine (Over.mk (SB.Hom.left (𝟙 T))).left := ‹IsAffine T.left›
    haveI : IsAffine (Over.mk (SB.Hom.left (s ≫ 𝟙 T))).left := ‹IsAffine T'.left›
    have hb := (isQCoh_assocPMod D.G).base_change c
    exact @isBC_transport.{u} ((OB Bsp).obj (op T)) ((OB Bsp).obj (op T')) (F.obj (op T)) (F.obj (op T'))
      ((assocPMod D.G).obj (op (Over.mk (SB.Hom.left (𝟙 T)))))
      ((assocPMod D.G).obj (op (Over.mk (SB.Hom.left (s ≫ 𝟙 T))))) _ _ _ (F.mod _) _ (F.mod _)
      ((assocPMod D.G).grp _) ((assocPMod D.G).mod (op (Over.mk (SB.Hom.left (𝟙 T)))))
      ((assocPMod D.G).grp _) ((assocPMod D.G).mod (op (Over.mk (SB.Hom.left (s ≫ 𝟙 T)))))
      _ _ _ _ _ (D.ι (𝟙 T)) (D.smul (𝟙 T)) (D.ι (s ≫ 𝟙 T)) (D.smul (s ≫ 𝟙 T))
      (fun x => D.nat s (𝟙 T) x) hb

/-- **Bridge**, for a module pulled back from a scheme `Y` under `B`: Tag 03DX with
`AlgMag.Leftover.isQCoh_restr`. Covers `B` a scheme (`Y = B`) and pull-backs from `S`. -/
theorem isQCoh_of_scheme {Y : Scheme.{u}} (P : ToScheme Bsp Y) (G : Y.Modules) [G.IsQuasicoherent] :
    IsQCoh (restr P (assocPMod G)) :=
  isQCoh_restr P (isQCoh_assocPMod G)

end Bridge

end AlgMag.S9BF

#print axioms AlgMag.S9BF.prop91
#print axioms AlgMag.S9BF.homAtEquivHomPush
#print axioms AlgMag.S9BF.homAtEquivHomPush_pull
#print axioms AlgMag.S9BF.hModuleEquivCoaction
#print axioms AlgMag.S9BF.cochainVEquivFinsupp
#print axioms AlgMag.S9BF.isQCoh_of_local
#print axioms AlgMag.S9BF.isQCoh_of_scheme
#print axioms AlgMag.Leftover.isQCoh_assocPMod
