/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Foundations
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# The functorial statements of §3 of *Algebraic Magnetism*

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §3. By Remark 3.3, Definition 3.1
makes sense for a functor with an action of `𝔸(M)`; every statement of this file is proved at that
generality (no representability, no topology).

## Main results

* `AlgMag.attractorBotEquiv`: `X^0` is the functor of fixed points (Remark 3.5).
* `AlgMag.fibreProductAction`, `AlgMag.isPullback_fibreProduct`,
  `AlgMag.existsUnique_fibreLift`: the cartesian square of Proposition 3.7 (i).
* `AlgMag.attractorFibreProductIso`: `(X₁ ×_{X₂} X₃)^N = X₁^N ×_{X₂^N} X₃^N`
  (Proposition 3.7 (ii)).
* `AlgMag.attractorProdIso`: `(Y ×_S Z)^N = Y^N ×_S Z^N` (Proposition 3.8).
* `AlgMag.attractorOverIso`: `X^N ×_S T = (X_T)^N` (Proposition 3.9).
* `AlgMag.magnetMap`: `X^N → X^L` for `N ⊆ L` (Fact 3.10).
* `AlgMag.attractorAction`, `AlgMag.magnetAction`, `AlgMag.attractorAction_smul_eq`:
  Remarks 3.11, 3.12, and the first assertion of Remark 3.13.
* `AlgMag.attractorMonoid`, `AlgMag.attractorGroup`: Proposition 3.14.
* `AlgMag.faceMap`, `AlgMag.magnetMap_comp_faceMap`: Fact 3.15.
* `AlgMag.attractorMap`: `f^N` (Fact 3.17); `AlgMag.mono_attractorMap`: Fact 3.18.
-/

open CategoryTheory Opposite Limits

universe w v u

namespace AlgMag

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : Type*} [AddCommMonoid M]

/-! ### Equivariant morphisms -/

/-- An `𝔸(M)`-equivariant morphism of functors with an action. -/
@[ext]
structure EquivariantHom {X Y : Cᵒᵖ ⥤ Type w} (aX : AAction 𝒪 M X) (aY : AAction 𝒪 M Y) where
  /-- The underlying morphism of functors. -/
  hom : X ⟶ Y
  map_smul : ∀ {U : Cᵒᵖ} (h : APt 𝒪 M U) (x : X.obj U),
    hom.app U (aX.smul h x) = aY.smul h (hom.app U x)

/-- The identity is equivariant. -/
def EquivariantHom.id {X : Cᵒᵖ ⥤ Type w} (aX : AAction 𝒪 M X) : EquivariantHom aX aX where
  hom := 𝟙 X
  map_smul _ _ := rfl

/-- A composite of equivariant morphisms is equivariant. -/
def EquivariantHom.comp {X Y Z : Cᵒᵖ ⥤ Type w} {aX : AAction 𝒪 M X} {aY : AAction 𝒪 M Y}
    {aZ : AAction 𝒪 M Z} (f : EquivariantHom aX aY) (g : EquivariantHom aY aZ) :
    EquivariantHom aX aZ where
  hom := f.hom ≫ g.hom
  map_smul h x := by
    change g.hom.app _ (f.hom.app _ _) = _
    rw [f.map_smul, g.map_smul]
    rfl

lemma hom_naturality_apply {X Y : Cᵒᵖ ⥤ Type w} (f : X ⟶ Y) {U V : Cᵒᵖ} (s : U ⟶ V)
    (x : X.obj U) : f.app V (X.map s x) = Y.map s (f.app U x) :=
  ConcreteCategory.congr_hom (f.naturality s) x

lemma hom_app_congr {X Y : Cᵒᵖ ⥤ Type w} {k l : X ⟶ Y} (h : k = l) (U : Cᵒᵖ) (x : X.obj U) :
    k.app U x = l.app U x := by
  rw [h]

/-! ### Fibre products of functors -/

/-- The fibre product `X₁ ×_{X₂} X₃` of functors, computed on points as in the proof of
Proposition 3.7. -/
def fibreProduct {X₁ X₂ X₃ : Cᵒᵖ ⥤ Type w} (f : X₁ ⟶ X₂) (g : X₃ ⟶ X₂) : Cᵒᵖ ⥤ Type w where
  obj U := {p : X₁.obj U × X₃.obj U // f.app U p.1 = g.app U p.2}
  map s := ↾ fun p => ⟨(X₁.map s p.1.1, X₃.map s p.1.2), by
    change f.app _ (X₁.map s p.1.1) = g.app _ (X₃.map s p.1.2)
    rw [hom_naturality_apply, hom_naturality_apply, p.2]⟩
  map_id U := by
    ext p
    · change X₁.map (𝟙 U) p.1.1 = p.1.1
      simp
    · change X₃.map (𝟙 U) p.1.2 = p.1.2
      simp
  map_comp s t := by
    ext p
    · change X₁.map (s ≫ t) p.1.1 = X₁.map t (X₁.map s p.1.1)
      simp
    · change X₃.map (s ≫ t) p.1.2 = X₃.map t (X₃.map s p.1.2)
      simp

section FibreProduct

variable {X₁ X₂ X₃ : Cᵒᵖ ⥤ Type w} (f : X₁ ⟶ X₂) (g : X₃ ⟶ X₂)

/-- The first projection of the fibre product. -/
def fibreFst : fibreProduct f g ⟶ X₁ where
  app _ := ↾ fun p => p.1.1
  naturality _ _ _ := rfl

/-- The second projection of the fibre product. -/
def fibreSnd : fibreProduct f g ⟶ X₃ where
  app _ := ↾ fun p => p.1.2
  naturality _ _ _ := rfl

/-- `fibreProduct f g` is the categorical fibre product in the category of functors. -/
theorem isPullback_fibreProduct :
    IsPullback (fibreFst f g) (fibreSnd f g) f g := by
  have w : fibreFst f g ≫ f = fibreSnd f g ≫ g := by
    ext U p
    exact p.2
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w
    (fun s => { app := fun U => ↾ fun y => ⟨(s.fst.app U y, s.snd.app U y),
                  hom_app_congr s.condition U y⟩
                naturality := ?_ }) ?_ ?_ ?_⟩⟩
  · intro U V t
    ext y
    exact Subtype.ext (Prod.ext (hom_naturality_apply s.fst t y) (hom_naturality_apply s.snd t y))
  · intro s
    rfl
  · intro s
    rfl
  · intro s m h₁ h₂
    ext U y
    exact Subtype.ext (Prod.ext (hom_app_congr h₁ U y) (hom_app_congr h₂ U y))

end FibreProduct

section FibreAction

variable {X₁ X₂ X₃ : Cᵒᵖ ⥤ Type w} {a₁ : AAction 𝒪 M X₁} {a₂ : AAction 𝒪 M X₂}
  {a₃ : AAction 𝒪 M X₃} (f : EquivariantHom a₁ a₂) (g : EquivariantHom a₃ a₂)

/-- **Proposition 3.7 (i).** The action of `𝔸(M)` on `X₁ ×_{X₂} X₃`, given by
`g • (x₁, x₃) = (g • x₁, g • x₃)`. -/
def fibreProductAction : AAction 𝒪 M (fibreProduct f.hom g.hom) where
  smul h p := ⟨(a₁.smul h p.1.1, a₃.smul h p.1.2), by
    rw [f.map_smul, g.map_smul, p.2]⟩
  one_smul p := Subtype.ext (Prod.ext (a₁.one_smul _) (a₃.one_smul _))
  mul_smul k h p := Subtype.ext (Prod.ext (a₁.mul_smul _ _ _) (a₃.mul_smul _ _ _))
  map_smul s h p := Subtype.ext (Prod.ext (a₁.map_smul _ _ _) (a₃.map_smul _ _ _))

/-- **Proposition 3.7 (i).** The first projection is equivariant. -/
def fibreFstHom : EquivariantHom (fibreProductAction f g) a₁ where
  hom := fibreFst f.hom g.hom
  map_smul _ _ := rfl

/-- **Proposition 3.7 (i).** The second projection is equivariant. -/
def fibreSndHom : EquivariantHom (fibreProductAction f g) a₃ where
  hom := fibreSnd f.hom g.hom
  map_smul _ _ := rfl

/-- **Proposition 3.7 (i).** The square is cartesian among functors with an action: a compatible
pair of equivariant morphisms lifts uniquely to an equivariant morphism to the fibre product. -/
theorem existsUnique_fibreLift {Y : Cᵒᵖ ⥤ Type w} {aY : AAction 𝒪 M Y}
    (p : EquivariantHom aY a₁) (q : EquivariantHom aY a₃) (h : p.hom ≫ f.hom = q.hom ≫ g.hom) :
    ∃! l : EquivariantHom aY (fibreProductAction f g),
      l.hom ≫ fibreFst f.hom g.hom = p.hom ∧ l.hom ≫ fibreSnd f.hom g.hom = q.hom := by
  have hpb := isPullback_fibreProduct f.hom g.hom
  refine ⟨⟨hpb.lift p.hom q.hom h, ?_⟩, ⟨hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩, ?_⟩
  · intro U k y
    have e₁ := hom_app_congr (hpb.lift_fst p.hom q.hom h) U
    have e₃ := hom_app_congr (hpb.lift_snd p.hom q.hom h) U
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine (e₁ _).trans ?_
      refine (p.map_smul k y).trans ?_
      exact congrArg (a₁.smul k) (e₁ y).symm
    · refine (e₃ _).trans ?_
      refine (q.map_smul k y).trans ?_
      exact congrArg (a₃.smul k) (e₃ y).symm
  · rintro l ⟨h₁, h₂⟩
    refine EquivariantHom.ext ?_
    exact hpb.hom_ext (by rw [h₁]; exact (hpb.lift_fst _ _ _).symm)
      (by rw [h₂]; exact (hpb.lift_snd _ _ _).symm)

end FibreAction

/-! ### Functoriality in the space (Facts 3.17, 3.18) -/

section AttractorMap

variable {X Y Z : Cᵒᵖ ⥤ Type u} {aX : AAction 𝒪 M X} {aY : AAction 𝒪 M Y} {aZ : AAction 𝒪 M Z}

/-- Composition of a point of `X^N` with an equivariant morphism. -/
def AttractorPt.push (f : EquivariantHom aX aY) {N : AddSubmonoid M} {T : C}
    (φ : AttractorPt aX N T) : AttractorPt aY N T where
  app t a := f.hom.app _ (φ.app t a)
  naturality s t a := by
    rw [φ.naturality, hom_naturality_apply]
  equivariant t h a := by
    rw [φ.equivariant, f.map_smul]

/-- **Fact 3.17.** An equivariant morphism `f : X → Y` induces `f^N : X^N → Y^N`. -/
def attractorMap (f : EquivariantHom aX aY) (N : AddSubmonoid M) :
    attractor aX N ⟶ attractor aY N where
  app _ := ↾ AttractorPt.push f
  naturality _ _ _ := rfl

@[simp] lemma attractorMap_app_app (f : EquivariantHom aX aY) (N : AddSubmonoid M) {T : Cᵒᵖ}
    (φ : AttractorPt aX N (unop T)) {T' : C} (t : T' ⟶ unop T) (a : APt 𝒪 N (op T')) :
    AttractorPt.app ((attractorMap f N).app T φ) t a = f.hom.app _ (φ.app t a) := rfl

/-- `(id)^N = id` (Fact 3.17). -/
theorem attractorMap_id (N : AddSubmonoid M) :
    attractorMap (EquivariantHom.id aX) N = 𝟙 (attractor aX N) := rfl

/-- `(f ≫ g)^N = f^N ≫ g^N` (Fact 3.17). -/
theorem attractorMap_comp (f : EquivariantHom aX aY) (g : EquivariantHom aY aZ)
    (N : AddSubmonoid M) :
    attractorMap (f.comp g) N = attractorMap f N ≫ attractorMap g N := rfl

/-- **Fact 3.18**, pointwise: if `X(U) → Y(U)` is injective for all `U`, so is
`X^N(T) → Y^N(T)` for all `T`. -/
theorem attractorMap_injective (f : EquivariantHom aX aY) (N : AddSubmonoid M)
    (hf : ∀ U, Function.Injective (f.hom.app U)) (T : Cᵒᵖ) :
    Function.Injective ((attractorMap f N).app T) := by
  intro φ ψ h
  refine AttractorPt.ext ?_
  funext T' t a
  apply hf
  have h' : AttractorPt.push f φ = AttractorPt.push f ψ := h
  exact congrArg (fun χ : AttractorPt aY N (unop T) => χ.app t a) h'

/-- **Fact 3.18.** If `X → Y` is an equivariant monomorphism, then `X^N → Y^N` is a monomorphism
(monomorphisms of functors to sets, which are the pointwise injective morphisms). -/
theorem mono_attractorMap (f : EquivariantHom aX aY) (N : AddSubmonoid M) [Mono f.hom] :
    Mono (attractorMap f N) := by
  have hinj : ∀ U, Function.Injective (f.hom.app U) := fun U =>
    (mono_iff_injective (f.hom.app U)).1 inferInstance
  refine (NatTrans.mono_iff_mono_app _).2 fun T => ?_
  exact (mono_iff_injective _).2 (attractorMap_injective f N hinj T)

end AttractorMap

/-! ### Proposition 3.7 (ii), Proposition 3.8 -/

section FibreAttractor

variable {X₁ X₂ X₃ : Cᵒᵖ ⥤ Type u} {a₁ : AAction 𝒪 M X₁} {a₂ : AAction 𝒪 M X₂}
  {a₃ : AAction 𝒪 M X₃} (f : EquivariantHom a₁ a₂) (g : EquivariantHom a₃ a₂)
  (N : AddSubmonoid M)

/-- The bijection underlying Proposition 3.7 (ii). -/
def attractorFibreProductEquiv (T : Cᵒᵖ) :
    (attractor (fibreProductAction f g) N).obj T ≃
      (fibreProduct (attractorMap f N) (attractorMap g N)).obj T where
  toFun φ := ⟨(AttractorPt.push (fibreFstHom f g) φ, AttractorPt.push (fibreSndHom f g) φ), by
    refine AttractorPt.ext ?_
    funext T' t a
    exact (AttractorPt.app (φ : AttractorPt _ N (unop T)) t a).2⟩
  invFun p :=
    { app := fun t a => ⟨(AttractorPt.app p.1.1 t a, AttractorPt.app p.1.2 t a),
        congrArg (fun χ : AttractorPt a₂ N (unop T) => χ.app t a) p.2⟩
      naturality := fun s t a => Subtype.ext (Prod.ext (AttractorPt.naturality p.1.1 s t a)
        (AttractorPt.naturality p.1.2 s t a))
      equivariant := fun t h a => Subtype.ext (Prod.ext (AttractorPt.equivariant p.1.1 t h a)
        (AttractorPt.equivariant p.1.2 t h a)) }
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Proposition 3.7 (ii).** `(X₁ ×_{X₂} X₃)^N = X₁^N ×_{X₂^N} X₃^N` as functors; the fibre product
on the right is the categorical one by `isPullback_fibreProduct`. -/
def attractorFibreProductIso :
    attractor (fibreProductAction f g) N ≅
      fibreProduct (attractorMap f N) (attractorMap g N) :=
  NatIso.ofComponents (fun T => (attractorFibreProductEquiv f g N T).toIso) (fun _ => rfl)

/-- The isomorphism of Proposition 3.7 (ii) is compatible with the first projections. -/
theorem attractorFibreProductIso_fst :
    (attractorFibreProductIso f g N).hom ≫ fibreFst _ _ = attractorMap (fibreFstHom f g) N := rfl

/-- The isomorphism of Proposition 3.7 (ii) is compatible with the second projections. -/
theorem attractorFibreProductIso_snd :
    (attractorFibreProductIso f g N).hom ≫ fibreSnd _ _ = attractorMap (fibreSndHom f g) N := rfl

end FibreAttractor

section Prod

variable {Y Z : Cᵒᵖ ⥤ Type u} (aY : AAction 𝒪 M Y) (aZ : AAction 𝒪 M Z) (N : AddSubmonoid M)

/-- The product of two functors, computed on points (`Y ×_S Z` on `Sch/S`). -/
def prodFunctor {C : Type*} [Category C] (Y Z : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj U := Y.obj U × Z.obj U
  map s := ↾ fun p => (Y.map s p.1, Z.map s p.2)
  map_id U := by
    ext p
    · change Y.map (𝟙 U) p.1 = p.1
      simp
    · change Z.map (𝟙 U) p.2 = p.2
      simp
  map_comp s t := by
    ext p
    · change Y.map (s ≫ t) p.1 = Y.map t (Y.map s p.1)
      simp
    · change Z.map (s ≫ t) p.2 = Z.map t (Z.map s p.2)
      simp

/-- The componentwise action on `Y ×_S Z` (Proposition 3.8). -/
def prodAction : AAction 𝒪 M (prodFunctor Y Z) where
  smul h p := (aY.smul h p.1, aZ.smul h p.2)
  one_smul _ := Prod.ext (aY.one_smul _) (aZ.one_smul _)
  mul_smul _ _ _ := Prod.ext (aY.mul_smul _ _ _) (aZ.mul_smul _ _ _)
  map_smul _ _ _ := Prod.ext (aY.map_smul _ _ _) (aZ.map_smul _ _ _)

/-- The bijection underlying Proposition 3.8. -/
def attractorProdEquiv (T : Cᵒᵖ) :
    (attractor (prodAction aY aZ) N).obj T ≃
      (prodFunctor (attractor aY N) (attractor aZ N)).obj T where
  toFun φ :=
    ({ app := fun t a => (AttractorPt.app (φ : AttractorPt _ N (unop T)) t a).1
       naturality := fun s t a =>
        congrArg Prod.fst (AttractorPt.naturality (φ : AttractorPt _ N (unop T)) s t a)
       equivariant := fun t h a =>
        congrArg Prod.fst (AttractorPt.equivariant (φ : AttractorPt _ N (unop T)) t h a) },
     { app := fun t a => (AttractorPt.app (φ : AttractorPt _ N (unop T)) t a).2
       naturality := fun s t a =>
        congrArg Prod.snd (AttractorPt.naturality (φ : AttractorPt _ N (unop T)) s t a)
       equivariant := fun t h a =>
        congrArg Prod.snd (AttractorPt.equivariant (φ : AttractorPt _ N (unop T)) t h a) })
  invFun p :=
    { app := fun t a => (AttractorPt.app p.1 t a, AttractorPt.app p.2 t a)
      naturality := fun s t a => Prod.ext (AttractorPt.naturality p.1 s t a)
        (AttractorPt.naturality p.2 s t a)
      equivariant := fun t h a => Prod.ext (AttractorPt.equivariant p.1 t h a)
        (AttractorPt.equivariant p.2 t h a) }
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Proposition 3.8.** `(Y ×_S Z)^N = Y^N ×_S Z^N`. -/
def attractorProdIso :
    attractor (prodAction aY aZ) N ≅ prodFunctor (attractor aY N) (attractor aZ N) :=
  NatIso.ofComponents (fun T => (attractorProdEquiv aY aZ N T).toIso) (fun _ => rfl)

end Prod

/-! ### Base change (Proposition 3.9) -/

section BaseChange

variable {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F) (N : AddSubmonoid M)

/-- **Proposition 3.9.** The `T`-functor `X_T` (the restriction of `X` to `C/T`) is canonically
endowed with an action of `𝔸(M)_T`. -/
def AAction.over (T : C) :
    AAction ((Over.forget T).op ⋙ 𝒪) M ((Over.forget T).op ⋙ F) where
  smul {U} h x := act.smul (U := op (unop U).left) h x
  one_smul {U} x := act.one_smul (U := op (unop U).left) x
  mul_smul {U} g h x := act.mul_smul (U := op (unop U).left) g h x
  map_smul {U V} f h x := act.map_smul (U := op (unop U).left) (V := op (unop V).left)
    f.unop.left.op h x

/-- The value at `s : V ⟶ W` over `T` of a point of `(X_T)^N` depends only on the underlying
morphism of `C`. -/
lemma attractorPt_over_app_congr {T : C} {W : Over T}
    (φ : AttractorPt (act.over T) N W) {V : Over T} (s : V ⟶ W) (a : APt 𝒪 N (op V.left)) :
    φ.app (Over.homMk s.left : Over.mk (s.left ≫ W.hom) ⟶ W) a = φ.app s a := by
  obtain ⟨Vl, r, Vh⟩ := V
  obtain ⟨sl, sr, sw⟩ := s
  have e : sl ≫ W.hom = Vh := by simpa using sw
  dsimp at sl e ⊢
  subst e
  rfl

/-- The bijection underlying Proposition 3.9. -/
def attractorOverEquiv (T : C) (W : (Over T)ᵒᵖ) :
    (attractor (act.over T) N).obj W ≃ ((Over.forget T).op ⋙ attractor act N).obj W where
  toFun φ :=
    { app := fun {T'} t a =>
        AttractorPt.app (φ : AttractorPt (act.over T) N (unop W))
          (Over.homMk t : Over.mk (t ≫ (unop W).hom) ⟶ unop W) a
      naturality := fun {T' T''} s t a => by
        have h := AttractorPt.naturality (φ : AttractorPt (act.over T) N (unop W))
          (Over.homMk s (by simp) : Over.mk ((s ≫ t) ≫ (unop W).hom) ⟶ Over.mk (t ≫ (unop W).hom))
          (Over.homMk t : Over.mk (t ≫ (unop W).hom) ⟶ unop W) a
        exact h
      equivariant := fun {T'} t h a =>
        AttractorPt.equivariant (φ : AttractorPt (act.over T) N (unop W))
          (Over.homMk t : Over.mk (t ≫ (unop W).hom) ⟶ unop W) h a }
  invFun ψ :=
    { app := fun {V} s a => AttractorPt.app (ψ : AttractorPt act N (unop W).left) s.left a
      naturality := fun {V V'} s t a =>
        AttractorPt.naturality (ψ : AttractorPt act N (unop W).left) s.left t.left a
      equivariant := fun {V} t h a =>
        AttractorPt.equivariant (ψ : AttractorPt act N (unop W).left) t.left h a }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext V s a
    exact attractorPt_over_app_congr act N φ s a
  right_inv _ := rfl

/-- **Proposition 3.9.** `X^N ×_S T = (X_T)^N` as `T`-functors. Here the left-hand side is the
restriction of `X^N` to `C/T`, which is the fibre product `X^N ×_S T` as a `T`-functor. -/
def attractorOverIso (T : C) :
    attractor (act.over T) N ≅ (Over.forget T).op ⋙ attractor act N :=
  NatIso.ofComponents (fun W => (attractorOverEquiv act N T W).toIso) (fun {W W'} s => by
    ext φ
    refine AttractorPt.ext ?_
    funext T' t a
    exact (attractorPt_over_app_congr act N (φ : AttractorPt (act.over T) N (unop W))
      ((Over.homMk t : Over.mk (t ≫ (unop W').hom) ⟶ unop W') ≫ s.unop) a).symm)

end BaseChange

/-! ### Functoriality in the magnet (Fact 3.10) -/

section Magnet

/-- Restriction of a point of `𝔸(L)` to `𝔸(N)` for `N ⊆ L`: the morphism `𝔸(L) → 𝔸(N)` of
Fact 2.13. -/
def APt.restrict {N L : AddSubmonoid M} (h : N ≤ L) {U : Cᵒᵖ} (a : APt 𝒪 L U) : APt 𝒪 N U :=
  a.comp (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion h))

@[simp] lemma APt.restrict_one {N L : AddSubmonoid M} (h : N ≤ L) {U : Cᵒᵖ} :
    APt.restrict h (1 : APt 𝒪 L U) = 1 := rfl

lemma APt.restrict_mul {N L : AddSubmonoid M} (h : N ≤ L) {U : Cᵒᵖ} (a b : APt 𝒪 L U) :
    APt.restrict h (a * b) = APt.restrict h a * APt.restrict h b := rfl

lemma APt.restrict_res {N L : AddSubmonoid M} (h : N ≤ L) {U V : Cᵒᵖ} (s : U ⟶ V)
    (a : APt 𝒪 L U) : APt.restrict h (APt.res s a) = APt.res s (APt.restrict h a) := rfl

lemma APt.restrict_toMagnet {N L : AddSubmonoid M} (h : N ≤ L) {U : Cᵒᵖ} (k : APt 𝒪 M U) :
    APt.restrict h (APt.toMagnet L k) = APt.toMagnet N k := rfl

variable {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F)

/-- A point of `X^N` as a point of `X^L`, for `N ⊆ L`, by precomposition with `𝔸(L) → 𝔸(N)`. -/
def AttractorPt.ofLE {act : AAction 𝒪 M F} {N L : AddSubmonoid M} (h : N ≤ L) {T : C}
    (φ : AttractorPt act N T) : AttractorPt act L T where
  app t a := φ.app t (APt.restrict h a)
  naturality s t a := φ.naturality s t (APt.restrict h a)
  equivariant t k a := φ.equivariant t k (APt.restrict h a)

/-- **Fact 3.10.** For magnets `N ⊆ L`, the morphism of functors `ρ_{N,L} : X^N → X^L`. -/
def magnetMap {N L : AddSubmonoid M} (h : N ≤ L) : attractor act N ⟶ attractor act L where
  app _ := ↾ AttractorPt.ofLE h
  naturality _ _ _ := rfl

@[simp] lemma magnetMap_app_app {N L : AddSubmonoid M} (h : N ≤ L) {T : Cᵒᵖ}
    (φ : AttractorPt act N (unop T)) {T' : C} (t : T' ⟶ unop T) (a : APt 𝒪 L (op T')) :
    AttractorPt.app ((magnetMap act h).app T φ) t a = φ.app t (APt.restrict h a) := rfl

/-- `ρ_{N,N} = id` (Fact 3.10). -/
theorem magnetMap_refl (N : AddSubmonoid M) : magnetMap act (le_refl N) = 𝟙 (attractor act N) := rfl

/-- `ρ_{N,L} ≫ ρ_{L,K} = ρ_{N,K}` (Fact 3.10). -/
theorem magnetMap_trans {N L K : AddSubmonoid M} (h₁ : N ≤ L) (h₂ : L ≤ K) :
    magnetMap act h₁ ≫ magnetMap act h₂ = magnetMap act (h₁.trans h₂) := rfl

/-- The morphisms `X^N → X` of §3 are natural in `T`: restriction of `x ↦ f(1)`. -/
theorem AttractorPt.toPoint_baseChange {act : AAction 𝒪 M F} {N : AddSubmonoid M} {T T' : C}
    (s : T' ⟶ T) (φ : AttractorPt act N T) :
    (AttractorPt.baseChange s φ).toPoint = F.map s.op φ.toPoint := by
  have h := φ.naturality s (𝟙 T) 1
  have hone : APt.res (𝒪 := 𝒪) (P := N) s.op 1 = 1 := by
    ext p; simp
  rw [hone, Category.comp_id] at h
  change φ.app (𝟙 T' ≫ s) 1 = _
  rw [Category.id_comp]
  exact h

/-- The morphism `ρ_{N,L}` is compatible with the evaluations `X^N → X` and `X^L → X`. -/
theorem AttractorPt.toPoint_ofLE {act : AAction 𝒪 M F} {N L : AddSubmonoid M} (h : N ≤ L) {T : C}
    (φ : AttractorPt act N T) : (AttractorPt.ofLE h φ).toPoint = φ.toPoint := rfl

/-- `f^N` commutes with `ρ_{N,L}` (Facts 3.10, 3.17). -/
theorem attractorMap_comp_magnetMap {X Y : Cᵒᵖ ⥤ Type u} {aX : AAction 𝒪 M X}
    {aY : AAction 𝒪 M Y} (f : EquivariantHom aX aY) {N L : AddSubmonoid M} (h : N ≤ L) :
    attractorMap f N ≫ magnetMap aY h = magnetMap aX h ≫ attractorMap f L := rfl

/-- The projections of `X^{⋂ Nᵢ}` to the `X^{Nᵢ}` form a cone under `Fact 3.10`: this is the
functorial part of the intersection statements (Proposition 3.24 itself requires `X` affine and is
not stated here). -/
theorem magnetMap_iInf_comp {ι : Sort*} (N : ι → AddSubmonoid M) {i : ι} {L : AddSubmonoid M}
    (h : N i ≤ L) :
    magnetMap act (iInf_le N i) ≫ magnetMap act h = magnetMap act ((iInf_le N i).trans h) := rfl

/-! ### Actions on the attractor (Remarks 3.11–3.13) -/

variable (N : AddSubmonoid M)

/-- **Remark 3.11.** The action of `𝔸(M)` on `X^N`: `(t • f)(a) = t • f(a)`. -/
def attractorAction : AAction 𝒪 M (attractor act N) where
  smul {U} h φ :=
    { app := fun {T'} t a => act.smul (APt.res t.op h) (AttractorPt.app φ t a)
      naturality := fun {T' T''} s t a => by
        rw [AttractorPt.naturality φ s t a, act.map_smul, ← APt.res_comp]
        rfl
      equivariant := fun {T'} t k a => by
        rw [AttractorPt.equivariant φ t k a, ← act.mul_smul, ← act.mul_smul, mul_comm] }
  one_smul {U} φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    have hone : APt.res t.op (1 : APt 𝒪 M U) = 1 := by
      ext p; simp
    change act.smul (APt.res t.op 1) _ = _
    rw [hone, act.one_smul]
  mul_smul {U} g h φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change act.smul (APt.res t.op (g * h)) _ = act.smul _ (act.smul _ _)
    rw [APt.res_mul, act.mul_smul]
  map_smul {U V} s h φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change act.smul (APt.res (t ≫ s.unop).op h) _ = act.smul (APt.res t.op (APt.res s h)) _
    rw [← APt.res_comp]
    rfl

/-- **Remark 3.12.** The action of `𝔸(N)` on `X^N`: `(t • f)(a) = f(t a)`. -/
def magnetAction : AAction 𝒪 N (attractor act N) where
  smul {U} b φ :=
    { app := fun {T'} t a => AttractorPt.app φ t (APt.res t.op b * a)
      naturality := fun {T' T''} s t a => by
        rw [← AttractorPt.naturality φ s t, APt.res_mul, ← APt.res_comp]
        rfl
      equivariant := fun {T'} t k a => by
        rw [← AttractorPt.equivariant φ t k, mul_left_comm] }
  one_smul {U} φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    have hone : APt.res t.op (1 : APt 𝒪 N U) = 1 := by
      ext p; simp
    change AttractorPt.app φ t (APt.res t.op 1 * a) = _
    rw [hone, one_mul]
  mul_smul {U} g h φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change AttractorPt.app φ t (APt.res t.op (g * h) * a) =
      AttractorPt.app φ t (APt.res t.op h * (APt.res t.op g * a))
    rw [APt.res_mul, mul_comm (APt.res t.op g), mul_assoc]
  map_smul {U V} s h φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change AttractorPt.app φ (t ≫ s.unop) (APt.res (t ≫ s.unop).op h * a) =
      AttractorPt.app φ (t ≫ s.unop) (APt.res t.op (APt.res s h) * a)
    rw [← APt.res_comp]
    rfl

/-- **Remark 3.13**, first assertion: the action of Remark 3.11 is obtained from that of
Remark 3.12 via the morphism of monoid schemes `𝔸(M) → 𝔸(N)`. The "sanitary check"
`(X^N_M)^L_M = (X^N_M)^{N ∩ L}_N` holds only under working assumptions and is not stated here. -/
theorem attractorAction_smul_eq {U : Cᵒᵖ} (h : APt 𝒪 M U) (φ : (attractor act N).obj U) :
    (attractorAction act N).smul h φ = (magnetAction act N).smul (APt.toMagnet N h) φ := by
  refine AttractorPt.ext ?_
  funext T' t a
  exact (AttractorPt.equivariant φ t (APt.res t.op h) a).symm

/-! ### Monoid and group structures (Proposition 3.14) -/

/-- A monoid structure on a functor: the restriction maps are morphisms of monoids. -/
structure IsMonoidFunctor (F : Cᵒᵖ ⥤ Type u) [∀ U, Monoid (F.obj U)] : Prop where
  map_one : ∀ {U V : Cᵒᵖ} (s : U ⟶ V), F.map s 1 = 1
  map_mul : ∀ {U V : Cᵒᵖ} (s : U ⟶ V) (x y : F.obj U), F.map s (x * y) = F.map s x * F.map s y

/-- `𝔸(M)` acts on `X` by monoid endomorphisms. -/
structure ActsByMonoidEnd [∀ U, Monoid (F.obj U)] (act : AAction 𝒪 M F) : Prop where
  smul_one : ∀ {U : Cᵒᵖ} (h : APt 𝒪 M U), act.smul h 1 = 1
  smul_mul : ∀ {U : Cᵒᵖ} (h : APt 𝒪 M U) (x y : F.obj U),
    act.smul h (x * y) = act.smul h x * act.smul h y

section MonoidStructure

variable [∀ U, Monoid (F.obj U)] {act} (hF : IsMonoidFunctor F) (ha : ActsByMonoidEnd act)
include hF ha

/-- **Proposition 3.14 (i).** If `X` is a monoid functor and `𝔸(M)` acts by monoid endomorphisms,
then each `X^N(T)` is a monoid, under the pointwise law (see `attractor_map_mul` for the
functoriality). The paper composes `g × h` with the diagonal of `𝔸(N)` and the multiplication. -/
@[instance_reducible] def attractorMonoid (T : C) : Monoid (AttractorPt act N T) where
  mul φ ψ :=
    { app := fun t a => φ.app t a * ψ.app t a
      naturality := fun s t a => by
        rw [hF.map_mul, φ.naturality, ψ.naturality]
      equivariant := fun t h a => by
        rw [φ.equivariant, ψ.equivariant, ha.smul_mul] }
  one :=
    { app := fun _ _ => 1
      naturality := fun s _ _ => (hF.map_one s.op).symm
      equivariant := fun _ h _ => (ha.smul_one h).symm }
  mul_assoc φ ψ χ := by
    refine AttractorPt.ext ?_
    funext T' t a
    exact mul_assoc _ _ _
  one_mul φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    exact one_mul _
  mul_one φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    exact mul_one _

/-- **Proposition 3.14 (i)**, functoriality: base change is a morphism of monoids, so `X^N` is a
monoid functor. -/
theorem attractor_map_mul {T T' : C} (s : T' ⟶ T) (φ ψ : AttractorPt act N T) :
    letI := attractorMonoid N hF ha T
    letI := attractorMonoid N hF ha T'
    AttractorPt.baseChange s (φ * ψ) = AttractorPt.baseChange s φ * AttractorPt.baseChange s ψ :=
  rfl

/-- **Proposition 3.14 (i)**, functoriality: base change preserves the unit. -/
theorem attractor_map_one {T T' : C} (s : T' ⟶ T) :
    letI := attractorMonoid (act := act) N hF ha T
    letI := attractorMonoid (act := act) N hF ha T'
    AttractorPt.baseChange s (1 : AttractorPt act N T) = 1 :=
  rfl

end MonoidStructure

section GroupStructure

variable [∀ U, Group (F.obj U)] {act} (hF : IsMonoidFunctor F) (ha : ActsByMonoidEnd act)
include hF ha

/-- **Proposition 3.14 (ii).** If `X` is a group functor and `𝔸(M)` acts by group endomorphisms,
then each `X^N(T)` is a group, with the monoid law of `attractorMonoid` (whose base change maps are
morphisms by `attractor_map_mul`). -/
@[instance_reducible] def attractorGroup (T : C) : Group (AttractorPt act N T) :=
  { attractorMonoid N hF ha T with
    inv := fun φ =>
      { app := fun t a => (φ.app t a)⁻¹
        naturality := fun s t a => by
          rw [φ.naturality]
          exact (map_inv (MonoidHom.mk' (F.map s.op) (hF.map_mul s.op)) _).symm
        equivariant := fun t h a => by
          rw [φ.equivariant]
          exact (map_inv (MonoidHom.mk' (act.smul h) (ha.smul_mul h)) _).symm }
    inv_mul_cancel := fun φ => by
      refine AttractorPt.ext ?_
      funext T' t a
      exact inv_mul_cancel _ }

end GroupStructure

/-! ### Fixed points (Remark 3.5) -/

/-- Every point of `𝔸(0)` is the unit. -/
lemma APt.bot_eq_one {U : Cᵒᵖ} (a : APt 𝒪 (⊥ : AddSubmonoid M) U) : a = 1 := by
  refine MonoidHom.ext fun p => ?_
  have hp : p = 1 :=
    Multiplicative.toAdd.injective (Subtype.ext (AddSubmonoid.mem_bot.1 (Multiplicative.toAdd p).2))
  rw [hp, map_one, map_one]

/-- The `T`-points of the functor of fixed points `X^{𝔸(M)}`: points `x` of `X(T)` such that
`h • x_{T'} = x_{T'}` for all `T' → T` and `h ∈ 𝔸(M)(T')`. -/
def FixedPt (T : C) : Type _ :=
  {x : F.obj (op T) // ∀ {T' : C} (t : T' ⟶ T) (h : APt 𝒪 M (op T')),
    act.smul h (F.map t.op x) = F.map t.op x}

/-- **Remark 3.5.** `X^0 = X^{𝔸(M)}`: evaluation at the unit is a bijection from the points of the
attractor of the magnet `0` to the fixed points. It is natural by `AttractorPt.toPoint_baseChange`.
-/
def attractorBotEquiv (T : C) : AttractorPt act (⊥ : AddSubmonoid M) T ≃ FixedPt act T where
  toFun φ := ⟨φ.toPoint, fun {T'} t h => by
    have hn := φ.naturality t (𝟙 T) 1
    rw [Category.comp_id, APt.bot_eq_one (APt.res t.op 1)] at hn
    have he := φ.equivariant t h 1
    rw [APt.bot_eq_one (APt.toMagnet _ h * 1)] at he
    change act.smul h (F.map t.op (φ.app (𝟙 T) 1)) = F.map t.op (φ.app (𝟙 T) 1)
    rw [← hn]
    exact he.symm⟩
  invFun x :=
    { app := fun t _ => F.map t.op x.1
      naturality := fun s t _ => by
        rw [← Functor.map_comp_apply]
        rfl
      equivariant := fun t h _ => (x.2 t h).symm }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    have hn := φ.naturality t (𝟙 T) 1
    rw [Category.comp_id, APt.bot_eq_one (APt.res t.op 1)] at hn
    rw [APt.bot_eq_one a]
    exact hn.symm
  right_inv x := by
    refine Subtype.ext ?_
    change F.map (𝟙 T).op x.1 = x.1
    simp

/-! ### Faces (Fact 3.15) -/

/-- `L` is a face of `N`: a submonoid of `N` such that `x + y ∈ L` with `x, y ∈ N` forces
`x, y ∈ L`. -/
structure IsFace (L N : AddSubmonoid M) : Prop where
  le : L ≤ N
  mem_of_add_mem : ∀ {x y : M}, x ∈ N → y ∈ N → x + y ∈ L → x ∈ L ∧ y ∈ L

open Classical in
/-- Extension by zero, the morphism `𝔸(L) → 𝔸(N)` attached to a face `L` of `N` (Fact 2.15). -/
noncomputable def APt.faceExt {L N : AddSubmonoid M} (hL : IsFace L N) {U : Cᵒᵖ} (a : APt 𝒪 L U) :
    APt 𝒪 N U where
  toFun n := if h : ((Multiplicative.toAdd n : N) : M) ∈ L then
    a (Multiplicative.ofAdd (⟨_, h⟩ : L)) else 0
  map_one' := by
    have h : ((Multiplicative.toAdd (1 : Multiplicative N) : N) : M) ∈ L := L.zero_mem
    rw [dite_eq_left h]
    exact a.map_one
  map_mul' x y := by
    by_cases hx : ((Multiplicative.toAdd x : N) : M) ∈ L
    · by_cases hy : ((Multiplicative.toAdd y : N) : M) ∈ L
      · have hxy : ((Multiplicative.toAdd (x * y) : N) : M) ∈ L := L.add_mem hx hy
        rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left hxy, ← a.map_mul]
        rfl
      · have hxy : ((Multiplicative.toAdd (x * y) : N) : M) ∉ L := fun h =>
          hy (hL.mem_of_add_mem (Multiplicative.toAdd x : N).2 (Multiplicative.toAdd y : N).2 h).2
        rw [dite_eq_right hy, dite_eq_right hxy, mul_zero]
    · have hxy : ((Multiplicative.toAdd (x * y) : N) : M) ∉ L := fun h =>
        hx (hL.mem_of_add_mem (Multiplicative.toAdd x : N).2 (Multiplicative.toAdd y : N).2 h).1
      rw [dite_eq_right hx, dite_eq_right hxy, zero_mul]

lemma APt.faceExt_pos {L N : AddSubmonoid M} (hL : IsFace L N) {U : Cᵒᵖ} (a : APt 𝒪 L U)
    {n : Multiplicative N} (h : ((Multiplicative.toAdd n : N) : M) ∈ L) :
    APt.faceExt hL a n = a (Multiplicative.ofAdd (⟨_, h⟩ : L)) :=
  dite_eq_left h

lemma APt.faceExt_neg {L N : AddSubmonoid M} (hL : IsFace L N) {U : Cᵒᵖ} (a : APt 𝒪 L U)
    {n : Multiplicative N} (h : ((Multiplicative.toAdd n : N) : M) ∉ L) :
    APt.faceExt hL a n = 0 :=
  dite_eq_right h

lemma APt.restrict_faceExt {L N : AddSubmonoid M} (hL : IsFace L N) {U : Cᵒᵖ} (a : APt 𝒪 L U) :
    APt.restrict hL.le (APt.faceExt hL a) = a := by
  refine MonoidHom.ext fun p => ?_
  exact APt.faceExt_pos hL a (n := AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hL.le) p)
    (Multiplicative.toAdd p).2

lemma APt.faceExt_res {L N : AddSubmonoid M} (hL : IsFace L N) {U V : Cᵒᵖ} (s : U ⟶ V)
    (a : APt 𝒪 L U) : APt.faceExt hL (APt.res s a) = APt.res s (APt.faceExt hL a) := by
  refine MonoidHom.ext fun n => ?_
  rw [APt.res_apply]
  by_cases h : ((Multiplicative.toAdd n : N) : M) ∈ L
  · rw [APt.faceExt_pos hL _ h, APt.faceExt_pos hL _ h]
    rfl
  · rw [APt.faceExt_neg hL _ h, APt.faceExt_neg hL _ h, map_zero]

lemma APt.faceExt_mul {L N : AddSubmonoid M} (hL : IsFace L N) {U : Cᵒᵖ} (k : APt 𝒪 M U)
    (a : APt 𝒪 L U) :
    APt.faceExt hL (APt.toMagnet L k * a) = APt.toMagnet N k * APt.faceExt hL a := by
  refine MonoidHom.ext fun n => ?_
  rw [MonoidHom.mul_apply]
  by_cases h : ((Multiplicative.toAdd n : N) : M) ∈ L
  · rw [APt.faceExt_pos hL _ h, APt.faceExt_pos hL _ h]
    rfl
  · rw [APt.faceExt_neg hL _ h, APt.faceExt_neg hL _ h, mul_zero]

/-- A point of `X^N` as a point of `X^L`, for a face `L` of `N`. -/
noncomputable def AttractorPt.ofFace {act : AAction 𝒪 M F} {L N : AddSubmonoid M}
    (hL : IsFace L N) {T : C} (φ : AttractorPt act N T) : AttractorPt act L T where
  app t a := φ.app t (APt.faceExt hL a)
  naturality s t a := by
    rw [APt.faceExt_res]
    exact φ.naturality s t _
  equivariant t k a := by
    rw [APt.faceExt_mul]
    exact φ.equivariant t k _

/-- **Fact 3.15.** For a face `L` of `N`, the morphism of functors `p_{N,L} : X^N → X^L`. -/
noncomputable def faceMap {L N : AddSubmonoid M} (hL : IsFace L N) :
    attractor act N ⟶ attractor act L where
  app _ := ↾ AttractorPt.ofFace hL
  naturality _ _ _ := rfl

/-- **Fact 3.15.** `p_{N,L} ∘ ρ_{L,N} = id` on `X^L`. -/
theorem magnetMap_comp_faceMap {L N : AddSubmonoid M} (hL : IsFace L N) :
    magnetMap act hL.le ≫ faceMap act hL = 𝟙 (attractor act L) := by
  ext T φ
  refine AttractorPt.ext ?_
  funext T' t a
  change AttractorPt.app φ t (APt.restrict hL.le (APt.faceExt hL a)) = _
  rw [APt.restrict_faceExt]
  rfl

end Magnet

end AlgMag
