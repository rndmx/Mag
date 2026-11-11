/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Attractors of functors with a monoid action

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §3.

Let `C` be a category with a presheaf of rings `𝒪` (for `C = Sch/S`, the functor `T ↦ Γ(T, 𝒪_T)`).
For a commutative monoid `P`, the `T`-points of `𝔸(P)` are the monoid maps from `P` to
`(𝒪(T), ·)`. By Remark 3.3, Definition 3.1 makes sense for any functor with an action of `𝔸(M)`;
we work at that generality, which contains algebraic spaces (see `AlgMag.AlgebraicSpace`).

## Main definitions

* `AlgMag.APt`: the points of `𝔸(P)`.
* `AlgMag.AAction`: an action of `𝔸(M)` on a presheaf (§3).
* `AlgMag.AttractorPt`, `AlgMag.attractor`: the attractor functor `X^N` (Definition 3.1).

## Main results

* `AlgMag.attractorTopEquiv`: `X^M = X` (Fact 3.6).
* `AlgMag.isSheaf_attractor`: `X^N` is a sheaf if `X` is one (Proposition 3.2).
-/

open CategoryTheory Opposite

universe u v

namespace AlgMag

variable {C : Type*} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The `U`-points of `𝔸(P)`: monoid maps from `P` to `(𝒪(U), ·)`. -/
abbrev APt (P : Type*) [AddCommMonoid P] (U : Cᵒᵖ) : Type _ := Multiplicative P →* 𝒪.obj U

variable {𝒪}

/-- Restriction of points of `𝔸(P)` along a morphism of the base. -/
def APt.res {P : Type*} [AddCommMonoid P] {U V : Cᵒᵖ} (f : U ⟶ V) (a : APt 𝒪 P U) : APt 𝒪 P V :=
  ((𝒪.map f).hom : 𝒪.obj U →+* 𝒪.obj V).toMonoidHom.comp a

@[simp] lemma APt.res_apply {P : Type*} [AddCommMonoid P] {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : APt 𝒪 P U) (p : Multiplicative P) : APt.res f a p = (𝒪.map f).hom (a p) := rfl

lemma APt.res_mul {P : Type*} [AddCommMonoid P] {U V : Cᵒᵖ} (f : U ⟶ V) (a b : APt 𝒪 P U) :
    APt.res f (a * b) = APt.res f a * APt.res f b := by
  ext p; simp

@[simp] lemma APt.res_id {P : Type*} [AddCommMonoid P] {U : Cᵒᵖ} (a : APt 𝒪 P U) :
    APt.res (𝟙 U) a = a := by
  ext p; simp

lemma APt.res_comp {P : Type*} [AddCommMonoid P] {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (a : APt 𝒪 P U) : APt.res (f ≫ g) a = APt.res g (APt.res f a) := by
  ext p; simp

variable {M : Type*} [AddCommMonoid M]

/-- The monoid morphism `𝔸(M) → 𝔸(N)` induced by a magnet `N ⊆ M`; through it `𝔸(M)` acts on
`𝔸(N)` (Fact 2.12). -/
def APt.toMagnet (N : AddSubmonoid M) {U : Cᵒᵖ} (h : APt 𝒪 M U) : APt 𝒪 N U :=
  h.comp (AddMonoidHom.toMultiplicative N.subtype)

@[simp] lemma APt.toMagnet_apply (N : AddSubmonoid M) {U : Cᵒᵖ} (h : APt 𝒪 M U)
    (n : Multiplicative N) :
    APt.toMagnet N h n = h (Multiplicative.ofAdd ((Multiplicative.toAdd n : N) : M)) := rfl

lemma APt.toMagnet_res (N : AddSubmonoid M) {U V : Cᵒᵖ} (f : U ⟶ V) (h : APt 𝒪 M U) :
    APt.toMagnet N (APt.res f h) = APt.res f (APt.toMagnet N h) := rfl

variable (𝒪 M) in
/-- An action of the monoid `𝔸(M)` on a presheaf `F`. -/
structure AAction (F : Cᵒᵖ ⥤ Type*) where
  /-- The action on `U`-points. -/
  smul : ∀ {U : Cᵒᵖ}, APt 𝒪 M U → F.obj U → F.obj U
  one_smul : ∀ {U : Cᵒᵖ} (x : F.obj U), smul 1 x = x
  mul_smul : ∀ {U : Cᵒᵖ} (g h : APt 𝒪 M U) (x : F.obj U), smul (g * h) x = smul g (smul h x)
  map_smul : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (h : APt 𝒪 M U) (x : F.obj U),
    F.map f (smul h x) = smul (APt.res f h) (F.map f x)

variable {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F) (N : AddSubmonoid M)

/-- A `T`-point of the attractor `X^N` (Definition 3.1): an `𝔸(M)_T`-equivariant `T`-morphism
`𝔸(N)_T → X_T`, given by its values on points over every `T' → T`. -/
@[ext]
structure AttractorPt (T : C) where
  /-- The value at a point of `𝔸(N)` over `t : T' ⟶ T`. -/
  app : ∀ {T' : C} (_ : T' ⟶ T), APt 𝒪 N (op T') → F.obj (op T')
  naturality : ∀ {T' T'' : C} (s : T'' ⟶ T') (t : T' ⟶ T) (a : APt 𝒪 N (op T')),
    app (s ≫ t) (APt.res s.op a) = F.map s.op (app t a)
  equivariant : ∀ {T' : C} (t : T' ⟶ T) (h : APt 𝒪 M (op T')) (a : APt 𝒪 N (op T')),
    app t (APt.toMagnet N h * a) = act.smul h (app t a)

/-- Base change of attractor points along `s : T'' ⟶ T`. -/
def AttractorPt.baseChange {act : AAction 𝒪 M F} {N : AddSubmonoid M} {T T'' : C} (s : T'' ⟶ T)
    (φ : AttractorPt act N T) : AttractorPt act N T'' where
  app t a := φ.app (t ≫ s) a
  naturality r t a := by
    rw [Category.assoc]; exact φ.naturality r (t ≫ s) a
  equivariant t h a := φ.equivariant (t ≫ s) h a

/-- The attractor functor `X^N` (Definition 3.1); on morphisms it is base change. -/
def attractor : Cᵒᵖ ⥤ Type _ where
  obj T := AttractorPt act N (unop T)
  map f := ↾ AttractorPt.baseChange f.unop
  map_id T := by
    ext φ T' t a
    change φ.app (t ≫ 𝟙 _) a = φ.app t a
    simp
  map_comp f g := by
    ext φ T' t a
    change φ.app (t ≫ g.unop ≫ f.unop) a = φ.app ((t ≫ g.unop) ≫ f.unop) a
    simp

/-- The unit point of `𝔸(N)` evaluates a point of `X^N` to a point of `X`: the morphism
`X^N → X` of §3. -/
def AttractorPt.toPoint {N : AddSubmonoid M} {act : AAction 𝒪 M F} {T : C}
    (φ : AttractorPt act N T) : F.obj (op T) := φ.app (𝟙 T) 1

/-- **Fact 3.6.** `X^M = X`: for the magnet `N = M`, evaluation at the unit is a bijection, whose
inverse sends `x` to the orbit map `a ↦ a • x`. -/
def attractorTopEquiv (T : C) : AttractorPt act (⊤ : AddSubmonoid M) T ≃ F.obj (op T) where
  toFun := AttractorPt.toPoint
  invFun x :=
    { app := fun {T'} t a =>
        act.smul (a.comp (AddMonoidHom.toMultiplicative
          (AddSubmonoid.topEquiv (M := M)).symm.toAddMonoidHom)) (F.map t.op x)
      naturality := fun {T' T''} s t a => by
        rw [act.map_smul, ← Functor.map_comp_apply]
        rfl
      equivariant := fun {T'} t h a => by
        rw [← act.mul_smul]
        congr 1 }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    have key := φ.equivariant t (a.comp (AddMonoidHom.toMultiplicative
      (AddSubmonoid.topEquiv (M := M)).symm.toAddMonoidHom)) 1
    have hnat := φ.naturality t.op.unop (𝟙 T) 1
    have ha : APt.toMagnet (⊤ : AddSubmonoid M) (a.comp (AddMonoidHom.toMultiplicative
        (AddSubmonoid.topEquiv (M := M)).symm.toAddMonoidHom)) * 1 = a := by
      ext p; simp [APt.toMagnet]; rfl
    rw [ha] at key
    have hone : APt.res (𝒪 := 𝒪) (P := (⊤ : AddSubmonoid M)) t.op 1 = 1 := by
      ext p; simp
    simp only [Quiver.Hom.unop_op, Category.comp_id] at hnat
    rw [hone] at hnat
    show act.smul _ (F.map t.op (φ.app (𝟙 T) 1)) = φ.app t a
    rw [← hnat, key]
  right_inv x := by
    show act.smul _ (F.map (𝟙 T).op x) = x
    have h1 : ((1 : APt 𝒪 (⊤ : AddSubmonoid M) (op T)).comp (AddMonoidHom.toMultiplicative
        (AddSubmonoid.topEquiv (M := M)).symm.toAddMonoidHom)) = 1 := by
      ext p; simp
    rw [h1, act.one_smul]
    simp

section Sheaf

variable {act N}

/-- The value at the identity of a point over `Y` determines its value over any `g : Z ⟶ Y`. -/
lemma AttractorPt.map_app_id {Y Z W : C} (φ : AttractorPt act N Y) (g : Z ⟶ Y) (u : Y ⟶ W)
    (a : APt 𝒪 N (op W)) :
    F.map g.op (φ.app (𝟙 Y) (APt.res u.op a)) = φ.app g (APt.res (g ≫ u).op a) := by
  have h := φ.naturality g (𝟙 Y) (APt.res u.op a)
  rw [Category.comp_id] at h
  rw [← h, ← APt.res_comp]
  rfl

@[simp] lemma attractor_map_app {T T'' : Cᵒᵖ} (f : T ⟶ T'') (φ : AttractorPt act N (unop T))
    {Z : C} (t : Z ⟶ unop T'') (a : APt 𝒪 N (op Z)) :
    AttractorPt.app ((attractor act N).map f φ) t a = φ.app (t ≫ f.unop) a := rfl

end Sheaf

/-- **Proposition 3.2.** If `X` is a sheaf for a topology on `C`, so is the attractor `X^N`. The
proof glues directly: a compatible family of equivariant maps is evaluated on the pulled back
covering of each `T' → T`. -/
theorem isSheaf_attractor (J : GrothendieckTopology C) (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J (attractor act N) := by
  intro T R hR x₀ hx
  let x : ∀ {Z : C} (w : Z ⟶ T), R w → AttractorPt act N Z := fun w hw => x₀ w hw
  have cong : ∀ {Z : C} {w w' : Z ⟶ T} (_ : w = w') (hw : R w) (hw' : R w')
      (c : APt 𝒪 N (op Z)), (x w hw).app (𝟙 Z) c = (x w' hw').app (𝟙 Z) c := by
    intro Z w w' e hw hw' c
    subst e
    rfl
  -- the compatibility of the family, evaluated
  have compat : ∀ {Y Z : C} {f : Y ⟶ T} (hf : R f) (g : Z ⟶ Y) (hg : R (g ≫ f))
      (c : APt 𝒪 N (op Z)), (x f hf).app g c = (x (g ≫ f) hg).app (𝟙 Z) c := by
    intro Y Z f hf g hg c
    have h := hx g (𝟙 Z) hf hg (by simp)
    have h' : (x f hf).app (𝟙 Z ≫ g) c = (x (g ≫ f) hg).app (𝟙 Z ≫ 𝟙 Z) c :=
      congrArg (fun φ : AttractorPt act N Z => φ.app (𝟙 Z) c) h
    simpa using h'
  have hloc : ∀ {T' : C} (t : T' ⟶ T) (a : APt 𝒪 N (op T')),
      Presieve.FamilyOfElements.Compatible (P := F) (R := (R.pullback t).arrows)
        (fun _ u hu => (x (u ≫ t) hu).app (𝟙 _) (APt.res u.op a)) := by
    intro T' t a Y₁ Y₂ Z g₁ g₂ u₁ u₂ hu₁ hu₂ comm
    have h₁ : R (g₁ ≫ u₁ ≫ t) := R.downward_closed hu₁ g₁
    have h₂ : R (g₂ ≫ u₂ ≫ t) := R.downward_closed hu₂ g₂
    change F.map g₁.op ((x (u₁ ≫ t) hu₁).app (𝟙 Y₁) (APt.res u₁.op a)) =
      F.map g₂.op ((x (u₂ ≫ t) hu₂).app (𝟙 Y₂) (APt.res u₂.op a))
    rw [AttractorPt.map_app_id (x (u₁ ≫ t) hu₁) g₁ u₁ a,
      AttractorPt.map_app_id (x (u₂ ≫ t) hu₂) g₂ u₂ a,
      compat hu₁ g₁ h₁, compat hu₂ g₂ h₂, comm]
    exact cong (by simp only [← Category.assoc, comm]) _ _ _
  have cover : ∀ {T' : C} (t : T' ⟶ T), Presieve.IsSheafFor F (R.pullback t).arrows :=
    fun t => hF _ (J.pullback_stable t hR)
  let glue : ∀ {T' : C} (t : T' ⟶ T), APt 𝒪 N (op T') → F.obj (op T') :=
    fun t a => (cover t).amalgamate _ (hloc t a)
  have glue_spec : ∀ {T' Y : C} (t : T' ⟶ T) (a : APt 𝒪 N (op T')) (u : Y ⟶ T')
      (hu : R (u ≫ t)), F.map u.op (glue t a) = (x (u ≫ t) hu).app (𝟙 Y) (APt.res u.op a) :=
    fun t a u hu => (cover t).valid_glue (hloc t a) u hu
  let φ : AttractorPt act N T :=
    { app := fun t a => glue t a
      naturality := by
        intro T' T'' s t a
        refine (cover (s ≫ t)).isSeparatedFor.ext fun Y u hu => ?_
        have hu' : R (u ≫ s ≫ t) := hu
        have hu'' : R ((u ≫ s) ≫ t) := by simpa using hu'
        rw [glue_spec _ _ u hu', ← Functor.map_comp_apply, ← op_comp, glue_spec _ _ _ hu'',
          ← APt.res_comp]
        exact cong (by simp) _ _ _
      equivariant := by
        intro T' t h a
        refine (cover t).isSeparatedFor.ext fun Y u hu => ?_
        rw [act.map_smul, glue_spec _ _ u hu, glue_spec _ _ u hu, APt.res_mul, ← APt.toMagnet_res]
        exact (x (u ≫ t) hu).equivariant (𝟙 Y) _ _ }
  refine ⟨φ, ?_, ?_⟩
  · intro Y f hf
    refine AttractorPt.ext ?_
    funext Z t a
    refine (cover (t ≫ f)).isSeparatedFor.ext fun W u hu => ?_
    change F.map u.op (glue (t ≫ f) a) = F.map u.op ((x f hf).app t a)
    rw [glue_spec _ _ u hu, ← (x f hf).naturality u t a,
      compat hf (u ≫ t) (by simpa using hu)]
    exact cong (by simp) _ _ _
  · intro y hy
    let y' : AttractorPt act N T := y
    change y' = φ
    refine AttractorPt.ext ?_
    funext T' t a
    refine (cover t).isSeparatedFor.ext fun W u hu => ?_
    change F.map u.op (y'.app t a) = F.map u.op (glue t a)
    rw [glue_spec _ _ u hu, ← y'.naturality u t a]
    have h : (x (u ≫ t) hu).app (𝟙 W) (APt.res u.op a) = y'.app (𝟙 W ≫ u ≫ t) (APt.res u.op a) :=
      congrArg (fun ψ : AttractorPt act N W => ψ.app (𝟙 W) (APt.res u.op a)) (hy (u ≫ t) hu).symm
    rw [h, Category.id_comp]

end AlgMag
