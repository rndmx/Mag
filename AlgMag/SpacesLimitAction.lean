/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec6FPR
import AlgMag.AlgebraicSpace
import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import AlgMag.ChartThm68
import AlgMag.AppendixA3
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Descent of an algebraic space with a `D(M)`-action to a stage of a limit

Mayeux, *Algebraic Magnetism*, proof of Theorem A.1: "By standard results on limits (as in Tag 07SJ),
the space `X` and the `G`-action then come from a finitely presented algebraic space `X₀ → S₀` with
`G₀`-action", used again at the start of the proof of Theorem A.2 = Theorem 6.8.

* `AlgMag.LimAct.exists_action_model`: Stacks 07SK applied to the action and its axioms.
* `AlgMag.LimAct.strongAtlas_of_limit`: Theorem 6.8 (i) and the strongly-FPR note, over a limit.
* `AlgMag.LimAct.closed_of_limit_torsionFree`, `Model.closed_of_stage`: Theorem A.1, closedness.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgMag.LimAct

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type u} [AddCommMonoid M]

lemma tex {A B : Type u} {f g : A ⟶ B} (h : ∀ x, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ h

/-- Extensionality for presheaf maps. -/
lemma pex {Y Y' : Cᵒᵖ ⥤ Type u} {f g : Y ⟶ Y'} (h : ∀ T x, f.app T x = g.app T x) : f = g :=
  NatTrans.ext (funext fun T => tex (h T))

variable (𝒪 M) in
/-- The functor of points of `D(M)`. -/
def aptP : Cᵒᵖ ⥤ Type u where
  obj T := APt 𝒪 M T
  map f := ↾APt.res f
  map_id T := tex fun a => APt.res_id a
  map_comp f g := tex fun a => APt.res_comp f g a

variable (𝒪 M) in
/-- The presheaf `D(M) × Y`. -/
def actP (Y : Cᵒᵖ ⥤ Type u) : Cᵒᵖ ⥤ Type u where
  obj T := APt 𝒪 M T × Y.obj T
  map f := ↾fun p => (APt.res f p.1, Y.map f p.2)
  map_id T := tex fun p => Prod.ext (APt.res_id p.1) (by simp)
  map_comp f g := tex fun p => Prod.ext (APt.res_comp f g p.1) (by simp)

variable {Y Y' Y'' Z : Cᵒᵖ ⥤ Type u}

variable (𝒪 M Y) in
/-- The projection `D(M) × Y → Y`. -/
def actSnd : actP 𝒪 M Y ⟶ Y where
  app T := ↾fun p => p.2
  naturality _ _ _ := rfl

variable (𝒪 M Y) in
/-- The projection `D(M) × Y → D(M)`. -/
def actGrp : actP 𝒪 M Y ⟶ aptP 𝒪 M where
  app T := ↾fun p => p.1
  naturality _ _ _ := rfl

/-- The map into `D(M) × Y` given by its components. -/
def actLift (g : Z ⟶ aptP 𝒪 M) (y : Z ⟶ Y) : Z ⟶ actP 𝒪 M Y where
  app T := ↾fun z => (g.app T z, y.app T z)
  naturality T T' f := tex fun z => Prod.ext
    (by change g.app T' (Z.map f z) = (aptP 𝒪 M).map f (g.app T z)
        exact NatTrans.naturality_apply g f z)
    (by change y.app T' (Z.map f z) = Y.map f (y.app T z)
        exact NatTrans.naturality_apply y f z)

@[reassoc (attr := simp)] lemma actLift_snd (g : Z ⟶ aptP 𝒪 M) (y : Z ⟶ Y) :
    actLift g y ≫ actSnd 𝒪 M Y = y := rfl

@[reassoc (attr := simp)] lemma actLift_grp (g : Z ⟶ aptP 𝒪 M) (y : Z ⟶ Y) :
    actLift g y ≫ actGrp 𝒪 M Y = g := rfl

lemma act_hom_ext {f g : Z ⟶ actP 𝒪 M Y} (h₁ : f ≫ actGrp 𝒪 M Y = g ≫ actGrp 𝒪 M Y)
    (h₂ : f ≫ actSnd 𝒪 M Y = g ≫ actSnd 𝒪 M Y) : f = g :=
  pex fun T x => Prod.ext (congrArg (fun k => k.app T x) h₁) (congrArg (fun k => k.app T x) h₂)

variable (𝒪 M) in
/-- `id × a`. -/
def actMap (a : Y ⟶ Y') : actP 𝒪 M Y ⟶ actP 𝒪 M Y' := actLift (actGrp 𝒪 M Y) (actSnd 𝒪 M Y ≫ a)

@[reassoc (attr := simp)] lemma actMap_snd (a : Y ⟶ Y') :
    actMap 𝒪 M a ≫ actSnd 𝒪 M Y' = actSnd 𝒪 M Y ≫ a := rfl

@[reassoc (attr := simp)] lemma actMap_grp (a : Y ⟶ Y') :
    actMap 𝒪 M a ≫ actGrp 𝒪 M Y' = actGrp 𝒪 M Y := rfl

@[reassoc] lemma actMap_comp (a : Y ⟶ Y') (b : Y' ⟶ Y'') :
    actMap 𝒪 M a ≫ actMap 𝒪 M b = actMap 𝒪 M (a ≫ b) := rfl

variable (𝒪 M Y) in
/-- The unit section `y ↦ (1, y)`. -/
def actUnit : Y ⟶ actP 𝒪 M Y where
  app T := ↾fun y => (1, y)
  naturality T T' f := tex fun y => Prod.ext
    (MonoidHom.ext fun p => (map_one ((𝒪.map f).hom)).symm) rfl

variable (𝒪 M Y) in
/-- `(g, (h, y)) ↦ (g h, y)`. -/
def actMul : actP 𝒪 M (actP 𝒪 M Y) ⟶ actP 𝒪 M Y where
  app T := ↾fun p => (p.1 * p.2.1, p.2.2)
  naturality T T' f := tex fun p => Prod.ext
    (APt.res_mul f p.1 p.2.1).symm rfl

@[reassoc] lemma actUnit_map (a : Y ⟶ Y') :
    a ≫ actUnit 𝒪 M Y' = actUnit 𝒪 M Y ≫ actMap 𝒪 M a := rfl

@[reassoc] lemma actMul_map (a : Y ⟶ Y') :
    actMap 𝒪 M (actMap 𝒪 M a) ≫ actMul 𝒪 M Y' = actMul 𝒪 M Y ≫ actMap 𝒪 M a := rfl

@[reassoc] lemma actUnit_snd : actUnit 𝒪 M Y ≫ actSnd 𝒪 M Y = 𝟙 Y := rfl

@[reassoc] lemma actMul_snd :
    actMul 𝒪 M Y ≫ actSnd 𝒪 M Y = actSnd 𝒪 M (actP 𝒪 M Y) ≫ actSnd 𝒪 M Y := rfl

/-- An action as a morphism. -/
def ofAct (act : AAction 𝒪 M Y) : actP 𝒪 M Y ⟶ Y where
  app T := ↾fun p => act.smul p.1 p.2
  naturality T T' f := tex fun p => (act.map_smul f p.1 p.2).symm

/-- The cartesian square `D(M) × Y → D(M) × Y'` over `Y → Y'`. -/
lemma isPullback_actMap (a : Y ⟶ Y') :
    IsPullback (actMap 𝒪 M a) (actSnd 𝒪 M Y) (actSnd 𝒪 M Y') a :=
  ⟨⟨rfl⟩, ⟨PullbackCone.IsLimit.mk (f := actSnd 𝒪 M Y') (g := a) (fst := actMap 𝒪 M a)
      (snd := actSnd 𝒪 M Y) rfl
    (fun (s : PullbackCone (actSnd 𝒪 M Y') a) => actLift (s.fst ≫ actGrp 𝒪 M Y') s.snd)
    (fun s => act_hom_ext rfl s.condition.symm)
    (fun s => rfl)
    (fun s m h₁ h₂ => act_hom_ext (by
      rw [← actMap_grp a, ← Category.assoc, h₁]; rfl) (by simpa using h₂))⟩⟩

/-- Base change of a cartesian square by `D(M) × -`. -/
lemma isPullback_act {W B L : Cᵒᵖ ⥤ Type u} {q : Y ⟶ W} {p : Y ⟶ L} {w : W ⟶ B} {π : L ⟶ B}
    (sq : IsPullback q p w π) :
    IsPullback (actMap 𝒪 M q) (actSnd 𝒪 M Y ≫ p) (actSnd 𝒪 M W ≫ w) π :=
  (isPullback_actMap (𝒪 := 𝒪) (M := M) q).paste_vert sq

variable (𝒪 M) in
/-- The object `D(M) × W` over the base of `W`. -/
abbrev actOver {B : Cᵒᵖ ⥤ Type u} (W : Over B) : Over B :=
  Over.mk (actSnd 𝒪 M W.left ≫ W.hom)

/-- An action on the stage `W`, compatible with the action on `Y` under a cartesian square. -/
structure Model {B L : Cᵒᵖ ⥤ Type u} (π : L ⟶ B) (Y : Over L) (act : AAction 𝒪 M Y.left)
    (W : Over B) where
  q : Y.left ⟶ W.left
  μ : actP 𝒪 M W.left ⟶ W.left
  sq : IsPullback q Y.hom W.hom π
  overB : μ ≫ W.hom = actSnd 𝒪 M W.left ≫ W.hom
  inv : ofAct act ≫ Y.hom = actSnd 𝒪 M Y.left ≫ Y.hom
  equiv : actMap 𝒪 M q ≫ μ = ofAct act ≫ q

variable {B B' L : Cᵒᵖ ⥤ Type u} {π : L ⟶ B} {Yo : Over L} {act : AAction 𝒪 M Yo.left} {W : Over B}

/-- Restriction of a model to a later stage. -/
noncomputable def Model.restrict (m : Model π Yo act W) (e : B' ⟶ B) (π' : L ⟶ B') (h : π' ≫ e = π) :
    Model π' Yo act ((Over.pullback e).obj W) where
  q := pullback.lift m.q (Yo.hom ≫ π') (by rw [m.sq.w, Category.assoc, h])
  μ := pullback.lift (actMap 𝒪 M (pullback.fst W.hom e) ≫ m.μ)
    (actSnd 𝒪 M (pullback W.hom e) ≫ pullback.snd W.hom e) (by
      rw [Category.assoc, m.overB, actMap_snd_assoc, Category.assoc, pullback.condition]; rfl)
  sq := by
    refine IsPullback.of_right (h₁₂ := pullback.fst W.hom e) (v₁₃ := W.hom) (h₂₂ := e) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback W.hom e)
    rw [pullback.lift_fst, h]
    exact m.sq
  overB := pullback.lift_snd _ _ _
  inv := m.inv
  equiv := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, actMap_comp_assoc, pullback.lift_fst, m.equiv,
        Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd]
      change actSnd 𝒪 M Yo.left ≫ pullback.lift _ _ _ ≫ pullback.snd W.hom e = _
      rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc (ofAct act), m.inv,
        Category.assoc]

lemma Model.restrict_q_fst (m : Model π Yo act W) (e : B' ⟶ B) (π' : L ⟶ B') (h : π' ≫ e = π) :
    (m.restrict e π' h).q ≫ pullback.fst W.hom e = m.q := pullback.lift_fst _ _ _

lemma Model.restrict_μ_fst (m : Model π Yo act W) (e : B' ⟶ B) (π' : L ⟶ B') (h : π' ≫ e = π) :
    (m.restrict e π' h).μ ≫ pullback.fst W.hom e = actMap 𝒪 M (pullback.fst W.hom e) ≫ m.μ :=
  pullback.lift_fst _ _ _

/-- The unit axiom for a model. -/
def Model.IsUnit (m : Model π Yo act W) : Prop := actUnit 𝒪 M W.left ≫ m.μ = 𝟙 _

/-- The associativity axiom for a model. -/
def Model.IsMul (m : Model π Yo act W) : Prop :=
  actMul 𝒪 M W.left ≫ m.μ = actMap 𝒪 M m.μ ≫ m.μ

lemma Model.restrict_isUnit (m : Model π Yo act W) (e : B' ⟶ B) (π' : L ⟶ B') (h : π' ≫ e = π)
    (hu : pullback.fst W.hom e ≫ actUnit 𝒪 M W.left ≫ m.μ = pullback.fst W.hom e) :
    (m.restrict e π' h).IsUnit := by
  unfold Model.IsUnit
  have o : (m.restrict e π' h).μ ≫ pullback.snd W.hom e = actSnd 𝒪 M _ ≫ pullback.snd W.hom e :=
    (m.restrict e π' h).overB
  have f1 := m.restrict_μ_fst e π' h
  apply pullback.hom_ext
  · calc _ = actUnit 𝒪 M (pullback W.hom e) ≫ (m.restrict e π' h).μ ≫ pullback.fst W.hom e :=
          Category.assoc _ _ _
      _ = actUnit 𝒪 M (pullback W.hom e) ≫ actMap 𝒪 M (pullback.fst W.hom e) ≫ m.μ := by rw [f1]
      _ = pullback.fst W.hom e ≫ actUnit 𝒪 M W.left ≫ m.μ := (actUnit_map_assoc _ _).symm
      _ = pullback.fst W.hom e := hu
      _ = _ := (Category.id_comp _).symm
  · calc _ = actUnit 𝒪 M (pullback W.hom e) ≫ (m.restrict e π' h).μ ≫ pullback.snd W.hom e :=
          Category.assoc _ _ _
      _ = actUnit 𝒪 M (pullback W.hom e) ≫ actSnd 𝒪 M _ ≫ pullback.snd W.hom e := by rw [o]
      _ = _ := (Category.id_comp _).symm

lemma Model.restrict_isMul (m : Model π Yo act W) (e : B' ⟶ B) (π' : L ⟶ B') (h : π' ≫ e = π)
    (hm : actMap 𝒪 M (actMap 𝒪 M (pullback.fst W.hom e)) ≫ actMul 𝒪 M W.left ≫ m.μ =
      actMap 𝒪 M (actMap 𝒪 M (pullback.fst W.hom e)) ≫ actMap 𝒪 M m.μ ≫ m.μ) :
    (m.restrict e π' h).IsMul := by
  unfold Model.IsMul
  have o : (m.restrict e π' h).μ ≫ pullback.snd W.hom e = actSnd 𝒪 M _ ≫ pullback.snd W.hom e :=
    (m.restrict e π' h).overB
  have f1 := m.restrict_μ_fst e π' h
  have k : actMap 𝒪 M (m.restrict e π' h).μ ≫ actMap 𝒪 M (pullback.fst W.hom e) =
      actMap 𝒪 M (actMap 𝒪 M (pullback.fst W.hom e)) ≫ actMap 𝒪 M m.μ := by
    rw [actMap_comp, f1, actMap_comp]
  apply pullback.hom_ext
  · calc _ = actMul 𝒪 M (pullback W.hom e) ≫ (m.restrict e π' h).μ ≫ pullback.fst W.hom e :=
          Category.assoc _ _ _
      _ = actMul 𝒪 M (pullback W.hom e) ≫ actMap 𝒪 M (pullback.fst W.hom e) ≫ m.μ := by rw [f1]
      _ = actMap 𝒪 M (actMap 𝒪 M (pullback.fst W.hom e)) ≫ actMul 𝒪 M W.left ≫ m.μ :=
          (actMul_map_assoc _ _).symm
      _ = actMap 𝒪 M (actMap 𝒪 M (pullback.fst W.hom e)) ≫ actMap 𝒪 M m.μ ≫ m.μ := hm
      _ = actMap 𝒪 M (m.restrict e π' h).μ ≫ actMap 𝒪 M (pullback.fst W.hom e) ≫ m.μ := by
          rw [reassoc_of% k]
      _ = actMap 𝒪 M (m.restrict e π' h).μ ≫ (m.restrict e π' h).μ ≫ pullback.fst W.hom e := by
          rw [f1]
      _ = _ := (Category.assoc _ _ _).symm
  · calc _ = actMul 𝒪 M (pullback W.hom e) ≫ (m.restrict e π' h).μ ≫ pullback.snd W.hom e :=
          Category.assoc _ _ _
      _ = actMul 𝒪 M (pullback W.hom e) ≫ actSnd 𝒪 M _ ≫ pullback.snd W.hom e := by rw [o]
      _ = actMap 𝒪 M (m.restrict e π' h).μ ≫ actSnd 𝒪 M _ ≫ pullback.snd W.hom e := by
          change actSnd 𝒪 M _ ≫ actSnd 𝒪 M _ ≫ pullback.snd W.hom e =
            actSnd 𝒪 M _ ≫ (m.restrict e π' h).μ ≫ pullback.snd W.hom e
          rw [o]
          rfl
      _ = actMap 𝒪 M (m.restrict e π' h).μ ≫ (m.restrict e π' h).μ ≫ pullback.snd W.hom e := by
          rw [o]
          rfl
      _ = _ := (Category.assoc _ _ _).symm

/-- Equality of two maps after base change, tested on a cartesian cover. -/
lemma pull_eq {A : Over B} {A' : Cᵒᵖ ⥤ Type u} {a : A' ⟶ A.left} {p : A' ⟶ L} {f g : A ⟶ W}
    (sq : IsPullback a p A.hom π) (h : a ≫ f.left = a ≫ g.left) :
    (Over.pullback π).map f = (Over.pullback π).map g := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi sq.isoPullback.hom]
  change sq.isoPullback.hom ≫ pullback.lift (pullback.fst A.hom π ≫ f.left) (pullback.snd A.hom π) _ =
    sq.isoPullback.hom ≫ pullback.lift (pullback.fst A.hom π ≫ g.left) (pullback.snd A.hom π) _
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst,
      sq.isoPullback_hom_fst_assoc, sq.isoPullback_hom_fst_assoc, h]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- Equality after base change gives equality on the first projection. -/
lemma fst_eq_of_pull_eq {A : Over B} {f g : A ⟶ W} {e : B' ⟶ B}
    (h : (Over.pullback e).map f = (Over.pullback e).map g) :
    pullback.fst A.hom e ≫ f.left = pullback.fst A.hom e ≫ g.left := by
  have := congrArg (fun k => k.left ≫ pullback.fst W.hom e) h
  change pullback.lift (pullback.fst A.hom e ≫ f.left) (pullback.snd A.hom e) _ ≫ _ =
    pullback.lift (pullback.fst A.hom e ≫ g.left) (pullback.snd A.hom e) _ ≫ _ at this
  rwa [pullback.lift_fst, pullback.lift_fst] at this

/-- The composite `W → D(M) × W → W`, as a morphism over the base. -/
def Model.unitMor (m : Model π Yo act W) : W ⟶ W :=
  Over.homMk (actUnit 𝒪 M W.left ≫ m.μ) (by
    rw [Category.assoc, m.overB]; exact actUnit_snd_assoc _)

/-- `(g, h, y) ↦ (g h) y`, over the base. -/
def Model.mulL (m : Model π Yo act W) : actOver 𝒪 M (actOver 𝒪 M W) ⟶ W :=
  Over.homMk (actMul 𝒪 M W.left ≫ m.μ) (by
    rw [Category.assoc, m.overB]; exact actMul_snd_assoc _)

/-- `(g, h, y) ↦ g (h y)`, over the base. -/
def Model.mulR (m : Model π Yo act W) : actOver 𝒪 M (actOver 𝒪 M W) ⟶ W :=
  Over.homMk (actMap 𝒪 M m.μ ≫ m.μ) (by
    rw [Category.assoc, m.overB, actMap_snd_assoc, m.overB]; rfl)

/-- The action of a model after base change to the limit is the unit. -/
lemma Model.pull_unit (m : Model π Yo act W) :
    (Over.pullback π).map m.unitMor = (Over.pullback π).map (𝟙 W) := by
  refine pull_eq (a := m.q) (p := Yo.hom) m.sq ?_
  change m.q ≫ actUnit 𝒪 M W.left ≫ m.μ = m.q ≫ 𝟙 _
  rw [actUnit_map_assoc, m.equiv, Category.comp_id, ← Category.assoc]
  have : actUnit 𝒪 M Yo.left ≫ ofAct act = 𝟙 _ := pex fun T x => act.one_smul x
  rw [this, Category.id_comp]

/-- Associativity of a model after base change to the limit. -/
lemma Model.pull_mul (m : Model π Yo act W) :
    (Over.pullback π).map m.mulL = (Over.pullback π).map m.mulR := by
  have s1 := isPullback_act (𝒪 := 𝒪) (M := M) m.sq
  have s2 := isPullback_act (𝒪 := 𝒪) (M := M) s1
  refine pull_eq (a := actMap 𝒪 M (actMap 𝒪 M m.q)) s2 ?_
  change actMap 𝒪 M (actMap 𝒪 M m.q) ≫ actMul 𝒪 M W.left ≫ m.μ =
    actMap 𝒪 M (actMap 𝒪 M m.q) ≫ actMap 𝒪 M m.μ ≫ m.μ
  have h1 : actMap 𝒪 M (actMap 𝒪 M m.q) ≫ actMap 𝒪 M m.μ =
      actMap 𝒪 M (ofAct act) ≫ actMap 𝒪 M m.q := by
    rw [actMap_comp, m.equiv, actMap_comp]
  rw [actMul_map_assoc, m.equiv, reassoc_of% h1, m.equiv]
  have : actMul 𝒪 M Yo.left ≫ ofAct act = actMap 𝒪 M (ofAct act) ≫ ofAct act :=
    pex fun T x => act.mul_smul x.1 x.2.1 x.2.2
  rw [← Category.assoc, this, Category.assoc]

/-- The action of a model satisfying the axioms. -/
def Model.toAct (m : Model π Yo act W) (hu : m.IsUnit) (hm : m.IsMul) : AAction 𝒪 M W.left where
  smul {U} h x := m.μ.app U ((h, x) : APt 𝒪 M U × W.left.obj U)
  one_smul {T} x := congrArg (fun k => k.app T x) hu
  mul_smul {T} g h x := congrArg (fun k => k.app T
    ((g, ((h, x) : APt 𝒪 M T × W.left.obj T)) : APt 𝒪 M T × (APt 𝒪 M T × W.left.obj T))) hm
  map_smul {U V} f h x := (NatTrans.naturality_apply m.μ f
    ((h, x) : APt 𝒪 M U × W.left.obj U)).symm

lemma Model.equivariant (m : Model π Yo act W) (hu : m.IsUnit) (hm : m.IsMul) :
    IsEquivariant act (m.toAct hu hm) m.q := fun {T} h x =>
  (congrArg (fun k => k.app T ((h, x) : APt 𝒪 M T × Yo.left.obj T)) m.equiv).symm

lemma Model.invariant (m : Model π Yo act W) (hu : m.IsUnit) (hm : m.IsMul) {T : Cᵒᵖ}
    (h : APt 𝒪 M T) (x : W.left.obj T) :
    W.hom.app T ((m.toAct hu hm).smul h x) = W.hom.app T x :=
  congrArg (fun k => k.app T ((h, x) : APt 𝒪 M T × W.left.obj T)) m.overB

section Stage

variable {Bi Bj : Cᵒᵖ ⥤ Type u} {πi : L ⟶ Bi} {Yi : Over Bi} {qi : Yo.left ⟶ Yi.left}

/-- The action at the limit, read on the base changes of a stage object. -/
noncomputable def limMor (sq : IsPullback qi Yo.hom Yi.hom πi)
    (hinv : ofAct act ≫ Yo.hom = actSnd 𝒪 M Yo.left ≫ Yo.hom) :
    (Over.pullback πi).obj (actOver 𝒪 M Yi) ⟶ (Over.pullback πi).obj Yi :=
  Over.homMk ((isPullback_act (𝒪 := 𝒪) (M := M) sq).isoPullback.inv ≫ ofAct act ≫
      sq.isoPullback.hom) (by
    change (_ ≫ _ ≫ _) ≫ pullback.snd _ _ = pullback.snd _ _
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd, hinv]
    rw [← Category.assoc]
    simp)

/-- From a morphism at a stage to a model: `g` is the morphism at stage `j` produced by Stacks 07SK,
fullness, from the action at the limit. -/
theorem model_of_stage {πj : L ⟶ Bj} {e : Bj ⟶ Bi} (he : πj ≫ e = πi)
    (sq : IsPullback qi Yo.hom Yi.hom πi)
    (hinv : ofAct act ≫ Yo.hom = actSnd 𝒪 M Yo.left ≫ Yo.hom)
    (g : (Over.pullback e).obj (actOver 𝒪 M Yi) ⟶ (Over.pullback e).obj Yi)
    (α : (Over.pullback πj).obj ((Over.pullback e).obj (actOver 𝒪 M Yi)) ≅
      (Over.pullback πi).obj (actOver 𝒪 M Yi))
    (β : (Over.pullback πj).obj ((Over.pullback e).obj Yi) ≅ (Over.pullback πi).obj Yi)
    (hα : α.hom.left ≫ pullback.fst (actOver 𝒪 M Yi).hom πi =
      pullback.fst ((Over.pullback e).obj (actOver 𝒪 M Yi)).hom πj ≫
        pullback.fst (actOver 𝒪 M Yi).hom e)
    (hβ : β.hom.left ≫ pullback.fst Yi.hom πi =
      pullback.fst ((Over.pullback e).obj Yi).hom πj ≫ pullback.fst Yi.hom e)
    (hf : α.hom ≫ limMor sq hinv = (Over.pullback πj).map g ≫ β.hom) :
    Nonempty (Model πj Yo act ((Over.pullback e).obj Yi)) := by
  have hq : qi ≫ Yi.hom = (Yo.hom ≫ πj) ≫ e := by rw [sq.w, Category.assoc, he]
  let qj : Yo.left ⟶ pullback Yi.hom e := pullback.lift qi (Yo.hom ≫ πj) hq
  have qj1 : qj ≫ pullback.fst Yi.hom e = qi := pullback.lift_fst _ _ _
  have qj2 : qj ≫ pullback.snd Yi.hom e = Yo.hom ≫ πj := pullback.lift_snd _ _ _
  let a := pullback.fst Yi.hom e
  let iota : actP 𝒪 M (pullback Yi.hom e) ⟶ pullback (actOver 𝒪 M Yi).hom e :=
    pullback.lift (actMap 𝒪 M a) (actSnd 𝒪 M _ ≫ pullback.snd Yi.hom e) (by
      change _ ≫ actSnd 𝒪 M _ ≫ Yi.hom = _
      rw [actMap_snd_assoc, Category.assoc]
      exact congrArg (fun k => actSnd 𝒪 M _ ≫ k) pullback.condition)
  have iota1 : iota ≫ pullback.fst (actOver 𝒪 M Yi).hom e = actMap 𝒪 M a := pullback.lift_fst _ _ _
  have iota2 : iota ≫ pullback.snd (actOver 𝒪 M Yi).hom e =
      actSnd 𝒪 M _ ≫ pullback.snd Yi.hom e := pullback.lift_snd _ _ _
  have gw : g.left ≫ pullback.snd Yi.hom e = pullback.snd (actOver 𝒪 M Yi).hom e := Over.w g
  have sqW : IsPullback qj Yo.hom (pullback.snd Yi.hom e) πj := by
    refine IsPullback.of_right (h₁₂ := pullback.fst Yi.hom e) (v₁₃ := Yi.hom) (h₂₂ := e) ?_ qj2
      (IsPullback.of_hasPullback Yi.hom e)
    rw [qj1, he]
    exact sq
  -- the point of the base change of `D(M) × Y_j`
  let E := (isPullback_act (𝒪 := 𝒪) (M := M) sq).isoPullback
  let s' : actP 𝒪 M Yo.left ⟶ pullback ((Over.pullback e).obj (actOver 𝒪 M Yi)).hom πj :=
    pullback.lift (actMap 𝒪 M qj ≫ iota) (actSnd 𝒪 M _ ≫ Yo.hom) (by
      change _ ≫ pullback.snd (actOver 𝒪 M Yi).hom e = _
      rw [Category.assoc, iota2, actMap_snd_assoc, qj2, Category.assoc])
  have s1 : s' ≫ pullback.fst _ _ = actMap 𝒪 M qj ≫ iota := pullback.lift_fst _ _ _
  have s2 : s' ≫ pullback.snd _ _ = actSnd 𝒪 M _ ≫ Yo.hom := pullback.lift_snd _ _ _
  have hs : s' ≫ α.hom.left = E.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα, reassoc_of% s1, iota1, actMap_comp]
      rw [show qj ≫ a = qi from qj1]
      exact (IsPullback.isoPullback_hom_fst _).symm
    · have w : α.hom.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w α.hom
      rw [Category.assoc, w, s2]
      exact (IsPullback.isoPullback_hom_snd _).symm
  have hmain := congrArg (fun k => s' ≫ k.left) hf
  simp only [Over.comp_left] at hmain
  have hLHS : s' ≫ α.hom.left ≫ (limMor sq hinv).left = ofAct act ≫ sq.isoPullback.hom := by
    rw [← Category.assoc, hs]
    change E.hom ≫ E.inv ≫ _ = _
    simp
  rw [hLHS] at hmain
  have hmain1 := congrArg (fun k => k ≫ pullback.fst Yi.hom πi) hmain
  have hmain2 : ofAct act ≫ qi = actMap 𝒪 M qj ≫ iota ≫ g.left ≫ a := by
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst, hβ] at hmain1
    rw [hmain1]
    simp only [Over.pullback_map_left, pullback.lift_fst_assoc]
    simp only [Category.assoc]
    rw [reassoc_of% s1]
  refine ⟨⟨qj, iota ≫ g.left, sqW, ?_, hinv, ?_⟩⟩
  · change (iota ≫ g.left) ≫ pullback.snd Yi.hom e = actSnd 𝒪 M _ ≫ pullback.snd Yi.hom e
    rw [Category.assoc, gw, iota2]
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, ← hmain2.symm.symm]
      change _ = ofAct act ≫ qj ≫ a
      rw [show qj ≫ a = qi from qj1, hmain2]
    · rw [Category.assoc, Category.assoc, Category.assoc, gw, iota2]
      change actSnd 𝒪 M _ ≫ qj ≫ pullback.snd Yi.hom e = ofAct act ≫ qj ≫ pullback.snd Yi.hom e
      rw [qj2, ← Category.assoc (ofAct act), hinv, Category.assoc]

end Stage

end AlgMag.LimAct

open AlgebraicGeometry




namespace AlgMag.LimAct

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommMonoid M]

local notation "𝒪S" => fppfO B S hS

variable (B S hS M) in
/-- `D(M) × Y` is an algebraic space, of finite presentation over `Y`. -/
def ActGood : Prop :=
  ∀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Y →
    IsAlgebraicSpace B S hS (actP (fppfO B S hS) M Y) ∧
      Space.IsFinitePresentation B S hS (actSnd (fppfO B S hS) M Y)

section

variable {Bs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

lemma actOver_good (hG : ActGood B S hS M) (hB : IsAlgebraicSpace B S hS Bs) {W : Over Bs}
    (hW : IsAlgebraicSpace B S hS W.left) (hfp : Space.IsFinitePresentation B S hS W.hom) :
    IsAlgebraicSpace B S hS (actOver (fppfO B S hS) M W).left ∧
      Space.IsFinitePresentation B S hS (actOver (fppfO B S hS) M W).hom :=
  ⟨(hG _ hW).1, Space.isFinitePresentation_comp B S hS (hG _ hW).1 hW hB _ _ (hG _ hW).2 hfp⟩

lemma pull_good {Bs' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : Bs' ⟶ Bs)
    (hB : IsAlgebraicSpace B S hS Bs) (hB' : IsAlgebraicSpace B S hS Bs') {W : Over Bs}
    (hW : IsAlgebraicSpace B S hS W.left) (hfp : Space.IsFinitePresentation B S hS W.hom) :
    IsAlgebraicSpace B S hS ((Over.pullback e).obj W).left ∧
      Space.IsFinitePresentation B S hS ((Over.pullback e).obj W).hom :=
  have hP := isAlgebraicSpace_pullback B S hS W.hom e hW hB' hB
  ⟨hP, Space.IsFinitePresentation.of_isPullback B S hS hP hW hB' hB
    (IsPullback.of_hasPullback W.hom e) hfp⟩

end

/-- `ActGood` from a representing object of `D(M)` of finite presentation over `S`. -/
theorem actGood_of_representable {T1 G0 : BigFppfOver B S hS} (hT : IsTerminal (yoneda.obj T1))
    (t : G0 ⟶ T1) (e : aptP (fppfO B S hS) M ≅ yoneda.obj G0)
    (hfp : Space.IsFinitePresentation B S hS (yoneda.map t)) : ActGood B S hS M := by
  intro Y hY
  have hT1 := isAlgebraicSpace_yoneda B S hS T1
  have hG0 := isAlgebraicSpace_yoneda B S hS G0
  have sq : IsPullback (actGrp (fppfO B S hS) M Y ≫ e.hom) (actSnd (fppfO B S hS) M Y)
      (yoneda.map t) (hT.from Y) :=
    ⟨⟨hT.hom_ext _ _⟩, ⟨PullbackCone.IsLimit.mk (f := yoneda.map t) (g := hT.from Y)
      (fst := actGrp (fppfO B S hS) M Y ≫ e.hom) (snd := actSnd (fppfO B S hS) M Y) (hT.hom_ext _ _)
      (fun (s : PullbackCone (yoneda.map t) (hT.from Y)) => actLift (s.fst ≫ e.inv) s.snd)
      (fun s => by
        rw [← Category.assoc, actLift_grp, Category.assoc, e.inv_hom_id, Category.comp_id])
      (fun s => rfl)
      (fun s m h₁ h₂ => act_hom_ext (by
        rw [actLift_grp, ← h₁, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id])
        (by rw [actLift_snd]; exact h₂))⟩⟩
  have hP := Space.isAlgebraicSpace_of_iso B S hS sq.isoPullback.symm
    (isAlgebraicSpace_pullback B S hS _ _ hG0 hY hT1)
  exact ⟨hP, Space.IsFinitePresentation.of_isPullback B S hS hP hG0 hY hT1 sq hfp⟩

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (hZ : B.Contains (⊤_ Scheme.{u}))
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), Space.IsAffineHom B S hS (D.map f))
  (hQc : ∀ i, Space.IsQuasiCompactSpace B S hS (D.obj i))
  (hQs : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
  (hconv : Space.SiteContainsBaseChangeLimits B S hS D)
  (hDlim : IsAlgebraicSpace B S hS (limit D))

include hD hAffine hQc hQs hconv hDlim in
/-- **Descent of a space with an action to a stage** (Stacks 07SK applied to the action morphism and
to the axioms; proof of Theorem A.1, first paragraph). An algebraic space `Y` of finite presentation
over `lim D` with an action of `D(M)` over `lim D` is the base change of `Y_k → D_k`, of finite
presentation, with an action of `D(M)` over `D_k`, by an equivariant cartesian square. -/
theorem exists_action_model (hG : ActGood B S hS M) (Y : Over (limit D))
    (hY : IsAlgebraicSpace B S hS Y.left) (hfp : Space.IsFinitePresentation B S hS Y.hom)
    (act : AAction (fppfO B S hS) M Y.left)
    (hinv : ofAct act ≫ Y.hom = actSnd (fppfO B S hS) M Y.left ≫ Y.hom) :
    ∃ (k : I) (W : Over (D.obj k)) (m : Model (limit.π D k) Y act W),
      IsAlgebraicSpace B S hS W.left ∧ Space.IsFinitePresentation B S hS W.hom ∧
      m.IsUnit ∧ m.IsMul := by
  obtain ⟨i, Yi, hYi, hYifp, ⟨ι⟩⟩ :=
    Space.exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits B S hS hZ D hD
      hAffine hQc hQs hconv hDlim Y hY hfp
  let qi : Y.left ⟶ Yi.left := ι.hom.left ≫ pullback.fst Yi.hom (limit.π D i)
  have sq : IsPullback qi Y.hom Yi.hom (limit.π D i) :=
    IsPullback.of_iso_pullback ⟨by
      have w : ι.hom.left ≫ pullback.snd Yi.hom (limit.π D i) = Y.hom := Over.w ι.hom
      rw [Category.assoc, pullback.condition, ← Category.assoc, w]⟩
      ((Over.forget _).mapIso ι) rfl (Over.w ι.hom)
  have hAi := actOver_good hG (hD i) hYi hYifp
  obtain ⟨j, e, g, α, β, hα, hβ, hf⟩ :=
    Space.exists_morphism_after_baseChange_of_siteContainsBaseChangeLimits B S hS hZ D hD
      hAffine hQc hQs hconv hDlim i (actOver (fppfO B S hS) M Yi) Yi hAi.1 hYi hAi.2 hYifp
      (limMor sq hinv)
  obtain ⟨m0⟩ := model_of_stage (limit.w D e) sq hinv g α β hα hβ hf
  have g0 := pull_good (D.map e) (hD i) (hD j) hYi hYifp
  -- the unit axiom
  obtain ⟨j1, e1, h1⟩ :=
    Space.eventually_eq_of_baseChange_eq_of_siteContainsBaseChangeLimits B S hS hZ D hD
      hAffine hQc hQs hconv j _ _ g0.1 g0.1 g0.2 g0.2 m0.unitMor (𝟙 _) m0.pull_unit
  have hu := fst_eq_of_pull_eq h1
  let m1 := m0.restrict (D.map e1) (limit.π D j1) (limit.w D e1)
  have m1u : m1.IsUnit := m0.restrict_isUnit _ _ _ (by
    simpa [Model.unitMor] using hu)
  have g1 := pull_good (D.map e1) (hD j) (hD j1) g0.1 g0.2
  have hA1 := actOver_good hG (hD j1) g1.1 g1.2
  have hA2 := actOver_good hG (hD j1) hA1.1 hA1.2
  -- associativity
  obtain ⟨j2, e2, h2⟩ :=
    Space.eventually_eq_of_baseChange_eq_of_siteContainsBaseChangeLimits B S hS hZ D hD
      hAffine hQc hQs hconv j1 _ _ hA2.1 g1.1 hA2.2 g1.2 m1.mulL m1.mulR m1.pull_mul
  have hm := fst_eq_of_pull_eq h2
  let W1 := (Over.pullback (D.map e1)).obj ((Over.pullback (D.map e)).obj Yi)
  let a2 := pullback.fst W1.hom (D.map e2)
  let iota2 : actP (fppfO B S hS) M (actP (fppfO B S hS) M (pullback W1.hom (D.map e2))) ⟶
      pullback (actOver (fppfO B S hS) M (actOver (fppfO B S hS) M W1)).hom (D.map e2) :=
    pullback.lift (actMap _ M (actMap _ M a2))
      (actSnd _ M _ ≫ actSnd _ M _ ≫ pullback.snd W1.hom (D.map e2)) (by
        change _ ≫ actSnd _ M _ ≫ actSnd _ M _ ≫ W1.hom = _
        rw [Category.assoc, Category.assoc]
        change actSnd _ M _ ≫ actSnd _ M _ ≫ a2 ≫ W1.hom = _
        rw [pullback.condition])
  have iota21 : iota2 ≫ pullback.fst _ (D.map e2) = actMap _ M (actMap _ M a2) :=
    pullback.lift_fst _ _ _
  let m2 := m1.restrict (D.map e2) (limit.π D j2) (limit.w D e2)
  have m2m : m2.IsMul := m1.restrict_isMul _ _ _ (by
    have e3 : ∀ {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
        (k : (actOver (fppfO B S hS) M (actOver (fppfO B S hS) M W1)).left ⟶ Q),
        iota2 ≫ pullback.fst _ (D.map e2) ≫ k = actMap _ M (actMap _ M a2) ≫ k := fun k => by
      rw [← Category.assoc, iota21]
    exact (e3 _).symm.trans ((congrArg (fun k => iota2 ≫ k) hm).trans (e3 _)))
  have m2u : m2.IsUnit := m1.restrict_isUnit _ _ _ (by
    have : actUnit (fppfO B S hS) M W1.left ≫ m1.μ = 𝟙 _ := m1u
    rw [this, Category.comp_id])
  have g2 := pull_good (D.map e2) (hD j1) (hD j2) g1.1 g1.2
  exact ⟨j2, _, m2, g2.1, g2.2, m2u, m2m⟩

end AlgMag.LimAct




namespace AlgMag.LimAct

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u}

/-- A system of algebraic spaces with limit `L`, in the form Stacks 07SK needs, with the absolute
properties of its stages. For `S = Spec ℤ` this is the system of `Spec` of finitely generated subrings
(`stageSystem` of Stacks `Quot/CoherentStackAffineApproximation`). -/
structure LimitData (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  I : Type u
  cat : Category.{u} I
  cof : IsCofiltered I
  D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i)
  hAffine : ∀ {i j : I} (f : i ⟶ j), Space.IsAffineHom B S hS (D.map f)
  hQc : ∀ i, Space.IsQuasiCompactSpace B S hS (D.obj i)
  hQs : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)
  hconv : Space.SiteContainsBaseChangeLimits B S hS D
  e : limit D ≅ L
  /-- Stacks 084W: separatedness of a morphism of finite presentation descends. -/
  sepDesc : ∀ (k : I) (W : Over (D.obj k)) (Y : Over (limit D)) (q : Y.left ⟶ W.left),
    IsAlgebraicSpace B S hS W.left → Space.IsFinitePresentation B S hS W.hom →
    IsPullback q Y.hom W.hom (limit.π D k) → Space.IsSeparated B S hS Y.hom →
    ∃ (j : I) (e : j ⟶ k), Space.IsSeparated B S hS (pullback.snd W.hom (D.map e))
  /-- The projections from the limit are affine (Stacks 07SF (1), in the form of `lemma67_i`). -/
  hπ : ∀ k, (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) (limit.π D k)
  /-- A separated space over a stage is separated over `S`: the stages are affine over `S`. -/
  stageSep : ∀ (k : I) (W : Over (D.obj k)), IsAlgebraicSpace B S hS W.left →
    Space.IsSeparated B S hS W.hom → Space.IsSeparatedOver B S hS W.left
  /-- A space of finite presentation over a stage is of finite type over `S`. -/
  stageFT : ∀ (k : I) (W : Over (D.obj k)), IsAlgebraicSpace B S hS W.left →
    Space.IsFinitePresentation B S hS W.hom →
    Space.IsFiniteType B S hS (terminal.from W.left)
  /-- The charts of a space of finite presentation over a stage are of finite type. -/
  stageCharts : ∀ (k : I) (W : Over (D.obj k)), IsAlgebraicSpace B S hS W.left →
    Space.IsFinitePresentation B S hS W.hom → ChartsOfFiniteType W.left

attribute [instance] LimitData.cat LimitData.cof

variable [AddCommGroup M] {hZ : B.Contains (⊤_ Scheme.{u})} {L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The descended model of `Y → L`, with separatedness if `Y → L` is separated. -/
theorem exists_stage (P : LimitData B S hS hZ L) (hL : IsAlgebraicSpace B S hS L)
    (hG : ActGood B S hS M) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ L)
    (hY : IsAlgebraicSpace B S hS Y) (hfp : Space.IsFinitePresentation B S hS p)
    (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T), p.app T (act.smul h x) = p.app T x) :
    ∃ (k : P.I) (W : Over (P.D.obj k))
      (m : Model (limit.π P.D k) (Over.mk (p ≫ P.e.inv)) act W),
      IsAlgebraicSpace B S hS W.left ∧ Space.IsFinitePresentation B S hS W.hom ∧
      m.IsUnit ∧ m.IsMul := by
  have hDlim := Space.isAlgebraicSpace_of_iso B S hS P.e.symm hL
  refine exists_action_model hZ P.D P.hD P.hAffine P.hQc P.hQs P.hconv hDlim hG
    (Over.mk (p ≫ P.e.inv)) hY ?_ act ?_
  · exact Space.IsFinitePresentation.of_isPullback B S hS hY hY hDlim hL
      (a := 𝟙 Y) (b := p ≫ P.e.inv) (f := p) (g := P.e.hom)
      (IsPullback.of_horiz_isIso (CommSq.mk (by simp))) hfp
  · refine pex fun T x => ?_
    exact congrArg (P.e.inv.app T) (hinv x.1 x.2)

/-- The projection `Y → W` to a stage is affine and the action is compatible. -/
theorem Model.isAffine_q {C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Bk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {π : C ⟶ Bk} {Yo : Over C} {act : AAction (fppfO B S hS) M Yo.left} {W : Over Bk}
    (m : Model π Yo act W) (hπ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) π) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) m.q :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback m.sq.flip hπ

/-- A point of the limit is fixed iff its image at the stage is: the square is cartesian and the
structure maps are invariant. -/
theorem Model.fixed_iff {C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Bk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {π : C ⟶ Bk} {Yo : Over C} {act : AAction (fppfO B S hS) M Yo.left} {W : Over Bk}
    (m : Model π Yo act W) (hu : m.IsUnit) (hm : m.IsMul) {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : Yo.left.obj T) :
    m.q.app T x ∈ (fixedPoints (m.toAct hu hm)).obj T → x ∈ (fixedPoints act).obj T := by
  intro hx T' s h
  have hq : m.q.app T' (act.smul h (Yo.left.map s x)) = m.q.app T' (Yo.left.map s x) := by
    have e := m.equivariant hu hm h (Yo.left.map s x)
    rw [e, NatTrans.naturality_apply m.q s x]
    exact hx s h
  have hp : Yo.hom.app T' (act.smul h (Yo.left.map s x)) = Yo.hom.app T' (Yo.left.map s x) :=
    congrArg (fun k => k.app T' ((h, Yo.left.map s x) : APt _ M T' × Yo.left.obj T')) m.inv
  exact (Types.isPullback_iff _ _ _ _).1 (m.sq.app T') |>.2.1 _ _ ⟨hq, hp⟩

/-- **Theorem A.1, closedness, case (ii), at the level of a stage**: if `W` has closed fixed points,
so has `Y`, the base change. -/
theorem Model.closed_of_stage {C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Bk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {π : C ⟶ Bk} {Yo : Over C} {act : AAction (fppfO B S hS) M Yo.left} {W : Over Bk}
    (m : Model π Yo act W) (hu : m.IsUnit) (hm : m.IsMul)
    (h : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
        (fixedPoints (m.toAct hu hm)).ι) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
        (fixedPoints act).ι := by
  have hf : IsEquivariant act (m.toAct hu hm) m.q := m.equivariant hu hm
  have hpb : IsFPR hf := (isFPR_iff hf).2 fun T x hx => m.fixed_iff hu hm x hx
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb h

/-- **Theorem 6.8 = Theorem A.2 (i)**, and Theorem 1.1 of the strongly-FPR note, for `Y` separated of
finite presentation over a limit `L` of stages, over `S` affine of finite type over `ℤ`, from §5 of the
chart proof: a strongly-FPR atlas by an affine scheme's base change. -/
theorem strongAtlas_of_limit [AddGroup.FG M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S))
    (h5 : ∀ [AddMonoid.FG M] [DecidableEq M], ChartAssembly.Section5FromEffectivity B S hS M)
    (P : LimitData B S hS hZ L) (hL : IsAlgebraicSpace B S hS L) (hG : ActGood B S hS M)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ L) (hY : IsAlgebraicSpace B S hS Y)
    (hfp : Space.IsFinitePresentation B S hS p) (hsep : Space.IsSeparated B S hS (p ≫ P.e.inv))
    (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T), p.app T (act.smul h x) = p.app T x) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ Y), IsStronglyFPRAtlas actV act v := by
  obtain ⟨k, W, m, hW, hWfp, mu, mm⟩ := exists_stage P hL hG p hY hfp act hinv
  obtain ⟨j, e, hj⟩ := P.sepDesc k W (Over.mk (p ≫ P.e.inv)) m.q hW hWfp m.sq hsep
  let m' := m.restrict (P.D.map e) (limit.π P.D j) (limit.w P.D e)
  have mu' : m'.IsUnit := m.restrict_isUnit _ _ _ (by
    have : actUnit (fppfO B S hS) M W.left ≫ m.μ = 𝟙 _ := mu
    rw [this, Category.comp_id])
  have mm' : m'.IsMul := m.restrict_isMul _ _ _ (by
    have : actMul (fppfO B S hS) M W.left ≫ m.μ = actMap _ M m.μ ≫ m.μ := mm
    rw [this])
  have gW := pull_good (P.D.map e) (P.hD k) (P.hD j) hW hWfp
  have hchart : ChartLemmaStatement B S hS M :=
    ChartAssembly.chartLemmaStatementFG_of_section5 h5 (AddGroup.fg_iff_addMonoid_fg.1 inferInstance)
  obtain ⟨V, actV, v, hv, -, -⟩ := ChartAssembly.thm11_ft_final hSft gW.1 (P.stageSep j _ gW.1 hj)
    (P.stageFT j _ gW.1 gW.2) (m'.toAct mu' mm') hchart
  have hs := StronglyFPR.strongAtlas_pullback (m'.isAffine_q (P.hπ j))
    (m'.equivariant mu' mm') hv
  exact ⟨_, _, _, hs⟩

/-- **Theorem A.1**, closedness, case (ii), for `M` torsion-free, `S` locally noetherian, `Y` of finite
presentation over a limit `L` of stages: `Y^{D(M)} → Y` is a closed immersion. -/
theorem closed_of_limit_torsionFree [AddGroup.FG M] [IsAddTorsionFree M] [IsLocallyNoetherian S]
    (P : LimitData B S hS hZ L) (hL : IsAlgebraicSpace B S hS L) (hG : ActGood B S hS M)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ L) (hY : IsAlgebraicSpace B S hS Y)
    (hfp : Space.IsFinitePresentation B S hS p) (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T), p.app T (act.smul h x) = p.app T x) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
        (fixedPoints act).ι := by
  obtain ⟨k, W, m, hW, hWfp, mu, mm⟩ := exists_stage P hL hG p hY hfp act hinv
  have hT : TorsionResidue M S := fun s q _ x hx => ⟨0, by
    have : x = 0 := by
      obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx
      exact (nsmul_right_injective hn.ne') (by simpa using hnx)
    simp [this]⟩
  exact m.closed_of_stage mu mm (AppA3.thmA1_closed hW (P.stageCharts k W hW hWfp) _ hT)

end AlgMag.LimAct


#print axioms AlgMag.LimAct.exists_action_model
#print axioms AlgMag.LimAct.strongAtlas_of_limit
#print axioms AlgMag.LimAct.closed_of_limit_torsionFree
