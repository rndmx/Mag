/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Functorial
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Tangent spaces and attractors (Algebraic Magnetism, §16.1)

Over a category `C` with binary products, the dual numbers are an object `D` (`I_S`), `I_T = T × D`,
and `TX(T) = Hom_T(I_T, X_T) = X(T × D)` by Yoneda. The concrete `I_S` over a scheme `S` is in
`AlgMag.Sec16Scheme`.
-/

open CategoryTheory Opposite Limits

universe w v u

set_option linter.unusedSectionVars false

namespace AlgMag

variable {C : Type*} [Category.{v} C] [HasBinaryProducts C] (D : C)

/-- `T ↦ I_T = T ×_S I_S` (§16.1). -/
noncomputable def dualF : C ⥤ C where
  obj T := T ⨯ D
  map f := prod.map f (𝟙 D)

/-- **§16.1.** The tangent space `TX`, `TX(R) = Hom_R(I_R, X_R) = X(I_R)`. -/
noncomputable def tangent (X : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w := (dualF D).op ⋙ X

/-- The morphism `Tf : TX → TY`. -/
noncomputable def tangentMap {X Y : Cᵒᵖ ⥤ Type w} (f : X ⟶ Y) : tangent D X ⟶ tangent D Y :=
  Functor.whiskerLeft (dualF D).op f

/-- **Remark 16.1 (i).** `T(X ×_Y Z) = TX ×_{TY} TZ`. -/
noncomputable def tangentFibreProductIso {X Y Z : Cᵒᵖ ⥤ Type w} (f : X ⟶ Y) (g : Z ⟶ Y) :
    tangent D (fibreProduct f g) ≅ fibreProduct (tangentMap D f) (tangentMap D g) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **Remark 16.1 (ii).** `X → Y` mono implies `TX → TY` mono. -/
theorem mono_tangentMap {X Y : Cᵒᵖ ⥤ Type w} (f : X ⟶ Y) [Mono f] : Mono (tangentMap D f) := by
  refine (NatTrans.mono_iff_mono_app _).2 fun T => ?_
  have : Mono (f.app ((dualF D).op.obj T)) := (NatTrans.mono_iff_mono_app f).1 inferInstance _
  exact this

/-- **Remark 16.1 (iii).** `TS = S`: for a functor with exactly one point everywhere (the final
functor `S` over `S`), `TS` identifies with `S`. -/
noncomputable def tangentFinalIso (X : Cᵒᵖ ⥤ Type w) [∀ U, Unique (X.obj U)] : tangent D X ≅ X :=
  NatIso.ofComponents (fun U =>
    (Equiv.ofUnique (X.obj ((dualF D).op.obj U)) (X.obj U)).toIso)
    (fun _ => by ext x; exact Subsingleton.elim (α := X.obj _) _ _)

variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommMonoid M]

lemma res_fst_map {P : Type*} [AddCommMonoid P] {T T' : C} (t : T' ⟶ T) (a : APt 𝒪 P (op T)) :
    APt.res (prod.fst : T' ⨯ D ⟶ T').op (APt.res t.op a) =
      APt.res (prod.map t (𝟙 D)).op (APt.res (prod.fst : T ⨯ D ⟶ T).op a) := by
  rw [← APt.res_comp, ← APt.res_comp, ← op_comp, ← op_comp, prod.map_fst]

/-- **§16.1.** The induced action of `D(M)_S` (more generally `𝔸(M)_S`) on `TX`. -/
noncomputable def tangentAction {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F) :
    AAction 𝒪 M (tangent D F) where
  smul {U} h x := act.smul (U := op (unop U ⨯ D)) (APt.res (prod.fst : unop U ⨯ D ⟶ unop U).op h) x
  one_smul {U} x := by
    have : APt.res (prod.fst : unop U ⨯ D ⟶ unop U).op (1 : APt 𝒪 M U) = 1 := by ext p; simp
    rw [this]; exact act.one_smul (U := op (unop U ⨯ D)) x
  mul_smul {U} g h x := by
    rw [APt.res_mul]; exact act.mul_smul (U := op (unop U ⨯ D)) _ _ x
  map_smul {U V} f h x := by
    refine (act.map_smul (U := op (unop U ⨯ D)) (V := op (unop V ⨯ D))
      (prod.map f.unop (𝟙 D)).op _ x).trans ?_
    congr 1
    exact (res_fst_map (𝒪 := 𝒪) D f.unop (T := unop U) (T' := unop V) h).symm

variable {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F) (N : AddSubmonoid M)

/-- The morphism `T' → I_{T'}` attached to `t : T' → I_T`. -/
noncomputable def graphMap {T T' : C} (t : T' ⟶ T ⨯ D) : T' ⟶ T' ⨯ D :=
  prod.lift (𝟙 T') (t ≫ prod.snd)

variable {D}

@[simp] lemma graphMap_fst {T T' : C} (t : T' ⟶ T ⨯ D) : graphMap D t ≫ prod.fst = 𝟙 T' :=
  prod.lift_fst _ _

lemma graphMap_map {T T' : C} (t : T' ⟶ T ⨯ D) :
    graphMap D t ≫ prod.map (t ≫ prod.fst) (𝟙 D) = t := by
  ext <;> simp [graphMap]

lemma graphMap_comp {T T' T'' : C} (s : T'' ⟶ T') (t : T' ⟶ T ⨯ D) :
    graphMap D (s ≫ t) ≫ prod.map s (𝟙 D) = s ≫ graphMap D t := by
  ext <;> simp [graphMap]

lemma res_graph_fst {P : Type*} [AddCommMonoid P] {T T' : C} (t : T' ⟶ T ⨯ D)
    (a : APt 𝒪 P (op T')) :
    APt.res (graphMap D t).op (APt.res (prod.fst : T' ⨯ D ⟶ T').op a) = a := by
  rw [← APt.res_comp, ← op_comp, graphMap_fst]
  exact APt.res_id a

lemma AttractorPt.app_congr {act : AAction 𝒪 M F} {N : AddSubmonoid M} {T T' : C}
    (φ : AttractorPt act N T) {t t' : T' ⟶ T} (h : t = t') {a a' : APt 𝒪 N (op T')} (h' : a = a') :
    φ.app t a = φ.app t' a' := by
  subst h h'; rfl

omit [HasBinaryProducts C] in
lemma map_map_eq (F : Cᵒᵖ ⥤ Type u) {A B B' Z : C} {f : B ⟶ A} {g : Z ⟶ B} {k : B' ⟶ A} {l : Z ⟶ B'}
    (e : g ≫ f = l ≫ k) (x : F.obj (op A)) :
    F.map g.op (F.map f.op x) = F.map l.op (F.map k.op x) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]

variable (D)

/-- The bijection of Proposition 16.2 on `T`-points. -/
noncomputable def tangentAttractorEquiv (T : C) :
    AttractorPt (tangentAction D act) N T ≃ AttractorPt act N (T ⨯ D) where
  toFun φ :=
    { app := fun {T'} t a => F.map (graphMap D t).op (φ.app (t ≫ prod.fst) a)
      naturality := fun {T' T''} s t a => by
        have h' : φ.app (s ≫ t ≫ prod.fst) (APt.res s.op a) =
            F.map (prod.map s (𝟙 D)).op (φ.app (t ≫ prod.fst) a) :=
          φ.naturality s (t ≫ prod.fst) a
        rw [show (s ≫ t) ≫ prod.fst = s ≫ t ≫ prod.fst from Category.assoc _ _ _, h']
        exact map_map_eq F (graphMap_comp s t) _
      equivariant := fun {T'} t h a => by
        have e' : φ.app (t ≫ prod.fst) (APt.toMagnet N h * a) =
            act.smul (U := op (T' ⨯ D)) (APt.res (prod.fst : T' ⨯ D ⟶ T').op h)
              (φ.app (t ≫ prod.fst) a) := φ.equivariant (t ≫ prod.fst) h a
        rw [e']
        refine (act.map_smul (graphMap D t).op _ _).trans ?_
        rw [res_graph_fst] }
  invFun ψ :=
    { app := fun {T'} t a => ψ.app (prod.map t (𝟙 D)) (APt.res (prod.fst : T' ⨯ D ⟶ T').op a)
      naturality := fun {T' T''} s t a => by
        have h := ψ.naturality (prod.map s (𝟙 D)) (prod.map t (𝟙 D))
          (APt.res (prod.fst : T' ⨯ D ⟶ T').op a)
        exact (ψ.app_congr (by simp) (res_fst_map D s a)).trans h
      equivariant := fun {T'} t h a => by
        have e := ψ.equivariant (prod.map t (𝟙 D)) (APt.res (prod.fst : T' ⨯ D ⟶ T').op h)
          (APt.res (prod.fst : T' ⨯ D ⟶ T').op a)
        refine Eq.trans (ψ.app_congr rfl ?_) e
        exact APt.res_mul _ _ _ }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change F.map (graphMap D (prod.map t (𝟙 D))).op
      (φ.app (prod.map t (𝟙 D) ≫ prod.fst) (APt.res (prod.fst : T' ⨯ D ⟶ T').op a)) = φ.app t a
    have h' : φ.app (prod.fst ≫ t) (APt.res (prod.fst : T' ⨯ D ⟶ T').op a) =
        F.map (prod.map (prod.fst : T' ⨯ D ⟶ T') (𝟙 D)).op (φ.app t a) :=
      φ.naturality (prod.fst : T' ⨯ D ⟶ T') t a
    rw [φ.app_congr (prod.map_fst t (𝟙 D)) rfl, h']
    have e : graphMap D (prod.map t (𝟙 D)) ≫ prod.map (prod.fst : T' ⨯ D ⟶ T') (𝟙 D) = 𝟙 _ := by
      ext <;> simp [graphMap]
    exact (map_map_eq F (l := 𝟙 _) (k := 𝟙 _) (by rw [e]; simp) _).trans (by
      rw [op_id, F.map_id]; rfl)
  right_inv ψ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change F.map (graphMap D t).op (ψ.app (prod.map (t ≫ prod.fst) (𝟙 D))
      (APt.res (prod.fst : T' ⨯ D ⟶ T').op a)) = ψ.app t a
    rw [← ψ.naturality]
    exact ψ.app_congr (graphMap_map t) (res_graph_fst t a)

lemma graphMap_comp_map {T T' T'' : C} (s : T ⟶ T'') (t : T' ⟶ T ⨯ D) :
    graphMap D (t ≫ prod.map s (𝟙 D)) = graphMap D t := by
  ext <;> simp [graphMap]

/-- **Proposition 16.2.** `(TX)^N = T(X^N)`, for any functor `X` with an action of `𝔸(M)`, in
particular of `D(M)` for `M` an abelian group. -/
noncomputable def tangentAttractorIso :
    attractor (tangentAction D act) N ≅ tangent D (attractor act N) :=
  NatIso.ofComponents (fun U => (tangentAttractorEquiv D act N (unop U)).toIso) (fun {U V} s => by
    ext φ
    refine AttractorPt.ext ?_
    funext T' t a
    change F.map (graphMap D t).op (AttractorPt.app (φ : AttractorPt _ N (unop U))
        ((t ≫ prod.fst) ≫ s.unop) a) =
      F.map (graphMap D (t ≫ prod.map s.unop (𝟙 D))).op
        (AttractorPt.app (φ : AttractorPt _ N (unop U))
        ((t ≫ prod.map s.unop (𝟙 D)) ≫ prod.fst) a)
    have e1 : ∀ t' : T' ⟶ unop V ⨯ D,
        (t' ≫ prod.fst) ≫ s.unop = (t' ≫ prod.map s.unop (𝟙 D)) ≫ prod.fst := fun t' => by simp
    refine (congrArg (F.map (graphMap D t).op) (AttractorPt.app_congr _ (e1 t) rfl)).trans ?_
    exact congrArg (fun g => F.map (Quiver.Hom.op g) _) (graphMap_comp_map D s.unop t).symm)

end AlgMag
