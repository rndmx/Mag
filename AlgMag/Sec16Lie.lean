/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec16Tangent
import AlgMag.Sec2Monoids
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Lie algebras, semidirect products and root groups (Algebraic Magnetism, §16.2, §16.3, §16.6)

Everything is proved for group functors on a category with binary products, with an action of
`𝔸(M)` by group endomorphisms; this contains `D(M)_S` acting by automorphisms on an `S`-group
functor. See `AlgMag.Sec16Scheme` for `Sch/S`.
-/

open CategoryTheory Opposite Limits

universe w w' v u

set_option linter.unusedSectionVars false

namespace AlgMag

/-! ### Group functors -/

/-- A group functor on `C`. -/
structure GrpFunctor (C : Type*) [Category.{v} C] where
  /-- The underlying functor. -/
  F : Cᵒᵖ ⥤ Type w
  /-- The group structure on points. -/
  grp : ∀ U, Group (F.obj U)
  map_mul : ∀ {U V : Cᵒᵖ} (s : U ⟶ V) (x y : F.obj U), F.map s (x * y) = F.map s x * F.map s y

attribute [instance] GrpFunctor.grp

variable {C : Type*} [Category.{v} C]

lemma GrpFunctor.map_one (G : GrpFunctor.{w} C) {U V : Cᵒᵖ} (s : U ⟶ V) : G.F.map s 1 = 1 :=
  (MonoidHom.mk' (G.F.map s) (G.map_mul s)).map_one

/-- The underlying monoid functor. -/
theorem GrpFunctor.isMonoidFunctor (G : GrpFunctor.{u} C) : IsMonoidFunctor G.F :=
  ⟨G.map_one, G.map_mul⟩

/-- A morphism of group functors. -/
structure GrpMor (G H : GrpFunctor.{w} C) where
  /-- The underlying morphism of functors. -/
  hom : G.F ⟶ H.F
  map_mul : ∀ {U : Cᵒᵖ} (x y : G.F.obj U), hom.app U (x * y) = hom.app U x * hom.app U y

lemma GrpMor.map_one {G H : GrpFunctor.{w} C} (f : GrpMor G H) {U : Cᵒᵖ} : f.hom.app U 1 = 1 :=
  (MonoidHom.mk' (f.hom.app U) f.map_mul).map_one

lemma GrpMor.map_inv {G H : GrpFunctor.{w} C} (f : GrpMor G H) {U : Cᵒᵖ} (x : G.F.obj U) :
    f.hom.app U x⁻¹ = (f.hom.app U x)⁻¹ :=
  _root_.map_inv (MonoidHom.mk' (f.hom.app U) f.map_mul) x

/-- Composition of morphisms of group functors. -/
def GrpMor.comp {G H K : GrpFunctor.{w} C} (f : GrpMor G H) (g : GrpMor H K) : GrpMor G K where
  hom := f.hom ≫ g.hom
  map_mul {U} x y := by
    change g.hom.app U (f.hom.app U (x * y)) = g.hom.app U (f.hom.app U x) * g.hom.app U (f.hom.app U y)
    rw [f.map_mul, g.map_mul]

/-- An isomorphism of group functors. -/
structure GrpIso (G H : GrpFunctor.{w} C) where
  /-- The underlying isomorphism of functors. -/
  iso : G.F ≅ H.F
  map_mul : ∀ {U : Cᵒᵖ} (x y : G.F.obj U), iso.hom.app U (x * y) = iso.hom.app U x * iso.hom.app U y

/-- The morphism underlying an isomorphism. -/
def GrpIso.toMor {G H : GrpFunctor.{w} C} (e : GrpIso G H) : GrpMor G H := ⟨e.iso.hom, e.map_mul⟩

lemma GrpIso.hom_inv {G H : GrpFunctor.{w} C} (e : GrpIso G H) {U : Cᵒᵖ} (x : G.F.obj U) :
    e.iso.inv.app U (e.iso.hom.app U x) = x :=
  hom_app_congr e.iso.hom_inv_id U x

lemma GrpIso.inv_hom {G H : GrpFunctor.{w} C} (e : GrpIso G H) {U : Cᵒᵖ} (x : H.F.obj U) :
    e.iso.hom.app U (e.iso.inv.app U x) = x :=
  hom_app_congr e.iso.inv_hom_id U x

/-- The inverse morphism of an isomorphism. -/
def GrpIso.invMor {G H : GrpFunctor.{w} C} (e : GrpIso G H) : GrpMor H G where
  hom := e.iso.inv
  map_mul {U} x y := by
    have := e.map_mul (e.iso.inv.app U x) (e.iso.inv.app U y)
    rw [e.inv_hom, e.inv_hom] at this
    rw [← this, e.hom_inv]

/-- Composition of isomorphisms of group functors. -/
def GrpIso.trans {G H K : GrpFunctor.{w} C} (e : GrpIso G H) (e' : GrpIso H K) : GrpIso G K where
  iso := e.iso ≪≫ e'.iso
  map_mul := (e.toMor.comp e'.toMor).map_mul

/-- The trivial group functor `e_S`. -/
def trivialGrp (C : Type*) [Category.{v} C] : GrpFunctor.{w} C where
  F := (Functor.const _).obj PUnit
  grp _ := inferInstanceAs (Group PUnit)
  map_mul _ _ _ := rfl

/-- The canonical morphism `e_S → G`. -/
def unitMor (G : GrpFunctor.{w} C) : GrpMor (trivialGrp C) G where
  hom := { app := fun _ => ↾ fun _ => 1, naturality := fun {U V} s => by
            ext x; exact (G.map_one s).symm }
  map_mul {U} _ _ := (mul_one (1 : G.F.obj U)).symm

/-- The fibre product of group functors. -/
def fibreGrp {A B E : GrpFunctor.{w} C} (f : GrpMor A B) (g : GrpMor E B) : GrpFunctor.{w} C where
  F := fibreProduct f.hom g.hom
  grp U :=
    { mul := fun p q => ⟨(p.1.1 * q.1.1, p.1.2 * q.1.2), by
        change f.hom.app U _ = g.hom.app U _
        rw [f.map_mul, g.map_mul, p.2, q.2]⟩
      one := ⟨(1, 1), by
        change f.hom.app U 1 = g.hom.app U 1
        rw [f.map_one, g.map_one]⟩
      inv := fun p => ⟨(p.1.1⁻¹, p.1.2⁻¹), by
        change f.hom.app U _ = g.hom.app U _
        rw [f.map_inv, g.map_inv, p.2]⟩
      mul_assoc := fun p q r => Subtype.ext (Prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _))
      one_mul := fun p => Subtype.ext (Prod.ext (one_mul _) (one_mul _))
      mul_one := fun p => Subtype.ext (Prod.ext (mul_one _) (mul_one _))
      inv_mul_cancel := fun p => Subtype.ext (Prod.ext (inv_mul_cancel _) (inv_mul_cancel _)) }
  map_mul s p q := Subtype.ext (Prod.ext (A.map_mul s _ _) (E.map_mul s _ _))

/-! ### Lie algebras -/

lemma map_map_eq' (F : Cᵒᵖ ⥤ Type w) {A B B' Z : C} {f : B ⟶ A} {g : Z ⟶ B} {k : B' ⟶ A}
    {l : Z ⟶ B'} (e : g ≫ f = l ≫ k) (x : F.obj (op A)) :
    F.map g.op (F.map f.op x) = F.map l.op (F.map k.op x) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]

variable [HasBinaryProducts C] {D : C}

/-- The zero section of the dual numbers: a family of points of `I_S`, natural in `T`. -/
structure DualPoint (D : C) where
  /-- The point. -/
  o : ∀ T : C, T ⟶ D
  comp_o : ∀ {T T' : C} (s : T' ⟶ T), s ≫ o T = o T'

/-- The zero section `T → I_T`. -/
noncomputable def DualPoint.zero (p : DualPoint D) (T : C) : T ⟶ T ⨯ D := prod.lift (𝟙 T) (p.o T)

lemma DualPoint.zero_map (p : DualPoint D) {T T' : C} (s : T' ⟶ T) :
    p.zero T' ≫ prod.map s (𝟙 D) = s ≫ p.zero T := by
  ext <;> simp [DualPoint.zero, p.comp_o]

lemma DualPoint.zero_fst (p : DualPoint D) (T : C) : p.zero T ≫ prod.fst = 𝟙 T := prod.lift_fst _ _

lemma DualPoint.graph_comp (p : DualPoint D) {T T' : C} (t : T' ⟶ T) :
    graphMap D (t ≫ p.zero T) = p.zero T' := by
  ext <;> simp [graphMap, DualPoint.zero, p.comp_o]

variable (D) in
/-- **§16.2.** `TG` is a group functor. -/
noncomputable def tangentGrp (G : GrpFunctor.{w} C) : GrpFunctor.{w} C where
  F := tangent D G.F
  grp U := G.grp ((dualF D).op.obj U)
  map_mul s x y := G.map_mul ((dualF D).op.map s) x y

/-- `Tf` for a morphism of group functors. -/
noncomputable def tangentMor {G H : GrpFunctor.{w} C} (f : GrpMor G H) :
    GrpMor (tangentGrp D G) (tangentGrp D H) where
  hom := tangentMap D f.hom
  map_mul {U} x y := f.map_mul (U := (dualF D).op.obj U) x y

/-- **§16.2.** The canonical morphism of group functors `TG → G`, by the zero section. -/
noncomputable def redMor (p : DualPoint D) (G : GrpFunctor.{w} C) : GrpMor (tangentGrp D G) G where
  hom :=
    { app := fun U => ↾ fun x => G.F.map (p.zero (unop U)).op x
      naturality := fun {U V} s => by
        ext x
        exact map_map_eq' G.F (p.zero_map s.unop) x }
  map_mul {U} x y := G.map_mul (p.zero (unop U)).op x y

/-- **§16.2.** `Lie(G) = e_S ×_G TG`. -/
noncomputable def Lie (p : DualPoint D) (G : GrpFunctor.{w} C) : GrpFunctor.{w} C :=
  fibreGrp (unitMor G) (redMor p G)

/-- The underlying element of `TG` of a point of `Lie(G)`. -/
noncomputable def Lie.val {p : DualPoint D} {G : GrpFunctor.{w} C} {U : Cᵒᵖ} (x : (Lie p G).F.obj U) :
    G.F.obj ((dualF D).op.obj U) := x.1.2

lemma Lie.prop {p : DualPoint D} {G : GrpFunctor.{w} C} {U : Cᵒᵖ} (x : (Lie p G).F.obj U) :
    G.F.map (p.zero (unop U)).op (Lie.val x) = 1 := x.2.symm

/-- A point of `Lie(G)` from an element of `TG` reducing to the unit. -/
noncomputable def Lie.mk {p : DualPoint D} {G : GrpFunctor.{w} C} {U : Cᵒᵖ}
    (x : G.F.obj ((dualF D).op.obj U)) (h : G.F.map (p.zero (unop U)).op x = 1) :
    (Lie p G).F.obj U := ⟨(PUnit.unit, x), h.symm⟩

lemma Lie.ext' {p : DualPoint D} {G : GrpFunctor.{w} C} {U : Cᵒᵖ} {x y : (Lie p G).F.obj U}
    (h : Lie.val x = Lie.val y) : x = y :=
  Subtype.ext (Prod.ext rfl h)

/-- `Lie(f)`. -/
noncomputable def lieMor (p : DualPoint D) {G H : GrpFunctor.{w} C} (f : GrpMor G H) :
    GrpMor (Lie p G) (Lie p H) where
  hom :=
    { app := fun U => ↾ fun x => Lie.mk (f.hom.app _ (Lie.val x)) (by
        have := hom_naturality_apply f.hom (p.zero (unop U)).op (Lie.val x)
        refine this.symm.trans ?_
        rw [Lie.prop, f.map_one])
      naturality := fun {U V} s => by
        ext x
        exact Lie.ext' (hom_naturality_apply f.hom ((dualF D).op.map s) (Lie.val x)) }
  map_mul {U} x y := Lie.ext' (f.map_mul (U := (dualF D).op.obj U) (Lie.val x) (Lie.val y))

/-- **Remark 16.3 (ii).** `G → H` mono implies `Lie(G) → Lie(H)` mono. -/
theorem mono_lieMor (p : DualPoint D) {G H : GrpFunctor.{w} C} (f : GrpMor G H) [Mono f.hom] :
    Mono (lieMor p f).hom := by
  refine (NatTrans.mono_iff_mono_app _).2 fun U => (mono_iff_injective _).2 fun x y h => ?_
  have hm : Mono (f.hom.app ((dualF D).op.obj U)) :=
    (NatTrans.mono_iff_mono_app f.hom).1 inferInstance _
  have e : f.hom.app _ (Lie.val x) = f.hom.app _ (Lie.val y) :=
    congrArg (Lie.val (p := p) (G := H)) h
  exact Lie.ext' ((mono_iff_injective _).1 hm e)

/-- **Remark 16.3 (iii).** `Lie(e_S) = e_S`. -/
noncomputable def lieTrivialIso (p : DualPoint D) :
    GrpIso (Lie p (trivialGrp.{w} C)) (trivialGrp.{w} C) where
  iso := NatIso.ofComponents (fun U =>
    { hom := ↾ fun _ => PUnit.unit
      inv := ↾ fun _ => Lie.mk (p := p) (G := trivialGrp.{w} C) (U := U) PUnit.unit rfl
      hom_inv_id := by ext x; exact Lie.ext' rfl
      inv_hom_id := rfl }) (fun _ => rfl)
  map_mul _ _ := rfl

/-- **Remark 16.3 (i).** `Lie(G ×_K H) = Lie(G) ×_{Lie(K)} Lie(H)`. -/
noncomputable def lieFibreIso (p : DualPoint D) {G K H : GrpFunctor.{w} C} (f : GrpMor G K)
    (g : GrpMor H K) :
    GrpIso (Lie p (fibreGrp f g)) (fibreGrp (lieMor p f) (lieMor p g)) where
  iso := NatIso.ofComponents (fun U =>
    { hom := ↾ fun x =>
        have h1 := congrArg Prod.fst (congrArg Subtype.val (Lie.prop x))
        have h2 := congrArg Prod.snd (congrArg Subtype.val (Lie.prop x))
        ⟨(Lie.mk (p := p) (Lie.val x).1.1 h1, Lie.mk (p := p) (Lie.val x).1.2 h2),
          Lie.ext' (Lie.val x).2⟩
      inv := ↾ fun y => Lie.mk (p := p) (G := fibreGrp f g)
        ⟨(Lie.val y.1.1, Lie.val y.1.2), congrArg (Lie.val (p := p) (G := K)) y.2⟩
        (Subtype.ext (Prod.ext (Lie.prop y.1.1) (Lie.prop y.1.2)))
      hom_inv_id := by ext x; exact Lie.ext' rfl
      inv_hom_id := by
        ext y
        exact Subtype.ext (Prod.ext (Lie.ext' rfl) (Lie.ext' rfl)) })
    (fun {U V} s => by
      ext x
      exact Subtype.ext (Prod.ext (Lie.ext' rfl) (Lie.ext' rfl)))
  map_mul _ _ := Subtype.ext (Prod.ext (Lie.ext' rfl) (Lie.ext' rfl))

/-! ### Attractors of group functors -/

variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommMonoid M]

/-- **Proposition 3.14 (ii)** as a group functor: the attractor `G^N`. -/
noncomputable def attrGrp (G : GrpFunctor.{u} C) (act : AAction 𝒪 M G.F) (ha : ActsByMonoidEnd act)
    (N : AddSubmonoid M) : GrpFunctor C where
  F := attractor act N
  grp T := attractorGroup N G.isMonoidFunctor ha (unop T)
  map_mul _ _ _ := rfl

/-- The face morphism `G^N → G^L` as a morphism of group functors (§16.3, cf. Fact 3.15). -/
noncomputable def faceMor {G : GrpFunctor.{u} C} (act : AAction 𝒪 M G.F) (ha : ActsByMonoidEnd act)
    {L N : AddSubmonoid M} (hL : IsFace L N) : GrpMor (attrGrp G act ha N) (attrGrp G act ha L) where
  hom := faceMap act hL
  map_mul _ _ := rfl

/-- The inclusion `G^L → G^N` as a morphism of group functors (§16.3, cf. Fact 3.10). -/
noncomputable def magnetMor {G : GrpFunctor.{u} C} (act : AAction 𝒪 M G.F) (ha : ActsByMonoidEnd act)
    {L N : AddSubmonoid M} (h : L ≤ N) : GrpMor (attrGrp G act ha L) (attrGrp G act ha N) where
  hom := magnetMap act h
  map_mul _ _ := rfl

variable (p : DualPoint D) {G : GrpFunctor.{u} C} (act : AAction 𝒪 M G.F) (ha : ActsByMonoidEnd act)
  (N : AddSubmonoid M)

include ha

lemma smul_lie_prop {U : Cᵒᵖ} (h : APt 𝒪 M U) (x : G.F.obj ((dualF D).op.obj U))
    (hx : G.F.map (p.zero (unop U)).op x = 1) :
    G.F.map (p.zero (unop U)).op ((tangentAction D act).smul h x) = 1 := by
  refine (act.map_smul (U := op (unop U ⨯ D)) (p.zero (unop U)).op _ x).trans ?_
  rw [hx, ← APt.res_comp, ← op_comp, p.zero_fst]
  exact ha.smul_one _

/-- **§16.2.** The induced action of `D(M)_S` on `Lie(G)`. -/
noncomputable def lieAction : AAction 𝒪 M (Lie p G).F where
  smul {U} h x := Lie.mk (p := p) ((tangentAction D act).smul h (Lie.val x))
    (smul_lie_prop p act ha h _ (Lie.prop x))
  one_smul x := Lie.ext' ((tangentAction D act).one_smul _)
  mul_smul g h x := Lie.ext' ((tangentAction D act).mul_smul _ _ _)
  map_smul s h x := Lie.ext' ((tangentAction D act).map_smul _ _ _)

/-- **§16.2.** `D(M)_S` acts on `Lie(G)` by group endomorphisms. -/
theorem actsByMonoidEnd_lie : ActsByMonoidEnd (lieAction p act ha) where
  smul_one h := Lie.ext' (ha.smul_one _)
  smul_mul h x y := Lie.ext' (ha.smul_mul _ _ _)

/-- `Lie(G) → TG` is equivariant. -/
noncomputable def lieVal : EquivariantHom (lieAction p act ha) (tangentAction D act) where
  hom := { app := fun _ => ↾ Lie.val, naturality := fun _ _ _ => rfl }
  map_smul _ _ := rfl

/-- The bijection of Proposition 16.4 on points. -/
noncomputable def lieAttractorEquiv (T : C) :
    AttractorPt (lieAction p act ha) N T ≃ (Lie p (attrGrp G act ha N)).F.obj (op T) where
  toFun φ := Lie.mk (p := p) (G := attrGrp G act ha N)
    (tangentAttractorEquiv D act N T (AttractorPt.push (lieVal p act ha) φ)) (by
      refine AttractorPt.ext ?_
      funext T' t a
      change G.F.map (graphMap D (t ≫ p.zero T)).op
        (Lie.val (φ.app ((t ≫ p.zero T) ≫ prod.fst) a)) = 1
      rw [p.graph_comp]
      exact Lie.prop _)
  invFun y :=
    let φt := (tangentAttractorEquiv D act N T).symm (Lie.val y)
    { app := fun {T'} t a => Lie.mk (φt.app t a) (by
        have hy : AttractorPt.app ((attrGrp G act ha N).F.map (p.zero T).op (Lie.val y)) t a = 1 := by
          rw [Lie.prop y]; rfl
        have hn := AttractorPt.naturality (Lie.val y) (p.zero T') (prod.map t (𝟙 D))
          (APt.res (prod.fst : T' ⨯ D ⟶ T').op a)
        refine hn.symm.trans (Eq.trans (AttractorPt.app_congr _ (p.zero_map t) ?_) hy)
        rw [← APt.res_comp, ← op_comp, p.zero_fst]
        exact APt.res_id a)
      naturality := fun s t a => Lie.ext' (φt.naturality s t a)
      equivariant := fun t h a => Lie.ext' (φt.equivariant t h a) }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    exact Lie.ext' (congrArg (fun χ => AttractorPt.app χ t a)
      ((tangentAttractorEquiv D act N T).left_inv (AttractorPt.push (lieVal p act ha) φ)))
  right_inv y := Lie.ext' ((tangentAttractorEquiv D act N T).right_inv (Lie.val y))

/-- **Proposition 16.4.** `Lie(G)^N = Lie(G^N)` as group functors. -/
noncomputable def lieAttractorIso :
    GrpIso (attrGrp (Lie p G) (lieAction p act ha) (actsByMonoidEnd_lie p act ha) N)
      (Lie p (attrGrp G act ha N)) where
  iso := NatIso.ofComponents (fun U => (lieAttractorEquiv p act ha N (unop U)).toIso)
    (fun {U V} s => by
      ext φ
      refine Lie.ext' ?_
      exact ConcreteCategory.congr_hom ((tangentAttractorIso D act N).hom.naturality s)
        (AttractorPt.push (lieVal p act ha) φ))
  map_mul {U} φ ψ := by
    refine Lie.ext' (AttractorPt.ext ?_)
    funext T' t a
    exact G.map_mul (graphMap D t).op _ _

omit ha in
/-- Congruence of fibre products of group functors. -/
noncomputable def fibreGrpCongr {A A' B B' E : GrpFunctor.{w} C} {f : GrpMor A B} {g : GrpMor E B}
    {f' : GrpMor A' B'} {g' : GrpMor E B'} (a : GrpIso A A') (b : GrpIso B B')
    (hf : ∀ {U} (x : A.F.obj U), b.iso.hom.app U (f.hom.app U x) = f'.hom.app U (a.iso.hom.app U x))
    (hg : ∀ {U} (y : E.F.obj U), b.iso.hom.app U (g.hom.app U y) = g'.hom.app U y) :
    GrpIso (fibreGrp f g) (fibreGrp f' g') where
  iso := NatIso.ofComponents (fun U =>
    { hom := ↾ fun x => ⟨(a.iso.hom.app U x.1.1, x.1.2), by
        change f'.hom.app U _ = g'.hom.app U _
        rw [← hf, ← hg]
        exact congrArg (b.iso.hom.app U) x.2⟩
      inv := ↾ fun y => ⟨(a.iso.inv.app U y.1.1, y.1.2), by
        change f.hom.app U _ = g.hom.app U _
        have h : b.iso.hom.app U (f.hom.app U (a.iso.inv.app U y.1.1)) =
            b.iso.hom.app U (g.hom.app U y.1.2) := by
          rw [hf, hg, a.inv_hom]; exact y.2
        have := congrArg (b.iso.inv.app U) h
        rwa [b.hom_inv, b.hom_inv] at this⟩
      hom_inv_id := by
        ext x
        exact Subtype.ext (Prod.ext (a.hom_inv _) rfl)
      inv_hom_id := by
        ext y
        exact Subtype.ext (Prod.ext (a.inv_hom _) rfl) })
    (fun {U V} s => by
      ext x
      exact Subtype.ext (Prod.ext (hom_naturality_apply a.iso.hom s x.1.1) rfl))
  map_mul _ _ := Subtype.ext (Prod.ext (a.map_mul _ _) rfl)

/-- `Lie(G)^L` receives `Lie(H)` for `H → G^L`, through Proposition 16.4. -/
noncomputable def lieLimitMor {L : AddSubmonoid M} {H : GrpFunctor C} (j : GrpMor H (attrGrp G act ha L)) :
    GrpMor (Lie p H) (attrGrp (Lie p G) (lieAction p act ha) (actsByMonoidEnd_lie p act ha) L) :=
  (lieMor p j).comp (lieAttractorIso p act ha L).invMor

lemma lieAttractorIso_face {L : AddSubmonoid M} (hL : IsFace L N) {U : Cᵒᵖ}
    (φ : (attrGrp (Lie p G) (lieAction p act ha) (actsByMonoidEnd_lie p act ha) N).F.obj U) :
    (lieAttractorIso p act ha L).iso.hom.app U
        ((faceMor (lieAction p act ha) (actsByMonoidEnd_lie p act ha) hL).hom.app U φ) =
      (lieMor p (faceMor act ha hL)).hom.app U ((lieAttractorIso p act ha N).iso.hom.app U φ) := by
  refine Lie.ext' (AttractorPt.ext ?_)
  funext T' t a
  rfl

/-- **Proposition 16.5.** `Lie(G)^N_{Lie(H)} = Lie(G^N_H)` as group functors, for a face `L` of `N`
(the paper's case is `L = N^×`, see `unitsIsFace`) and `H → G^L`, where by Proposition 4.2
`X^N_{L,Z} = X^N ×_{X^L} Z`. The monomorphism assumption of the paper is not needed. -/
noncomputable def lieAttractorLimitIso {L : AddSubmonoid M} (hL : IsFace L N) {H : GrpFunctor C}
    (j : GrpMor H (attrGrp G act ha L)) :
    GrpIso
      (fibreGrp (faceMor (lieAction p act ha) (actsByMonoidEnd_lie p act ha) hL)
        (lieLimitMor p act ha j))
      (Lie p (fibreGrp (faceMor act ha hL) j)) :=
  GrpIso.trans (fibreGrpCongr (f := faceMor (lieAction p act ha) (actsByMonoidEnd_lie p act ha) hL) (g := lieLimitMor p act ha j) (f' := lieMor p (faceMor act ha hL)) (g' := lieMor p j)
    (lieAttractorIso p act ha N) (lieAttractorIso p act ha L)
    (fun φ => lieAttractorIso_face p act ha N hL φ)
    (fun {U} y => (lieAttractorIso p act ha L).inv_hom _))
    { iso := (lieFibreIso p (faceMor act ha hL) j).iso.symm
      map_mul := (lieFibreIso p (faceMor act ha hL) j).invMor.map_mul }

omit ha in
/-- **Proposition 2.17.** `N^×` is a face of `N`. -/
theorem unitsIsFace (N : AddSubmonoid M) : IsFace (unitsFace N) N :=
  ⟨unitsFace_le N, fun hx hy h => faceCond_unitsFace N _ hx _ hy h⟩

/-! ### Semidirect products (§16.3) -/

omit ha in
/-- A group with a split surjection is a semidirect product. -/
noncomputable def semidirectOfSection {A B : Type*} [Group A] [Group B] (q : A →* B) (s : B →* A)
    (hs : ∀ b, q (s b) = b) :
    A ≃* q.ker ⋊[(MulAut.conjNormal (H := q.ker)).comp s] B where
  toFun a := ⟨⟨a * s (q a)⁻¹, by simp [MonoidHom.mem_ker, hs]⟩, q a⟩
  invFun x := x.1 * s x.2
  left_inv a := by simp
  right_inv x := by
    have hk : q (x.1 : A) = 1 := x.1.2
    refine SemidirectProduct.ext ?_ ?_
    · refine Subtype.ext ?_
      simp [hk, hs]
    · simp [hk, hs]
  map_mul' a b := by
    refine SemidirectProduct.ext ?_ ?_
    · refine Subtype.ext ?_
      simp [mul_assoc, MulAut.conjNormal_apply]
    · simp

variable {L : AddSubmonoid M} (hL : IsFace L N)

/-- The kernel `G^N_{e_G}` of `G^N → G^L`: the attractor with prescribed limit the unit (§16.3). -/
noncomputable def attrKernel : GrpFunctor C :=
  fibreGrp (faceMor act ha hL) (unitMor (attrGrp G act ha L))

/-- The morphism `G^N(T) → G^L(T)` of §16.3. -/
noncomputable def faceHom (T : Cᵒᵖ) : (attrGrp G act ha N).F.obj T →* (attrGrp G act ha L).F.obj T :=
  MonoidHom.mk' ((faceMor act ha hL).hom.app T) (faceMor act ha hL).map_mul

/-- The morphism `G^L(T) → G^N(T)` of §16.3. -/
noncomputable def magnetHom (T : Cᵒᵖ) : (attrGrp G act ha L).F.obj T →* (attrGrp G act ha N).F.obj T :=
  MonoidHom.mk' ((magnetMor act ha hL.le).hom.app T) (magnetMor act ha hL.le).map_mul

lemma faceHom_magnetHom (T : Cᵒᵖ) (x : (attrGrp G act ha L).F.obj T) :
    faceHom act ha N hL T (magnetHom act ha N hL T x) = x :=
  hom_app_congr (magnetMap_comp_faceMap act hL) T x

/-- **Proposition 16.6.** `G^N` is the semidirect product of `G^N_{e_G} = ker(G^N → G^L)` and `G^L`,
functorially in `T`, for any group functor `G` and any face `L` of `N`, in particular `L = N^×`
(`unitsIsFace`). -/
noncomputable def attrSemidirect (T : Cᵒᵖ) :
    (attrGrp G act ha N).F.obj T ≃*
      (faceHom act ha N hL T).ker ⋊[(MulAut.conjNormal (H := (faceHom act ha N hL T).ker)).comp
        (magnetHom act ha N hL T)] (attrGrp G act ha L).F.obj T :=
  semidirectOfSection _ _ (faceHom_magnetHom act ha N hL T)

/-- The multiplication map on points. -/
noncomputable def attrMulEquiv (T : Cᵒᵖ) :
    (attrKernel act ha N hL).F.obj T × (attrGrp G act ha L).F.obj T ≃ (attrGrp G act ha N).F.obj T where
  toFun x := x.1.1.1 * magnetHom act ha N hL T x.2
  invFun y :=
    (⟨(y * magnetHom act ha N hL T (faceHom act ha N hL T y)⁻¹, PUnit.unit), by
      change faceHom act ha N hL T _ = 1
      simp [faceHom_magnetHom]⟩, faceHom act ha N hL T y)
  left_inv x := by
    have hk : faceHom act ha N hL T x.1.1.1 = 1 := x.1.2
    refine Prod.ext (Subtype.ext (Prod.ext ?_ rfl)) ?_
    · simp [hk, faceHom_magnetHom]
    · simp [hk, faceHom_magnetHom]
  right_inv y := by simp

/-- **Proposition 16.6**, "in particular": the multiplication map
`G^N_{e_G} × G^L → G^N` is an isomorphism of functors. -/
noncomputable def attrMulIso :
    prodFunctor (attrKernel act ha N hL).F (attrGrp G act ha L).F ≅ (attrGrp G act ha N).F :=
  NatIso.ofComponents (fun T => (attrMulEquiv act ha N hL T).toIso) (fun {U V} s => by
    ext x
    exact ((attrGrp G act ha N).map_mul s x.1.1.1 (magnetHom act ha N hL U x.2)).symm)

/-! ### Root groups (§16.6) -/

/-- **Definition 16.14.** The root group `G^{[α⟩}` attached to `α` (in the magnet language: the
attractor of the monoid generated by `α`). -/
noncomputable def rootAttr (α : M) : GrpFunctor C :=
  attrGrp G act ha (AddSubmonoid.closure {α})

/-- **Definition 16.14.** The attractor `G^{[α⟩}_{e_S}` with prescribed limit the trivial subgroup,
relatively to the face `[α⟩^×`. -/
noncomputable def rootKernel (α : M) : GrpFunctor C :=
  attrKernel act ha (AddSubmonoid.closure {α}) (unitsIsFace _)

/-- **Proposition 16.15 (iii)**, second isomorphism: `Lie(G^{[α⟩}) = Lie(G)^{[α⟩}`. -/
noncomputable def lieRootAttrIso (α : M) :
    GrpIso (rootAttr (lieAction p act ha) (actsByMonoidEnd_lie p act ha) α)
      (Lie p (rootAttr act ha α)) :=
  lieAttractorIso p act ha _

/-- **Proposition 16.15 (iii)**, first isomorphism: `Lie(G^{[α⟩}_{e_S}) = Lie(G)^{[α⟩}_{e_S}`, where
the right-hand side is the attractor with prescribed limit `Lie(e_S)`, identified with `e_S` by
`lieTrivialIso`. -/
noncomputable def lieRootKernelIso (α : M) :
    GrpIso
      (fibreGrp (faceMor (lieAction p act ha) (actsByMonoidEnd_lie p act ha)
          (unitsIsFace (AddSubmonoid.closure {α})))
        (lieLimitMor p act ha (unitMor (attrGrp G act ha (unitsFace (AddSubmonoid.closure {α}))))))
      (Lie p (rootKernel act ha α)) :=
  lieAttractorLimitIso p act ha _ (unitsIsFace _) _

end AlgMag
