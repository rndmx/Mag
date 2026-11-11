/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalProp91

/-!
# Proposition 9.1 of *Algebraic Magnetism* as an isomorphism of presheaves on the affine base

`tenF` is `T ↦ 𝒜(T) ⊗_{𝒪(T)} G(T)` on the affine objects of the site of `B`, a base of the site; `pushF` is
`f_* f^* G` on the whole site. `prop91_natIso` is the printed canonical morphism as a natural isomorphism from `tenF`
to the restriction of `pushF`. A sheaf is determined by its restriction to a base, so this is the printed identity
`f_* f^* F = F ⊗ 𝒜`, where the tensor product is the sheaf with these values on affine objects.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace AlgMag.FinalMisc

open AlgMag.S9B AlgMag.S9BF AlgMag.S9BS AlgMag.S9BR AlgMag.S9BP AlgMag.B2 AlgMag.Final
open AlgMag.S9 (PMod)

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} {G : PMod (OB Bsp)} {X : (SB Bsp)ᵒᵖ ⥤ Type u}

variable (Bsp) in
/-- The affine objects of the site of `B`. -/
abbrev AffC : Type _ := ObjectProperty.FullSubcategory (fun T : SB Bsp => IsAffine T.left)

instance (T : AffC Bsp) : IsAffine T.obj.left := T.property

variable (X G) in
/-- `f_* f^* G` as a presheaf on the site of `B`. -/
def pushF : (SB Bsp)ᵒᵖ ⥤ Type (u + 1) where
  obj T := PushSec X G T.unop
  map s := ↾ fun σ => pushRes s.unop σ
  map_id T := by
    ext σ W t x
    change σ.val (t ≫ 𝟙 _) x = _
    rw [Category.comp_id]
    rfl
  map_comp s s' := by
    ext σ W t x
    change σ.val (t ≫ s'.unop ≫ s.unop) x = σ.val ((t ≫ s'.unop) ≫ s.unop) x
    rw [Category.assoc]

/-- The pullback `(s ×_B X)^* : 𝒜(T) → 𝒜(T')`. -/
def rhoA (r : AffOver X) {T T' : SB Bsp} [IsAffine T.left] [IsAffine T'.left] (s : T' ⟶ T) :
    (OB Bsp).obj (op (r.P T)) →+* (OB Bsp).obj (op (r.P T')) :=
  ((OB Bsp).map (r.lift (r.pr T' ≫ s) (r.univ T')).op).hom

lemma rhoA_pr (r : AffOver X) {T T' : SB Bsp} [IsAffine T.left] [IsAffine T'.left] (s : T' ⟶ T)
    (c : (OB Bsp).obj (op T)) :
    rhoA r s (((OB Bsp).map (r.pr T).op).hom c) =
      ((OB Bsp).map (r.pr T').op).hom (((OB Bsp).map s.op).hom c) := by
  have e : r.lift (r.pr T' ≫ s) (r.univ T') ≫ r.pr T = r.pr T' ≫ s := r.lift_pr _ _
  have e2 := congrArg (fun k => ((OB Bsp).map k.op).hom c) e
  simp only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply] at e2
  exact e2

/-- The restriction of `𝒜 ⊗ G` along `s`, `a ⊗ g ↦ (s ×_B X)^* a ⊗ s^* g`. -/
def tensRes (r : AffOver X) {T T' : SB Bsp} [IsAffine T.left] [IsAffine T'.left] (s : T' ⟶ T) :
    TensAt r G T →+ TensAt r G T' :=
  letI := ((OB Bsp).map (r.pr T).op).hom.toAlgebra
  letI := ((OB Bsp).map (r.pr T').op).hom.toAlgebra
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun g => rhoA r s a ⊗ₜ G.map s.op g
          map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
          map_add' := fun g g' => by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by
        ext g
        simp only [map_zero, TensorProduct.zero_tmul]
        rfl
      map_add' := fun a a' => by
        ext g
        simp only [map_add, TensorProduct.add_tmul]
        rfl }
    (fun c a g => by
      change rhoA r s (c • a) ⊗ₜ G.map s.op g = rhoA r s a ⊗ₜ G.map s.op (c • g)
      rw [G.map_smul, Algebra.smul_def, map_mul]
      change (rhoA r s (((OB Bsp).map (r.pr T).op).hom c) * rhoA r s a) ⊗ₜ _ = _
      rw [rhoA_pr, TensorProduct.tmul_smul]
      exact (congrArg (· ⊗ₜ _) (Algebra.smul_def _ _).symm).trans (TensorProduct.smul_tmul' _ _ _).symm)

lemma tensRes_tmul (r : AffOver X) {T T' : SB Bsp} [IsAffine T.left] [IsAffine T'.left] (s : T' ⟶ T)
    (a : (OB Bsp).obj (op (r.P T))) (g : G.obj (op T)) :
    tensRes r s (tmulAt r T a g) = tmulAt r T' (rhoA r s a) (G.map s.op g) := rfl

lemma ten_induction (r : AffOver X) (T : SB Bsp) [IsAffine T.left] {p : TensAt r G T → Prop}
    (h0 : p 0) (h1 : ∀ a g, p (tmulAt r T a g)) (h2 : ∀ x y, p x → p y → p (x + y)) (x : TensAt r G T) : p x :=
  letI := ((OB Bsp).map (r.pr T).op).hom.toAlgebra
  TensorProduct.induction_on x h0 h1 h2

variable (G) in
/-- `T ↦ 𝒜(T) ⊗_{𝒪(T)} G(T)`, on the affine objects. -/
def tenF (r : AffOver X) : (AffC Bsp)ᵒᵖ ⥤ Type u where
  obj T := TensAt r G T.unop.obj
  map s := ↾ fun p => tensRes r s.unop.hom p
  map_id T := by
    ext p
    refine ten_induction r T.unop.obj (p := fun p => tensRes r (𝟙 _) p = p) (map_zero _) (fun a g => ?_)
      (fun x y hx hy => by rw [map_add, hx, hy]) p
    rw [tensRes_tmul]
    have e : r.lift (r.pr T.unop.obj ≫ 𝟙 _) (r.univ T.unop.obj) = 𝟙 _ := by
      refine r.uniq _ _ ?_ ?_
      · rw [r.lift_pr, Category.comp_id, Category.id_comp]
      · rw [r.lift_univ, op_id, X.map_id]; rfl
    have e1 : rhoA r (𝟙 T.unop.obj) a = a := by
      change ((OB Bsp).map (r.lift (r.pr T.unop.obj ≫ 𝟙 _) (r.univ T.unop.obj)).op).hom a = a
      rw [e]; simp
    rw [e1, op_id, G.map_id]
  map_comp {T₁ T₂ T₃} s s' := by
    ext p
    refine ten_induction r T₁.unop.obj
      (p := fun p => tensRes r (s'.unop.hom ≫ s.unop.hom) p = tensRes r s'.unop.hom (tensRes r s.unop.hom p))
      (by simp) (fun a g => ?_) (fun x y hx hy => by simp only [map_add, hx, hy]) p
    change tmulAt r _ (rhoA r _ a) (G.map _ g) = tmulAt r _ (rhoA r _ (rhoA r _ a)) (G.map _ (G.map _ g))
    have e : r.lift (r.pr T₃.unop.obj ≫ s'.unop.hom) (r.univ T₃.unop.obj) ≫
        r.lift (r.pr T₂.unop.obj ≫ s.unop.hom) (r.univ T₂.unop.obj) =
        r.lift (r.pr T₃.unop.obj ≫ s'.unop.hom ≫ s.unop.hom) (r.univ T₃.unop.obj) := by
      rw [r.comp_lift, ← Category.assoc, r.lift_pr, r.lift_univ, Category.assoc]
    have e1 : rhoA r (s'.unop.hom ≫ s.unop.hom) a = rhoA r s'.unop.hom (rhoA r s.unop.hom a) := by
      change ((OB Bsp).map _).hom a = ((OB Bsp).map _).hom (((OB Bsp).map _).hom a)
      rw [← e, op_comp, Functor.map_comp]
      rfl
    rw [e1, op_comp, G.map_comp]

/-- The inclusion of the affine objects. -/
abbrev inclA : (AffC Bsp)ᵒᵖ ⥤ (SB Bsp)ᵒᵖ := (ObjectProperty.ι _).op

/-- **Proposition 9.1**: the printed canonical morphism is an isomorphism of presheaves on the affine base,
`G ⊗_𝒪 𝒜 ≅ f_* f^* G`, for `G` quasi-coherent in the printed sense and `f : X → B` affine. Its value on `a ⊗ g` at
`(t, x)` is `a(t, x) • t^* g`. `tenF` takes values in `Type u` and `pushF` in `Type (u + 1)`, so the isomorphism is
stated after `uliftFunctor`. -/
theorem prop91_natIso (r : AffOver X) (hG : PrintedQCoh G) :
    ∃ Φ : tenF G r ⋙ uliftFunctor.{u + 1} ≅ inclA ⋙ pushF G X ⋙ uliftFunctor.{u},
      ∀ (T : AffC Bsp) (a : (OB Bsp).obj (op (r.P T.obj))) (g : G.obj (op T.obj)) {T' : SB Bsp}
        (t : T' ⟶ T.obj) (x : X.obj (op T')),
        ((Φ.hom.app (op T)) ⟨tmulAt r T.obj a g⟩).down.val t x =
          ((OB Bsp).map (r.lift t x).op).hom a • G.map t.op g := by
  obtain ⟨Φ, h1, h2, h3⟩ := prop91_iso r hG
  have hnat : ∀ {T T' : AffC Bsp} (s : T' ⟶ T) (p : TensAt r G T.obj),
      Φ T'.obj (tensRes r s.hom p) = pushRes s.hom (Φ T.obj p) := by
    intro T T' s p
    refine ten_induction r T.obj
      (p := fun p => Φ T'.obj (tensRes r s.hom p) = pushRes s.hom (Φ T.obj p)) ?_ (fun a g => h3 s.hom a g)
      (fun x y hx hy => ?_) p
    · ext W t x
      have a0 := h1 T'.obj 0 0 t x
      have b0 := h1 T.obj 0 0 (t ≫ s.hom) x
      rw [add_zero] at a0 b0
      rw [map_zero]
      exact (left_eq_add.mp a0).trans (left_eq_add.mp b0).symm
    · ext W t z
      rw [map_add]
      refine (h1 _ _ _ t z).trans ?_
      refine Eq.trans ?_ (h1 T.obj x y (t ≫ s.hom) z).symm
      rw [hx, hy]
      rfl
  refine ⟨NatIso.ofComponents (fun T => Equiv.toIso (Equiv.ulift.trans ((Φ T.unop.obj).trans Equiv.ulift.symm))) ?_,
    fun T a g _ t x => h2 T.obj a g t x⟩
  intro T T' s
  ext ⟨p⟩
  exact congrArg ULift.up (hnat s.unop p)

end AlgMag.FinalMisc

#print axioms AlgMag.FinalMisc.prop91_natIso
