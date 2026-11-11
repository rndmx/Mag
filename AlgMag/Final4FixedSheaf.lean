/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec8Representability

/-!
# Proposition 3.35 with a sheaf condition on the extension sieves only

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Proposition 3.35 (closed direction).
The construction of section `Glue` of `Sec8Representability` is repeated, with "`F` is a `J`-sheaf and the extension sieves of
points of `D(Z)` are `J`-covering" is replaced by "`F` is a sheaf for every pullback of every
extension sieve".
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe w u v

namespace AlgMag.Final4Fix

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : Type*} [AddCommGroup M] {F : Cᵒᵖ ⥤ Type u}
variable {act : AAction 𝒪 M F} {Z : AddSubgroup M}

theorem existsUnique_glue' (hsh : ∀ {T T' : C} (a : APt 𝒪 Z.toAddSubmonoid (op T)) (r : T' ⟶ T),
      Presieve.IsSheafFor F ((extSieve 𝒪 Z a).pullback r).arrows)
    {T : C} {x : F.obj (op T)} (hx : x ∈ (fixedPoints (quotientAction act Z)).obj (op T))
    {T' : C} (t : T' ⟶ T) (a : APt 𝒪 Z.toAddSubmonoid (op T')) :
    ∃! y : F.obj (op T'), ∀ {T'' : C} (s : T'' ⟶ T') (h : APt 𝒪 M (op T'')),
      APt.toMagnet Z.toAddSubmonoid h = APt.res s.op a →
        F.map s.op y = act.smul h (F.map (s ≫ t).op x) := by
  have sh : Presieve.IsSheafFor F (extSieve 𝒪 Z a).arrows := by
    simpa using hsh a (𝟙 _)
  let fam : Presieve.FamilyOfElements F (extSieve 𝒪 Z a).arrows := fun _ s hs =>
    act.smul hs.choose (F.map (s ≫ t).op x)
  have hc : fam.Compatible := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ comm
    change F.map g₁.op (act.smul _ _) = F.map g₂.op (act.smul _ _)
    rw [act.map_smul, act.map_smul, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp]
    have e1 : g₁ ≫ f₁ ≫ t = g₂ ≫ f₂ ≫ t := by
      rw [← Category.assoc, comm, Category.assoc]
    rw [e1]
    apply smul_eq_of_fixed hx
    rw [APt.toMagnet_res, APt.toMagnet_res, h₁.choose_spec, h₂.choose_spec, ← APt.res_comp,
      ← APt.res_comp, ← op_comp, ← op_comp, comm]
  have key : ∀ {T'' : C} (s : T'' ⟶ T') (hs : (extSieve 𝒪 Z a).arrows s)
      (h : APt 𝒪 M (op T'')), APt.toMagnet Z.toAddSubmonoid h = APt.res s.op a →
        fam s hs = act.smul h (F.map (s ≫ t).op x) := by
    intro T'' s hs h e
    exact smul_eq_of_fixed hx _ (hs.choose_spec.trans e.symm)
  refine ⟨sh.amalgamate fam hc, ?_, ?_⟩
  · intro T'' s h e
    rw [show F.map s.op (sh.amalgamate fam hc) = fam s ⟨h, e⟩ from sh.valid_glue hc s ⟨h, e⟩]
    exact key s ⟨h, e⟩ h e
  · intro y hy
    refine sh.isSeparatedFor.ext fun Y s hs => ?_
    rw [show F.map s.op (sh.amalgamate fam hc) = fam s hs from sh.valid_glue hc s hs]
    exact hy s hs.choose hs.choose_spec

/-- A point of `X^Z` is computed from its underlying point. -/
lemma AttractorPt.app_eq_smul_toPoint {T : C} (φ : AttractorPt act Z.toAddSubmonoid T)
    {T' : C} (t : T' ⟶ T) (h : APt 𝒪 M (op T')) :
    φ.app t (APt.toMagnet Z.toAddSubmonoid h) = act.smul h (F.map t.op φ.toPoint) := by
  have e := φ.equivariant t h 1
  rw [mul_one] at e
  rw [e]
  congr 1
  have hnat := φ.naturality t (𝟙 T) 1
  have hone : APt.res (𝒪 := 𝒪) (P := Z.toAddSubmonoid) t.op 1 = 1 := by
    ext p; simp
  rw [Category.comp_id, hone] at hnat
  exact hnat

/-- The attractor point attached to a fixed point. -/
noncomputable def attOfFixed' (hsh : ∀ {T T' : C} (a : APt 𝒪 Z.toAddSubmonoid (op T)) (r : T' ⟶ T),
      Presieve.IsSheafFor F ((extSieve 𝒪 Z a).pullback r).arrows) {T : C}
    {x : F.obj (op T)} (hx : x ∈ (fixedPoints (quotientAction act Z)).obj (op T)) :
    AttractorPt act Z.toAddSubmonoid T where
  app t a := (existsUnique_glue' hsh hx t a).choose
  naturality := by
    intro T' T'' s t a
    refine (existsUnique_glue' hsh hx (s ≫ t) (APt.res s.op a)).unique
      (existsUnique_glue' hsh hx (s ≫ t) (APt.res s.op a)).choose_spec.1 ?_
    intro W r h e
    rw [← Functor.map_comp_apply, ← op_comp, ← Category.assoc]
    refine (existsUnique_glue' hsh hx t a).choose_spec.1 (r ≫ s) h ?_
    rw [e, ← APt.res_comp, ← op_comp]
  equivariant := by
    intro T' t h a
    refine (existsUnique_glue' hsh hx t _).unique
      (existsUnique_glue' hsh hx t _).choose_spec.1 ?_
    intro W r k e
    have sh := hsh a r
    refine sh.isSeparatedFor.ext fun W' q hq => ?_
    obtain ⟨b, hb⟩ := hq
    have hb' : APt.toMagnet Z.toAddSubmonoid b = APt.res (q ≫ r).op a := hb
    have hg := (existsUnique_glue' hsh hx t a).choose_spec.1 (q ≫ r) b hb'
    rw [act.map_smul, act.map_smul, ← Functor.map_comp_apply (f := r.op), ← op_comp, hg,
      ← act.mul_smul, act.map_smul, ← Functor.map_comp_apply, ← op_comp, Category.assoc]
    have hA : q ≫ r ≫ t = (q ≫ r) ≫ t := by simp
    rw [hA]
    refine smul_eq_of_fixed hx _ ?_
    rw [APt.toMagnet_res, e, ← APt.res_comp, ← op_comp]
    refine MonoidHom.ext fun n => ?_
    have := DFunLike.congr_fun hb' n
    simp only [APt.res_apply, MonoidHom.mul_apply, map_mul, APt.toMagnet_apply] at this ⊢
    rw [this]
    simp only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]

/-- **Proposition 3.35**, for a sheaf `F`, on a site where every point of `D(Z)` extends locally to
a point of `D(M)`: the underlying point is a bijection `X^Z(T) ≃ X^{D(M/Z)}(T)`. -/
noncomputable def attractorFixedEquivOfSheaf (hsh : ∀ {T T' : C} (a : APt 𝒪 Z.toAddSubmonoid (op T)) (r : T' ⟶ T),
      Presieve.IsSheafFor F ((extSieve 𝒪 Z a).pullback r).arrows) (T : C) :
    (fixedPoints (quotientAction act Z)).obj (op T) ≃ AttractorPt act Z.toAddSubmonoid T where
  toFun x := attOfFixed' hsh x.2
  invFun φ := ⟨φ.toPoint, φ.toPoint_mem_fixedPoints⟩
  left_inv x := by
    refine Subtype.ext ?_
    have h := (existsUnique_glue' hsh x.2 (𝟙 T) 1).choose_spec.1 (𝟙 T) 1 (by
      ext p; simp [APt.toMagnet])
    have e : F.map (𝟙 T).op (attOfFixed' hsh x.2).toPoint = _ := h
    simpa [act.one_smul] using e
  right_inv φ := by
    have key : ∀ {T' : C} (t : T' ⟶ T) (a : APt 𝒪 Z.toAddSubmonoid (op T')),
        (attOfFixed' hsh (act := act) (Z := Z) φ.toPoint_mem_fixedPoints).app t a =
          φ.app t a := by
      intro T' t a
      refine ((existsUnique_glue' hsh φ.toPoint_mem_fixedPoints t a).unique
        (existsUnique_glue' hsh φ.toPoint_mem_fixedPoints t a).choose_spec.1 ?_)
      intro W s h e
      rw [← φ.naturality, ← e, AttractorPt.app_eq_smul_toPoint]
    refine AttractorPt.ext ?_
    funext T' t a
    exact key t a


end AlgMag.Final4Fix
