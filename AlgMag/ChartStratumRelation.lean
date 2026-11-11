/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumOrbit
import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Sheaf

/-!
# The equivalence relation of a free `D(Z)`-action (affine stratum lemma, step 5)

For an action `β` of `D(Z)` on a presheaf `Y`, `relP β` is `D(Z) × Y`, with target `(a, x) ↦ a • x`
and source `(a, x) ↦ x`. Freeness makes it an equivalence relation over the terminal presheaf.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] {Z : AddSubgroup M}
variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The inverse of a point of `D(Z)`. -/
noncomputable def zInv {T : (BigFppfOver B S hS)ᵒᵖ} (a : APt (fppfO B S hS) Z.toAddSubmonoid T) :
    APt (fppfO B S hS) Z.toAddSubmonoid T where
  toFun w := a (Multiplicative.ofAdd ⟨-((Multiplicative.toAdd w : Z.toAddSubmonoid) : M),
    Z.neg_mem (Multiplicative.toAdd w).2⟩)
  map_one' := by
    refine Eq.trans (congrArg a ?_) (map_one a)
    exact Subtype.ext (show (-(0 : M)) = 0 from neg_zero)
  map_mul' x y := by
    refine Eq.trans (congrArg a ?_) (map_mul a _ _)
    exact Subtype.ext (neg_add _ _)

lemma zInv_mul {T : (BigFppfOver B S hS)ᵒᵖ} (a : APt (fppfO B S hS) Z.toAddSubmonoid T) :
    zInv a * a = 1 := by
  refine MonoidHom.ext fun w => ?_
  refine (map_mul a _ _).symm.trans (Eq.trans (congrArg a ?_) (map_one a))
  exact Subtype.ext (neg_add_cancel _)

variable (β : AAction (fppfO B S hS) Z.toAddSubmonoid Y)

/-- `D(Z) × Y`, as a presheaf. -/
noncomputable def relP (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (Z : AddSubgroup M) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj T := APt (fppfO B S hS) Z.toAddSubmonoid T × Y.obj T
  map f := ↾ fun r => (APt.res f r.1, Y.map f r.2)
  map_id T := by
    ext1
    refine DFunLike.ext _ _ fun r => ?_
    refine Prod.ext ?_ ?_
    · exact APt.res_id _
    · simp
  map_comp f g := by
    ext1
    refine DFunLike.ext _ _ fun r => ?_
    refine Prod.ext ?_ ?_
    · exact APt.res_comp f g _
    · simp

/-- The source `(a, x) ↦ x`. -/
noncomputable def relSrc : relP Y Z ⟶ Y where
  app T := ↾ fun r => r.2
  naturality _ _ _ := rfl

/-- The target `(a, x) ↦ a • x`. -/
noncomputable def relTgt : relP Y Z ⟶ Y where
  app T := ↾ fun r => β.smul r.1 r.2
  naturality _ _ f := by
    ext1
    refine DFunLike.ext _ _ fun r => ?_
    exact (β.map_smul f r.1 r.2).symm

/-- `Y`, over the terminal presheaf. -/
noncomputable abbrev overT (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) := Over.mk (terminal.from F)

/-- The pre-relation of `β`. -/
noncomputable def relJ : Space.PreRelation (overT (relP Y Z)) (overT Y) :=
  prod.lift (Over.homMk (relTgt β) (terminal.hom_ext _ _)) (Over.homMk relSrc (terminal.hom_ext _ _))

lemma relJ_target : (relJ β).target.left = relTgt β :=
  congrArg (fun k : overT (relP Y Z) ⟶ overT Y => k.left) (prod.lift_fst _ _)

lemma relJ_source : (relJ β).source.left = relSrc :=
  congrArg (fun k : overT (relP Y Z) ⟶ overT Y => k.left) (prod.lift_snd _ _)

/-- **Affine stratum lemma, step 5**: for a free action the relation is an equivalence relation. -/
theorem relJ_isEquivalenceRelation
    (hfree : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (a b : APt (fppfO B S hS) Z.toAddSubmonoid T)
      (x : Y.obj T), β.smul a x = β.smul b x → a = b) :
    IsEquivalenceRelation (relJ β).target (relJ β).source := by
  rw [Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation]
  have repr : ∀ {T : BigFppfOver B S hS} (r : yoneda.obj T ⟶ relP Y Z),
      ∃ c : relP Y Z |>.obj (op T), r = yonedaEquiv.symm c :=
    fun r => ⟨yonedaEquiv r, (yonedaEquiv.symm_apply_apply r).symm⟩
  constructor
  · refine ⟨fun {W} f g e => ?_⟩
    apply Over.OverMorphism.ext
    have e1 : f.left ≫ relTgt β = g.left ≫ relTgt β := by
      rw [← relJ_target β]
      change (f ≫ relJ β ≫ prod.fst).left = (g ≫ relJ β ≫ prod.fst).left
      rw [← Category.assoc, e, Category.assoc]
    have e2 : f.left ≫ relSrc = g.left ≫ relSrc := by
      rw [← relJ_source β]
      change (f ≫ relJ β ≫ prod.snd).left = (g ≫ relJ β ≫ prod.snd).left
      rw [← Category.assoc, e, Category.assoc]
    refine NatTrans.ext (funext fun T => ?_)
    ext1
    refine DFunLike.ext _ _ fun w => ?_
    have e1' := ConcreteCategory.congr_hom (NatTrans.congr_app e1 T) w
    have e2' := ConcreteCategory.congr_hom (NatTrans.congr_app e2 T) w
    have e2'' : (f.left.app T w).2 = (g.left.app T w).2 := e2'
    have e1'' : β.smul (f.left.app T w).1 (f.left.app T w).2 =
        β.smul (g.left.app T w).1 (g.left.app T w).2 := e1'
    rw [e2''] at e1''
    exact Prod.ext (hfree _ _ _ e1'') e2''
  · intro T b
    have key : ∀ x y : Space.TestPoint T b (overT Y), (relJ β).Rel b x y ↔
        ∃ a : APt (fppfO B S hS) Z.toAddSubmonoid (op T),
          β.smul a (yonedaEquiv y.1) = yonedaEquiv x.1 := by
      intro x y
      constructor
      · rintro ⟨r, h1, h2⟩
        refine ⟨(yonedaEquiv r.1).1, ?_⟩
        rw [relJ_target] at h1
        rw [relJ_source] at h2
        rw [← h1, ← h2, yonedaEquiv_comp, yonedaEquiv_comp]
        rfl
      · rintro ⟨a, ha⟩
        let c : (relP Y Z).obj (op T) := (a, yonedaEquiv y.1)
        have ec : yonedaEquiv (yonedaEquiv.symm c) = c := Equiv.apply_symm_apply _ _
        refine ⟨⟨yonedaEquiv.symm c, terminal.hom_ext _ _⟩, ?_, ?_⟩
        · rw [relJ_target]
          apply yonedaEquiv.injective
          rw [yonedaEquiv_comp, ← ha]
          change (relTgt β).app _ (yonedaEquiv (yonedaEquiv.symm c)) = _
          rw [ec]
          rfl
        · rw [relJ_source]
          apply yonedaEquiv.injective
          rw [yonedaEquiv_comp]
          change relSrc.app _ (yonedaEquiv (yonedaEquiv.symm c)) = _
          rw [ec]
          rfl
    refine ⟨fun x => (key x x).2 ⟨1, β.one_smul _⟩, fun {x y} h => ?_, fun {x y w} h k => ?_⟩
    · obtain ⟨a, ha⟩ := (key x y).1 h
      refine (key y x).2 ⟨zInv a, ?_⟩
      rw [← ha, ← β.mul_smul, zInv_mul, β.one_smul]
    · obtain ⟨a, ha⟩ := (key x y).1 h
      obtain ⟨c, hc⟩ := (key y w).1 k
      refine (key x w).2 ⟨a * c, ?_⟩
      rw [β.mul_smul, hc, ha]

end AlgMag.ChartStratum
