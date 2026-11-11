/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Site

/-!
# Chart lemma, Artin approximation step: `Spec R'` of a graded ring, as an object with action

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

* `rObj`: `Spec R'` over the base, for `ρ : Γ(S) → R'`.
* `rAct`, `mem_homog_rAct`: the action of a grading (`gradedAction`).
* `rMap`, `equivariant_rMap`: graded ring maps give equivariant maps.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

namespace AlgMag.ChartS5

section Transport

variable {M A A' : Type*} [AddCommGroup M] [DecidableEq M] [CommRing A] [CommRing A']

/-- The grading transported along a ring isomorphism. -/
def tGrade (e : A ≃+* A') (𝒜 : M → AddSubgroup A) (d : M) : AddSubgroup A' :=
  (𝒜 d).map e.toAddMonoidHom

lemma mem_tGrade (e : A ≃+* A') (𝒜 : M → AddSubgroup A) {d : M} {a : A} (ha : a ∈ 𝒜 d) :
    e a ∈ tGrade e 𝒜 d := ⟨a, ha, rfl⟩

/-- Transport of a graded ring structure. -/
noncomputable def tGradedRing (e : A ≃+* A') (𝒜 : M → AddSubgroup A) [GradedRing 𝒜] :
    GradedRing (tGrade e 𝒜) :=
  letI : SetLike.GradedMonoid (tGrade e 𝒜) :=
    { one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one e⟩
      mul_mem := by
        rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, map_mul e a b⟩ }
  letI toFun : A' →+ ⨁ d, tGrade e 𝒜 d :=
    ((DFinsupp.mapRange.addMonoidHom (β₁ := fun d => 𝒜 d) (β₂ := fun d => tGrade e 𝒜 d)
      (fun d => ((e.toAddMonoidHom.addSubgroupMap (𝒜 d)) :
        𝒜 d →+ tGrade e 𝒜 d)))).comp
      ((decomposeAddEquiv 𝒜).toAddMonoidHom.comp e.symm.toAddMonoidHom)
  have hmap : ∀ (d : M) (a : 𝒜 d), toFun (e a) =
      DirectSum.of (fun d => tGrade e 𝒜 d) d ⟨e a, a, a.2, rfl⟩ := by
    intro d a
    change DFinsupp.mapRange.addMonoidHom _ (decompose 𝒜 (e.symm (e a))) = _
    rw [e.symm_apply_apply, decompose_coe]
    exact DFinsupp.mapRange_single (hf := fun _ => map_zero _)
  letI dec : Decomposition (tGrade e 𝒜) := Decomposition.ofAddHom _ toFun
    (by
      ext x
      obtain ⟨a, rfl⟩ := e.surjective x
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
      induction a using Decomposition.inductionOn 𝒜 with
      | zero => simp
      | @homogeneous i a =>
        rw [hmap i a]
        simp
      | add a b ha hb =>
        rw [map_add, map_add, map_add, ha, hb])
    (by
      ext d ⟨_, a, ha, rfl⟩
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
      rw [coeAddMonoidHom_of]
      exact congrArg Subtype.val (DFunLike.congr_fun (hmap d ⟨a, ha⟩) _))
  { dec with }

end Transport

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M] [hSa : IsAffine S]

local notation "SCH" => BigFppfOver.toScheme B S hS
local notation "TOP" => siteTop (B := B) (S := S) (hS := hS)

instance instAffTop : IsAffine ((BigFppfOver.toScheme B S hS).obj (siteTop (B := B) (S := S) (hS := hS))) :=
  hSa

variable {R' : Type u} [CommRing R'] (ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* R')
  (hC : B.Contains (Spec (.of R')))

/-- `Spec R'` over `S`. -/
noncomputable abbrev rObj : BigFppfOver B S hS := spObj (siteTop (B := B) (S := S) (hS := hS)) ρ hC

/-- `R' ≃ Γ(Spec R')`. -/
noncomputable abbrev rSec : R' ≃+* Γ((SCH).obj (rObj ρ hC), ⊤) :=
  RingEquiv.ofBijective _ (spSec_bijective _ ρ hC)

variable (𝒜 : M → AddSubgroup R') [GradedRing 𝒜] (h0 : ∀ s, ρ s ∈ 𝒜 0)

/-- The action on `Spec R'` of a grading of `R'`. -/
noncomputable def rAct : AAction (fppfO B S hS) M (yoneda.obj (rObj ρ hC)) :=
  letI := tGradedRing (rSec ρ hC) 𝒜
  ChartMain.gradedAction (rObj ρ hC) (tGrade (rSec ρ hC) 𝒜) (rObj ρ hC).hom.hom rfl (fun s => by
    have e : ((SCH).map (spToT _ ρ hC)).appTop.hom s = rSec ρ hC (ρ s) := spToT_appTop _ ρ hC s
    have e' : ((rObj ρ hC).hom.hom).appTop.hom s = ((SCH).map (spToT _ ρ hC)).appTop.hom s := by
      have : (rObj ρ hC).hom.hom = (SCH).map (spToT _ ρ hC) ≫ 𝟙 S := rfl
      exact congrArg (fun z => z.appTop.hom s) (this.trans (Category.comp_id _))
    rw [e', e]
    exact mem_tGrade _ 𝒜 (h0 s))

/-- The grading of `rAct` is `𝒜`. -/
theorem mem_homog_rAct {d : M} {a : R'} :
    rSec ρ hC a ∈ ChartMain.homog (rAct ρ hC 𝒜 h0) d ↔ a ∈ 𝒜 d := by
  letI := tGradedRing (rSec ρ hC) 𝒜
  have e : ChartMain.homog (rAct ρ hC 𝒜 h0) d = tGrade (rSec ρ hC) 𝒜 d :=
    homog_gradedAction (rObj ρ hC) (tGrade (rSec ρ hC) 𝒜) (rObj ρ hC).hom.hom rfl _ d
  rw [e]
  constructor
  · rintro ⟨c, hc, h⟩
    have : c = a := (rSec ρ hC).injective h
    exact this ▸ hc
  · exact fun h => mem_tGrade _ 𝒜 h

section Map

variable {R'' : Type u} [CommRing R''] {ρ' : RT (siteTop (B := B) (S := S) (hS := hS)) →+* R''}
  {hC' : B.Contains (Spec (.of R''))} (𝒜' : M → AddSubgroup R'') [GradedRing 𝒜']
  (h0' : ∀ s, ρ' s ∈ 𝒜' 0)

/-- A graded ring map gives an equivariant map. -/
theorem equivariant_rMap (π : R' →+* R'') (hπ : π.comp ρ = ρ') (hm : ∀ d, ∀ a ∈ 𝒜 d, π a ∈ 𝒜' d) :
    IsEquivariant (rAct ρ' hC' 𝒜' h0') (rAct ρ hC 𝒜 h0)
      (yoneda.map (spMap _ (hC := hC) (hC' := hC') π hπ)) := by
  refine ChartMain.equivariant_of_map_mem _ _ fun d a ha => ?_
  obtain ⟨a₀, rfl⟩ := (rSec ρ hC).surjective a
  have e := spMap_appTop _ (hC := hC) (hC' := hC') π hπ a₀
  refine (congrArg (· ∈ _) e).mpr ?_
  exact (mem_homog_rAct ρ' hC' 𝒜' h0').2 (hm d a₀ ((mem_homog_rAct ρ hC 𝒜 h0).1 ha))

end Map

/-- `T → S`, as a map of the site. -/
noncomputable abbrev toTop' (T : BigFppfOver B S hS) : T ⟶ siteTop (B := B) (S := S) (hS := hS) :=
  Over.mkIdTerminal.from T

section Lift

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (actT : AAction (fppfO B S hS) M (yoneda.obj T))

/-- A graded ring map to `Γ(T)` gives an equivariant map from `T`. -/
theorem equivariant_rLift (ψ : R' →+* Γ((SCH).obj T, ⊤))
    (hψ : ψ.comp ρ = ((SCH).map (toTop' T)).appTop.hom)
    (hm : ∀ d, ∀ a ∈ 𝒜 d, ψ a ∈ ChartMain.homog actT d) :
    IsEquivariant actT (rAct ρ hC 𝒜 h0) (yoneda.map (spLift _ ρ hC (toTop' T) ψ hψ)) := by
  refine ChartMain.equivariant_of_map_mem _ _ fun d a ha => ?_
  obtain ⟨a₀, rfl⟩ := (rSec ρ hC).surjective a
  have e := spLift_appTop _ ρ hC (toTop' T) ψ hψ a₀
  refine (congrArg (· ∈ _) e).mpr ?_
  exact hm d a₀ ((mem_homog_rAct ρ hC 𝒜 h0).1 ha)

end Lift

section Level

variable {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
  (Dr : J → Type u) [∀ j, CommRing (Dr j)]
  (ρs : ∀ j, RT (siteTop (B := B) (S := S) (hS := hS)) →+* Dr j)
  (hCs : ∀ j, B.Contains (Spec (.of (Dr j))))
  (πs : ∀ {j k : J}, j ≤ k → Dr j →+* Dr k)
  (π_id : ∀ j (h : j ≤ j), πs h = RingHom.id _)
  (π_comp : ∀ {j k l : J} (h : j ≤ k) (h' : k ≤ l), (πs h').comp (πs h) = πs (h.trans h'))
  (π_ρ : ∀ {j k : J} (h : j ≤ k), (πs h).comp (ρs j) = ρs k)

/-- The rings, as a diagram. -/
noncomputable def lvlF : Jᵒᵖᵒᵖ ⥤ CommRingCat.{u} where
  obj j := .of (Dr j.unop.unop)
  map {j k} f := CommRingCat.ofHom (πs (leOfHom f.unop.unop))
  map_id j := by
    apply CommRingCat.hom_ext
    exact π_id _ _
  map_comp {a b c} f g := by
    apply CommRingCat.hom_ext
    exact (π_comp _ _).symm

/-- The objects, as a diagram. -/
noncomputable def lvlD : Jᵒᵖ ⥤ BigFppfOver B S hS where
  obj j := rObj (ρs j.unop) (hCs j.unop)
  map {j k} f := spMap _ (hC := hCs k.unop) (hC' := hCs j.unop) (πs (leOfHom f.unop)) (π_ρ _)
  map_id j := by
    refine site_hom_ext ?_
    change Spec.map (CommRingCat.ofHom (πs _)) = 𝟙 _
    rw [π_id]
    exact Spec.map_id _
  map_comp {a b c} f g := by
    refine site_hom_ext ?_
    change Spec.map (CommRingCat.ofHom (πs _)) =
      Spec.map (CommRingCat.ofHom (πs _)) ≫ Spec.map (CommRingCat.ofHom (πs _))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, π_comp]

instance : AffDg (lvlD (B := B) (S := S) (hS := hS) Dr ρs hCs πs π_id π_comp π_ρ) :=
  ⟨fun _ => inferInstanceAs (IsAffine (Spec _))⟩

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (ψs : ∀ j, Dr j →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  (hψ : ∀ j, (ψs j).comp (ρs j) = ((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom)
  (ψ_π : ∀ {j k : J} (h : j ≤ k), (ψs k).comp (πs h) = ψs j)

/-- The cocone on the rings. -/
noncomputable def lvlCocone : Cocone (lvlF Dr πs π_id π_comp) where
  pt := Γ((SCH).obj T, ⊤)
  ι := { app := fun j => CommRingCat.ofHom (ψs j.unop.unop)
         naturality := fun j k f => by
           refine (CommRingCat.hom_ext ?_ : _ = _).trans (Category.comp_id _).symm
           exact ψ_π _ }

omit [∀ j, CommRing (Dr j)] in
lemma spLift_spMap {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    {ρ₁ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* R₁}
    {ρ₂ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* R₂} {h₁ : B.Contains (Spec (.of R₁))}
    {h₂ : B.Contains (Spec (.of R₂))} (π : R₁ →+* R₂) (hπ : π.comp ρ₁ = ρ₂)
    (ψ₁ : R₁ →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (ψ₂ : R₂ →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (e : ψ₂.comp π = ψ₁) (h1) (h2) :
    spLift _ ρ₂ h₂ (toTop' T) ψ₂ h2 ≫ spMap _ (hC := h₁) (hC' := h₂) π hπ =
      spLift _ ρ₁ h₁ (toTop' T) ψ₁ h1 := by
  refine ChartMain.siteExt (ChartMain.toAffine_ext ?_)
  ext x
  obtain ⟨x₀, rfl⟩ := (RingEquiv.ofBijective _ (spSec_bijective _ ρ₁ h₁)).surjective x
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  change ((BigFppfOver.toScheme B S hS).map (spLift _ ρ₂ h₂ (toTop' T) ψ₂ h2)).appTop.hom
    (((BigFppfOver.toScheme B S hS).map (spMap _ (hC := h₁) (hC' := h₂) π hπ)).appTop.hom
      (spSec _ ρ₁ h₁ x₀)) = _
  rw [spMap_appTop]
  refine (spLift_appTop _ _ _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (spLift_appTop _ _ _ _ _ _ x₀).symm
  exact congrArg (fun r => r x₀) e

/-- The cone with vertex `T`. -/
noncomputable def lvlCone : Cone (lvlD (B := B) (S := S) (hS := hS) Dr ρs hCs πs π_id π_comp π_ρ) where
  pt := T
  π := { app := fun j => spLift _ (ρs j.unop) (hCs j.unop) (toTop' T) (ψs j.unop) (hψ _)
         naturality := fun j k f => (Category.id_comp _).trans
           (spLift_spMap (πs (leOfHom f.unop)) (π_ρ _) _ _ (ψ_π _) _ _).symm }

/-- The cone is a limit, if `Γ(T)` is the colimit. -/
theorem isLimit_lvlCone (hc : IsColimit (lvlCocone (B := B) (S := S) (hS := hS) (T := T) Dr πs π_id π_comp ψs ψ_π)) :
    Nonempty (IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      (lvlCone Dr ρs hCs πs π_id π_comp π_ρ ψs hψ ψ_π))) := by
  have h3 := isLimitConeRightOpOfCocone _ hc
  have h4 := isLimitOfPreserves Scheme.Spec h3
  let α : (lvlF Dr πs π_id π_comp).rightOp ⋙ Scheme.Spec ≅
      lvlD (B := B) (S := S) (hS := hS) Dr ρs hCs πs π_id π_comp π_ρ ⋙ (BigFppfOver.toScheme B S hS) :=
    NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} f =>
      (Category.comp_id _).trans (Eq.trans rfl (Category.id_comp _).symm))
  have h5 := (IsLimit.postcomposeHomEquiv α _).symm h4
  exact ⟨h5.ofIsoLimit (Cone.ext ((BigFppfOver.toScheme B S hS).obj T).isoSpec.symm (fun i => by
    refine (Category.comp_id _).trans ?_
    change Spec.map _ = ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv ≫
      ((BigFppfOver.toScheme B S hS).obj T).toSpecΓ ≫ Spec.map _
    have h : ((BigFppfOver.toScheme B S hS).obj T).toSpecΓ = ((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom := rfl
    rw [h, Iso.inv_hom_id_assoc]
    rfl))⟩

/-- The colimit criterion for `lvlCocone`. -/
noncomputable def isColimit_lvl (hs : ∀ c, ∃ j y, ψs j y = c)
    (hi : ∀ j y, ψs j y = 0 → ∃ (k : J) (h : j ≤ k), πs h y = 0) :
    IsColimit (lvlCocone (B := B) (S := S) (hS := hS) (T := T) Dr πs π_id π_comp ψs ψ_π) := by
  haveI : ReflectsColimit (lvlF Dr πs π_id π_comp) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro c
    obtain ⟨j, y, hy⟩ := hs c
    exact ⟨op (op j), y, hy.symm⟩
  · intro j a' b' hab
    let a : Dr j.unop.unop := a'
    let b : Dr j.unop.unop := b'
    have hab' : ψs j.unop.unop a = ψs j.unop.unop b := hab
    have hd : ψs j.unop.unop (a - b) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hab'
    obtain ⟨k, h, hk⟩ := hi _ _ hd
    refine ⟨op (op k), (homOfLE h).op.op, ?_⟩
    have e : πs h a = πs h b := by
      rw [← sub_eq_zero, ← map_sub]; exact hk
    exact e

variable (𝒢 : ∀ j, M → AddSubgroup (Dr j)) [∀ j, GradedRing (𝒢 j)] (h0s : ∀ j s, ρs j s ∈ 𝒢 j 0)
  (πm : ∀ {j k : J} (h : j ≤ k), ∀ d, ∀ a ∈ 𝒢 j d, πs h a ∈ 𝒢 k d)

include π_ρ πm in
/-- **Artin approximation step**: `φ` spreads to an equivariant map from a finite level. -/
theorem exists_level {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
    (actT : AAction (fppfO B S hS) M (yoneda.obj T))
    (ψm : ∀ j, ∀ d, ∀ a ∈ 𝒢 j d, ψs j a ∈ ChartMain.homog actT d)
    (hc : IsColimit (lvlCocone (B := B) (S := S) (hS := hS) (T := T) Dr πs π_id π_comp ψs ψ_π))
    (φ : yoneda.obj T ⟶ X) (hφ : IsEquivariant actT actX φ) :
    ∃ (j : J) (xj : yoneda.obj (rObj (ρs j) (hCs j)) ⟶ X),
      IsEquivariant (rAct (ρs j) (hCs j) (𝒢 j) (h0s j)) actX xj ∧
      yoneda.map (spLift _ (ρs j) (hCs j) (toTop' T) (ψs j) (hψ j)) ≫ xj = φ := by
  haveI : IsFiltered J := isFiltered_of_directed_le_nonempty J
  obtain ⟨hL⟩ := isLimit_lvlCone Dr ρs hCs πs π_id π_comp π_ρ ψs hψ ψ_π hc
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj (lvlCone (B := B) (S := S) (hS := hS) (T := T) Dr ρs hCs πs π_id π_comp π_ρ ψs hψ ψ_π).pt) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj T))
  obtain ⟨i, xi, h1, h2⟩ := exists_equivariant_rep actX hl
    (lvlD (B := B) (S := S) (hS := hS) Dr ρs hCs πs π_id π_comp π_ρ)
    (lvlCone Dr ρs hCs πs π_id π_comp π_ρ ψs hψ ψ_π) hL
    (fun i => rAct (ρs i.unop) (hCs i.unop) (𝒢 i.unop) (h0s i.unop)) actT
    (fun {i j} f => equivariant_rMap _ _ _ _ _ _ _ (π_ρ _) (πm _))
    (fun i => equivariant_rLift _ _ _ _ actT (ψs i.unop) (hψ _) (ψm i.unop))
    φ hφ
  exact ⟨i.unop, xi, h1, h2⟩

end Level

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.exists_level
