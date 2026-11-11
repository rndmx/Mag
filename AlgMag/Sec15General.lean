/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec5Etale
import AlgMag.Sec8Representability
import AlgMag.Sec15PureMagnets
import AlgMag.Final4FixedSheaf
import AlgMag.Final4ExtFpqc

/-!
# Pure magnets of non-affine spaces

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §15.

## Main results

* `AlgMag.attractorOrder_affine`, `AlgMag.attractorOrder_of_isAffineHom`: Proposition 3.29 and Fact 3.34
  (i), whence Proposition 15.1 and Theorem 15.3 for `X` affine over an arbitrary `S`.
* `AlgMag.IsPure.attractorImage_lt`: the implication of Proposition 15.1 which needs only 3.29.
* `AlgMag.prop155`, `AlgMag.prop155_pure`: Proposition 15.5.
* `AlgMag.thm154_i`, `AlgMag.thm154_ii`: Theorem 15.4, with `S` quasi-compact.
* `AlgMag.rem156`, `AlgMag.rem158`: Remarks 15.6 and 15.8.
* `AlgMag.pureMagnets_trivial_action`: Example 15.10 (i) for an arbitrary space.

## Departures from the paper

Theorem 15.4 needs `S` quasi-compact. Over `S = ⊔_{n ≥ 1} Spec k`, let `D(ℤ)` act on `X = ⊔_n 𝔸¹` with
weight `n` on the `n`-th copy. Then `X` is affine and finitely presented over `S`, and `X^N` determines
`N ∩ ℕ_{>0}`, so infinitely many magnets are pure.

The proof of Proposition 15.5 here does not use Theorem 8.3 or Corollary 11.6: the point of `X^L` lifts
to `U^L` after an étale cover (`AlgMag.exists_atlas_lift`), and points of `X^N` glue. "Locally of finite
presentation" appears as `AlgMag.IsLimitPreserving` and `AlgMag.ChartsOfFiniteType`.

`AttractorOrder` under Fact 3.34 (ii), (iii) is not proved here.

The paper takes `M` a finitely generated abelian group. Here `M` is a commutative monoid for
Theorem 15.4 (i) and an abelian group for Proposition 15.5 and Theorem 15.4 (ii), with
`[Fact (Cardinal.mk M < B.cutoff)]`, which puts `Spec R[M]` in the site; it holds for `M` finitely
generated (`fact_cutoff_of_fg`). The sheaf condition of `U` for the extension sieves of points of
`D(Z)` is fpqc descent (`Final4Ext.isSheafFor_extSieve`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
set_option linter.unusedSectionVars false

namespace AlgMag

section Order
variable {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {F : Cᵒᵖ ⥤ Type u}
variable {M : Type*} [AddCommMonoid M]

/-- **Proposition 3.29**, for images in `X`, with no hypothesis: `N ≤ L` gives `X^N ⊆ X^L`. -/
theorem attractorImage_monotone (act : AAction 𝒪 M F) : Monotone (attractorImage act) := by
  intro N L h T
  rintro _ ⟨φ, rfl⟩
  exact ⟨AttractorPt.ofLE h φ, rfl⟩

/-- `AttractorOrder` for `N ↦ X^N ⊆ X` as soon as a point lying in all `X^{N_i}` lies in
`X^{⋂ N_i}`. -/
theorem attractorOrder_of_mem_sInf (act : AAction 𝒪 M F)
    (h : ∀ (s : Set (AddSubmonoid M)), s.Nonempty → ∀ (T : C) (t : F.obj (op T)),
      (∀ N ∈ s, t ∈ attractorImage act N T) → t ∈ attractorImage act (sInf s) T) :
    AttractorOrder (attractorImage act) where
  monotone := attractorImage_monotone act
  sInf_of_const s y hne hy := by
    obtain ⟨N₀, h₀⟩ := id hne
    refine le_antisymm ((attractorImage_monotone act (sInf_le h₀)).trans_eq (hy N₀ h₀)) ?_
    intro T t ht
    exact h s hne T t fun N hN => by
      rw [hy N hN]; exact ht

/-- **Proposition 15.1**, implication (ii) ⇒ (i), which uses only Proposition 3.29: for a pure magnet
every strictly smaller magnet has a strictly smaller attractor. No hypothesis on `X`. -/
theorem IsPure.attractorImage_lt (act : AAction 𝒪 M F) {N : AddSubmonoid M}
    (hN : IsPure (attractorImage act) N) {L : AddSubmonoid M} (hL : L < N) :
    attractorImage act L < attractorImage act N := by
  refine lt_of_le_of_ne (attractorImage_monotone act hL.le) fun e => ?_
  exact absurd (hN L e.symm) (not_le_of_gt hL)

end Order

section GB
variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M] {X : Over S} [IsAffineHom X.hom]

/-- **Fact 3.34 (i)** and **Proposition 3.29**, `X` affine over an arbitrary `S`, `M` any commutative
monoid: `N ↦ X^N ⊆ X` satisfies `AttractorOrder`. Hence **Proposition 15.1**
(`isPure_iff_lt`) and **Theorem 15.3** (`pureEquivRange`) hold in this case. -/
theorem attractorOrder_affine (act : AAction (GB.overO S) M (yoneda.obj X)) :
    AttractorOrder (attractorImage act) := by
  refine attractorOrder_of_mem_sInf act fun s _ T t ht => ?_
  obtain ⟨φ, hφ⟩ := (GB.exists_toPoint_iInf_iff act (fun N : s => (N : AddSubmonoid M))
    (T := T) t).2 fun N => ht N N.2
  have e : (⨅ N : s, (N : AddSubmonoid M)) = sInf s := (sInf_eq_iInf' s).symm
  exact ⟨AttractorPt.ofLE e.le φ, hφ⟩
end GB

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
local notation "Sch" => BigFppfOver.toScheme B S hS
attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Glue
variable {M : Type u} [AddCommMonoid M] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {act : AAction (fppfO B S hS) M F}

/-- A point of `X` lying in `X^N` on a covering sieve lies in `X^N`, when `X^N → X` is injective on
points. -/
theorem exists_toPoint_of_sieve (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    {N : AddSubmonoid M}
    (hinj : ∀ T : BigFppfOver B S hS,
      Function.Injective (AttractorPt.toPoint : AttractorPt act N T → F.obj (op T)))
    {T : BigFppfOver B S hS} (t : F.obj (op T)) (R : Sieve T)
    (hR : R ∈ BigFppfOver.topology B S hS T)
    (h : ∀ {Y : BigFppfOver B S hS} (g : Y ⟶ T), R g →
      ∃ φ : AttractorPt act N Y, φ.toPoint = F.map g.op t) :
    ∃ φ : AttractorPt act N T, φ.toPoint = t := by
  have hsh := isSheaf_attractor act N _ hF
  let x : Presieve.FamilyOfElements (attractor act N) R.arrows :=
    fun Y g hg => (h g hg).choose
  have hx : ∀ {Y} (g : Y ⟶ T) (hg : R g),
      AttractorPt.toPoint (x g hg : AttractorPt act N Y) = F.map g.op t :=
    fun g hg => (h g hg).choose_spec
  have hc : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    apply hinj Z
    change AttractorPt.toPoint (AttractorPt.baseChange g₁ (x f₁ h₁)) =
      AttractorPt.toPoint (AttractorPt.baseChange g₂ (x f₂ h₂))
    rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, hx f₁ h₁, hx f₂ h₂,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]
  obtain ⟨φ, hφ, -⟩ := hsh R hR x hc
  refine ⟨φ, (hF R hR).isSeparatedFor.ext fun Y g hg => ?_⟩
  have := congrArg AttractorPt.toPoint (hφ g hg)
  rw [← hx g hg, ← this]
  exact (AttractorPt.toPoint_baseChange g φ).symm

end Glue

section Affine
variable {M : Type u} [AddCommMonoid M] [Fact (Cardinal.mk M < B.cutoff)]
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom] {aU : AAction (fppfO B S hS) M (yoneda.obj U)}

/-- **Corollary 3.30** for `U` affine over `S`. -/
theorem toPoint_injective_affine (N : AddSubmonoid M) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.toPoint : AttractorPt aU N T → (yoneda.obj U).obj (op T)) := by
  intro φ ψ h
  refine ofLE_injective_of_dense (BigFppfOver.isSheaf_of_type_yoneda_obj U)
    (hasDensePullback_yoneda U) (le_top : N ≤ ⊤) T ?_
  exact (attractorTopEquiv aU T).injective h

lemma coeff_inclR_of_notMem {T : BigFppfOver B S hS} {L N : AddSubmonoid M} (h : L ≤ N)
    (x : AddMonoidAlgebra (RT T) L) (n : N) (hn : (n : M) ∉ L) : (inclR T h x).coeff n = 0 := by
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨l, rfl⟩
  exact hn l.2

lemma coeff_inclR {T : BigFppfOver B S hS} {L N : AddSubmonoid M} (h : L ≤ N)
    (x : AddMonoidAlgebra (RT T) L) (l : L) :
    (inclR T h x).coeff (AddSubmonoid.inclusion h l) = x.coeff l :=
  Finsupp.mapDomain_apply (AddSubmonoid.inclusion_injective h) _ _

/-- The value of a point of `U^N` on `Γ(T)[N]`, as a ring map from the chart. -/
theorem exists_chart_ring {T : BigFppfOver B S hS} [IsAffine ((Sch).obj T)] {N : AddSubmonoid M}
    (φ : AttractorPt aU N T) :
    ∃ (ψ : chartA T U →+* AddMonoidAlgebra (RT T) N) (hψ : ψ.comp (chartα T U) = ρN T N),
      ptOf (hC := contains_any T N) ψ hψ =
        φ.app (spToT T (ρN T N) (contains_any T N)) (spPt (monN _ N)) :=
  exists_ptOf (T := T) (U := U) (hC := contains_any T N) _

/-- **Fact 3.34 (i)**, on points, for `T` affine: the heart is `R[⋂ N_i] = ⋂ R[N_i]` inside `R[M]`. -/
theorem exists_sInf_affine {s : Set (AddSubmonoid M)} (hne : s.Nonempty)
    {T : BigFppfOver B S hS} [IsAffine ((Sch).obj T)] (t : (yoneda.obj U).obj (op T))
    (h : ∀ N ∈ s, ∃ φ : AttractorPt aU N T, φ.toPoint = t) :
    ∃ φ : AttractorPt aU (sInf s) T, φ.toPoint = t := by
  classical
  obtain ⟨N₀, h₀⟩ := hne
  obtain ⟨φ₀, hφ₀⟩ := h N₀ h₀
  obtain ⟨ψ₀, hψ₀, e₀⟩ := exists_chart_ring φ₀
  have hP : sInf s ≤ N₀ := sInf_le h₀
  have hcomp : ∀ (N₁ N₂ : AddSubmonoid M) (φ₁ : AttractorPt aU N₁ T) (φ₂ : AttractorPt aU N₂ T),
      φ₁.toPoint = φ₂.toPoint → ∀ (ψ₁ : chartA T U →+* AddMonoidAlgebra (RT T) N₁)
        (h₁ : ψ₁.comp (chartα T U) = ρN T N₁) (ψ₂ : chartA T U →+* AddMonoidAlgebra (RT T) N₂)
        (h₂ : ψ₂.comp (chartα T U) = ρN T N₂),
        ptOf (hC := contains_any T N₁) ψ₁ h₁ =
          φ₁.app (spToT T (ρN T N₁) (contains_any T N₁)) (spPt (monN _ N₁)) →
        ptOf (hC := contains_any T N₂) ψ₂ h₂ =
          φ₂.app (spToT T (ρN T N₂) (contains_any T N₂)) (spPt (monN _ N₂)) →
        ∀ a, inclR T (le_top : N₁ ≤ ⊤) (ψ₁ a) = inclR T (le_top : N₂ ≤ ⊤) (ψ₂ a) := by
    intro N₁ N₂ φ₁ φ₂ ht ψ₁ h₁ ψ₂ h₂ e₁ e₂ a
    have hφ : AttractorPt.ofLE (le_top : N₁ ≤ ⊤) φ₁ = AttractorPt.ofLE (le_top : N₂ ≤ ⊤) φ₂ :=
      (attractorTopEquiv aU T).injective ht
    have u₁ := ofLE_universal (le_top : N₁ ≤ ⊤) φ₁
    have u₂ := ofLE_universal (le_top : N₂ ≤ ⊤) φ₂
    rw [hφ, u₂, ← e₁, ← e₂] at u₁
    change spMap T (hC := contains_any T N₂) (hC' := contains_any T ⊤) (inclR T le_top)
        (incl_ρN le_top) ≫ ptOf ψ₂ h₂ =
      spMap T (hC := contains_any T N₁) (hC' := contains_any T ⊤) (inclR T le_top)
        (incl_ρN le_top) ≫ ptOf ψ₁ h₁ at u₁
    rw [spMap_comp_ptOf, spMap_comp_ptOf] at u₁
    have := ptOf_injective _ _ u₁
    exact (DFunLike.congr_fun this a).symm
  have hmem : ∀ a, ψ₀ a ∈ (inclR T hP).range := by
    intro a
    refine mem_range_incl hP _ fun n hn => ?_
    refine AddSubmonoid.mem_sInf.mpr fun N hN => ?_
    by_contra hnN
    obtain ⟨φ, hφ⟩ := h N hN
    obtain ⟨ψ, hψ, e⟩ := exists_chart_ring φ
    have key := hcomp N N₀ φ φ₀ (hφ.trans hφ₀.symm) ψ hψ ψ₀ hψ₀ e e₀ a
    have c₁ := coeff_inclR_of_notMem (le_top : N ≤ ⊤) (ψ a) ⟨(n : M), trivial⟩ hnN
    have c₂ := coeff_inclR (le_top : N₀ ≤ ⊤) (ψ₀ a) n
    rw [key] at c₁
    exact hn (c₂.symm.trans c₁)
  have hinj := incl_injective T hP
  let e : AddMonoidAlgebra (RT T) (sInf s : AddSubmonoid M) ≃+* (inclR T hP).range :=
    RingEquiv.ofBijective (inclR T hP).rangeRestrict
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), (inclR T hP).rangeRestrict_surjective⟩
  let ψP : chartA T U →+* AddMonoidAlgebra (RT T) (sInf s : AddSubmonoid M) :=
    (e.symm : _ →+* _).comp (ψ₀.codRestrict (inclR T hP).range hmem)
  have hψP : ∀ a, inclR T hP (ψP a) = ψ₀ a := fun a => by
    have := e.apply_symm_apply (ψ₀.codRestrict (inclR T hP).range hmem a)
    exact congrArg Subtype.val this
  have hα : ψP.comp (chartα T U) = ρN T (sInf s) := by
    refine RingHom.ext fun x => hinj ?_
    change inclR T hP (ψP (chartα T U x)) = (inclR T hP).comp (ρN T (sInf s)) x
    rw [hψP, incl_ρN]
    exact DFunLike.congr_fun hψ₀ x
  have hcomp2 : (inclR T hP).comp ψP = ψ₀ := RingHom.ext hψP
  obtain ⟨φ', hφ'⟩ := exists_ofLE_of_pull (hasDensePullback_yoneda U) hP φ₀
    (ptOf (hC := contains_any T _) ψP hα) (by
      rw [← e₀]
      change spMap T (hC := contains_any T _) (hC' := contains_any T N₀) (inclR T hP)
        (incl_ρN hP) ≫ ptOf ψP hα = _
      rw [spMap_comp_ptOf]
      have hr : ∀ (ψ' : chartA T U →+* AddMonoidAlgebra (RT T) N₀)
          (h' : ψ'.comp (chartα T U) = ρN T N₀), ψ' = ψ₀ →
          ptOf (hC := contains_any T N₀) ψ' h' = ptOf (hC := contains_any T N₀) ψ₀ hψ₀ := by
        rintro _ _ rfl; rfl
      exact hr _ _ hcomp2)
  exact ⟨φ', by rw [← hφ₀, ← hφ']; rfl⟩

/-- **Fact 3.34 (i)** with **Proposition 3.29** on the site: `U` affine over `S`. -/
theorem attractorOrder_of_isAffineHom (aU : AAction (fppfO B S hS) M (yoneda.obj U)) :
    AttractorOrder (attractorImage aU) := by
  refine attractorOrder_of_mem_sInf aU fun s hne T t ht => ?_
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  refine exists_toPoint_of_sieve (BigFppfOver.isSheaf_of_type_yoneda_obj U)
    (fun T => toPoint_injective_affine _ T) t _ hcov ?_
  rintro Y g ⟨W, a, b, ⟨i⟩, rfl⟩
  have := hV i
  obtain ⟨φ, hφ⟩ := exists_sInf_affine (aU := aU) hne (T := V i) ((yoneda.obj U).map (π i).op t) (by
    intro N hN
    obtain ⟨χ, hχ⟩ := ht N hN
    exact ⟨AttractorPt.baseChange (π i) χ, by rw [AttractorPt.toPoint_baseChange, hχ]⟩)
  refine ⟨AttractorPt.baseChange a φ, ?_⟩
  rw [AttractorPt.toPoint_baseChange, hφ, ← Functor.map_comp_apply, ← op_comp]

end Affine

section Atlas

variable {M : Type u} [AddCommGroup M] [Fact (Cardinal.mk M < B.cutoff)]
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {f : yoneda.obj U ⟶ X}

/-- The units `N^×` of a magnet of a group, as a subgroup. -/
noncomputable def unitsSubgroup (N : AddSubmonoid M) : AddSubgroup M where
  toAddSubmonoid := unitsFace N
  neg_mem' := by
    intro x hx
    obtain ⟨y, hy, e⟩ := unitsFace_isGroup N hx
    rwa [neg_eq_of_add_eq_zero_right e]

lemma isFace_units (N : AddSubmonoid M) : IsFace (unitsSubgroup N).toAddSubmonoid N :=
  ⟨unitsFace_le N, fun hx hy h => faceCond_unitsFace N _ hx _ hy h⟩

/-- An equivariant atlas morphism is étale in the sense of Tag 03FR. -/
lemma isEtale_of_atlas (hat : IsEquivariantAtlas aU aX f) : Space.IsEtale B S hS f := by
  intro V φ hφ
  exact MorphismProperty.comp_mem _ _ _ hφ hat.etale

/-- The geometric step of **Proposition 15.5** (the diagram with Cartesian squares in its proof): a
point `x` of `X^L` lifts, after a surjective étale base change, to a point of `U^L`. One lifts the
point `p_{L,L^×}(x)`; it is fixed under `D(M/L^×)` by Proposition 3.35, its lift stays fixed since
`U → X` is strongly-FPR, and Proposition 5.1 then gives the point of `U^L`. -/
theorem exists_atlas_lift (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) (hat : IsStronglyFPRAtlas aU aX f) {L : AddSubmonoid M}
    {T : BigFppfOver B S hS} (x : AttractorPt aX L T) :
    ∃ (T' : BigFppfOver B S hS) (q : T' ⟶ T) (w : AttractorPt aU L T'),
      Surjective ((Sch).map q) ∧ Etale ((Sch).map q) ∧
      AttractorPt.push ⟨f, hat.atlas.equivariant⟩ w = AttractorPt.baseChange q x := by
  let F : EquivariantHom aU aX := ⟨f, hat.atlas.equivariant⟩
  let Z := unitsSubgroup L
  have hQ : IsFace Z.toAddSubmonoid L := isFace_units L
  let x₀ : AttractorPt aX Z.toAddSubmonoid T := AttractorPt.ofFace hQ x
  let g₀ : yoneda.obj T ⟶ X := yonedaEquiv.symm x₀.toPoint
  let rep := hat.atlas.etale.rep
  let T' := rep.pullback g₀
  let q : T' ⟶ T := rep.snd g₀
  let u : T' ⟶ U := rep.fst' g₀
  have hu : f.app (op T') u = X.map q.op x₀.toPoint := by
    have h2 : yoneda.map u ≫ f = yoneda.map q ≫ g₀ := by
      rw [Functor.relativelyRepresentable.map_fst']
      exact rep.w g₀
    have h3 := congrArg (fun k => k.app (op T') (𝟙 T')) h2
    have h4 : (yoneda.map u ≫ f).app (op T') (𝟙 T') = f.app (op T') u := by
      change f.app (op T') (𝟙 T' ≫ u) = _
      rw [Category.id_comp]
    have h5 : (yoneda.map q ≫ g₀).app (op T') (𝟙 T') = X.map q.op x₀.toPoint := by
      change g₀.app (op T') (𝟙 T' ≫ q) = _
      rw [Category.id_comp]
      simp [g₀, yonedaEquiv_symm_app_apply]
    exact h4.symm.trans (h3.trans h5)
  have hfix : u ∈ (fixedPoints (quotientAction aU Z)).obj (op T') := by
    refine (isFPR_iff (IsEquivariant.comap (actU := aU) (actX := aX) (f := f) hat.atlas.equivariant (QuotientAddGroup.mk' Z))).mp (hat.isStronglyFPR Z) (op T') u ?_
    rw [hu, ← AttractorPt.toPoint_baseChange]
    exact (AttractorPt.baseChange q x₀).toPoint_mem_fixedPoints
  have hsh : ∀ {W W' : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op W))
      (r : W' ⟶ W), Presieve.IsSheafFor (yoneda.obj U) ((extSieve (fppfO B S hS) Z a).pullback r).arrows :=
    fun a r => Final4Ext.isSheafFor_extSieve U Z a r
  let wZ : AttractorPt aU Z.toAddSubmonoid T' :=
    Final4Fix.attractorFixedEquivOfSheaf hsh T' ⟨u, hfix⟩
  have hwZ : wZ.toPoint = u := congrArg Subtype.val
    ((Final4Fix.attractorFixedEquivOfSheaf (act := aU) hsh T').symm_apply_apply ⟨u, hfix⟩)
  have hpush : AttractorPt.ofFace hQ (AttractorPt.baseChange q x) = AttractorPt.push F wZ := by
    apply attractor_toPoint_injective_sep hX hsep
    change (AttractorPt.baseChange q x₀).toPoint = f.app (op T') wZ.toPoint
    rw [AttractorPt.toPoint_baseChange, hwZ, hu]
  obtain ⟨w, hw⟩ := (isFaceCartesian_of_separated hX hsep hlim F (isEtale_of_atlas hat.atlas) hQ T').2
    ⟨(AttractorPt.baseChange q x, wZ), hpush⟩
  exact ⟨T', q, w, hat.atlas.surjective.property_snd g₀, hat.atlas.etale.property_snd g₀,
    congrArg (fun p => p.1.1) hw⟩

/-- **Proposition 15.5**, the key implication for `N ≤ L`. -/
theorem attractorImage_le_of_atlas (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) (hat : IsStronglyFPRAtlas aU aX f) {N L : AddSubmonoid M}
    (hU : attractorImage aU L ≤ attractorImage aU N) :
    attractorImage aX L ≤ attractorImage aX N := by
  rintro T _ ⟨x, rfl⟩
  obtain ⟨T', q, w, hs, he, hw⟩ := exists_atlas_lift hX hsep hlim hat x
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  refine exists_toPoint_of_sieve hsX (fun T => attractor_toPoint_injective_sep hX hsep N T) _ _
    (Space.sieve_generate_singleton_mem_topology_over B S hS q hs he) ?_
  rintro Y g ⟨W, a, b, ⟨⟩, rfl⟩
  obtain ⟨w', hw'⟩ := hU T' ⟨w, rfl⟩
  refine ⟨AttractorPt.baseChange a (AttractorPt.push ⟨f, hat.atlas.equivariant⟩ w'), ?_⟩
  have h1 : (AttractorPt.push ⟨f, hat.atlas.equivariant⟩ w').toPoint =
      (AttractorPt.baseChange q x).toPoint := by
    rw [← hw]
    exact congrArg (f.app (op T')) hw'
  rw [AttractorPt.toPoint_baseChange, h1, AttractorPt.toPoint_baseChange,
    ← Functor.map_comp_apply, ← op_comp]

/-- **Proposition 15.5.** Let `U → X` be an `S`-affine strongly-FPR atlas of the separated algebraic
space `X`, locally of finite presentation over `S` in the form `IsLimitPreserving`, `M` an abelian
group. Then `U^N = U^L` implies `X^N = X^L`. -/
theorem prop155 (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) (hat : IsStronglyFPRAtlas aU aX f) {N L : AddSubmonoid M}
    (hU : attractorImage aU N = attractorImage aU L) :
    attractorImage aX N = attractorImage aX L := by
  have hord := attractorOrder_of_isAffineHom aU
  have hinf : attractorImage aU (N ⊓ L) = attractorImage aU N := by
    rw [← sInf_pair]
    refine hord.sInf_of_const _ _ ⟨N, by simp⟩ ?_
    rintro K (rfl | rfl)
    · rfl
    · exact hU.symm
  have key : ∀ K : AddSubmonoid M, attractorImage aU K = attractorImage aU N →
      attractorImage aX K ≤ attractorImage aX (N ⊓ L) := fun K hK =>
    attractorImage_le_of_atlas hX hsep hlim hat (by rw [hK, hinf])
  exact le_antisymm
    ((key N rfl).trans (attractorImage_monotone aX inf_le_right))
    ((key L hU.symm).trans (attractorImage_monotone aX inf_le_left))

/-- **Proposition 15.5**, last assertion: `Π(a_X) ⊆ Π(a_U)`. -/
theorem prop155_pure (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) (hat : IsStronglyFPRAtlas aU aX f) :
    pureMagnets (attractorImage aX) ⊆ pureMagnets (attractorImage aU) :=
  pureMagnets_subset_of_reflects fun _ _ h => prop155 hX hsep hlim hat h

/-- **Theorem 15.4 (ii)** and **Remark 15.6**, reduced to the `S`-affine atlas: if `U` has finitely many
pure magnets then so has `X`, and `X` has finitely many attractors. The second assertion does not use
Fact 3.34 for `X`. -/
theorem finite_of_atlas (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) (hat : IsStronglyFPRAtlas aU aX f)
    (hfin : (pureMagnets (attractorImage aU)).Finite) :
    (pureMagnets (attractorImage aX)).Finite ∧ (Set.range (attractorImage aX)).Finite := by
  refine ⟨hfin.subset (prop155_pure hX hsep hlim hat), ?_⟩
  have hord := attractorOrder_of_isAffineHom aU
  refine (hfin.image (attractorImage aX)).subset ?_
  rintro _ ⟨N, rfl⟩
  exact ⟨pureOf (attractorImage aU) (attractorImage aU N),
    isPure_pureOf hord ⟨N, rfl⟩, prop155 hX hsep hlim hat (map_pureOf hord ⟨N, rfl⟩)⟩

end Atlas

section Finite

variable {M : Type u} [AddCommMonoid M] [Fact (Cardinal.mk M < B.cutoff)]
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
variable {Y T₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]

/-- `Γ(T₀) → Γ(Y)`. -/
noncomputable abbrev secMap (s : Y ⟶ T₀) : RT T₀ →+* RT Y := ((Sch).map s).appTop.hom

lemma spOver_w (s : Y ⟶ T₀) {R' : Type u} [CommRing R'] (ρ : RT Y →+* R') :
    Spec.map (CommRingCat.ofHom (ρ.comp (secMap s))) ≫ ((Sch).obj T₀).isoSpec.inv ≫ T₀.hom.hom =
      Spec.map (CommRingCat.ofHom ρ) ≫ ((Sch).obj Y).isoSpec.inv ≫ Y.hom.hom := by
  have h₁ := Scheme.isoSpec_inv_naturality ((Sch).map s)
  have h₂ : Spec.map (CommRingCat.ofHom (ρ.comp (secMap s))) =
      Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map ((Sch).map s).appTop := by
    rw [← Spec.map_comp]
    rfl
  rw [h₂, Category.assoc, ← Category.assoc (Spec.map ((Sch).map s).appTop), h₁, Category.assoc,
    site_w s]

/-- For `s : Y ⟶ T₀`, the morphism `Spec R' → Y`, the source being seen over `T₀`. -/
noncomputable def spOver (s : Y ⟶ T₀) {R' : Type u} [CommRing R'] (ρ : RT Y →+* R')
    (hC : B.Contains (Spec (.of R'))) : spObj T₀ (ρ.comp (secMap s)) hC ⟶ Y :=
  siteHom (Spec.map (CommRingCat.ofHom ρ) ≫ ((Sch).obj Y).isoSpec.inv) (spOver_w s ρ).symm

/-- The identity of `Spec R'`, from over `Y` to over `T₀`. -/
noncomputable def spConv (s : Y ⟶ T₀) {R' : Type u} [CommRing R'] (ρ : RT Y →+* R')
    (hC : B.Contains (Spec (.of R'))) : spObj Y ρ hC ⟶ spObj T₀ (ρ.comp (secMap s)) hC :=
  siteHom (𝟙 _) ((Category.id_comp _).trans (spOver_w s ρ))

lemma spConv_spOver (s : Y ⟶ T₀) {R' : Type u} [CommRing R'] (ρ : RT Y →+* R')
    (hC : B.Contains (Spec (.of R'))) : spConv s ρ hC ≫ spOver s ρ hC = spToT Y ρ hC :=
  site_hom_ext (Category.id_comp _)

lemma spMap_spConv (s : Y ⟶ T₀) {R' R'' : Type u} [CommRing R'] [CommRing R''] {ρ : RT Y →+* R'}
    {ρ' : RT Y →+* R''} (hC : B.Contains (Spec (.of R'))) (hC' : B.Contains (Spec (.of R'')))
    (π : R' →+* R'') (hπ : π.comp ρ = ρ') :
    spMap Y (hC := hC) (hC' := hC') π hπ ≫ spConv s ρ hC =
      spConv s ρ' hC' ≫ spMap T₀ (hC := hC) (hC' := hC') π
        (by rw [← RingHom.comp_assoc, hπ]) :=
  site_hom_ext ((Category.comp_id _).trans (Category.id_comp _).symm)

lemma spMap_spOver (s : Y ⟶ T₀) {R' R'' : Type u} [CommRing R'] [CommRing R''] {ρ : RT Y →+* R'}
    {ρ' : RT Y →+* R''} (hC : B.Contains (Spec (.of R'))) (hC' : B.Contains (Spec (.of R'')))
    (π : R' →+* R'') (hπ : π.comp ρ = ρ') :
    spMap T₀ (hC := hC) (hC' := hC') π (by rw [← RingHom.comp_assoc, hπ]) ≫ spOver s ρ hC =
      spOver s ρ' hC' := by
  subst hπ
  refine site_hom_ext ?_
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- `R[N] → R[M]`. -/
noncomputable def thetaN (R : Type u) [CommRing R] (N : AddSubmonoid M) :
    RH (AddMonoidAlgebra R N) (AddMonoidAlgebra R M) :=
  AddMonoidAlgebra.mapDomainRingHom _ N.subtype

/-- The ring map to `R[N]` of a point of `U^N(Y)`, seen over `T₀`, composed with `R[N] → R[M]`, is
`ψ₀[M] ∘ γ`: the coaction computes the value of the point on `R[N]`. -/
theorem theta_comp_eq (s : Y ⟶ T₀) {N : AddSubmonoid M} (φ : AttractorPt aU N Y)
    {γ : RH (chartA T₀ U) (AddMonoidAlgebra (chartA T₀ U) M)}
    (hγ : γ.comp (chartα T₀ U) = (jr _ M).comp (chartα T₀ U))
    (hγp : ∀ {R' : Type u} [CommRing R'] {ρ : RT T₀ →+* R'} (hC : B.Contains (Spec (.of R')))
        (ψ : chartA T₀ U →+* R') (hψ : ψ.comp (chartα T₀ U) = ρ),
        aU.smul (U := op (spObj T₀ ((jr R' M).comp ρ) (contains_M hC))) (spPt (eM R' M))
          (spMap T₀ (hC := hC) (hC' := contains_M hC) (jr R' M) rfl ≫ ptOf ψ hψ) =
        ptOf (hC := contains_M hC) ((mapR ψ M).comp γ) (by
          rw [RingHom.comp_assoc, hγ, ← RingHom.comp_assoc, mapR_jr, RingHom.comp_assoc, hψ]))
    (ψ₀ : chartA T₀ U →+* RT Y) (hψ₀ : ψ₀.comp (chartα T₀ U) = (RingHom.id _).comp (secMap s))
    (e₀ : ptOf (hC := contains_RT Y) ψ₀ hψ₀ =
      φ.app (spOver s (RingHom.id _) (contains_RT Y)) 1)
    (ψ : chartA T₀ U →+* AddMonoidAlgebra (RT Y) N)
    (hψ : ψ.comp (chartα T₀ U) = (ρN Y N).comp (secMap s))
    (e : ptOf (hC := contains_any Y N) ψ hψ =
      φ.app (spOver s (ρN Y N) (contains_any Y N)) (spPt (monN _ N))) :
    (thetaN (RT Y) N).comp ψ = (mapR ψ₀ M).comp γ := by
  have hR := contains_RT Y
  have hθ : (thetaN (RT Y) N).comp ((ρN Y N).comp (secMap s)) =
      (jr (RT Y) M).comp ((RingHom.id _).comp (secMap s)) := by
    refine RingHom.ext fun x => ?_
    change AddMonoidAlgebra.mapDomainRingHom _ N.subtype (AddMonoidAlgebra.single 0 _) =
      AddMonoidAlgebra.single 0 _
    simp
  let t_M := spOver s (jr (RT Y) M) (contains_M hR)
  -- the equivariance of `φ`
  have h1 := φ.equivariant (T' := spObj T₀ ((jr (RT Y) M).comp ((RingHom.id _).comp (secMap s)))
      (contains_M hR)) t_M (spPt (eM (RT Y) M)) 1
  have h2 : APt.toMagnet N (spPt (T := T₀) (ρ := (jr (RT Y) M).comp ((RingHom.id _).comp (secMap s)))
      (hC := contains_M hR) (eM (RT Y) M)) * 1 =
      APt.res (spMap T₀ (hC := contains_any Y N) (hC' := contains_M hR) (thetaN (RT Y) N) hθ).op
        (spPt (monN _ N)) := by
    rw [mul_one, spPt_res]
    refine MonoidHom.ext fun p => ?_
    refine congrArg (spSec T₀ ((jr (RT Y) M).comp ((RingHom.id _).comp (secMap s))) (contains_M hR)) ?_
    change AddMonoidAlgebra.single ((Multiplicative.toAdd p : N) : M) 1 =
      AddMonoidAlgebra.mapDomainRingHom _ N.subtype
        (AddMonoidAlgebra.single (Multiplicative.toAdd p) 1)
    simp
  have h3 : φ.app t_M (APt.res (spMap T₀ (hC := contains_any Y N) (hC' := contains_M hR)
      (thetaN (RT Y) N) hθ).op (spPt (monN _ N))) =
      spMap T₀ (hC := contains_any Y N) (hC' := contains_M hR) (thetaN (RT Y) N) hθ ≫
        ptOf ψ hψ := by
    rw [e]
    have := φ.naturality (spMap T₀ (hC := contains_any Y N) (hC' := contains_M hR)
      (thetaN (RT Y) N) hθ) (spOver s (ρN Y N) (contains_any Y N)) (spPt (monN _ N))
    have ht : spMap T₀ (hC := contains_any Y N) (hC' := contains_M hR) (thetaN (RT Y) N) hθ ≫
        spOver s (ρN Y N) (contains_any Y N) = t_M := by
      refine site_hom_ext ?_
      change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      · 
        change AddMonoidAlgebra.mapDomainRingHom _ N.subtype (AddMonoidAlgebra.single 0 x) =
          AddMonoidAlgebra.single 0 x
        simp
    rw [ht] at this
    exact this
  have h4 : φ.app t_M 1 = spMap T₀ (hC := hR) (hC' := contains_M hR) (jr (RT Y) M) rfl ≫
      ptOf ψ₀ hψ₀ := by
    rw [e₀]
    have := φ.naturality (spMap T₀ (hC := hR) (hC' := contains_M hR) (jr (RT Y) M) rfl)
      (spOver s (RingHom.id _) hR) 1
    have ht : spMap T₀ (hC := hR) (hC' := contains_M hR) (jr (RT Y) M) rfl ≫
        spOver s (RingHom.id _) hR = t_M := by
      refine site_hom_ext ?_
      change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
    rw [ht] at this
    have hone : APt.res (spMap T₀ (hC := hR) (hC' := contains_M hR) (jr (RT Y) M) rfl).op
        (1 : APt (fppfO B S hS) N (op (spObj T₀ ((RingHom.id _).comp (secMap s)) hR))) = 1 := by
      ext p; simp
    rw [hone] at this
    exact this
  rw [h2, h3, h4, hγp hR ψ₀ hψ₀, spMap_comp_ptOf] at h1
  exact ptOf_injective _ _ h1

/-- **Theorem 15.4 (i)**, the local step: if `γ` of `T₀` has degrees in `E` on generators of
`Γ(U_{T₀})` over `Γ(T₀)`, then for `Y → T₀` a point of `U^N(Y)` lies in `U^{⟨N ∩ E⟩}(Y)`. -/
theorem exists_closure_inter (s : Y ⟶ T₀) {E : Set M} {G : Set (chartA T₀ U)}
    (hG : ∀ a : chartA T₀ U, a ∈ Subring.closure (Set.range (chartα T₀ U) ∪ G))
    {γ : RH (chartA T₀ U) (AddMonoidAlgebra (chartA T₀ U) M)}
    (hE : ∀ g ∈ G, ∀ m, (γ g).coeff m ≠ 0 → m ∈ E)
    (hγ : γ.comp (chartα T₀ U) = (jr _ M).comp (chartα T₀ U))
    (hγp : ∀ {R' : Type u} [CommRing R'] {ρ : RT T₀ →+* R'} (hC : B.Contains (Spec (.of R')))
        (ψ : chartA T₀ U →+* R') (hψ : ψ.comp (chartα T₀ U) = ρ),
        aU.smul (U := op (spObj T₀ ((jr R' M).comp ρ) (contains_M hC))) (spPt (eM R' M))
          (spMap T₀ (hC := hC) (hC' := contains_M hC) (jr R' M) rfl ≫ ptOf ψ hψ) =
        ptOf (hC := contains_M hC) ((mapR ψ M).comp γ) (by
          rw [RingHom.comp_assoc, hγ, ← RingHom.comp_assoc, mapR_jr, RingHom.comp_assoc, hψ]))
    {N : AddSubmonoid M} (φ : AttractorPt aU N Y) :
    ∃ φ' : AttractorPt aU (AddSubmonoid.closure ((N : Set M) ∩ E)) Y, φ'.toPoint = φ.toPoint := by
  classical
  set P := AddSubmonoid.closure ((N : Set M) ∩ E) with hPdef
  have hP : P ≤ N := AddSubmonoid.closure_le.mpr Set.inter_subset_left
  have hR := contains_RT Y
  obtain ⟨ψ₀, hψ₀, e₀⟩ := exists_ptOf (T := T₀) (U := U) (hC := hR)
    (φ.app (spOver s (RingHom.id _) hR) 1)
  obtain ⟨ψ, hψ, e⟩ := exists_ptOf (T := T₀) (U := U) (hC := contains_any Y N)
    (φ.app (spOver s (ρN Y N) (contains_any Y N)) (spPt (monN _ N)))
  have hθ := theta_comp_eq s φ hγ hγp ψ₀ hψ₀ e₀ ψ hψ e
  have hgen : ∀ g ∈ G, ψ g ∈ (inclR Y hP).range := by
    intro g hg
    refine mem_range_incl hP _ fun n hn => ?_
    refine AddSubmonoid.subset_closure ⟨n.2, hE g hg n ?_⟩
    intro h0
    have h1 : (thetaN (RT Y) N (ψ g)).coeff (n : M) = (ψ g).coeff n :=
      Finsupp.mapDomain_apply N.subtype_injective _ _
    have h2 : thetaN (RT Y) N (ψ g) = mapR ψ₀ M (γ g) := DFunLike.congr_fun hθ g
    have h3 : (mapR ψ₀ M (γ g)).coeff (n : M) = ψ₀ ((γ g).coeff (n : M)) :=
      Finsupp.mapRange_apply (hf := map_zero ψ₀)
    rw [h2, h3, h0, map_zero] at h1
    exact hn h1.symm
  have hmem : ∀ a, ψ a ∈ (inclR Y hP).range := by
    intro a
    have hc := hG a
    induction hc using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨r, rfl⟩ | hx
      · refine ⟨ρN Y P (secMap s r), ?_⟩
        have h1 := DFunLike.congr_fun hψ r
        have h2 := DFunLike.congr_fun (incl_ρN (T := Y) hP) (secMap s r)
        exact h2.trans h1.symm
      · exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | one => rw [map_one]; exact one_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have hinj := incl_injective Y hP
  let e' : AddMonoidAlgebra (RT Y) P ≃+* (inclR Y hP).range :=
    RingEquiv.ofBijective (inclR Y hP).rangeRestrict
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), (inclR Y hP).rangeRestrict_surjective⟩
  let ψP : chartA T₀ U →+* AddMonoidAlgebra (RT Y) P :=
    (e'.symm : _ →+* _).comp (ψ.codRestrict (inclR Y hP).range hmem)
  have hψP : ∀ a, inclR Y hP (ψP a) = ψ a := fun a => by
    have := e'.apply_symm_apply (ψ.codRestrict (inclR Y hP).range hmem a)
    exact congrArg Subtype.val this
  have hα : ψP.comp (chartα T₀ U) = (ρN Y P).comp (secMap s) := by
    refine RingHom.ext fun x => hinj ?_
    change inclR Y hP (ψP (chartα T₀ U x)) = (inclR Y hP).comp (ρN Y P) (secMap s x)
    rw [hψP, incl_ρN]
    exact DFunLike.congr_fun hψ x
  have hcomp2 : (inclR Y hP).comp ψP = ψ := RingHom.ext hψP
  obtain ⟨φ', hφ'⟩ := exists_ofLE_of_pull (hasDensePullback_yoneda U) hP φ
    (spConv s (ρN Y P) (contains_any Y P) ≫ ptOf (hC := contains_any Y P) ψP hα) (by
      change spMap Y (hC := contains_any Y P) (hC' := contains_any Y N) (inclR Y hP) (incl_ρN hP) ≫
        spConv s (ρN Y P) (contains_any Y P) ≫ ptOf (hC := contains_any Y P) ψP hα = _
      rw [← Category.assoc, spMap_spConv, Category.assoc, spMap_comp_ptOf]
      have hr : ∀ (ψ' : chartA T₀ U →+* AddMonoidAlgebra (RT Y) N)
          (h' : ψ'.comp (chartα T₀ U) = (ρN Y N).comp (secMap s)), ψ' = ψ →
          ptOf (hC := contains_any Y N) ψ' h' = ptOf (hC := contains_any Y N) ψ hψ := by
        rintro _ _ rfl; rfl
      rw [hr _ _ hcomp2, e]
      have hn := φ.naturality (spConv s (ρN Y N) (contains_any Y N))
        (spOver s (ρN Y N) (contains_any Y N)) (spPt (monN _ N))
      rw [spConv_spOver] at hn
      exact hn.symm)
  exact ⟨φ', by rw [← hφ']; rfl⟩

/-- `Γ(T) → Γ(U_T)` is of finite type when `U → S` is locally of finite type. -/
lemma finiteType_chartα (T U : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] [IsAffineHom U.hom.hom]
    [LocallyOfFiniteType U.hom.hom] : (chartα T U).FiniteType := by
  have hW := (IsPullback.of_hasPullback (Over.mkIdTerminal.from T : T ⟶ siteTop)
    (Over.mkIdTerminal.from U : U ⟶ siteTop)).map (Sch)
  have htU : LocallyOfFiniteType ((Sch).map (Over.mkIdTerminal.from U : U ⟶ siteTop)) := by
    have : (Sch).map (Over.mkIdTerminal.from U : U ⟶ siteTop) = U.hom.hom := by
      have := site_w (Over.mkIdTerminal.from U : U ⟶ siteTop)
      simpa using this
    rw [this]; infer_instance
  have hp₁ : LocallyOfFiniteType ((Sch).map (chartFst T U)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hW.flip htU
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hp₁

/-- Finitely many elements generate `Γ(U_T)` over `Γ(T)`, with finitely many degrees for the coaction:
the proof of **Theorem 15.4 (i)** on one chart. -/
theorem exists_chart_degrees (T U : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] [IsAffineHom U.hom.hom]
    [LocallyOfFiniteType U.hom.hom] (γ : RH (chartA T U) (AddMonoidAlgebra (chartA T U) M)) :
    ∃ (G : Set (chartA T U)) (E : Set M), E.Finite ∧
      (∀ a : chartA T U, a ∈ Subring.closure (Set.range (chartα T U) ∪ G)) ∧
      ∀ g ∈ G, ∀ m, (γ g).coeff m ≠ 0 → m ∈ E := by
  classical
  have hft := finiteType_chartα T U
  algebraize [chartα T U]
  obtain ⟨G, hG⟩ := (inferInstance : Algebra.FiniteType (RT T) (chartA T U)).out
  refine ⟨G, ↑(G.biUnion fun g => (γ g).coeff.support), Finset.finite_toSet _, fun a => ?_,
    fun g hg m hm => ?_⟩
  · have ha : a ∈ Algebra.adjoin (RT T) (G : Set (chartA T U)) := by
      rw [hG]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem y hy => exact Subring.subset_closure (Or.inr hy)
    | algebraMap r => exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    | add x y _ _ hx hy => exact Subring.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subring.mul_mem _ hx hy
  · exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨g, hg, Finsupp.mem_support_iff.mpr hm⟩)

/-- The key step of **Theorem 15.4 (i)**: for `U` of finite type and affine over a quasi-compact `S`,
there is a finite set `E ⊆ M` such that `U^N = U^{⟨N ∩ E⟩}` for all magnets `N`. -/
theorem exists_finite_degrees_site [CompactSpace S] [LocallyOfFiniteType U.hom.hom]
    (aU : AAction (fppfO B S hS) M (yoneda.obj U)) :
    ∃ E : Set M, E.Finite ∧ ∀ N : AddSubmonoid M,
      attractorImage aU N = attractorImage aU (AddSubmonoid.closure ((N : Set M) ∩ E)) := by
  classical
  have hC : ∀ V : S.affineOpens, B.Contains (V.1 : Scheme.{u}) := fun V =>
    Scheme.size_lt_of_isOpenImmersion V.1.ι hS
  let TV : S.affineOpens → BigFppfOver B S hS := fun V => siteObject B S hS (hC V) V.1.ι
  have hTV : ∀ V, IsAffine ((Sch).obj (TV V)) := fun V => V.2
  have hch := fun V => (haveI := hTV V; exists_gamma (TV V) U aU)
  choose γ hγ hγp using hch
  have hdeg := fun V => (haveI := hTV V; exists_chart_degrees (TV V) U (γ V))
  choose G Es hEs hG hE using hdeg
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun V : S.affineOpens => (V.1 : Set S))
    (fun V => V.1.isOpen) (fun x _ => by
      obtain ⟨V, y, hy⟩ := S.directedAffineCover.exists_eq x
      exact Set.mem_iUnion.mpr ⟨V, by rw [← hy]; exact y.2⟩)
  refine ⟨⋃ V ∈ F, Es V, F.finite_toSet.biUnion fun V _ => hEs V, fun N => ?_⟩
  set E : Set M := ⋃ V ∈ F, Es V with hEdef
  refine le_antisymm ?_ (attractorImage_monotone aU
    (AddSubmonoid.closure_le.mpr Set.inter_subset_left))
  rintro T _ ⟨φ, rfl⟩
  -- the affine opens of `T` lying over a chart
  let I := {W : ((Sch).obj T).affineOpens //
    ∃ V ∈ F, Set.range (W.1.ι ≫ T.hom.hom) ⊆ (V.1 : Set S)}
  have hCI : ∀ i : I, B.Contains (i.1.1 : Scheme.{u}) := fun i =>
    Scheme.size_lt_of_isOpenImmersion i.1.1.ι T.left.property
  let W : I → BigFppfOver B S hS := fun i => siteObject B S hS (hCI i) (i.1.1.ι ≫ T.hom.hom)
  let π : ∀ i, W i ⟶ T := fun i => siteHom i.1.1.ι rfl
  have hcov : Sieve.ofArrows W π ∈ BigFppfOver.topology B S hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS π
      (fun i => inferInstanceAs (IsOpenImmersion i.1.1.ι)) fun x => ?_
    obtain ⟨V, hV⟩ := Set.mem_iUnion.mp (hF (Set.mem_univ (T.hom.hom x)))
    obtain ⟨hVF, hxV⟩ := Set.mem_iUnion.mp hV
    let O : ((Sch).obj T).Opens := T.hom.hom ⁻¹ᵁ V.1
    obtain ⟨_, ⟨W', hW', rfl⟩, hx, hsub⟩ := ((Sch).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (O : Set _) from hxV) O.isOpen
    refine ⟨⟨⟨W', hW'⟩, V, hVF, ?_⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    rintro _ ⟨y, rfl⟩
    exact hsub y.2
  refine exists_toPoint_of_sieve (BigFppfOver.isSheaf_of_type_yoneda_obj U)
    (fun T => toPoint_injective_affine _ T) _ _ hcov ?_
  rintro Y g ⟨Z, a, b, ⟨i⟩, rfl⟩
  obtain ⟨V, hVF, hr⟩ := i.2
  have hW : IsAffine ((Sch).obj (W i)) := i.1.2
  have := hTV V
  let s : W i ⟶ TV V := siteHom (IsOpenImmersion.lift V.1.ι (i.1.1.ι ≫ T.hom.hom) (by
    rw [Scheme.Opens.range_ι]; exact hr)) (IsOpenImmersion.lift_fac _ _ _)
  obtain ⟨φ', hφ'⟩ := exists_closure_inter (aU := aU) (Y := W i) s (hG V) (hE V) (hγ V) (hγp V)
    (AttractorPt.baseChange (π i) φ)
  have hgen : AddSubmonoid.closure ((N : Set M) ∩ Es V) ≤ AddSubmonoid.closure ((N : Set M) ∩ E) :=
    AddSubmonoid.closure_mono (Set.inter_subset_inter_right _ (Set.subset_biUnion_of_mem hVF))
  refine ⟨AttractorPt.baseChange a (AttractorPt.ofLE hgen φ'), ?_⟩
  rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_ofLE, hφ', AttractorPt.toPoint_baseChange,
    ← Functor.map_comp_apply, ← op_comp]

/-- **Theorem 15.4 (i)**, with **Remark 15.6**. `U` affine and of finite type over a **quasi-compact**
`S` (a hypothesis the statement needs, see the file header), `M` a commutative monoid:
`Π(a)` is finite, and so is the set of attractors. -/
theorem thm154_i [CompactSpace S] [LocallyOfFiniteType U.hom.hom]
    (aU : AAction (fppfO B S hS) M (yoneda.obj U)) :
    (pureMagnets (attractorImage aU)).Finite ∧ (Set.range (attractorImage aU)).Finite := by
  obtain ⟨E, hE, h⟩ := exists_finite_degrees_site aU
  have hfin := finite_pureMagnets_of_inter hE h
  have hord := attractorOrder_of_isAffineHom aU
  refine ⟨hfin, (hfin.image (attractorImage aU)).subset ?_⟩
  rintro y hy
  exact ⟨_, isPure_pureOf hord hy, map_pureOf hord hy⟩

end Finite

section FiniteGroup

variable {M : Type u} [AddCommGroup M] [Fact (Cardinal.mk M < B.cutoff)]
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}

/-- "`X` is locally of finite type over `S`": every étale chart is. It holds for `X` finitely presented
over `S`, the hypothesis of Theorem 15.4. -/
def ChartsOfFiniteType (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ X),
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ → LocallyOfFiniteType V.hom.hom

/-- **Theorem 15.4 (ii)**, with **Remark 15.6**. `M` an abelian group, `S`
quasi-compact, `X` a separated algebraic space locally of finite presentation over `S`, with an
`S`-affine strongly-FPR atlas: `Π(a)` is finite, and so is the set of attractors `X^N ⊆ X`. -/
theorem thm154_ii [CompactSpace S] (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) (hft : ChartsOfFiniteType X) {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) :
    (pureMagnets (attractorImage aX)).Finite ∧ (Set.range (attractorImage aX)).Finite := by
  have : LocallyOfFiniteType U.hom.hom := hft U f hat.atlas.etale
  exact finite_of_atlas hX hsep hlim hat (thm154_i aU).1

/-- **Remark 15.6**, as printed: the set of `X^{D(M/Z)} = X^Z` for subgroups `Z ⊆ M` is finite. -/
theorem rem156 [CompactSpace S] (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hlim : IsLimitPreserving X) (hft : ChartsOfFiniteType X) {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) :
    (Set.range fun Z : AddSubgroup M => attractorImage aX Z.toAddSubmonoid).Finite :=
  (thm154_ii hX hsep hlim hft hat).2.subset (by rintro _ ⟨Z, rfl⟩; exact ⟨_, rfl⟩)

/-- Conjecture 6.9 (ii), in the form used by **Remark 15.8**, over `S` and for `M`. -/
def Conj69ii (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] : Prop :=
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (aX : AAction (fppfO B S hS) M X),
    IsAlgebraicSpace B S hS X → IsSeparatedOver X → IsLimitPreserving X → ChartsOfFiniteType X →
    ∃ (U : BigFppfOver B S hS) (_ : IsAffineHom U.hom.hom)
      (aU : AAction (fppfO B S hS) M (yoneda.obj U)) (f : yoneda.obj U ⟶ X),
      IsStronglyFPRAtlas aU aX f

/-- **Remark 15.8.** Conjecture 6.9 implies the finiteness of Conjecture 15.7. (This is an implication
between conjectures; neither is proved.) `S` is quasi-compact, as it must be. -/
theorem rem158 [CompactSpace S] (hc : Conj69ii B S hS M) (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X) (hft : ChartsOfFiniteType X) :
    (pureMagnets (attractorImage aX)).Finite := by
  obtain ⟨U, hU, aU, f, hat⟩ := hc X aX hX hsep hlim hft
  exact (thm154_ii hX hsep hlim hft hat).1

/-- **Theorem 15.4 (ii)**, with **Remark 15.6**, for an arbitrary abelian group `M` (with `#M` below
the cutoff of the site). -/
alias thm154_ii_any := thm154_ii

/-- **Proposition 15.5**, for an arbitrary abelian group `M` (with `#M` below the cutoff of the site). -/
alias prop155_any := prop155

end FiniteGroup

section Examples

variable {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {F : Cᵒᵖ ⥤ Type u}
variable {M : Type*} [AddCommMonoid M]

/-- The trivial action of `𝔸(M)` on any functor. -/
def AAction.trivial (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (M : Type*) [AddCommMonoid M] (F : Cᵒᵖ ⥤ Type u) :
    AAction 𝒪 M F where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  map_smul _ _ _ := rfl

/-- **Example 15.10 (i)** for an arbitrary space: the trivial action has `Π(a) = {0}`. -/
theorem pureMagnets_trivial_action :
    pureMagnets (attractorImage (AAction.trivial 𝒪 M F)) = {⊥} := by
  have htop : ∀ N : AddSubmonoid M, attractorImage (AAction.trivial 𝒪 M F) N = fun _ => Set.univ := by
    intro N
    funext T
    refine Set.eq_univ_of_forall fun x => ?_
    refine ⟨⟨fun t _ => F.map t.op x, fun s t _ => ?_, fun _ _ _ => rfl⟩, ?_⟩
    · rw [op_comp, Functor.map_comp_apply]
    · change F.map (𝟙 T).op x = x
      simp
  ext N
  simp only [Set.mem_singleton_iff]
  exact ⟨fun hN => le_bot_iff.mp (hN ⊥ ((htop N).trans (htop ⊥).symm)), fun e => e ▸ isPure_bot⟩

end Examples

end AlgMag

#print axioms AlgMag.attractorImage_monotone
#print axioms AlgMag.attractorOrder_affine
#print axioms AlgMag.attractorOrder_of_isAffineHom
#print axioms AlgMag.IsPure.attractorImage_lt
#print axioms AlgMag.exists_atlas_lift
#print axioms AlgMag.prop155
#print axioms AlgMag.prop155_pure
#print axioms AlgMag.finite_of_atlas
#print axioms AlgMag.thm154_i
#print axioms AlgMag.thm154_ii
#print axioms AlgMag.rem156
#print axioms AlgMag.rem158
#print axioms AlgMag.pureMagnets_trivial_action
