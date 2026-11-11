/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec6Atlas

/-!
# From equivariant étale charts to `Z`-FPR atlases (Theorem 6.8 = A.2, gluing step)

Mayeux, *Algebraic Magnetism*, §6 and proof of Theorem A.2: "consider `U := ⨆_x U(x)`".

* `AlgMag.EtaleChartFamily`: jointly surjective equivariant étale `S`-affine charts.
* `AlgMag.isZFPRAtlas_of_family`: the coproduct of a family of `Z`-FPR charts is a `Z`-FPR atlas.
* `AlgMag.isSAffineAtlas_of_family`: for a finite family it is `S`-affine.
* `AlgMag.isZFPRAtlas_of_family_irreducible`: case (ii) of Theorem 6.8, where each chart is
  automatically `Z`-FPR by Theorem A.1.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A jointly surjective family of equivariant étale morphisms to `X` from `S`-affine schemes. -/
structure EtaleChartFamily (actX : AAction (fppfO B S hS) M X) (A : Type u)
    (U : A → BigFppfOver B S hS) where
  /-- The action on each chart. -/
  act : ∀ a, AAction (fppfO B S hS) M (yoneda.obj (U a))
  /-- The morphism to `X`. -/
  f : ∀ a, yoneda.obj (U a) ⟶ X
  equivariant : ∀ a, IsEquivariant (act a) actX (f a)
  etale : ∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (f a)
  isAffineHom : ∀ a, IsAffineHom (structMap (U a))
  covers : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X) (t : (SCH).obj T),
    ∃ a, t ∈ Set.range ((SCH).map ((etale a).rep.snd x))

variable {A : Type u} {U : A → BigFppfOver B S hS} {V : BigFppfOver B S hS} {j : ∀ a, U a ⟶ V}

/-- The coproduct of a chart family is an equivariant atlas; the pieces are the affine decomposition. -/
theorem exists_atlas_of_family (hX : IsAlgebraicSpace B S hS X) {actX : AAction (fppfO B S hS) M X}
    (L : EtaleChartFamily actX A U) (hV : IsColimit (Cofan.mk V j)) :
    ∃ v : yoneda.obj V ⟶ X, (∀ (a : A) {Y : BigFppfOver B S hS} (c : Y ⟶ U a),
        v.app (op Y) (c ≫ j a) = (L.f a).app (op Y) c) ∧
      IsEquivariantAtlas (coprodAction L.act hV) actX v := by
  have hoi := fun a => isOpenImmersion_toScheme_map_cofan hV a
  have hXs : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  obtain ⟨v, hv⟩ := exists_hom_yoneda_of_isColimit_cofan
    (F := fun _ : A => (⟨X, hX.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)))
    (P := ⟨X, hX.isSheaf⟩) (fun _ => 𝟙 _) (U := U) (fun a => L.f a) hV
  have hv' : ∀ (a : A) {Y : BigFppfOver B S hS} (c : Y ⟶ U a),
      v.app (op Y) (c ≫ j a) = (L.f a).app (op Y) c := by
    intro a Y c
    have := congrArg (fun k => k.app (op Y) c) (hv a)
    exact this
  refine ⟨v, hv', ?_⟩
  let actV := coprodAction L.act hV
  have heq : IsEquivariant actV actX v := by
    intro T h t
    refine (hXs _ (cutSieve_mem hV (T := unop T) t)).isSeparatedFor.ext ?_
    rintro Y i ⟨a, c, hc⟩
    have h1 : X.map i.op (v.app T (actV.smul h t)) = v.app (op Y) (i ≫ actV.smul h t) :=
      (NatTrans.naturality_apply v i.op _).symm
    have h2 : X.map i.op (v.app T t) = v.app (op Y) (i ≫ t) :=
      (NatTrans.naturality_apply v i.op _).symm
    rw [h1, coprodAction_spec L.act hV h t i a c hc, hv', L.equivariant, actX.map_smul, h2, hc, hv']
  have hdec := coprod_decomposition L.act hV L.isAffineHom
  have hrep : yoneda.relativelyRepresentable v := hX.diagonal_representable.of_diag v
  have hpiece : ∀ {T P : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X) (fst : yoneda.obj P ⟶ yoneda.obj V)
      (snd : P ⟶ T), IsPullback fst (yoneda.map snd) v g → ∀ a : A,
      ∃ n : (L.etale a).rep.pullback g ⟶ P, n ≫ snd = (L.etale a).rep.snd g ∧
        n ≫ yoneda.preimage fst = (L.etale a).rep.fst' g ≫ j a := by
    intro T P g fst snd hpb a
    have hc : (yoneda.map ((L.etale a).rep.fst' g ≫ j a)) ≫ v =
        yoneda.map ((L.etale a).rep.snd g) ≫ g := by
      have h1 : yoneda.map (j a) ≫ v = L.f a := (hv a).trans (Category.comp_id (L.f a))
      rw [yoneda.map_comp, Category.assoc, h1, Functor.relativelyRepresentable.map_fst']
      exact (L.etale a).rep.w g
    let l := hpb.lift _ _ hc
    have hl₁ : l ≫ fst = yoneda.map ((L.etale a).rep.fst' g ≫ j a) := hpb.lift_fst _ _ hc
    have hl₂ : l ≫ yoneda.map snd = yoneda.map ((L.etale a).rep.snd g) := hpb.lift_snd _ _ hc
    refine ⟨yoneda.preimage l, yoneda.map_injective ?_, yoneda.map_injective ?_⟩
    · rw [yoneda.map_comp, Functor.map_preimage, hl₂]
    · rw [yoneda.map_comp, Functor.map_preimage, Functor.map_preimage, hl₁]
  refine ⟨heq, ⟨hrep, ?_⟩, ⟨hrep, ?_⟩, ⟨A, _, hdec⟩⟩
  · intro T P g fst snd hpb
    refine (surjective_iff _).mpr fun y => ?_
    obtain ⟨a, z, hz⟩ := L.covers T g y
    obtain ⟨n, hn, -⟩ := hpiece g fst snd hpb a
    refine ⟨(SCH).map n z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← (SCH).map_comp, hn]
    exact hz
  · intro T P g fst snd hpb
    let φ := yoneda.preimage fst
    have hφ : yoneda.map φ = fst := Functor.map_preimage _ _
    have hPext : ∀ {Q : BigFppfOver B S hS} {x y : Q ⟶ P}, x ≫ φ = y ≫ φ → x ≫ snd = y ≫ snd →
        x = y := by
      intro Q x y h1 h2
      apply yoneda.map_injective
      refine hpb.hom_ext ?_ ?_
      · rw [← hφ, ← yoneda.map_comp, ← yoneda.map_comp, h1]
      · rw [← yoneda.map_comp, ← yoneda.map_comp, h2]
    have hex := fun a => exists_restrict_bigFppfOver P
      ((SCH).map φ ⁻¹ᵁ (have := hoi a; ((SCH).map (j a)).opensRange))
    choose Y p hp hr hl using hex
    have hpo := hp
    have hcov : (⨆ a, ((SCH).map (p a)).opensRange) = ⊤ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion,
        Set.mem_univ, iff_true]
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1
        ((iUnion_range_toScheme_map_cofan hV).symm ▸ Set.mem_univ ((SCH).map φ x))
      refine ⟨a, ?_⟩
      change x ∈ Set.range ((SCH).map (p a))
      rw [hr a]
      exact ha
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
    refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) _ hcov).mpr fun a => ?_
    have := hoi a
    have := hpo a
    obtain ⟨c, hc⟩ := exists_factor_open (j a) (p a ≫ φ) (by
      rintro _ ⟨y, rfl⟩
      have hy : (SCH).map (p a) y ∈ (Set.range ((SCH).map (p a))) := ⟨y, rfl⟩
      rw [hr a] at hy
      rw [(SCH).map_comp, Scheme.Hom.comp_apply]
      exact hy)
    obtain ⟨n, hn, hnφ⟩ := hpiece g fst snd hpb a
    obtain ⟨n', hn'⟩ := hl a n (by
      rintro _ ⟨z, rfl⟩
      change (SCH).map φ ((SCH).map n z) ∈ Set.range ((SCH).map (j a))
      rw [← Scheme.Hom.comp_apply, ← (SCH).map_comp]
      have e : n ≫ φ = (L.etale a).rep.fst' g ≫ j a := hnφ
      rw [e, (SCH).map_comp, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩)
    have hsq : yoneda.map c ≫ L.f a = yoneda.map (p a ≫ snd) ≫ g := by
      have h1 : yoneda.map (j a) ≫ v = L.f a := (hv a).trans (Category.comp_id (L.f a))
      rw [← h1, ← Category.assoc, ← yoneda.map_comp, hc, yoneda.map_comp, Category.assoc, hφ,
        hpb.w, yoneda.map_comp, Category.assoc]
    let m := (L.etale a).rep.lift' c (p a ≫ snd) hsq
    have hm₁ : m ≫ (L.etale a).rep.fst' g = c := (L.etale a).rep.lift'_fst _ _ _
    have hm₂ : m ≫ (L.etale a).rep.snd g = p a ≫ snd := (L.etale a).rep.lift'_snd _ _ _
    have hjm := j_mono hV a
    have hpm : Mono (p a) := (SCH).mono_of_mono_map (IsOpenImmersion.mono _)
    have hmn : m ≫ n = p a := hPext
      (by rw [Category.assoc, hnφ, ← Category.assoc, hm₁, hc])
      (by rw [Category.assoc, hn, hm₂])
    have hiso : IsIso m := by
      refine ⟨n', ?_, ?_⟩
      · rw [← cancel_mono (p a), Category.assoc, hn', hmn, Category.id_comp]
      · refine (L.etale a).rep.hom_ext' ?_ ?_
        · rw [← cancel_mono (j a)]
          simp only [Category.assoc, Category.id_comp]
          rw [← Category.assoc m, hm₁, hc, ← Category.assoc, hn', hnφ]
        · rw [Category.assoc, hm₂, ← Category.assoc, hn', hn, Category.id_comp]
    have hsndA : Etale ((SCH).map ((L.etale a).rep.snd g)) := (L.etale a).property_snd g
    have e : ((SCH).map (p a)).opensRange.ι ≫ (SCH).map snd =
        ((SCH).map (p a)).isoOpensRange.inv ≫ (SCH).map m ≫
          (SCH).map ((L.etale a).rep.snd g) := by
      rw [← (SCH).map_comp, hm₂, (SCH).map_comp, ← Category.assoc,
        Scheme.Hom.isoOpensRange_inv_comp]
    rw [e]
    infer_instance

/-- **Gluing step of Theorem A.2.** Fixed-point reflection is local on the coproduct: if every chart
is `Z`-FPR, so is the coproduct. -/
theorem isZFPR_coprod (hV : IsColimit (Cofan.mk V j)) {Z : AddSubgroup M}
    {actX : AAction (fppfO B S hS) M X} (L : EtaleChartFamily actX A U)
    {v : yoneda.obj V ⟶ X} (hv : ∀ (a : A) {Y : BigFppfOver B S hS} (c : Y ⟶ U a),
      v.app (op Y) (c ≫ j a) = (L.f a).app (op Y) c)
    (heq : IsEquivariant (coprodAction L.act hV) actX v)
    (hfpr : ∀ a, IsZFPR (L.equivariant a) Z) : IsZFPR heq Z := by
  refine (isFPR_iff (heq.comap (QuotientAddGroup.mk' Z))).mpr fun T t hfix => ?_
  intro T' s h
  let r : unop T' ⟶ unop T := s.unop
  change (coprodAction L.act hV).smul _ (r ≫ t) = r ≫ t
  refine hom_ext_cut hV (T := unop T') (r ≫ t) fun {Y} i a c hc => ?_
  rw [coprodAction_spec L.act hV _ (r ≫ t) i a c hc, hc]
  have hfc : c ∈ (fixedPoints (quotientAction (L.act a) Z)).obj (op Y) := by
    refine (isFPR_iff (IsEquivariant.comap (L.equivariant a) (QuotientAddGroup.mk' Z))).mp (hfpr a) (op Y) c ?_
    intro T'' s' k
    have e : (L.f a).app (op Y) c = X.map (i ≫ r).op (v.app T t) := by
      rw [← hv a c, ← hc, ← Category.assoc]
      exact NatTrans.naturality_apply v (i ≫ r).op t
    have hk := hfix ((i ≫ r).op ≫ s') k
    rw [Functor.map_comp_apply] at hk
    rw [e]
    exact hk
  have hc' := hfc (𝟙 _) (APt.res i.op h)
  have e1 : (yoneda.obj (U a)).map (𝟙 (op Y)) c = c := by simp
  rw [e1] at hc'
  exact congrArg (· ≫ j a) hc'

/-- **Theorem 6.8 = A.2, assembly.** The coproduct of a family of `Z`-FPR charts is a `Z`-FPR atlas. -/
theorem isZFPRAtlas_of_family (hX : IsAlgebraicSpace B S hS X) {actX : AAction (fppfO B S hS) M X}
    (L : EtaleChartFamily actX A U) (hV : IsColimit (Cofan.mk V j)) {Z : AddSubgroup M}
    (hfpr : ∀ a, IsZFPR (L.equivariant a) Z) :
    ∃ v : yoneda.obj V ⟶ X, IsZFPRAtlas (coprodAction L.act hV) actX v Z := by
  obtain ⟨v, hv, hat⟩ := exists_atlas_of_family hX L hV
  exact ⟨v, hat, isZFPR_coprod hV L hv hat.equivariant hfpr⟩

/-- For a finite family the atlas is `S`-affine (the quasi-compact clause of Theorem 6.8). -/
theorem isSAffineAtlas_of_family [Finite A] (hX : IsAlgebraicSpace B S hS X)
    {actX : AAction (fppfO B S hS) M X} (L : EtaleChartFamily actX A U)
    (hV : IsColimit (Cofan.mk V j)) {Z : AddSubgroup M}
    (hfpr : ∀ a, IsZFPR (L.equivariant a) Z) :
    ∃ v : yoneda.obj V ⟶ X, IsZFPRAtlas (coprodAction L.act hV) actX v Z ∧
      IsSAffineAtlas (coprodAction L.act hV) actX v := by
  obtain ⟨v, hv⟩ := isZFPRAtlas_of_family hX L hV hfpr
  exact ⟨v, hv, hv.atlas, A, inferInstance, _, coprod_decomposition L.act hV L.isAffineHom⟩

/-- **Theorem 6.8 (ii) from charts**: if `D(M/Z)` has irreducible fibres, in particular if `M/Z` is
torsion-free, Theorem A.1 makes any chart family a `Z`-FPR atlas. -/
theorem isZFPRAtlas_of_family_irreducible (hX : IsAlgebraicSpace B S hS X)
    {actX : AAction (fppfO B S hS) M X} (L : EtaleChartFamily actX A U)
    (hV : IsColimit (Cofan.mk V j)) {Z : AddSubgroup M}
    (hM : B.Contains (Spec (ZMon (M ⧸ Z)))) (hirr : IrreducibleFibres (M ⧸ Z) S) :
    ∃ v : yoneda.obj V ⟶ X, IsZFPRAtlas (coprodAction L.act hV) actX v Z := by
  obtain ⟨v, -, hat⟩ := exists_atlas_of_family hX L hV
  exact ⟨v, isZFPRAtlas_of_atlas hM hirr hat⟩

end AlgMag

#print axioms AlgMag.isZFPRAtlas_of_family
#print axioms AlgMag.isSAffineAtlas_of_family
#print axioms AlgMag.isZFPRAtlas_of_family_irreducible
