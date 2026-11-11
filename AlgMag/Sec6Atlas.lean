/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
import AlgMag.AppendixA
import AlgMag.Sec7Linearizable

/-!
# Atlases: the parts of §6 and §7 resting on Appendix A

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §6, §7.

## Main results

* `AlgMag.lemma67_i`, `AlgMag.lemma67_ii`: **Lemma 6.7** in full (atlas part).
* `AlgMag.isZFPRAtlas_of_atlas`: in **Theorem 6.8 (ii)** every equivariant atlas is a `Z`-FPR atlas.
* `AlgMag.fact73`: **Fact 7.3**.

The existence assertion of Theorem 6.8 is not proved here, see the report: it rests on the étale
local structure theorem of Alper, Hall and Rydh.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- In **Theorem 6.8 (ii)**, with `M/Z` torsion-free and finitely generated, every equivariant atlas
is automatically a `Z`-FPR atlas (Theorem A.1); the same for connected fibres of `D(M/Z)`. -/
theorem isZFPRAtlas_of_atlas {Z : AddSubgroup M} (hM : B.Contains (Spec (ZMon (M ⧸ Z))))
    (hirr : IrreducibleFibres (M ⧸ Z) S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
    {actX : AAction (fppfO B S hS) M X} {f : yoneda.obj U ⟶ X}
    (h : IsEquivariantAtlas actU actX f) : IsZFPRAtlas actU actX f Z :=
  ⟨h, isZFPR_of_etale hM hirr h.equivariant h.etale⟩

section Lemma67

variable {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
  {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX : AAction (fppfO B S hS) M X}
  {actX' : AAction (fppfO B S hS) M X'} {f : yoneda.obj U ⟶ X} {g : X' ⟶ X}

section Points

variable (hg : yoneda.relativelyRepresentable g) (f)

lemma app_eq_yonedaEquiv {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W Y : BigFppfOver B S hS}
    (φ : yoneda.obj W ⟶ F) (t : Y ⟶ W) : φ.app (op Y) t = yonedaEquiv (yoneda.map t ≫ φ) := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma w_sq {Y : BigFppfOver B S hS} (x : X'.obj (op Y)) (t : Y ⟶ U)
    (w : g.app _ x = f.app _ t) : yonedaEquiv.symm x ≫ g = yoneda.map t ≫ f := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
  exact w

/-- A point of `W = X' ×_X U`, from its two components. -/
noncomputable def wLift {Y : BigFppfOver B S hS} (x : X'.obj (op Y)) (t : Y ⟶ U)
    (w : g.app _ x = f.app _ t) : Y ⟶ hg.pullback f :=
  hg.lift (yonedaEquiv.symm x) t (w_sq f x t w)

lemma fst_wLift {Y : BigFppfOver B S hS} (x : X'.obj (op Y)) (t : Y ⟶ U)
    (w : g.app _ x = f.app _ t) : (hg.fst f).app (op Y) (wLift f hg x t w) = x := by
  rw [app_eq_yonedaEquiv, wLift, hg.lift_fst, Equiv.apply_symm_apply]

lemma wLift_snd {Y : BigFppfOver B S hS} (x : X'.obj (op Y)) (t : Y ⟶ U)
    (w : g.app _ x = f.app _ t) : wLift f hg x t w ≫ hg.snd f = t :=
  hg.lift_snd _ _ _

lemma w_ext {Y : BigFppfOver B S hS} {t t' : Y ⟶ hg.pullback f}
    (h₁ : (hg.fst f).app (op Y) t = (hg.fst f).app (op Y) t') (h₂ : t ≫ hg.snd f = t' ≫ hg.snd f) :
    t = t' := by
  refine hg.hom_ext ?_ h₂
  apply yonedaEquiv.injective
  rw [← app_eq_yonedaEquiv, ← app_eq_yonedaEquiv]
  exact h₁

lemma w_comm {Y : BigFppfOver B S hS} (t : Y ⟶ hg.pullback f) :
    g.app _ ((hg.fst f).app (op Y) t) = f.app _ (t ≫ hg.snd f) := by
  have h := congrArg (fun k => k.app (op Y) t) (hg.w f)
  exact h

lemma fst_map {Y Y' : BigFppfOver B S hS} (i : Y' ⟶ Y) (t : Y ⟶ hg.pullback f) :
    (hg.fst f).app (op Y') (i ≫ t) = X'.map i.op ((hg.fst f).app (op Y) t) :=
  NatTrans.naturality_apply (hg.fst f) i.op t

end Points

lemma pb_w (hg : yoneda.relativelyRepresentable g) (f : yoneda.obj U ⟶ X)
    (hf : IsEquivariant actU actX f) (hgeq : IsEquivariant actX' actX g)
    {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (t : unop T ⟶ hg.pullback f) :
    g.app _ (actX'.smul h ((hg.fst f).app T t)) = f.app _ (actU.smul h (t ≫ hg.snd f)) := by
  rw [hgeq, hf]
  exact congrArg _ (w_comm f hg t)

/-- The action on the base change `U ×_X X'`, represented by `W`, of an equivariant morphism. -/
noncomputable def pullbackAction (hg : yoneda.relativelyRepresentable g) (f : yoneda.obj U ⟶ X)
    (hf : IsEquivariant actU actX f) (hgeq : IsEquivariant actX' actX g) :
    AAction (fppfO B S hS) M (yoneda.obj (hg.pullback f)) where
  smul {T} h t := wLift f hg (Y := unop T) (actX'.smul h ((hg.fst f).app T t))
    (actU.smul h (t ≫ hg.snd f)) (pb_w hg f hf hgeq h t)
  one_smul {T} t := by
    refine w_ext f hg (Y := unop T) ?_ ?_
    · rw [fst_wLift, actX'.one_smul]
    · rw [wLift_snd]
      exact actU.one_smul _
  mul_smul {T} g' h t := by
    refine w_ext f hg (Y := unop T) ?_ ?_
    · rw [fst_wLift, fst_wLift, fst_wLift, actX'.mul_smul]
    · rw [wLift_snd, wLift_snd, wLift_snd]
      exact actU.mul_smul _ _ _
  map_smul {T T'} s h t := by
    refine w_ext f hg (Y := unop T') ?_ ?_
    · change (hg.fst f).app _ (s.unop ≫ wLift f hg _ _ _) = _
      rw [fst_map, fst_wLift, fst_wLift, actX'.map_smul]
      congr 1
      exact (NatTrans.naturality_apply (hg.fst f) s t).symm
    · rw [wLift_snd]
      change s.unop ≫ wLift f hg _ _ _ ≫ hg.snd f = _
      rw [wLift_snd]
      exact actU.map_smul s h (t ≫ hg.snd f)

variable {Z : AddSubgroup M}

lemma pullbackAction_fst (hg : yoneda.relativelyRepresentable g)
    (hf : IsEquivariant actU actX f) (hgeq : IsEquivariant actX' actX g) :
    IsEquivariant (pullbackAction hg f hf hgeq) actX' (hg.fst f) := by
  intro T h t
  exact fst_wLift f hg (Y := unop T) _ _ (pb_w hg f hf hgeq h t)

lemma pullbackAction_snd (hg : yoneda.relativelyRepresentable g)
    (hf : IsEquivariant actU actX f) (hgeq : IsEquivariant actX' actX g) :
    IsEquivariant (pullbackAction hg f hf hgeq) actU (yoneda.map (hg.snd f)) := by
  intro T h t
  exact wLift_snd f hg (Y := unop T) _ _ (pb_w hg f hf hgeq h t)

/-- The decomposition of `U ×_X X'` given by that of `U`, for `X' → X` affine. -/
lemma decomposition_pullback (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    (hf : IsEquivariant actU actX f) (hgeq : IsEquivariant actX' actX g)
    {A : Type u} {V : A → ((SCH).obj U).Opens} (hV : IsAffineDecomposition actU V) :
    IsAffineDecomposition (pullbackAction hg.rep f hf hgeq)
      (fun a => (SCH).map (hg.rep.snd f) ⁻¹ᵁ V a) := by
  have haff : IsAffineHom ((SCH).map (hg.rep.snd f)) := hg.property_snd f
  refine ⟨fun a b hab => ?_, ?_, ?_, ?_⟩
  · have := (hV.disjoint hab)
    rw [Function.onFun, disjoint_iff] at this ⊢
    rw [← Scheme.Hom.preimage_inf, this]
    rfl
  · rw [← Scheme.Hom.preimage_iSup, hV.iSup_eq_top]
    rfl
  · intro a T t h ht
    have e : actU.smul h (t ≫ hg.rep.snd f) =
        (pullbackAction hg.rep f hf hgeq).smul h t ≫ hg.rep.snd f :=
      (wLift_snd f hg.rep (Y := T) _ _ (pb_w hg.rep f hf hgeq h t)).symm
    have hr : Set.range ((SCH).map (t ≫ hg.rep.snd f)) ⊆ V a := by
      rintro _ ⟨y, rfl⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact ht ⟨y, rfl⟩
    have := hV.stable a (t ≫ hg.rep.snd f) h hr
    rintro _ ⟨y, rfl⟩
    have h2 := this ⟨y, rfl⟩
    rw [e, Functor.map_comp, Scheme.Hom.comp_apply] at h2
    exact h2
  · intro a
    have h1 := hV.isAffineHom a
    let q := (SCH).map (hg.rep.snd f)
    have e : ((q ⁻¹ᵁ V a).ι ≫ structMap (hg.rep.pullback f)) =
        (q ∣_ V a) ≫ (V a).ι ≫ structMap U := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      congr 1
      exact (congrArg (B.inclusion.map) (Over.w (hg.rep.snd f))).symm
    have hq : IsAffineHom (q ∣_ V a) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (isPullback_morphismRestrict q (V a)).flip haff
    rw [e]
    infer_instance

/-- **Lemma 6.7 (i).** If `U → X` is a `Z`-FPR atlas and `X' → X` is equivariant and affine, then
`U ×_X X' → X'` is a `Z`-FPR atlas of `X'`. -/
theorem lemma67_i (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    (hgeq : IsEquivariant actX' actX g) (h : IsZFPRAtlas actU actX f Z) :
    IsZFPRAtlas (pullbackAction hg.rep f h.atlas.equivariant hgeq) actX' (hg.rep.fst f) Z := by
  have hpb : IsPullback (yoneda.map (hg.rep.snd f)) (hg.rep.fst f) f g :=
    (hg.rep.isPullback f).flip
  have hat : IsEquivariantAtlas (pullbackAction hg.rep f h.atlas.equivariant hgeq) actX'
      (hg.rep.fst f) := by
    obtain ⟨A, V, hV⟩ := h.atlas.decomposition
    refine ⟨pullbackAction_fst _ _ _, ?_, ?_, ⟨A, _, decomposition_pullback hg _ hgeq hV⟩⟩
    · exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb
        h.atlas.surjective
    · exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb
        h.atlas.etale
  exact ⟨hat, IsZFPR.of_isPullback hpb (pullbackAction_snd _ _ _) (pullbackAction_fst _ _ _) hgeq
    h.isZFPR⟩

/-- **Lemma 6.7 (ii).** If moreover `U → X` is `S`-affine, so is `U ×_X X' → X'`. -/
theorem lemma67_ii (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    (hgeq : IsEquivariant actX' actX g) (h : IsZFPRAtlas actU actX f Z)
    (hfin : HasFiniteAffineDecomposition actU) :
    IsSAffineAtlas (pullbackAction hg.rep f h.atlas.equivariant hgeq) actX' (hg.rep.fst f) := by
  refine ⟨(lemma67_i hg hgeq h).atlas, ?_⟩
  obtain ⟨A, hA, V, hV⟩ := hfin
  exact ⟨A, hA, _, decomposition_pullback hg _ hgeq hV⟩

end Lemma67

section Fact73

variable {A : Type u} {U : A → BigFppfOver B S hS} {V : BigFppfOver B S hS} {j : ∀ a, U a ⟶ V}

/-- A morphism into an open immersion of the site with image inside factors through it. -/
lemma exists_factor_open {W V : BigFppfOver B S hS} (i : W ⟶ V)
    [IsOpenImmersion ((SCH).map i)] {Y : BigFppfOver B S hS} (g : Y ⟶ V)
    (hg : Set.range ((SCH).map g) ⊆ Set.range ((SCH).map i)) : ∃ c : Y ⟶ W, c ≫ i = g := by
  have fac := IsOpenImmersion.lift_fac ((SCH).map i) ((SCH).map g) hg
  refine ⟨Over.homMk (ObjectProperty.homMk (IsOpenImmersion.lift ((SCH).map i) ((SCH).map g) hg)) ?_,
    ?_⟩
  · apply B.inclusion.map_injective
    have h1 : (SCH).map i ≫ structMap V = structMap W := congrArg B.inclusion.map (Over.w i)
    have h2 : (SCH).map g ≫ structMap V = structMap Y := congrArg B.inclusion.map (Over.w g)
    change IsOpenImmersion.lift ((SCH).map i) ((SCH).map g) hg ≫ structMap W = structMap Y
    rw [← h1, ← Category.assoc, fac, h2]
  · apply (SCH).map_injective
    rw [(SCH).map_comp]
    exact fac

/-- The sieve of the morphisms `i` to `T` such that `i ≫ t` lies in one member of the coproduct. -/
def cutSieve (j : ∀ a, U a ⟶ V) {T : BigFppfOver B S hS} (t : T ⟶ V) : Sieve T where
  arrows Y i := ∃ (a : A) (c : Y ⟶ U a), i ≫ t = c ≫ j a
  downward_closed := by
    rintro Y Y' i ⟨a, c, h⟩ u
    exact ⟨a, u ≫ c, by rw [Category.assoc, h, Category.assoc]⟩

lemma cutSieve_mem (hV : IsColimit (Cofan.mk V j)) {T : BigFppfOver B S hS} (t : T ⟶ V) :
    cutSieve j t ∈ BigFppfOver.topology B S hS T := by
  have hoi := fun a => isOpenImmersion_toScheme_map_cofan hV a
  have hex := fun a => exists_restrict_bigFppfOver T ((SCH).map t ⁻¹ᵁ ((SCH).map (j a)).opensRange)
  choose Y p hp hr hl using hex
  have hcov : Sieve.ofArrows Y p ∈ BigFppfOver.topology B S hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS p hp fun w => ?_
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1
      ((iUnion_range_toScheme_map_cofan hV).symm ▸ Set.mem_univ ((SCH).map t w))
    refine ⟨a, ?_⟩
    rw [hr a]
    exact ha
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  rintro Z i ⟨W, u, e, ⟨a⟩, rfl⟩
  have := hoi a
  obtain ⟨c, hc⟩ := exists_factor_open (j a) (p a ≫ t) (by
    rintro _ ⟨y, rfl⟩
    have hy : (SCH).map (p a) y ∈ ((SCH).map t ⁻¹ᵁ ((SCH).map (j a)).opensRange : Set _) := by
      rw [← hr a]
      exact ⟨y, rfl⟩
    rw [(SCH).map_comp, Scheme.Hom.comp_apply]
    exact hy)
  exact ⟨a, u ≫ c, by rw [Category.assoc, Category.assoc, hc]⟩

lemma hom_ext_cut (hV : IsColimit (Cofan.mk V j)) {T W : BigFppfOver B S hS} (t : T ⟶ V)
    {s s' : T ⟶ W} (h : ∀ {Y : BigFppfOver B S hS} (i : Y ⟶ T) (a : A) (c : Y ⟶ U a),
      i ≫ t = c ≫ j a → i ≫ s = i ≫ s') : s = s' := by
  refine ((BigFppfOver.isSheaf_of_type_yoneda_obj W) _ (cutSieve_mem hV t)).isSeparatedFor.ext ?_
  rintro Y i ⟨a, c, hc⟩
  exact h i a c hc

lemma j_mono (hV : IsColimit (Cofan.mk V j)) (a : A) : Mono (j a) :=
  have := isOpenImmersion_toScheme_map_cofan hV a
  (SCH).mono_of_mono_map (IsOpenImmersion.mono _)

/-- Two descriptions of a point of the coproduct on `Y`: the indices agree or `Y` is empty. -/
lemma isEmpty_of_ne (hV : IsColimit (Cofan.mk V j)) {Y : BigFppfOver B S hS} {a a' : A}
    (haa : a ≠ a') (c : Y ⟶ U a) (c' : Y ⟶ U a') (h : c ≫ j a = c' ≫ j a') :
    IsEmpty ((SCH).obj Y) := by
  refine ⟨fun y => ?_⟩
  have h1 := congrArg (fun m : (SCH).obj Y ⟶ (SCH).obj V => m y) (congrArg (SCH).map h)
  simp only [Functor.map_comp, Scheme.Hom.comp_apply] at h1
  exact ne_toScheme_map_cofan hV haa _ _ h1

variable (act : ∀ a, AAction (fppfO B S hS) M (yoneda.obj (U a)))

lemma smul_val_indep (hV : IsColimit (Cofan.mk V j)) {Y : BigFppfOver B S hS}
    (k : APt (fppfO B S hS) M (op Y)) {a a' : A} (c : Y ⟶ U a) (c' : Y ⟶ U a')
    (h : c ≫ j a = c' ≫ j a') :
    ((act a).smul k c : Y ⟶ U a) ≫ j a = ((act a').smul k c' : Y ⟶ U a') ≫ j a' := by
  by_cases haa : a = a'
  · subst haa
    have := j_mono hV a
    rw [(cancel_mono (j a)).1 h]
  · have hempty := isEmpty_of_ne hV haa c c' h
    have hbot := BigFppfOver.bot_mem_topology Y hempty
    exact ((BigFppfOver.isSheaf_of_type_yoneda_obj V).subsingleton_obj_of_bot_mem _ hbot).elim _ _

/-- Existence of the action on the coproduct: `h • t` is computed piecewise. -/
lemma exists_smul (hV : IsColimit (Cofan.mk V j)) {T : BigFppfOver B S hS}
    (h : APt (fppfO B S hS) M (op T)) (t : T ⟶ V) :
    ∃ s : T ⟶ V, ∀ {Y : BigFppfOver B S hS} (i : Y ⟶ T) (a : A) (c : Y ⟶ U a),
      i ≫ t = c ≫ j a → i ≫ s = ((act a).smul (APt.res i.op h) c : Y ⟶ U a) ≫ j a := by
  have hsh := BigFppfOver.isSheaf_of_type_yoneda_obj (B := B) (S := S) (hS := hS) V
  let val : ∀ {Y : BigFppfOver B S hS} (i : Y ⟶ T), (cutSieve j t).arrows i → (Y ⟶ V) :=
    fun {Y} i hi => ((act hi.choose).smul (APt.res i.op h) hi.choose_spec.choose : Y ⟶ _) ≫ j _
  have hval : ∀ {Y : BigFppfOver B S hS} (i : Y ⟶ T) (hi : (cutSieve j t).arrows i) (a : A)
      (c : Y ⟶ U a), i ≫ t = c ≫ j a →
      val i hi = ((act a).smul (APt.res i.op h) c : Y ⟶ U a) ≫ j a := by
    intro Y i hi a c hc
    exact smul_val_indep act hV _ _ _ (hi.choose_spec.choose_spec.symm.trans hc)
  let fam : Presieve.FamilyOfElements (yoneda.obj V) (cutSieve j t).arrows :=
    fun Y i hi => val i hi
  have hcomp : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Y' i u hi
    obtain ⟨a, c, hc⟩ := id hi
    change val (u ≫ i) _ = u ≫ val i hi
    rw [hval i hi a c hc, hval (u ≫ i) ((cutSieve j t).downward_closed hi u) a (u ≫ c)
      (by rw [Category.assoc, hc, Category.assoc])]
    have e := (act a).map_smul u.op (APt.res i.op h) c
    rw [← Category.assoc]
    refine congrArg (· ≫ j a) (Eq.trans ?_ e.symm)
    rw [op_comp, APt.res_comp]
    rfl
  obtain ⟨s, hs, -⟩ := hsh _ (cutSieve_mem hV t) fam hcomp
  refine ⟨s, fun {Y} i a c hc => ?_⟩
  have hi : (cutSieve j t).arrows i := ⟨a, c, hc⟩
  exact (hs i hi).trans (hval i hi a c hc)

/-- The action of `D(M)` on a coproduct of schemes with action. -/
noncomputable def coprodAction (hV : IsColimit (Cofan.mk V j)) :
    AAction (fppfO B S hS) M (yoneda.obj V) where
  smul {T} h t := (exists_smul act hV (T := unop T) h t).choose
  one_smul {T} t := by
    refine hom_ext_cut hV (T := unop T) t fun i a c hc => ?_
    have := (exists_smul act hV (T := unop T) 1 t).choose_spec i a c hc
    refine this.trans ?_
    have e : APt.res i.op (1 : APt (fppfO B S hS) M (op (unop T))) = 1 := by
      ext p; simp
    rw [e, (act a).one_smul, hc]
  mul_smul {T} g h t := by
    refine hom_ext_cut hV (T := unop T) t fun i a c hc => ?_
    have h1 := (exists_smul act hV (T := unop T) (g * h) t).choose_spec i a c hc
    have h2 := (exists_smul act hV (T := unop T) h t).choose_spec i a c hc
    have h3 := (exists_smul act hV (T := unop T) g _).choose_spec i a _ h2
    refine h1.trans (Eq.trans ?_ h3.symm)
    rw [APt.res_mul, (act a).mul_smul]
  map_smul {T T'} s h t := by
    let r : unop T' ⟶ unop T := s.unop
    refine hom_ext_cut hV (T := unop T') (r ≫ t) fun i a c hc => ?_
    have h1 := (exists_smul act hV (T := unop T) h t).choose_spec (i ≫ r) a c
      (by rw [Category.assoc, hc])
    have h2 := (exists_smul act hV (T := unop T') (APt.res s h) (r ≫ t)).choose_spec i a c hc
    change i ≫ r ≫ _ = i ≫ _
    rw [← Category.assoc]
    have er : APt.res (i ≫ r).op h = APt.res i.op (APt.res s h) := by
      change APt.res (s ≫ i.op) h = _
      rw [APt.res_comp]
    rw [er] at h1
    exact h1.trans h2.symm

lemma coprodAction_spec (hV : IsColimit (Cofan.mk V j)) {T Y : BigFppfOver B S hS}
    (h : APt (fppfO B S hS) M (op T)) (t : T ⟶ V) (i : Y ⟶ T) (a : A) (c : Y ⟶ U a)
    (hc : i ≫ t = c ≫ j a) :
    i ≫ ((coprodAction act hV).smul h t : T ⟶ V) =
      ((act a).smul (APt.res i.op h) c : Y ⟶ U a) ≫ j a :=
  (exists_smul act hV (T := T) h t).choose_spec i a c hc

/-- The pieces of a coproduct form a decomposition, if the pieces are `S`-affine. -/
lemma coprod_decomposition (hV : IsColimit (Cofan.mk V j))
    (haff : ∀ a, IsAffineHom (structMap (U a))) :
    IsAffineDecomposition (coprodAction act hV) (fun a =>
      have := isOpenImmersion_toScheme_map_cofan hV a
      ((SCH).map (j a)).opensRange) := by
  have hoi := fun a => isOpenImmersion_toScheme_map_cofan hV a
  refine ⟨fun a b hab => ?_, ?_, ?_, ?_⟩
  · refine disjoint_iff.mpr (TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.mpr ?_))
    rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ne_toScheme_map_cofan hV hab y z (hy.trans hz.symm)
  · ext x
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion,
      Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1
      ((iUnion_range_toScheme_map_cofan hV).symm ▸ Set.mem_univ x)
    exact ⟨a, ha⟩
  · intro a T t h ht
    have := hoi a
    obtain ⟨c, hc⟩ := exists_factor_open (j a) t ht
    have e := coprodAction_spec act hV h t (𝟙 T) a c (by rw [Category.id_comp, hc])
    rw [Category.id_comp] at e
    rw [e]
    rintro _ ⟨y, rfl⟩
    rw [(SCH).map_comp, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · intro a
    have := hoi a
    have := haff a
    have e : (((SCH).map (j a)).opensRange).ι ≫ structMap V =
        ((SCH).map (j a)).isoOpensRange.inv ≫ structMap (U a) := by
      have h1 : (SCH).map (j a) ≫ structMap V = structMap (U a) :=
        congrArg B.inclusion.map (Over.w (j a))
      rw [← h1, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    change IsAffineHom (((SCH).map (j a)).opensRange.ι ≫ structMap V)
    rw [e]
    infer_instance

/-- **Fact 7.3.** If the action on the algebraic space `X` is Zariski locally linearizable, the
disjoint union of the stable `S`-affine opens is a strongly-FPR equivariant atlas.

The disjoint union is given as a coproduct `V` in the site: the paper's category of schemes has no
size cutoff, whereas here the coproduct must be below the cutoff of `B`. It is if `A` is countable
(Stacks: `schemeSizeBelow_isClosedUnderColimitsOfShape_discrete`). The paper's "`S`-space" is here an
algebraic space, which is what gives representability of `V → X`. -/
theorem fact73 {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {actX : AAction (fppfO B S hS) M X} (L : ZariskiLocallyLinearizable actX A U)
    (hV : IsColimit (Cofan.mk V j)) :
    ∃ (actV : AAction (fppfO B S hS) M (yoneda.obj V)) (v : yoneda.obj V ⟶ X),
      IsStronglyFPRAtlas actV actX v := by
  have hoi := fun a => isOpenImmersion_toScheme_map_cofan hV a
  have hXs : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  obtain ⟨v, hv⟩ := exists_hom_yoneda_of_isColimit_cofan
    (F := fun _ : A => (⟨X, hX.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)))
    (P := ⟨X, hX.isSheaf⟩) (fun _ => 𝟙 _) (U := U) (fun a => L.j a) hV
  have hv' : ∀ (a : A) {Y : BigFppfOver B S hS} (c : Y ⟶ U a),
      v.app (op Y) (c ≫ j a) = (L.j a).app (op Y) c := by
    intro a Y c
    have := congrArg (fun k => k.app (op Y) c) (hv a)
    exact this
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
  have hmono : ∀ a, Mono (L.j a) := fun a =>
    MorphismProperty.presheaf_mono_of_le (fun _ _ q hq => by
      have : IsOpenImmersion ((SCH).map q) := hq
      exact (MorphismProperty.monomorphisms.iff _).2
        ((SCH).mono_of_mono_map (IsOpenImmersion.mono _)))
      (L.isOpen a)
  have hrep : yoneda.relativelyRepresentable v := hX.diagonal_representable.of_diag v
  have hpiece : ∀ {T P : BigFppfOver B S hS} (g : yoneda.obj T ⟶ X) (fst : yoneda.obj P ⟶ yoneda.obj V)
      (snd : P ⟶ T), IsPullback fst (yoneda.map snd) v g → ∀ a : A,
      ∃ n : (L.isOpen a).rep.pullback g ⟶ P, n ≫ snd = (L.isOpen a).rep.snd g ∧
        n ≫ yoneda.preimage fst = (L.isOpen a).rep.fst' g ≫ j a := by
    intro T P g fst snd hpb a
    have hc : (yoneda.map ((L.isOpen a).rep.fst' g ≫ j a)) ≫ v =
        yoneda.map ((L.isOpen a).rep.snd g) ≫ g := by
      have h1 : yoneda.map (j a) ≫ v = L.j a := (hv a).trans (Category.comp_id (L.j a))
      rw [yoneda.map_comp, Category.assoc, h1, Functor.relativelyRepresentable.map_fst']
      exact (L.isOpen a).rep.w g
    let l := hpb.lift _ _ hc
    have hl₁ : l ≫ fst = yoneda.map ((L.isOpen a).rep.fst' g ≫ j a) := hpb.lift_fst _ _ hc
    have hl₂ : l ≫ yoneda.map snd = yoneda.map ((L.isOpen a).rep.snd g) := hpb.lift_snd _ _ hc
    refine ⟨yoneda.preimage l, yoneda.map_injective ?_, yoneda.map_injective ?_⟩
    · rw [yoneda.map_comp, Functor.map_preimage, hl₂]
    · rw [yoneda.map_comp, Functor.map_preimage, Functor.map_preimage, hl₁]
  have hat : IsEquivariantAtlas actV actX v := by
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
      have : IsZariskiLocalAtSource (@Etale.{u}) := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
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
        change _ ∈ _
        have e : n ≫ φ = (L.isOpen a).rep.fst' g ≫ j a := hnφ
        rw [e, (SCH).map_comp, Scheme.Hom.comp_apply]
        exact ⟨_, rfl⟩)
      have hsq : yoneda.map c ≫ L.j a = yoneda.map (p a ≫ snd) ≫ g := by
        have h1 : yoneda.map (j a) ≫ v = L.j a := (hv a).trans (Category.comp_id (L.j a))
        rw [← h1, ← Category.assoc, ← yoneda.map_comp, hc, yoneda.map_comp, Category.assoc, hφ,
          hpb.w, yoneda.map_comp, Category.assoc]
      let m := (L.isOpen a).rep.lift' c (p a ≫ snd) hsq
      have hm₁ : m ≫ (L.isOpen a).rep.fst' g = c := (L.isOpen a).rep.lift'_fst _ _ _
      have hm₂ : m ≫ (L.isOpen a).rep.snd g = p a ≫ snd := (L.isOpen a).rep.lift'_snd _ _ _
      have hjm := j_mono hV a
      have hpm : Mono (p a) := (SCH).mono_of_mono_map (IsOpenImmersion.mono _)
      have hmn : m ≫ n = p a := hPext
        (by rw [Category.assoc, hnφ, ← Category.assoc, hm₁, hc])
        (by rw [Category.assoc, hn, hm₂])
      have hiso : IsIso m := by
        refine ⟨n', ?_, ?_⟩
        · rw [← cancel_mono (p a), Category.assoc, hn', hmn, Category.id_comp]
        · refine (L.isOpen a).rep.hom_ext' ?_ ?_
          · rw [← cancel_mono (j a)]
            simp only [Category.assoc, Category.id_comp]
            rw [← Category.assoc m, hm₁, hc, ← Category.assoc, hn', hnφ]
          · rw [Category.assoc, hm₂, ← Category.assoc, hn', hn, Category.id_comp]
      have hsndA : IsOpenImmersion ((SCH).map ((L.isOpen a).rep.snd g)) :=
        (L.isOpen a).property_snd g
      have e : ((SCH).map (p a)).opensRange.ι ≫ (SCH).map snd =
          ((SCH).map (p a)).isoOpensRange.inv ≫ (SCH).map m ≫
            (SCH).map ((L.isOpen a).rep.snd g) := by
        rw [← (SCH).map_comp, hm₂, (SCH).map_comp, ← Category.assoc,
          Scheme.Hom.isoOpensRange_inv_comp]
      rw [e]
      infer_instance
  refine ⟨actV, v, isStronglyFPRAtlas_of_decomposition hat hdec ?_⟩
  intro a Y t t' ht ht' e
  have := hoi a
  obtain ⟨c, rfl⟩ := exists_factor_open (j a) t ht
  obtain ⟨c', rfl⟩ := exists_factor_open (j a) t' ht'
  rw [hv', hv'] at e
  have hm := (NatTrans.mono_iff_mono_app _).1 (hmono a) (op Y)
  have hc : c = c' := (mono_iff_injective _).1 hm e
  rw [hc]

end Fact73

end AlgMag

#print axioms AlgMag.isZFPRAtlas_of_atlas
#print axioms AlgMag.lemma67_i
#print axioms AlgMag.lemma67_ii
#print axioms AlgMag.fact73
