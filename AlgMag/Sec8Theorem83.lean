/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec8Representability
import AlgMag.Sec5Etale
import AlgMag.Sec12Topology
import AlgMag.Sec14Ind
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Theorem 8.3: representability of attractors

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §8.

`M` is a finitely generated abelian group, `N ⊆ M` a magnet, `N^×` (`AlgMag.unitsSub N`) its face of
invertible elements, `X` an algebraic space over `S` with an action of `D(M)_S` and a `N^×`-FPR atlas.
`X` is assumed separated, and `N` finitely generated or `X` limit preserving (author-approved form of
the hypotheses).

## Main results

* `AlgMag.thm83_repr`, `AlgMag.thm83`: representability, (i), (ii), (iii), (v).
* `AlgMag.thm83_vii`: (vii).
* `AlgMag.exists_chartAttr`: Theorem 3.20 and Corollary 3.22 for a disjoint union of stable `S`-affine
  schemes, on the site.
* `AlgMag.app_mem_iff`: the values of a point of `U^N` stay in one piece of the atlas (the idempotents
  of `Γ(T)[N]` that are invariant under `D(M)` lie in `Γ(T)`).
* `AlgMag.isFaceCartesian_of_pieces`: Proposition 5.1 for an equivariant atlas.
* `AlgMag.prop121_of_atlas`, `AlgMag.prop144_of_atlas`: Propositions 12.1 and 14.4 with their
  representability assumption discharged.
-/

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

/-- The face `N^×` of invertible elements of a magnet `N` of an abelian group. -/
def unitsSub {M : Type*} [AddCommGroup M] (N : AddSubmonoid M) : AddSubgroup M where
  carrier := {x | x ∈ N ∧ -x ∈ N}
  add_mem' := fun {a b} ha hb => ⟨N.add_mem ha.1 hb.1, by
    rw [neg_add]; exact N.add_mem ha.2 hb.2⟩
  zero_mem' := ⟨N.zero_mem, by simp [N.zero_mem]⟩
  neg_mem' := fun {a} ha => ⟨ha.2, by simpa using ha.1⟩

lemma isFace_unitsSub {M : Type*} [AddCommGroup M] (N : AddSubmonoid M) :
    IsFace (unitsSub N).toAddSubmonoid N := by
  refine ⟨fun x hx => hx.1, fun {x y} hx hy h => ?_⟩
  have hn : -(x + y) ∈ N := h.2
  refine ⟨⟨hx, ?_⟩, ⟨hy, ?_⟩⟩
  · have := N.add_mem hn hy
    simpa [neg_add, add_assoc, add_comm, add_left_comm] using this
  · have := N.add_mem hn hx
    simpa [neg_add, add_assoc, add_comm, add_left_comm] using this

/-- Transport of the sheaf condition across a natural bijection, between different universes. -/
theorem isSheaf_of_equiv {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ Type*} {G : Cᵒᵖ ⥤ Type*} (e : ∀ T, F.obj T ≃ G.obj T)
    (he : ∀ {T T'} (s : T ⟶ T') (x : F.obj T), e T' (F.map s x) = G.map s (e T x))
    (hF : Presieve.IsSheaf J F) : Presieve.IsSheaf J G := by
  intro T R hR x hx
  have hes : ∀ {T T'} (s : T ⟶ T') (y : G.obj T),
      (e T').symm (G.map s y) = F.map s ((e T).symm y) := by
    intro T T' s y
    apply (e T').injective
    rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]
  let x' : Presieve.FamilyOfElements F R := fun Y f hf => (e (op Y)).symm (x f hf)
  have hx' : x'.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    change F.map g₁.op ((e _).symm (x f₁ h₁)) = F.map g₂.op ((e _).symm (x f₂ h₂))
    rw [← hes, ← hes, hx g₁ g₂ h₁ h₂ w]
  obtain ⟨t, ht, hu⟩ := hF R hR x' hx'
  refine ⟨e _ t, fun Y f hf => ?_, fun y hy => ?_⟩
  · rw [← he, ht f hf]
    exact Equiv.apply_symm_apply _ _
  · apply (e _).symm.injective
    rw [Equiv.symm_apply_apply]
    refine hu _ fun Y f hf => ?_
    rw [← hes, hy f hf]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Small

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M)

lemma countable_of_fg83 : Countable M := by
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ M
  exact hf.countable

lemma contains_zmon_N (hS : B.Contains S) (N : AddSubmonoid M) : B.Contains (Spec (ZMon N)) := by
  have := countable_of_fg83 (M := M)
  exact contains_zmon_countable hS N

instance small_attractorPt (T : BigFppfOver B S hS) : Small.{u} (AttractorPt act N T) := by
  let U := monAffUniversal N (contains_zmon_N hS N) T
  exact small_of_injective (f := fun φ => ((attractorPtEquivOfUniversal (act := act) U φ).1))
    (fun a b h => (attractorPtEquivOfUniversal U).injective (Subtype.ext h))

lemma bc83_id {T : BigFppfOver B S hS} (φ : AttractorPt act N T) : φ.baseChange (𝟙 T) = φ :=
  AttractorPt.ext (by
    funext T' t a
    exact congrArg (fun q => φ.app q a) (Category.comp_id t))

lemma bc83_comp {T T' T'' : BigFppfOver B S hS} (s : T' ⟶ T) (r : T'' ⟶ T') (φ : AttractorPt act N T) :
    φ.baseChange (r ≫ s) = (φ.baseChange s).baseChange r :=
  AttractorPt.ext (by
    funext W t a
    exact congrArg (fun q => φ.app q a) (Category.assoc t r s).symm)

/-- The attractor `X^N` as a presheaf in the universe of the site. -/
noncomputable def attP : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj T := Shrink.{u} (AttractorPt act N (unop T))
  map f := ↾ fun x => equivShrink _ (((equivShrink _).symm x).baseChange f.unop)
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    change equivShrink _ (((equivShrink (AttractorPt act N (unop T))).symm x).baseChange (𝟙 (unop T))) = x
    rw [bc83_id, Equiv.apply_symm_apply]
  map_comp {A C D} f g := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    change equivShrink _ (((equivShrink (AttractorPt act N (unop A))).symm x).baseChange (g.unop ≫ f.unop)) =
      equivShrink _ (((equivShrink (AttractorPt act N (unop C))).symm (equivShrink _
        (((equivShrink (AttractorPt act N (unop A))).symm x).baseChange f.unop))).baseChange g.unop)
    rw [Equiv.symm_apply_apply, bc83_comp]

/-- `attP` represents `X^N`. -/
noncomputable def attPRep : RepresentsAttractor act N (attP act N) where
  equiv T := (equivShrink _).symm
  naturality s z := by
    change (equivShrink _).symm (equivShrink _ _) = _
    rw [Equiv.symm_apply_apply]
    rfl

theorem isSheaf_attP (hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) (attP act N) :=
  isSheaf_of_equiv (F := attractor act N) (fun T => equivShrink (AttractorPt act N (unop T)))
    (fun {T T'} s x => congrArg (equivShrink (AttractorPt act N (unop T')))
      (congrArg (AttractorPt.baseChange s.unop)
        ((equivShrink (AttractorPt act N (unop T))).symm_apply_apply x).symm))
    (isSheaf_attractor act N _ hX)

end Small

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Core

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Theorem 3.20 and Corollary 3.22 on a chart: `U^N` is a closed subscheme of `U`. -/
structure ChartAttr {U : BigFppfOver B S hS} (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (N : AddSubmonoid M) where
  W : BigFppfOver B S hS
  j : W ⟶ U
  r : RepresentsAttractor actU N (yoneda.obj W)
  closed : IsClosedImmersion ((SCH).map j)
  toPoint_r : ∀ (T : BigFppfOver B S hS) (y : T ⟶ W), (r.equiv T y).toPoint = y ≫ j

/-- The conclusion of the representability part of **Theorem 8.3**: `X^N` is represented by an
algebraic space `P`, `X^{N^×}` by a closed subspace `Y` of `X`, the natural map `P → Y` is affine. -/
structure Thm83Repr {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)
    (N : AddSubmonoid M) where
  P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  c : P ⟶ Y
  i : Y ⟶ X
  rP : RepresentsAttractor actX N P
  rY : RepresentsAttractor actX (unitsSub N).toAddSubmonoid Y
  algP : IsAlgebraicSpace B S hS P
  algY : IsAlgebraicSpace B S hS Y
  affine_c : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) (SCH))) c
  closed_i : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) i
  i_eq : ∀ (T : BigFppfOver B S hS) (y : Y.obj (op T)), i.app (op T) y = (rY.equiv T y).toPoint
  c_eq : ∀ (T : BigFppfOver B S hS) (p : P.obj (op T)),
    rY.equiv T (c.app (op T) p) = AttractorPt.ofFace (isFace_unitsSub N) (rP.equiv T p)

variable {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {actX : AAction (fppfO B S hS) M X}

/-- The representability part of **Theorem 8.3**: if `U → X` is a `N^×`-FPR atlas, if `U^N` is a closed
subscheme of `U` and the morphism to `U^{N^×}` is affine, and if Proposition 5.1 holds for the chart,
then `X^N` is an algebraic space, affine over the closed subspace `X^{N^×}` of `X`. -/
theorem thm83_core (hX : IsAlgebraicSpace B S hS X) (N : AddSubmonoid M) (f : EquivariantHom actU actX)
    (hg : IsZFPRAtlas actU actX f.hom (unitsSub N))
    (rN : ChartAttr actU N)
    (hc : IsFaceCartesian f (isFace_unitsSub N))
    (haff : ∀ (Wz : BigFppfOver B S hS) (jz : Wz ⟶ U) (l : rN.W ⟶ Wz),
      IsClosedImmersion ((SCH).map jz) →
      (∀ {T : BigFppfOver B S hS} (y : T ⟶ U), (∃ c : T ⟶ Wz, c ≫ jz = y) ↔
        y ∈ (fixedPoints (quotientAction actU (unitsSub N))).obj (op T)) →
      (∀ {T : BigFppfOver B S hS} (v : T ⟶ rN.W),
        v ≫ l ≫ jz = (AttractorPt.ofFace (isFace_unitsSub N) (rN.r.equiv T v)).toPoint) →
      AlgebraicGeometry.IsAffineHom ((SCH).map l)) :
    Nonempty (Thm83Repr actX N) := by
  classical
  set Z := unitsSub N with hZ
  have hF := isFace_unitsSub N
  have hd := hg.atlas.decomposition
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hshU : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj U) :=
    BigFppfOver.isSheaf_of_type_yoneda_obj U
  have hcov : ∀ {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)),
      extSieve (fppfO B S hS) Z a ∈ BigFppfOver.topology B S hS T := fun a => extSieve_mem Z a
  let Y := (fixedPoints (quotientAction actX Z)).toFunctor
  let i : Y ⟶ X := (fixedPoints (quotientAction actX Z)).ι
  have hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y := isSheaf_fixedPoints hX.isSheaf actX Z
  haveI hcM : Countable M := countable_of_fg83
  haveI hcQ : Countable (M ⧸ Z) := Quotient.countable
  obtain ⟨Wz, jz, hjz, hiff⟩ := exists_closed_fixed (contains_zmon_countable hS M) hd (Z := Z)
    (contains_zmon_countable hS (M ⧸ Z))
  have hι := presheaf_fixed_ι jz hjz hiff
  have hpb : IsPullback (fixedMap (IsEquivariant.comap (actU := actU) (actX := actX) (f := f.hom)
        hg.atlas.equivariant (QuotientAddGroup.mk' Z)))
      (fixedPoints (quotientAction actU Z)).ι i f.hom := hg.isZFPR
  have hsq : IsPullback hpb.isoPullback.inv (pullback.snd i f.hom)
      (fixedPoints (quotientAction actU Z)).ι (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩
  have hVi := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hι
  have hres := Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hYs hX
    hg.atlas.surjective hg.atlas.etale hVi
  -- the two equivalences of Proposition 3.35
  let eX := fun T => attractorFixedEquivOfCover (act := actX) hsh hcov T
  let eU := fun T => attractorFixedEquivOfCover (act := actU) hshU hcov T
  have heXpt : ∀ T (y : Y.obj (op T)), (eX T y).toPoint = y.1 := fun T y =>
    congrArg Subtype.val ((eX T).symm_apply_apply y)
  have heUpt : ∀ T (y : (fixedPoints (quotientAction actU Z)).toFunctor.obj (op T)),
      (eU T y).toPoint = y.1 := fun T y =>
    congrArg Subtype.val ((eU T).symm_apply_apply y)
  have hXinj : ∀ T (φ ψ : AttractorPt actX Z.toAddSubmonoid T), φ.toPoint = ψ.toPoint → φ = ψ := by
    intro T φ ψ h
    exact (eX T).symm.injective (Subtype.ext h)
  have hUinj : ∀ T (φ ψ : AttractorPt actU Z.toAddSubmonoid T), φ.toPoint = ψ.toPoint → φ = ψ := by
    intro T φ ψ h
    exact (eU T).symm.injective (Subtype.ext h)
  -- the chart
  let κ : yoneda.obj Wz ⟶ (fixedPoints (quotientAction actU Z)).toFunctor :=
    { app := fun T => ↾ fun c => ⟨(c : unop T ⟶ Wz) ≫ jz, (hiff _).1 ⟨c, rfl⟩⟩
      naturality := fun T T' s => by
        ext c
        exact Subtype.ext (Category.assoc _ _ _) }
  have hmj : Mono jz := by
    have : Mono ((SCH).map jz) := inferInstance
    refine ⟨fun {T} a b h => (SCH).map_injective ?_⟩
    apply (cancel_mono ((SCH).map jz)).1
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  have hκ : IsIso κ := by
    refine (NatTrans.isIso_iff_isIso_app κ).2 fun T => ?_
    refine (isIso_iff_bijective _).2 ⟨fun c c' h => ?_, fun y => ?_⟩
    · exact (cancel_mono jz).1 (congrArg Subtype.val h)
    · obtain ⟨c, hc'⟩ := (hiff (T := unop T) y.1).2 y.2
      exact ⟨c, Subtype.ext hc'⟩
  let g₀ : yoneda.obj Wz ⟶ Y := κ ≫ fixedMap (IsEquivariant.comap (actU := actU) (actX := actX)
    (f := f.hom) hg.atlas.equivariant (QuotientAddGroup.mk' Z))
  have h1 : IsPullback κ g₀ (fixedMap (IsEquivariant.comap (actU := actU) (actX := actX)
      (f := f.hom) hg.atlas.equivariant (QuotientAddGroup.mk' Z))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
  have h2 := h1.paste_horiz hpb.flip
  rw [Category.id_comp] at h2
  have hs₀ := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h2
    hg.atlas.surjective
  have he₀ := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h2
    hg.atlas.etale
  -- the affine map
  let P := attP actX N
  let rP := attPRep actX N
  let c : P ⟶ Y :=
    { app := fun T => ↾ fun p => ⟨(AttractorPt.ofFace hF (rP.equiv (unop T) p)).toPoint,
        AttractorPt.toPoint_mem_fixedPoints _⟩
      naturality := fun T T' s => by
        refine ConcreteCategory.hom_ext _ _ fun p => Subtype.ext ?_
        change (AttractorPt.ofFace hF (rP.equiv (unop T') (P.map s.unop.op p))).toPoint =
          X.map s (AttractorPt.ofFace hF (rP.equiv (unop T) p)).toPoint
        rw [rP.naturality s.unop p, ofFace_baseChange, AttractorPt.toPoint_baseChange]
        rfl }
  have hcpt : ∀ T (p : P.obj (op T)), (c.app (op T) p).1 =
      (AttractorPt.ofFace hF (rP.equiv T p)).toPoint := fun T p => rfl
  have hlex : ∃ l : rN.W ⟶ Wz, l ≫ jz = (AttractorPt.ofFace hF (rN.r.equiv rN.W (𝟙 _))).toPoint :=
    (hiff _).2 (AttractorPt.toPoint_mem_fixedPoints _)
  obtain ⟨l, hl⟩ := hlex
  have hlv : ∀ {T : BigFppfOver B S hS} (v : T ⟶ rN.W),
      v ≫ l ≫ jz = (AttractorPt.ofFace hF (rN.r.equiv T v)).toPoint := by
    intro T v
    have hn := rN.r.naturality v (𝟙 rN.W)
    have e : (yoneda.obj rN.W).map v.op (𝟙 rN.W) = v := by simp
    rw [e] at hn
    rw [hn, ofFace_baseChange, AttractorPt.toPoint_baseChange, ← hl]
    rfl
  have hlaff := haff Wz jz l hjz hiff hlv
  let m : yoneda.obj rN.W ⟶ P :=
    { app := fun T => ↾ fun v => (rP.equiv (unop T)).symm (AttractorPt.push f (rN.r.equiv (unop T) v))
      naturality := fun T T' s => by
        refine ConcreteCategory.hom_ext _ _ fun v => ?_
        apply (rP.equiv (unop T')).injective
        change rP.equiv _ ((rP.equiv _).symm (AttractorPt.push f (rN.r.equiv (unop T')
            ((yoneda.obj rN.W).map s.unop.op v)))) =
          rP.equiv (unop T') (P.map s.unop.op ((rP.equiv (unop T)).symm
            (AttractorPt.push f (rN.r.equiv (unop T) v))))
        rw [Equiv.apply_symm_apply, rP.naturality, Equiv.apply_symm_apply, rN.r.naturality]
        rfl }
  have hmpt : ∀ T (v : T ⟶ rN.W), rP.equiv T (m.app (op T) v) =
      AttractorPt.push f (rN.r.equiv T v) := fun T v => Equiv.apply_symm_apply _ _
  have hsq2 : IsPullback m (yoneda.map l) c g₀ := by
    refine IsPullback.of_forall_isPullback_app fun T => ?_
    refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · refine ConcreteCategory.hom_ext _ _ fun v => Subtype.ext ?_
      have hv := hlv (T := unop T) v
      change (AttractorPt.ofFace hF (rP.equiv (unop T) (m.app (op (unop T)) v))).toPoint =
        f.hom.app T ((v : unop T ⟶ rN.W) ≫ l ≫ jz)
      rw [hmpt, ← AttractorPt.push_ofFace, hv]
      rfl
    · rintro v v' ⟨e1, e2⟩
      apply (rN.r.equiv (unop T)).injective
      apply (hc (unop T)).1
      refine Subtype.ext (Prod.ext ?_ ?_)
      · have := congrArg (rP.equiv (unop T)) e1
        exact (hmpt (unop T) v).symm.trans (this.trans (hmpt (unop T) v'))
      · apply hUinj
        have e2' : (v : unop T ⟶ rN.W) ≫ l = (v' : unop T ⟶ rN.W) ≫ l := e2
        change (AttractorPt.ofFace hF _).toPoint = (AttractorPt.ofFace hF _).toPoint
        rw [← hlv, ← hlv, ← Category.assoc, e2', Category.assoc]
    · intro p w e
      let w' : unop T ⟶ Wz := w
      have e' : (AttractorPt.ofFace hF (rP.equiv (unop T) p)).toPoint =
          f.hom.app T (w' ≫ jz) := congrArg Subtype.val e
      let ψ := eU (unop T) (κ.app T w)
      have hψ : ψ.toPoint = w' ≫ jz := heUpt _ _
      have hfc : AttractorPt.ofFace hF (rP.equiv (unop T) p) = AttractorPt.push f ψ := by
        apply hXinj
        rw [e']
        change _ = f.hom.app _ ψ.toPoint
        rw [hψ]
      obtain ⟨u, hu⟩ := (hc (unop T)).2 ⟨(rP.equiv (unop T) p, ψ), hfc⟩
      have hu₁ : AttractorPt.push f u = rP.equiv (unop T) p := congrArg (fun q => q.1.1) hu
      have hu₂ : AttractorPt.ofFace hF u = ψ := congrArg (fun q => q.1.2) hu
      refine ⟨(rN.r.equiv (unop T)).symm u, ?_, ?_⟩
      · apply (rP.equiv (unop T)).injective
        refine (hmpt (unop T) _).trans ?_
        rw [Equiv.apply_symm_apply, hu₁]
      · apply (cancel_mono jz).1
        change ((rN.r.equiv (unop T)).symm u ≫ l) ≫ jz = w' ≫ jz
        rw [Category.assoc, hlv, Equiv.apply_symm_apply, hu₂, hψ]
  have hyl : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map l) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ l).2 hlaff
  have hsq3 : IsPullback hsq2.isoPullback.inv (pullback.snd c g₀) (yoneda.map l) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩
  have hV := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq3 hyl
  have hshP := isSheaf_attP actX N hsh
  have hPs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr hshP
  have hRI : MorphismProperty.RespectsIso (@AlgebraicGeometry.IsAffineHom.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hfin := Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS) hPs hres.1 hs₀ he₀ hV
  refine ⟨⟨P, Y, c, i, rP, ⟨fun T => eX T, fun s z => attractorFixedEquivOfCover_naturality hsh hcov s z⟩,
    hfin.1, hres.1, hfin.2, hres.2, fun T y => ?_, fun T p => ?_⟩⟩
  · exact (heXpt T y).symm
  · apply (eX T).symm.injective
    refine ((eX T).symm_apply_apply _).trans (Subtype.ext ?_)
    exact hcpt T p

end Core

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Coact

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (N : AddSubmonoid M)

/-- `Spec Γ(T)[N] = 𝔸(N)_T` for `T` affine. -/
noncomputable abbrev cP : BigFppfOver B S hS := spObj T (ρN T N) (contains_any T N)

/-- The structure morphism. -/
noncomputable abbrev cπ : cP T N ⟶ T := spToT T (ρN T N) (contains_any T N)

/-- Elements of `Γ(T)[N]` as functions on `𝔸(N)_T`. -/
noncomputable abbrev cι : AddMonoidAlgebra (RT T) N →+* Γ((SCH).obj (cP T N), ⊤) :=
  spSec T (ρN T N) (contains_any T N)

/-- The universal point of `𝔸(N)_T`. -/
noncomputable abbrev cU : UniversalPoint (fppfO B S hS) N T :=
  spUniversal T N (contains_any T N)

lemma hM_of (hS : B.Contains S) (M : Type u) [AddCommGroup M] [AddGroup.FG M] :
    B.Contains (Spec (ZMon M)) := by
  have := countable_of_fg83 (M := M)
  exact contains_zmon_countable hS M

/-- `D(M) × 𝔸(N)_T`. -/
noncomputable abbrev cQ : BigFppfOver B S hS := monAffObj M (hM_of hS M) (cP T N)

/-- The projection `D(M) × 𝔸(N)_T → 𝔸(N)_T`. -/
noncomputable abbrev cpr : cQ T N ⟶ cP T N := prj (hM_of hS M) (cP T N)

/-- The universal point of `D(M)`. -/
noncomputable abbrev cor' : APt (fppfO B S hS) M (op (cQ T N)) := cor (hM_of hS M) (cP T N)

/-- The point `(h, x) ↦ h x` of `𝔸(N)` on `D(M) × 𝔸(N)_T`. -/
noncomputable abbrev cpt : APt (fppfO B S hS) N (op (cQ T N)) :=
  APt.toMagnet N (cor' T N) * APt.res (cpr T N).op (cU T N).u

/-- The action morphism `D(M) × 𝔸(N)_T → 𝔸(N)_T`. -/
noncomputable def ccoact : cQ T N ⟶ cP T N :=
  (cU T N).lift (cpr T N ≫ (cU T N).π) (cpt T N)

lemma ccoact_ι_single (n : N) (r : RT T) :
    ((SCH).map (ccoact T N)).appTop.hom (cι T N (AddMonoidAlgebra.single n r)) =
      MonAff.evalRing M ((SCH).obj (cP T N))
        (AddMonoidAlgebra.single (n : M) (cι T N (AddMonoidAlgebra.single n r))) := by
  have h0 : ((SCH).map (ccoact T N)).appTop.hom (cι T N (AddMonoidAlgebra.single n r)) =
      pointRing (cpr T N ≫ cπ T N) (cpt T N) (AddMonoidAlgebra.single n r) :=
    spLift_appTop T (ρN T N) (contains_any T N) (cpr T N ≫ cπ T N) _ (pointRing_comp _ _) _
  rw [h0, pointRing_single]
  have e1 : AddMonoidAlgebra.single (n : M) (cι T N (AddMonoidAlgebra.single n r)) =
      AddMonoidAlgebra.single (n : M) 1 *
        AddMonoidAlgebra.single 0 (cι T N (AddMonoidAlgebra.single n r)) := by
    rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul]
  rw [e1, map_mul, MonAff.evalRing_single_one, MonAff.evalRing_single_zero]
  have e2 : (AddMonoidAlgebra.single n r : AddMonoidAlgebra (RT T) N) =
      ρN T N r * monN (RT T) N (Multiplicative.ofAdd n) := by
    change _ = AddMonoidAlgebra.single 0 r * AddMonoidAlgebra.single n 1
    rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  have e3 : ((SCH).map (cpr T N ≫ cπ T N)).appTop.hom r =
      (MonAff.π M ((SCH).obj (cP T N))).appTop.hom (cι T N (ρN T N r)) := by
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map (cpr T N)).appTop.hom (((SCH).map (cπ T N)).appTop.hom r) = _
    rw [spToT_appTop]
    rfl
  rw [e3, e2, map_mul, map_mul]
  change _ * (MonAff.coord M _ (Multiplicative.ofAdd (n : M)) *
    (MonAff.π M _).appTop.hom (cι T N (monN (RT T) N (Multiplicative.ofAdd n)))) =
    MonAff.coord M _ (Multiplicative.ofAdd (n : M)) *
      (_ * (MonAff.π M _).appTop.hom (cι T N (monN (RT T) N (Multiplicative.ofAdd n))))
  ring

/-- If a function `x` on `𝔸(N)_T` satisfies `x(h·p) = h^m x(p)`, then `x` is supported in degree `m`:
this is the homogeneity computation behind Theorem 3.20, on `Γ(T)[N]`. -/
theorem coeff_eq_zero_of_coact (x : AddMonoidAlgebra (RT T) N) (m : M)
    (he : ((SCH).map (ccoact T N)).appTop.hom (cι T N x) =
      ptS (cor' T N) (Multiplicative.ofAdd m) * ((SCH).map (cpr T N)).appTop.hom (cι T N x))
    (n : N) (hn : (n : M) ≠ m) : x.coeff n = 0 := by
  classical
  have hAff : IsAffine ((SCH).obj (cP T N)) := inferInstance
  let D : AddMonoidAlgebra Γ((SCH).obj (cP T N), ⊤) M :=
    ∑ k ∈ x.coeff.support, AddMonoidAlgebra.single (k : M)
      (cι T N (AddMonoidAlgebra.single k (x.coeff k)))
  have hx : x = ∑ k ∈ x.coeff.support, AddMonoidAlgebra.single k (x.coeff k) := eq_sum_single x
  have hD : ((SCH).map (ccoact T N)).appTop.hom (cι T N x) =
      MonAff.evalRing M ((SCH).obj (cP T N)) D := by
    conv_lhs => rw [hx]
    simp only [D, map_sum]
    exact Finset.sum_congr rfl fun k _ => ccoact_ι_single T N k _
  have hR : ptS (cor' T N) (Multiplicative.ofAdd m) * ((SCH).map (cpr T N)).appTop.hom (cι T N x) =
      MonAff.evalRing M ((SCH).obj (cP T N)) (AddMonoidAlgebra.single m (cι T N x)) := by
    have e1 : AddMonoidAlgebra.single m (cι T N x) =
        AddMonoidAlgebra.single m 1 * AddMonoidAlgebra.single 0 (cι T N x) := by
      rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul]
    rw [e1, map_mul, MonAff.evalRing_single_one, MonAff.evalRing_single_zero]
    rfl
  have hinj := MonAff.evalRing_injective M ((SCH).obj (cP T N)) (hD.symm.trans (he.trans hR))
  have hc := congrArg (fun z => AddMonoidAlgebra.coeff z (n : M)) hinj
  have hcL : AddMonoidAlgebra.coeff D (n : M) = cι T N (AddMonoidAlgebra.single n (x.coeff n)) := by
    simp only [D]
    by_cases hk : n ∈ x.coeff.support
    · rw [AddMonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_eq_single n]
      · simp [AddMonoidAlgebra.coeff_single]
      · intro b _ hb
        have : (b : M) ≠ n := fun e => hb (Subtype.ext e)
        simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, this]
      · intro h; exact absurd hk h
    · have h0 : x.coeff n = 0 := by simpa using hk
      rw [AddMonoidAlgebra.coeff_sum, Finset.sum_apply', h0]
      simp only [AddMonoidAlgebra.single_zero, map_zero]
      refine Finset.sum_eq_zero fun b hb => ?_
      have : (b : M) ≠ n := fun e => hk ((Subtype.ext e : b = n) ▸ hb)
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, this]
  have hcR : AddMonoidAlgebra.coeff (AddMonoidAlgebra.single m (cι T N x)) (n : M) = 0 := by
    simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hn.symm]
  have h0 : cι T N (AddMonoidAlgebra.single n (x.coeff n)) = 0 :=
    hcL.symm.trans ((by exact hc : _ = _).trans hcR)
  have hs := (spSec_bijective T (ρN T N) (contains_any T N)).1 (h0.trans (map_zero _).symm)
  have := congrArg (fun z => AddMonoidAlgebra.coeff z n) hs
  simpa [AddMonoidAlgebra.coeff_single] using this

end Coact

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Pieces

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {V : ((BigFppfOver.toScheme B S hS).obj U).Opens}

omit [AddGroup.FG M] in
/-- A point of a stable open stays there under the action. -/
lemma smul_mem_of_mem (hst : IsStableOpen actU V) {T : BigFppfOver B S hS} (y : T ⟶ U)
    (h : APt (fppfO B S hS) M (op T)) (q : (SCH).obj T) (hq : (SCH).map y q ∈ V) :
    (SCH).map (smulS actU h y) q ∈ V := by
  let O : ((SCH).obj T).Opens := (SCH).map y ⁻¹ᵁ V
  let s : openObj O ⟶ T := openJ O
  have hr : Set.range ((SCH).map (s ≫ y)) ⊆ V := by
    rintro _ ⟨p, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact p.2
  have := hst (s ≫ y) (APt.res s.op h) hr
  rw [← show s ≫ smulS actU h y = actU.smul (U := op (openObj O)) (APt.res s.op h) (s ≫ y) from
    comp_smulS s h y] at this
  have hm := this ⟨(⟨q, hq⟩ : O), rfl⟩
  rw [Functor.map_comp] at hm
  exact (congrArg (· ∈ V) (Scheme.Hom.comp_apply ((SCH).map s) ((SCH).map (smulS actU h y))
    (⟨q, hq⟩ : O))).mp hm

omit [AddGroup.FG M] in
/-- **Stability of an open**, as an equivalence: `h y ∈ V` iff `y ∈ V`, for `h` a point of `D(M)`. -/
lemma smul_mem_iff (hst : IsStableOpen actU V) {T : BigFppfOver B S hS} (y : T ⟶ U)
    (h : APt (fppfO B S hS) M (op T)) (q : (SCH).obj T) :
    (SCH).map (smulS actU h y) q ∈ V ↔ (SCH).map y q ∈ V := by
  refine ⟨fun hq => ?_, smul_mem_of_mem hst y h q⟩
  let h' : APt (fppfO B S hS) M (op T) := h.comp invMonoidHom
  have e : h' * h = 1 := by
    refine MonoidHom.ext fun m => ?_
    change h (m⁻¹) * h m = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  have := smul_mem_of_mem hst (smulS actU h y) h' q hq
  rwa [← smulS_mul, e, smulS_one] at this

end Pieces

section LemmaA

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {A : Type u} {V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens}

lemma idem_eq_of_basicOpen {X : Scheme.{u}} [IsAffine X] {e f : Γ(X, ⊤)} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (h : X.basicOpen e = X.basicOpen f) : e = f := by
  have key : ∀ {a b : Γ(X, ⊤)}, IsIdempotentElem a → IsIdempotentElem b →
      X.basicOpen a = X.basicOpen b → a * (1 - b) = 0 := by
    intro a b ha hb hab
    have hi : IsIdempotentElem (a * (1 - b)) := ha.mul hb.one_sub
    have hemp : X.basicOpen (a * (1 - b)) = ⊥ := by
      rw [Scheme.basicOpen_mul, hab, ← Scheme.basicOpen_mul]
      have : b * (1 - b) = 0 := by
        rw [mul_sub, mul_one, hb.eq, sub_self]
      rw [this, Scheme.basicOpen_zero]
    have hss : Subsingleton Γ(X, X.basicOpen (a * (1 - b))) := by
      rw [hemp]
      infer_instance
    obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X (U := ⊤)
      (isCompact_univ) (a * (1 - b)) (a * (1 - b)) (Subsingleton.elim _ _)
    have hpw : ∀ k : ℕ, (a * (1 - b)) ^ k * (a * (1 - b)) = a * (1 - b) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_assoc, hi.eq, ih]
    rwa [hpw] at hn
  have h1 := key he hf h
  have h2 := key hf he h.symm
  have : e = e * f := by
    rw [mul_sub, mul_one, sub_eq_zero] at h1
    exact h1
  rw [this, mul_comm]
  rw [mul_sub, mul_one, sub_eq_zero] at h2
  exact h2.symm

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (N : AddSubmonoid M)

/-- **The pieces of the atlas do not mix** (the homogeneity of idempotents of `Γ(T)[N]`). Let `g` be an
equivariant map from `𝔸(N)_T` to the disjoint union `U` of stable opens. Then the preimage of a piece
in `𝔸(N)_T` comes from `T`. -/
theorem exists_function_of_piece (hV : IsAffineDecomposition actU V) (b : A)
    (φ : AttractorPt actU N T) :
    ∃ r : RT T, ∀ {T₁ : BigFppfOver B S hS} (t : T₁ ⟶ T) (a : APt (fppfO B S hS) N (op T₁)) (p : (SCH).obj T₁),
      (SCH).map (φ.app t a) p ∈ V b ↔ p ∈ ((SCH).obj T₁).basicOpen (((SCH).map t).appTop.hom r) := by
  classical
  let Uni := cU T N
  let g : cP T N ⟶ U := φ.app Uni.π Uni.u
  let O : ((SCH).obj (cP T N)).Opens := (SCH).map g ⁻¹ᵁ V b
  have hclop : IsClopen (O : Set ((SCH).obj (cP T N))) := by
    refine ⟨?_, O.2⟩
    have hc : (O : Set ((SCH).obj (cP T N)))ᶜ = ⋃ c : {c // c ≠ b}, ((SCH).map g ⁻¹ᵁ V c.1 : ((SCH).obj (cP T N)).Opens) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        have : (SCH).map g x ∈ iSup V := by rw [hV.iSup_eq_top]; trivial
        obtain ⟨c, hc⟩ := (TopologicalSpace.Opens.mem_iSup).1 this
        refine ⟨⟨c, fun e => hx (show (SCH).map g x ∈ V b from e ▸ hc)⟩, hc⟩
      · rintro ⟨⟨c, hcb⟩, hc⟩ hx
        have hd := hV.disjoint hcb
        have hm : (SCH).map g x ∈ (V c ⊓ V b : ((SCH).obj U).Opens) := ⟨hc, hx⟩
        rw [disjoint_iff.1 hd] at hm
        exact hm
    rw [← isOpen_compl_iff, hc]
    exact isOpen_iUnion fun c => TopologicalSpace.Opens.isOpen _
  let sO : Set (PrimeSpectrum (AddMonoidAlgebra (RT T) N)) := (O : Set ((SCH).obj (cP T N)))
  obtain ⟨e, hei, heO⟩ := (PrimeSpectrum.isClopen_iff (s := sO)).1 hclop
  have hb : ((SCH).obj (cP T N)).basicOpen (cι T N e) = O := by
    have h0 := basicOpen_eq_of_affine (R := .of (AddMonoidAlgebra (RT T) N)) e
    refine TopologicalSpace.Opens.ext ?_
    exact (congrArg SetLike.coe h0).trans heO.symm
  have hpre : ∀ {T₁ : BigFppfOver B S hS} (f : T₁ ⟶ cP T N) (p : (SCH).obj T₁),
      (SCH).map (f ≫ g) p ∈ V b ↔ p ∈ ((SCH).obj T₁).basicOpen (((SCH).map f).appTop.hom (cι T N e)) := by
    intro T₁ f p
    rw [← Scheme.preimage_basicOpen_top, hb, Functor.map_comp, Scheme.Hom.comp_apply]
    rfl
  -- homogeneity
  have hcg : ccoact T N ≫ g = smulS actU (cor' T N) (cpr T N ≫ g) := by
    have h1 := φ.equivariant (cpr T N ≫ Uni.π) (cor' T N) (APt.res (cpr T N).op Uni.u)
    have h2 := φ.naturality (cpr T N) Uni.π Uni.u
    have h3 := φ.app_eq_of_universal Uni (cpr T N ≫ Uni.π) (cpt T N)
    refine h3.symm.trans (h1.trans ?_)
    rw [h2]
    rfl
  have heq : ((SCH).map (ccoact T N)).appTop.hom (cι T N e) =
      ((SCH).map (cpr T N)).appTop.hom (cι T N e) := by
    have hA0 : IsAffine (MonAff M ((SCH).obj (cP T N))) :=
      .of_isIso (MonAff.isoOfIsAffine M ((SCH).obj (cP T N))).hom
    have hAffQ : IsAffine ((SCH).obj (cQ T N)) := hA0
    refine idem_eq_of_basicOpen ((hei.map (cι T N)).map _) ((hei.map (cι T N)).map _) ?_
    refine TopologicalSpace.Opens.ext (Set.ext fun q => ?_)
    have l := hpre (ccoact T N) q
    have r := hpre (cpr T N) q
    rw [hcg, smul_mem_iff (hV.stable b)] at l
    exact l.symm.trans r
  have hc0 : ∀ n : N, (n : M) ≠ 0 → e.coeff n = 0 := by
    intro n hn
    refine coeff_eq_zero_of_coact T N e 0 ?_ n hn
    rw [heq]
    have : ptS (cor' T N) (Multiplicative.ofAdd (0 : M)) = 1 := map_one _
    rw [this, one_mul]
  have hes : e = AddMonoidAlgebra.single 0 (e.coeff 0) := by
    refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun n => ?_)
    by_cases hn : n = 0
    · subst hn
      simp [AddMonoidAlgebra.coeff_single]
    · have : (n : M) ≠ 0 := fun h => hn (Subtype.ext h)
      rw [hc0 n this]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hn]
  refine ⟨e.coeff 0, fun {T₁} t a p => ?_⟩
  have hl : φ.app t a = Uni.lift t a ≫ g := φ.app_eq_of_universal Uni t a
  have hpl := hpre (Uni.lift t a) p
  rw [hl]
  have hv : ((SCH).map (Uni.lift t a)).appTop.hom (cι T N e) = ((SCH).map t).appTop.hom (e.coeff 0) := by
    have h0 : ((SCH).map (Uni.lift t a)).appTop.hom (cι T N e) = pointRing t a e :=
      spLift_appTop T (ρN T N) (contains_any T N) t _ (pointRing_comp _ _) _
    rw [h0]
    conv_lhs => rw [hes]
    rw [pointRing_single, ofAdd_zero, map_one, mul_one]
  exact hpl.trans (iff_of_eq (congrArg (fun z => p ∈ ((SCH).obj T₁).basicOpen z) hv))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- **The pieces of the atlas do not mix.** If `φ` is a point of `U^N(T)`, where `U` is a disjoint union
of stable opens, the value of `φ` at any point of `𝔸(N)` lies in the same piece as the value at `1`. -/
theorem app_mem_iff (hV : IsAffineDecomposition actU V) (b : A)
    {N : AddSubmonoid M} {T : BigFppfOver B S hS} (φ : AttractorPt actU N T) {T₁ : BigFppfOver B S hS}
    (t : T₁ ⟶ T) (a : APt (fppfO B S hS) N (op T₁)) (p : (SCH).obj T₁) :
    (SCH).map (φ.app t a) p ∈ V b ↔ (SCH).map (φ.app t 1) p ∈ V b := by
  obtain ⟨W, hW, hpW⟩ : ∃ W : ((SCH).obj T₁).Opens, IsAffineOpen W ∧ p ∈ W := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ := ((SCH).obj T₁).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ p) isOpen_univ
    exact ⟨W, hW, hx⟩
  let P := openObj W
  let s : P ⟶ T₁ := openJ W
  have : IsAffine ((SCH).obj P) := hW
  obtain ⟨r, hr⟩ := exists_function_of_piece P N hV b (φ.baseChange (s ≫ t))
  have hval : ∀ c : APt (fppfO B S hS) N (op T₁), s ≫ φ.app t c =
      AttractorPt.app (φ.baseChange (s ≫ t)) (𝟙 P) (APt.res s.op c) := by
    intro c
    have h := φ.naturality s t c
    have e : AttractorPt.app (φ.baseChange (s ≫ t)) (𝟙 P) (APt.res s.op c) =
        φ.app (𝟙 P ≫ s ≫ t) (APt.res s.op c) := rfl
    rw [e, Category.id_comp, h]
    rfl
  let q : (SCH).obj P := (⟨p, hpW⟩ : W)
  have hq : ∀ c : APt (fppfO B S hS) N (op T₁), (SCH).map (φ.app t c) p ∈ V b ↔
      q ∈ ((SCH).obj P).basicOpen (((SCH).map (𝟙 P)).appTop.hom r) := by
    intro c
    have := hr (𝟙 P) (APt.res s.op c) q
    rw [← hval, Functor.map_comp, Scheme.Hom.comp_apply] at this
    exact this
  exact (hq a).trans (hq 1).symm

end LemmaA

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] GB.gradedAlgebraOf

section Bridge

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {A : Type u} {V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens}

lemma mono_openJ {V : ((BigFppfOver.toScheme B S hS).obj U).Opens} : Mono (openJ V) := by
  refine ⟨fun {T} a b h => (SCH).map_injective ?_⟩
  apply (cancel_mono (iV V)).1
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- A section vanishes if it vanishes on an open neighbourhood of each point. -/
lemma section_eq_zero_of_opens {X : Scheme.{u}} (s : Γ(X, ⊤))
    (h : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ O.ι.appTop.hom s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ s 0 fun x hx => ?_
  obtain ⟨O, hxO, hO⟩ := h x
  rw [Scheme.Opens.ι_appTop O] at hO
  have hx' : x ∈ O.ι ''ᵁ ⊤ := ⟨⟨x, hxO⟩, trivial, rfl⟩
  rw [map_zero]
  refine (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE le_top) x hx' s).symm.trans ?_
  exact (congrArg (ConcreteCategory.hom (X.presheaf.germ _ x hx')) hO).trans (map_zero _)

/-- The action of `D(M)` on a stable open, on the site. -/
noncomputable def pieceAct {W : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (hst : IsStableOpen actU W) : AAction (fppfO B S hS) M (yoneda.obj (openObj W)) := by
  have hl : ∀ {T : BigFppfOver B S hS} (h : APt (fppfO B S hS) M (op T)) (t : T ⟶ openObj W),
      ∃ t' : T ⟶ openObj W, t' ≫ openJ W = smulS actU h (t ≫ openJ W) := fun {T} h t =>
    exists_lift_open _ fun p => smul_mem_of_mem hst _ h p (by
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact ((SCH).map t p).2)
  have hm := mono_openJ (V := W)
  refine
    { smul := fun {T} h t => (hl (T := unop T) h t).choose
      one_smul := fun {T} x => ?_
      mul_smul := fun {T} g h x => ?_
      map_smul := fun {T T'} f h x => ?_ }
  · apply (cancel_mono (openJ W)).1
    exact (hl _ _).choose_spec.trans (smulS_one _)
  · apply (cancel_mono (openJ W)).1
    refine (hl _ _).choose_spec.trans ?_
    rw [smulS_mul]
    refine Eq.trans ?_ (hl _ _).choose_spec.symm
    rw [(hl h x).choose_spec]
  · apply (cancel_mono (openJ W)).1
    change (f.unop ≫ (hl _ _).choose) ≫ openJ W = (hl _ _).choose ≫ openJ W
    rw [Category.assoc, (hl _ _).choose_spec, (hl _ _).choose_spec, comp_smulS]
    exact congrArg (smulS actU (APt.res f h)) (Category.assoc _ _ _).symm

lemma pieceAct_spec {W : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (hst : IsStableOpen actU W) {T : BigFppfOver B S hS} (h : APt (fppfO B S hS) M (op T))
    (t : T ⟶ openObj W) :
    ((pieceAct hst).smul (U := op T) h t : T ⟶ openObj W) ≫ openJ W = smulS actU h (t ≫ openJ W) :=
  Exists.choose_spec (p := fun t' : T ⟶ openObj W => t' ≫ openJ W = smulS actU h (t ≫ openJ W)) _

/-- The inclusion of a stable open is equivariant. -/
noncomputable def pieceJ {W : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (hst : IsStableOpen actU W) : EquivariantHom (pieceAct hst) actU where
  hom := yoneda.map (openJ W)
  map_smul {T} h x := pieceAct_spec hst (T := unop T) h x

/-- `ccoact` is compatible with the action through a point of the attractor. -/
lemma coact_comp {F : BigFppfOver B S hS} {act : AAction (fppfO B S hS) M (yoneda.obj F)}
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (N : AddSubmonoid M)
    (φ : AttractorPt act N T) :
    ccoact T N ≫ φ.app (cU T N).π (cU T N).u =
      smulS act (cor' T N) (cpr T N ≫ φ.app (cU T N).π (cU T N).u) := by
  have h1 := φ.equivariant (cpr T N ≫ (cU T N).π) (cor' T N) (APt.res (cpr T N).op (cU T N).u)
  have h2 := φ.naturality (cpr T N) (cU T N).π (cU T N).u
  have h3 := φ.app_eq_of_universal (cU T N) (cpr T N ≫ (cU T N).π) (cpt T N)
  refine h3.symm.trans (h1.trans ?_)
  rw [h2]
  rfl

/-- **Theorem 3.20, the homogeneous elements of degree outside `N` vanish**: if `τ : T → V` underlies a
point of `U^N(T)`, `T` affine, it kills the homogeneous functions on `V` of degree outside `N`. -/
theorem ptX_eq_zero_of_att (hV : IsAffineDecomposition actU V) (b : A)
    {N : AddSubmonoid M} {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (φ : AttractorPt actU N T) (τ : T ⟶ openObj (V b)) (hτ : τ ≫ openJ (V b) = φ.toPoint)
    [IsAffineHom (openOver (V b)).hom]
    {U₀ : S.Opens} (hU₀ : IsAffineOpen U₀) (hT : GB.LiesOver (ov T) U₀) {m : M} (hm : m ∉ N)
    {a : GB.Aalg (openOver (V b)) U₀}
    (ha : a ∈ GB.gradingOf hU₀ (overAct (hM_of hS M) (hV.stable b)) m) :
    GB.ptX (openOver (V b)) hU₀ (ov T) hT (ovMap τ) a = 0 := by
  have hM := hM_of hS M
  have hst : IsStableOpen actU (V b) := hV.stable b
  have hmJ := mono_openJ (V := V b)
  let g : cP T N ⟶ U := φ.app (cU T N).π (cU T N).u
  have hone : ∀ {T₁ : BigFppfOver B S hS} (t : T₁ ⟶ T), φ.app t 1 = t ≫ τ ≫ openJ (V b) := by
    intro T₁ t
    have h := φ.naturality t (𝟙 T) 1
    have e : APt.res (𝒪 := fppfO B S hS) (P := N) t.op 1 = 1 := by ext p; simp
    rw [Category.comp_id, e] at h
    rw [h, hτ]
    rfl
  obtain ⟨g', hg'⟩ := exists_lift_open (V := V b) g (fun p => by
    refine (app_mem_iff hV b φ (cU T N).π (cU T N).u p).2 ?_
    rw [hone]
    have e : (SCH).map ((cU T N).π ≫ τ ≫ openJ (V b)) = (SCH).map ((cU T N).π ≫ τ) ≫ iV (V b) := by
      rw [← Category.assoc, Functor.map_comp]
    rw [e]
    exact ((SCH).map ((cU T N).π ≫ τ) p).2)
  have hPl : GB.LiesOver (ov (cP T N)) U₀ := hT.of_hom (ovHom (cU T N).π)
  have hQl : GB.LiesOver (ov (cQ T N)) U₀ := hPl.of_hom (ovHom (cpr T N))
  set bb := GB.ptX (openOver (V b)) hU₀ (ov (cP T N)) hPl (ovMap g') a with hbb
  obtain ⟨x, hx⟩ := (spSec_bijective T (ρN T N) (contains_any T N)).2 bb
  -- the action on points
  let y : cQ T N ⟶ openObj (V b) := cpr T N ≫ g'
  let z : cQ T N ⟶ openObj (V b) := ccoact T N ≫ g'
  have hz : z ≫ openJ (V b) = smulS actU (cor' T N) (y ≫ openJ (V b)) := by
    have e := coact_comp T N φ
    have e1 : z ≫ openJ (V b) = ccoact T N ≫ g := by
      rw [← hg']; exact Category.assoc _ _ _
    have e2 : y ≫ openJ (V b) = cpr T N ≫ g := by
      rw [← hg']; exact Category.assoc _ _ _
    rw [e1, e2]
    exact e
  let h₀ : APt (GB.overO S) M (op (ov (cQ T N))) := ptS (cor' T N)
  have hz' : ovMap z = (overAct hM hst).smul (U := op (ov (cQ T N))) h₀ (ovMap y) := by
    refine Over.OverMorphism.ext ?_
    apply (cancel_mono (iV (V b))).1
    have e := smul_eq_actMor hM hst y (cor' T N)
    rw [← hz, Functor.map_comp] at e
    exact e.trans (Category.assoc _ _ _).symm
  have hs := GB.ptX_smul_of_mem hU₀ (overAct hM hst) hQl h₀ (ovMap y) ha
  rw [← hz'] at hs
  have hzc : GB.ptX (openOver (V b)) hU₀ (ov (cQ T N)) hQl (ovMap z) a =
      ((SCH).map (ccoact T N)).appTop.hom bb := by
    have e : ovMap z = ovHom (ccoact T N) ≫ ovMap g' := Over.OverMorphism.ext ((SCH).map_comp _ _)
    rw [e, GB.ptX_comp (openOver (V b)) hU₀ hPl hQl]
    rfl
  have hyc : GB.ptX (openOver (V b)) hU₀ (ov (cQ T N)) hQl (ovMap y) a =
      ((SCH).map (cpr T N)).appTop.hom bb := by
    have e : ovMap y = ovHom (cpr T N) ≫ ovMap g' := Over.OverMorphism.ext ((SCH).map_comp _ _)
    rw [e, GB.ptX_comp (openOver (V b)) hU₀ hPl hQl]
    rfl
  have he : ((SCH).map (ccoact T N)).appTop.hom (cι T N x) =
      ptS (cor' T N) (Multiplicative.ofAdd m) * ((SCH).map (cpr T N)).appTop.hom (cι T N x) := by
    have hx' : cι T N x = bb := hx
    rw [hx', ← hzc, ← hyc]
    exact hs
  have hx0 : x = 0 := by
    refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun n => ?_)
    exact coeff_eq_zero_of_coact T N x m he n (fun e => hm (e ▸ n.2))
  have hbb0 : bb = 0 := hx.symm.trans ((congrArg _ hx0).trans (map_zero _))
  let l : T ⟶ cP T N := (cU T N).lift (𝟙 T) 1
  have hl : l ≫ g' = τ := by
    apply (cancel_mono (openJ (V b))).1
    rw [Category.assoc, hg']
    have h1 := φ.app_eq_of_universal (cU T N) (𝟙 T) 1
    have h2 := hone (𝟙 T)
    rw [Category.id_comp] at h2
    exact h1.symm.trans h2
  have e : ovMap τ = ovHom l ≫ ovMap g' := by
    rw [← hl]; exact Over.OverMorphism.ext ((SCH).map_comp _ _)
  rw [e, GB.ptX_comp (openOver (V b)) hU₀ hPl hT]
  change ((SCH).map l).appTop.hom bb = 0
  rw [hbb0]
  exact map_zero _

end Bridge

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] GB.gradedAlgebraOf

section Bridge2

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {A : Type u} {V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens}

/-- A point of `U^N`, with value at `1` in the piece `V b`, gives a point of `(V b)^N` on all schemes. -/
theorem exists_over_att (hV : IsAffineDecomposition actU V) (b : A)
    {N : AddSubmonoid M} {T : BigFppfOver B S hS} (φ : AttractorPt actU N T)
    (t : T ⟶ openObj (V b)) (ht : t ≫ openJ (V b) = φ.toPoint) :
    ∃ φo : AttractorPt (overAct (hM_of hS M) (hV.stable b)) N (ov T), φo.toPoint = ovMap t := by
  have hA : IsAffineHom (openOver (V b)).hom := hV.isAffineHom b
  refine GB.exists_att_of_local _ (ovMap t) ?_
  intro W f U₀ hW
  refine (GB.exists_att_iff_kills _ U₀.2 hW _).2 ?_
  intro a ha
  refine Submodule.span_induction (p := fun a _ =>
    GB.ptX (openOver (V b)) U₀.2 W hW (f ≫ ovMap t) a = 0) ?_ ?_ ?_ ?_ ha
  · intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx
    obtain ⟨m, hm, hx⟩ := hx
    refine section_eq_zero_of_opens _ fun q => ?_
    have hfq : f.left q ∈ (structMap T ⁻¹ᵁ U₀.1 : ((SCH).obj T).Opens) := by
      have := hW.mem q
      have e := Over.w f
      change (W.hom q) ∈ _ at this
      rw [← e] at this
      exact this
    obtain ⟨_, ⟨A', hA', rfl⟩, hxA, hle⟩ := ((SCH).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      hfq (TopologicalSpace.Opens.isOpen _)
    let A0 : ((SCH).obj T).Opens := A'
    have hA0 : IsAffineOpen A0 := hA'
    let P := openObj A0
    let s : P ⟶ T := openJ A0
    have hPa : IsAffine ((SCH).obj P) := hA0
    have hPl : GB.LiesOver (ov P) U₀.1 := by
      refine top_le_iff.1 fun p _ => ?_
      exact hle (p.2)
    let O : W.left.Opens := f.left ⁻¹ᵁ A0
    let Wq : Over S := Over.mk (O.ι ≫ W.hom)
    let ιq : Wq ⟶ W := Over.homMk O.ι rfl
    have hWq : GB.LiesOver Wq U₀.1 := hW.of_hom ιq
    have hrg : Set.range (O.ι ≫ f.left) ⊆ Set.range (iV A0) := by
      rw [show Set.range (iV A0) = (A0 : Set _) from Scheme.Opens.range_ι A0]
      rintro _ ⟨p, rfl⟩
      exact p.2
    let k₀ : O.toScheme ⟶ (SCH).obj P := IsOpenImmersion.lift (iV A0) (O.ι ≫ f.left) hrg
    have hk₀ : k₀ ≫ iV A0 = O.ι ≫ f.left := IsOpenImmersion.lift_fac _ _ _
    let k : Wq ⟶ ov P := Over.homMk k₀ (by
      change k₀ ≫ iV A0 ≫ structMap T = O.ι ≫ W.hom
      rw [← Category.assoc, hk₀, Category.assoc]
      exact congrArg (fun z => O.ι ≫ z) (Over.w f))
    have hcomp : ιq ≫ f ≫ ovMap t = k ≫ ovMap (s ≫ t) := by
      refine Over.OverMorphism.ext ?_
      change O.ι ≫ f.left ≫ (SCH).map t = k₀ ≫ (SCH).map (s ≫ t)
      rw [Functor.map_comp, ← Category.assoc k₀, ]
      change _ = (k₀ ≫ iV A0) ≫ _
      rw [hk₀, Category.assoc]
    have h0 := ptX_eq_zero_of_att hV b (φ.baseChange s) (s ≫ t) (by
      rw [Category.assoc, ht, AttractorPt.toPoint_baseChange]
      rfl) U₀.2 hPl hm hx
    refine ⟨O, hxA, ?_⟩
    have e1 := GB.ptX_comp (openOver (V b)) U₀.2 hW hWq ιq (f ≫ ovMap t)
    have e2 := GB.ptX_comp (openOver (V b)) U₀.2 hPl hWq k (ovMap (s ≫ t))
    rw [hcomp, e2] at e1
    have e3 := DFunLike.congr_fun e1 x
    change (k₀.appTop).hom (GB.ptX (openOver (V b)) U₀.2 (ov P) hPl (ovMap (s ≫ t)) x) =
      (O.ι.appTop).hom _ at e3
    rw [h0] at e3
    exact e3.symm.trans (map_zero _)
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- A morphism over `S` to `V`, as a morphism of the site. -/
noncomputable def siteOf {W : ((BigFppfOver.toScheme B S hS).obj U).Opens} {T : BigFppfOver B S hS}
    (m : ov T ⟶ openOver W) : T ⟶ openObj W :=
  Over.homMk (ObjectProperty.homMk m.left) (by
    apply B.inclusion.map_injective
    exact Over.w m)

lemma overSmul_siteOf {W : ((BigFppfOver.toScheme B S hS).obj U).Opens} (hst : IsStableOpen actU W)
    {T : BigFppfOver B S hS} (m : ov T ⟶ openOver W) (h : APt (fppfO B S hS) M (op T)) :
    siteOf (overSmul (hM_of hS M) hst (T := ov T) h m) ≫ openJ W =
      smulS actU h (siteOf m ≫ openJ W) := by
  apply (SCH).map_injective
  rw [smul_eq_actMor (hM_of hS M) hst (siteOf m) h, Functor.map_comp]
  exact Category.assoc _ _ _

lemma siteOf_comp {W : ((BigFppfOver.toScheme B S hS).obj U).Opens} {T T' : BigFppfOver B S hS}
    (r : T' ⟶ T) (m : ov T ⟶ openOver W) : siteOf (ovHom r ≫ m) = r ≫ siteOf m := by
  apply (SCH).map_injective
  rw [Functor.map_comp]
  rfl

/-- A point of a magnet on the site, on all schemes. -/
abbrev castPt {P : Type*} [AddCommMonoid P] {T : BigFppfOver B S hS}
    (a : APt (fppfO B S hS) P (op T)) : APt (GB.overO S) P (op (ov T)) := a

/-- A point of `(V b)^N` on all schemes gives a point of `U^N` on the site. -/
theorem exists_site_att {W : ((BigFppfOver.toScheme B S hS).obj U).Opens} (hst : IsStableOpen actU W)
    {N : AddSubmonoid M} {T : BigFppfOver B S hS}
    (φo : AttractorPt (overAct (hM_of hS M) hst) N (ov T)) :
    ∃ φ : AttractorPt actU N T, φ.toPoint = siteOf φo.toPoint ≫ openJ W := by
  have hovc : ∀ {T₁ T₂ : BigFppfOver B S hS} (r : T₂ ⟶ T₁) (s : T₁ ⟶ T),
      ovHom (r ≫ s) = ovHom r ≫ ovHom s :=
    fun r s => Over.OverMorphism.ext ((SCH).map_comp r s)
  have hov1 : ovHom (𝟙 T) = 𝟙 (ov T) := Over.OverMorphism.ext ((SCH).map_id T)
  refine ⟨{ app := fun {T'} s a => siteOf (φo.app (ovHom s) (castPt a)) ≫ openJ W
            naturality := fun {T' T''} r s a => ?_
            equivariant := fun {T'} s h a => ?_ }, ?_⟩
  · have hn : φo.app (ovHom (r ≫ s)) (castPt (APt.res r.op a)) =
        ovHom r ≫ φo.app (ovHom s) (castPt a) := by
      rw [hovc]
      exact φo.naturality (ovHom r) (ovHom s) (castPt a)
    refine (congrArg (fun q => siteOf q ≫ openJ W) hn).trans ?_
    change siteOf _ ≫ openJ W = r ≫ siteOf _ ≫ openJ W
    rw [siteOf_comp, Category.assoc]
  · have he : φo.app (ovHom s) (castPt (APt.toMagnet N h * a)) =
        overSmul (hM_of hS M) hst (T := ov T') (castPt h) (φo.app (ovHom s) (castPt a)) :=
      φo.equivariant (ovHom s) (castPt h) (castPt a)
    refine (congrArg (fun q => siteOf q ≫ openJ W) he).trans ?_
    exact overSmul_siteOf hst _ h
  · change siteOf (φo.app (ovHom (𝟙 T)) (castPt 1)) ≫ openJ W = siteOf (φo.app (𝟙 (ov T)) 1) ≫ openJ W
    rw [hov1]
    rfl

/-- Theorem 3.20 and Corollary 3.22 on a stable `S`-affine piece. -/
theorem exists_closed_att_piece (hV : IsAffineDecomposition actU V) (b : A) (N : AddSubmonoid M) :
    ∃ (Zs : Scheme.{u}) (i : Zs ⟶ (SCH).obj (openObj (V b))), IsClosedImmersion i ∧
      ∀ {T : BigFppfOver B S hS} (t : T ⟶ openObj (V b)),
        (∃ z : (SCH).obj T ⟶ Zs, z ≫ i = (SCH).map t) ↔
          ∃ φ : AttractorPt actU N T, φ.toPoint = t ≫ openJ (V b) := by
  have hA : IsAffineHom (openOver (V b)).hom := hV.isAffineHom b
  let act := overAct (hM_of hS M) (hV.stable b)
  refine ⟨(GB.Zatt act N).left, (GB.iAtt act N).left, inferInstance, fun {T} t => ⟨?_, ?_⟩⟩
  · rintro ⟨z, hz⟩
    have hw : z ≫ (GB.Zatt act N).hom = structMap T := by
      have h1 := Over.w (GB.iAtt act N)
      refine (congrArg (fun q => z ≫ q) h1.symm).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun q => q ≫ (openOver (V b)).hom) hz).trans ?_
      exact Over.w (ovMap t)
    let z' : ov T ⟶ GB.Zatt act N := Over.homMk z hw
    obtain ⟨φo, hφo⟩ := (GB.exists_lift_iff act N (ovMap t)).1 ⟨z', Over.OverMorphism.ext hz⟩
    obtain ⟨φ, hφ⟩ := exists_site_att (hV.stable b) φo
    refine ⟨φ, hφ.trans ?_⟩
    rw [hφo]
    rfl
  · rintro ⟨φ, hφ⟩
    obtain ⟨φo, hφo⟩ := exists_over_att hV b φ t hφ.symm
    obtain ⟨z, hz⟩ := (GB.exists_lift_iff act N (ovMap t)).2 ⟨φo, hφo⟩
    exact ⟨z.left, congrArg Over.Hom.left hz⟩

end Bridge2

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Glue

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {A : Type u} {V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens}

/-- The open cover of `T` by the preimages of the pieces. -/
lemma cover_mem (hV : IsAffineDecomposition actU V) {T : BigFppfOver B S hS} (y : T ⟶ U) :
    Sieve.ofArrows (fun b => openObj ((SCH).map y ⁻¹ᵁ V b)) (fun b => openJ ((SCH).map y ⁻¹ᵁ V b)) ∈
      BigFppfOver.topology B S hS T := by
  refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS _
    (fun b => inferInstanceAs (IsOpenImmersion (iV _))) fun x => ?_
  have : (SCH).map y x ∈ iSup V := by rw [hV.iSup_eq_top]; trivial
  obtain ⟨c, hc⟩ := (TopologicalSpace.Opens.mem_iSup).1 this
  refine ⟨c, (⟨x, hc⟩ : ((SCH).map y ⁻¹ᵁ V c : ((SCH).obj T).Opens)), rfl⟩

lemma app_one_eq {N : AddSubmonoid M} {T T₁ : BigFppfOver B S hS} (φ : AttractorPt actU N T)
    (t : T₁ ⟶ T) : φ.app t 1 = t ≫ φ.toPoint := by
  have h := φ.naturality t (𝟙 T) 1
  have e : APt.res (𝒪 := fppfO B S hS) (P := N) t.op 1 = 1 := by ext p; simp
  rw [Category.comp_id, e] at h
  exact h

/-- A point of `U^N` with value at `1` in a piece comes from a point of the attractor of that piece. -/
theorem exists_piece_lift (hV : IsAffineDecomposition actU V) (b : A) {N : AddSubmonoid M}
    {T : BigFppfOver B S hS} (φ : AttractorPt actU N T) (ht : ∀ p, (SCH).map φ.toPoint p ∈ V b) :
    ∃ φ' : AttractorPt (pieceAct (hV.stable b)) N T, AttractorPt.push (pieceJ (hV.stable b)) φ' = φ := by
  have hl : ∀ {T₁ : BigFppfOver B S hS} (t : T₁ ⟶ T) (a : APt (fppfO B S hS) N (op T₁)),
      ∃ t' : T₁ ⟶ openObj (V b), t' ≫ openJ (V b) = φ.app t a := by
    intro T₁ t a
    refine exists_lift_open _ fun p => (app_mem_iff hV b φ t a p).2 ?_
    rw [app_one_eq, Functor.map_comp]
    exact ht _
  have hmJ := mono_openJ (V := V b)
  refine ⟨{ app := fun {T₁} t a => (hl t a).choose
            naturality := fun {T₁ T₂} s t a => ?_
            equivariant := fun {T₁} t h a => ?_ }, ?_⟩
  · apply (cancel_mono (openJ (V b))).1
    refine (hl _ _).choose_spec.trans ?_
    rw [φ.naturality]
    change s ≫ φ.app t a = (s ≫ (hl t a).choose) ≫ openJ (V b)
    rw [Category.assoc, (hl t a).choose_spec]
  · apply (cancel_mono (openJ (V b))).1
    refine (hl _ _).choose_spec.trans ?_
    rw [φ.equivariant]
    refine Eq.trans ?_ (pieceAct_spec (hV.stable b) h _).symm
    rw [(hl t a).choose_spec]
    rfl
  · refine AttractorPt.ext ?_
    funext T₁ t a
    exact (hl t a).choose_spec

/-- A presheaf map from a separated scheme over `S` to the base: `S`-affine objects are separated. -/
lemma isSeparatedOver_openObj (hV : IsAffineDecomposition actU V) (b : A) :
    IsSeparatedOver (yoneda.obj (openObj (V b))) := by
  let w : openObj (V b) ⟶ siteTop (B := B) (S := S) (hS := hS) := Over.mkIdTerminal.from _
  have e : toBase (yoneda.obj (openObj (V b))) = yoneda.map w := by
    ext T r
    exact Over.mkIdTerminal.hom_ext _ _
  have hA : IsAffineHom ((SCH).map w) := by
    have hA' : IsAffineHom (openOver (V b)).hom := hV.isAffineHom b
    have e' : (SCH).map w ≫ 𝟙 _ = (openOver (V b)).hom := by
      rw [Category.comp_id]
      exact congrArg B.inclusion.map (Over.w w)
    rw [Category.comp_id] at e'
    rw [e']
    exact hA'
  change Space.IsSeparated B S hS (toBase _)
  rw [e]
  exact (Space.isSeparated_yoneda_map_iff B S hS w).2 inferInstance

/-- `U^N → U` is a monomorphism, for `U` a disjoint union of stable `S`-affine schemes. -/
theorem toPoint_injective_U (hV : IsAffineDecomposition actU V) {N : AddSubmonoid M}
    {T : BigFppfOver B S hS} {φ ψ : AttractorPt actU N T} (h : φ.toPoint = ψ.toPoint) : φ = ψ := by
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) (attractor actU N) :=
    isSheaf_attractor actU N _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  refine (hsh _ (cover_mem hV φ.toPoint)).isSeparatedFor.ext fun W g hg => ?_
  obtain ⟨_, r, s', ⟨b⟩, rfl⟩ := hg
  suffices e : AttractorPt.baseChange (openJ ((SCH).map φ.toPoint ⁻¹ᵁ V b)) φ =
      AttractorPt.baseChange (openJ ((SCH).map φ.toPoint ⁻¹ᵁ V b)) ψ from
    congrArg (AttractorPt.baseChange r) e
  let J₀ := openJ ((SCH).map φ.toPoint ⁻¹ᵁ V b)
  have hp : ∀ p, (SCH).map (J₀ ≫ φ.toPoint) p ∈ V b := fun p => by
    rw [Functor.map_comp]
    exact p.2
  have hφ₀ : (AttractorPt.baseChange J₀ φ).toPoint = J₀ ≫ φ.toPoint := AttractorPt.toPoint_baseChange _ _
  have hψ₀ : (AttractorPt.baseChange J₀ ψ).toPoint = J₀ ≫ φ.toPoint :=
    (AttractorPt.toPoint_baseChange _ _).trans (congrArg (fun q => J₀ ≫ q) h.symm)
  obtain ⟨φ', hφ'⟩ := exists_piece_lift hV b (AttractorPt.baseChange J₀ φ) (by rw [hφ₀]; exact hp)
  obtain ⟨ψ', hψ'⟩ := exists_piece_lift hV b (AttractorPt.baseChange J₀ ψ) (by rw [hψ₀]; exact hp)
  rw [← hφ', ← hψ']
  congr 1
  refine attractor_toPoint_injective_sep (isAlgebraicSpace_yoneda B S hS _)
    (isSeparatedOver_openObj hV b) N _ ?_
  have hmJ := mono_openJ (V := V b)
  apply (cancel_mono (openJ (V b))).1
  have h1 := congrArg AttractorPt.toPoint hφ'
  have h2 := congrArg AttractorPt.toPoint hψ'
  exact h1.trans (hφ₀.trans (hψ₀.symm.trans h2.symm))

/-- `U^N` is local on the source among points of `U`. -/
theorem exists_att_of_cover (hV : IsAffineDecomposition actU V) {N : AddSubmonoid M}
    {T : BigFppfOver B S hS} (y : T ⟶ U)
    (H : ∀ b, ∃ φ : AttractorPt actU N (openObj ((SCH).map y ⁻¹ᵁ V b)),
      φ.toPoint = openJ ((SCH).map y ⁻¹ᵁ V b) ≫ y) :
    ∃ φ : AttractorPt actU N T, φ.toPoint = y := by
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) (attractor actU N) :=
    isSheaf_attractor actU N _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  choose φs hφs using H
  have hsf : (Presieve.ofArrows _ (fun b => openJ ((SCH).map y ⁻¹ᵁ V b))).IsSheafFor (attractor actU N) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hsh _ (cover_mem hV y)
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf φs (by
    intro i j Z gi gj hij
    apply toPoint_injective_U hV
    change AttractorPt.toPoint (AttractorPt.baseChange gi (φs i)) =
      AttractorPt.toPoint (AttractorPt.baseChange gj (φs j))
    rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, hφs, hφs]
    change gi ≫ _ ≫ y = gj ≫ _ ≫ y
    rw [← Category.assoc, ← Category.assoc, hij])
  refine ⟨t, ?_⟩
  refine (BigFppfOver.isSheaf_of_type_yoneda_obj U _ (cover_mem hV y)).isSeparatedFor.ext fun W g hg => ?_
  obtain ⟨_, r, s', ⟨b⟩, rfl⟩ := hg
  have h1 : (AttractorPt.baseChange (openJ ((SCH).map y ⁻¹ᵁ V b)) t).toPoint = (φs b).toPoint :=
    congrArg AttractorPt.toPoint (ht b)
  have h2 : openJ ((SCH).map y ⁻¹ᵁ V b) ≫ t.toPoint = openJ ((SCH).map y ⁻¹ᵁ V b) ≫ y :=
    ((AttractorPt.toPoint_baseChange (openJ ((SCH).map y ⁻¹ᵁ V b)) t).symm.trans h1).trans (hφs b)
  change (r ≫ openJ _) ≫ t.toPoint = (r ≫ openJ _) ≫ y
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun q => r ≫ q) h2

/-- **Theorem 3.20 and Corollary 3.22 for an equivariant atlas**: `U^N` is a closed subscheme of `U`. -/
theorem exists_chartAttr (hV : IsAffineDecomposition actU V) (N : AddSubmonoid M) :
    Nonempty (ChartAttr actU N) := by
  have hone := fun b => exists_closed_att_piece hV b N
  choose Zs i hi hfx using hone
  let σ := fun a => Sigma.ι Zs a
  let f : ∐ Zs ⟶ (SCH).obj U := Sigma.desc fun a => i a ≫ iV (V a)
  have hσf : ∀ a, σ a ≫ f = i a ≫ iV (V a) := fun a => Sigma.ι_desc _ _
  have hmemV : ∀ a (q : Zs a), f (σ a q) ∈ V a := by
    intro a q
    have e : f (σ a q) = iV (V a) (i a q) := by
      rw [← Scheme.Hom.comp_apply, hσf, Scheme.Hom.comp_apply]
    rw [e]
    exact (i a q).2
  have hrange : ∀ a, Set.range (σ a) = SetLike.coe (f ⁻¹ᵁ V a) := by
    intro a
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact hmemV a q
    · intro hx
      obtain ⟨b, q, rfl⟩ := (sigmaOpenCover Zs).exists_eq x
      have hb : f (σ b q) ∈ V b := hmemV b q
      by_cases hab : a = b
      · subst hab
        exact ⟨q, rfl⟩
      · exact absurd (show f (σ b q) ∈ (V a ⊓ V b : ((SCH).obj U).Opens) from ⟨hx, hb⟩)
          (by rw [disjoint_iff.1 (hV.disjoint hab)]; simp)
  have hclosed : IsClosedImmersion f := by
    refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) (f := f) V
      hV.iSup_eq_top).2 fun a => ?_
    let e : Zs a ≅ (f ⁻¹ᵁ V a).toScheme := IsOpenImmersion.isoOfRangeEq (σ a) (f ⁻¹ᵁ V a).ι (by
      rw [hrange a, Scheme.Opens.range_ι])
    have he : e.hom ≫ (f ⁻¹ᵁ V a).ι = σ a := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hres : e.hom ≫ (f ∣_ V a) = i a := by
      apply (cancel_mono (V a).ι).1
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, he]
      exact hσf a
    let i' : Zs a ⟶ (V a).toScheme := i a
    have hi' : IsClosedImmersion i' := hi a
    have h2 : (f ∣_ V a) = e.inv ≫ i' := (Iso.eq_inv_comp e).2 hres
    rw [h2]
    infer_instance
  have hWc : B.Contains (∐ Zs) := Scheme.size_lt_of_isClosedImmersion f U.left.2
  let W : BigFppfOver B S hS := siteObject B S hS hWc (f ≫ structMap U)
  let j : W ⟶ U := Over.homMk (ObjectProperty.homMk f) rfl
  have hj : (SCH).map j = f := rfl
  have hiff : ∀ {T : BigFppfOver B S hS} (y : T ⟶ U), (∃ c : T ⟶ W, c ≫ j = y) ↔
      ∃ φ : AttractorPt actU N T, φ.toPoint = y := by
    intro T y
    constructor
    · rintro ⟨c, rfl⟩
      refine exists_att_of_cover hV _ fun a => ?_
      let O := (SCH).map (c ≫ j) ⁻¹ᵁ V a
      let P := openObj O
      let pJ : P ⟶ T := openJ O
      obtain ⟨t, ht⟩ := exists_lift_open (V := V a) (pJ ≫ c ≫ j) (fun p => by
        rw [Functor.map_comp]
        exact p.2)
      have hrng : Set.range ((SCH).map (pJ ≫ c)) ⊆ Set.range (σ a) := by
        rw [hrange a]
        rintro _ ⟨p, rfl⟩
        change f ((SCH).map (pJ ≫ c) p) ∈ V a
        have hk : (SCH).map (pJ ≫ c ≫ j) = (SCH).map (pJ ≫ c) ≫ f := by
          rw [← Category.assoc]
          exact Functor.map_comp _ _ _
        have e : f ((SCH).map (pJ ≫ c) p) = (SCH).map (pJ ≫ c ≫ j) p := by
          rw [hk, Scheme.Hom.comp_apply]
        rw [e, ← ht, Functor.map_comp, Scheme.Hom.comp_apply]
        exact ((SCH).map t p).2
      let z := IsOpenImmersion.lift (σ a) ((SCH).map (pJ ≫ c)) hrng
      have hz : z ≫ σ a = (SCH).map (pJ ≫ c) := IsOpenImmersion.lift_fac _ _ _
      have hzi : z ≫ i a = (SCH).map t := by
        apply (cancel_mono (iV (V a))).1
        rw [Category.assoc, ← hσf a, ← Category.assoc, hz, ← hj, ← Functor.map_comp, Category.assoc,
          ← ht, Functor.map_comp]
      obtain ⟨φ, hφ⟩ := (hfx a t).1 ⟨z, hzi⟩
      exact ⟨φ, hφ.trans ht⟩
    · rintro ⟨φ, rfl⟩
      let O : A → ((SCH).obj T).Opens := fun a => (SCH).map φ.toPoint ⁻¹ᵁ V a
      have hO : TopologicalSpace.IsOpenCover O := by
        change iSup O = ⊤
        rw [show iSup O = (SCH).map φ.toPoint ⁻¹ᵁ iSup V from (Scheme.Hom.preimage_iSup _ _).symm,
          hV.iSup_eq_top]
        rfl
      have hlift : ∀ a, ∃ z : (O a).toScheme ⟶ ∐ Zs, z ≫ f = (O a).ι ≫ (SCH).map φ.toPoint := by
        intro a
        let P := openObj (O a)
        let pJ : P ⟶ T := openJ (O a)
        obtain ⟨t, ht⟩ := exists_lift_open (V := V a) (pJ ≫ φ.toPoint) (fun p => by
          rw [Functor.map_comp]
          exact p.2)
        obtain ⟨z, hz⟩ := (hfx a t).2 ⟨AttractorPt.baseChange pJ φ, by
          rw [ht]; exact AttractorPt.toPoint_baseChange _ _⟩
        have hmap := congrArg (SCH).map ht
        rw [Functor.map_comp, Functor.map_comp] at hmap
        refine ⟨z ≫ σ a, (Category.assoc _ _ _).trans ?_⟩
        refine (congrArg (fun q => z ≫ q) (hσf a)).trans ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (fun q => q ≫ iV (V a)) hz).trans ?_
        exact hmap
      choose z hz using hlift
      let 𝒰 := ((SCH).obj T).openCoverOfIsOpenCover O hO
      have : Mono f := inferInstance
      let c₀ : (SCH).obj T ⟶ ∐ Zs := 𝒰.glueMorphisms z (fun a b => by
        apply (cancel_mono f).1
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (fun q => pullback.fst (𝒰.f a) (𝒰.f b) ≫ q) (hz a)).trans ?_
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        refine Eq.trans ?_ (congrArg (fun q => pullback.snd (𝒰.f a) (𝒰.f b) ≫ q) (hz b)).symm
        refine (Category.assoc _ _ _).symm.trans ?_
        refine Eq.trans ?_ (Category.assoc _ _ _)
        exact congrArg (fun q => q ≫ (SCH).map φ.toPoint) pullback.condition)
      have hc₀ : c₀ ≫ f = (SCH).map φ.toPoint := by
        refine Scheme.Cover.hom_ext 𝒰 _ _ fun a => ?_
        refine (Category.assoc _ _ _).symm.trans ?_
        exact (congrArg (fun q => q ≫ f) (Scheme.Cover.ι_glueMorphisms 𝒰 z _ a)).trans (hz a)
      let c : T ⟶ W := Over.homMk (ObjectProperty.homMk c₀) (by
        apply B.inclusion.map_injective
        have hw : (SCH).map φ.toPoint ≫ structMap U = structMap T :=
          congrArg B.inclusion.map (Over.w φ.toPoint)
        refine Eq.trans ?_ hw
        rw [← hc₀]
        exact (Category.assoc _ _ _).symm)
      refine ⟨c, ?_⟩
      apply (SCH).map_injective
      rw [Functor.map_comp]
      exact hc₀
  have hmono : Mono j := by
    have : Mono f := inferInstance
    refine ⟨fun {T} a b h => (SCH).map_injective ?_⟩
    apply (cancel_mono f).1
    rw [← hj, ← Functor.map_comp, ← Functor.map_comp, h]
  let toAtt : ∀ T, (T ⟶ W) → AttractorPt actU N T := fun T c => ((hiff (c ≫ j)).1 ⟨c, rfl⟩).choose
  have htoAtt : ∀ T (c : T ⟶ W), (toAtt T c).toPoint = c ≫ j :=
    fun T c => ((hiff (c ≫ j)).1 ⟨c, rfl⟩).choose_spec
  have hbij : ∀ T, Function.Bijective (toAtt T) := by
    intro T
    refine ⟨fun c c' h => ?_, fun φ => ?_⟩
    · apply (cancel_mono j).1
      rw [← htoAtt, ← htoAtt, h]
    · obtain ⟨c, hc⟩ := (hiff φ.toPoint).2 ⟨φ, rfl⟩
      refine ⟨c, toPoint_injective_U hV ?_⟩
      rw [htoAtt, hc]
  refine ⟨⟨W, j, ⟨fun T => Equiv.ofBijective (toAtt T) (hbij T), fun {T T'} s z => ?_⟩, hclosed,
    fun T y => htoAtt T y⟩⟩
  apply toPoint_injective_U hV
  refine (htoAtt T' _).trans ?_
  rw [AttractorPt.toPoint_baseChange]
  change (s ≫ z) ≫ j = s ≫ (toAtt T z).toPoint
  rw [htoAtt, Category.assoc]

end Glue

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Face

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {A : Type u} {V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}

lemma toPoint_ofFace_mem_iff (hV : IsAffineDecomposition actU V) (b : A) {Q N : AddSubmonoid M}
    (hQ : IsFace Q N) {T : BigFppfOver B S hS} (u : AttractorPt actU N T) (p : (SCH).obj T) :
    (SCH).map (AttractorPt.ofFace hQ u).toPoint p ∈ V b ↔ (SCH).map u.toPoint p ∈ V b :=
  app_mem_iff hV b u (𝟙 T) _ p

lemma push_pieceJ_injective {W : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (hst : IsStableOpen actU W) {N : AddSubmonoid M} {T : BigFppfOver B S hS}
    {a b : AttractorPt (pieceAct hst) N T} (h : AttractorPt.push (pieceJ hst) a = AttractorPt.push (pieceJ hst) b) :
    a = b := by
  have hm := mono_openJ (V := W)
  refine AttractorPt.ext ?_
  funext T' t c
  apply (cancel_mono (openJ W)).1
  exact congrArg (fun φ => AttractorPt.app φ t c) h

/-- **Proposition 5.1 for an equivariant atlas** from the case of a `D(M)`-stable `S`-affine piece. -/
theorem isFaceCartesian_of_pieces (hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
    (hV : IsAffineDecomposition actU V) (f : EquivariantHom actU actX) {Q N : AddSubmonoid M}
    (hQ : IsFace Q N)
    (H : ∀ b, IsFaceCartesian ((pieceJ (hV.stable b)).comp f) hQ) :
    IsFaceCartesian f hQ := by
  have hshU : Presieve.IsSheaf (BigFppfOver.topology B S hS) (attractor actU N) :=
    isSheaf_attractor actU N _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  have hshUQ : Presieve.IsSheaf (BigFppfOver.topology B S hS) (attractor actU Q) :=
    isSheaf_attractor actU Q _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  have hshX : Presieve.IsSheaf (BigFppfOver.topology B S hS) (attractor actX N) :=
    isSheaf_attractor actX N _ hX
  have hinj : ∀ (T : BigFppfOver B S hS) (u u' : AttractorPt actU N T), AttractorPt.push f u = AttractorPt.push f u' →
      AttractorPt.ofFace hQ u = AttractorPt.ofFace hQ u' → u = u' := by
    intro T u u' h₁ h₂
    let y := (AttractorPt.ofFace hQ u).toPoint
    refine (hshU _ (cover_mem hV y)).isSeparatedFor.ext fun W g hg => ?_
    obtain ⟨_, r, s', ⟨b⟩, rfl⟩ := hg
    let J₀ := openJ ((SCH).map y ⁻¹ᵁ V b)
    suffices e : AttractorPt.baseChange J₀ u = AttractorPt.baseChange J₀ u' from
      congrArg (AttractorPt.baseChange r) e
    have hp : ∀ (v : AttractorPt actU N T), AttractorPt.ofFace hQ v = AttractorPt.ofFace hQ u →
        ∀ q, (SCH).map (AttractorPt.baseChange J₀ v).toPoint q ∈ V b := by
      intro v hv q
      rw [AttractorPt.toPoint_baseChange]
      change (SCH).map (J₀ ≫ v.toPoint) q ∈ V b
      rw [Functor.map_comp]
      refine (toPoint_ofFace_mem_iff hV b hQ v _).1 ?_
      rw [hv]
      exact q.2
    obtain ⟨a, ha⟩ := exists_piece_lift hV b (AttractorPt.baseChange J₀ u) (hp u rfl)
    obtain ⟨a', ha'⟩ := exists_piece_lift hV b (AttractorPt.baseChange J₀ u') (hp u' h₂.symm)
    rw [← ha, ← ha']
    congr 1
    refine (H b _).1 (Subtype.ext (Prod.ext ?_ ?_))
    · change AttractorPt.push f (AttractorPt.push (pieceJ (hV.stable b)) a) = AttractorPt.push f (AttractorPt.push (pieceJ (hV.stable b)) a')
      rw [ha, ha']
      exact congrArg (AttractorPt.baseChange J₀) h₁
    · apply push_pieceJ_injective (hV.stable b)
      change AttractorPt.ofFace hQ (AttractorPt.push (pieceJ (hV.stable b)) a) = AttractorPt.ofFace hQ (AttractorPt.push (pieceJ (hV.stable b)) a')
      rw [ha, ha']
      exact congrArg (AttractorPt.baseChange J₀) h₂
  intro T
  refine ⟨fun u u' h => hinj T u u' (congrArg (fun p => p.1.1) h) (congrArg (fun p => p.1.2) h), ?_⟩
  rintro ⟨⟨x, w⟩, hxw⟩
  change AttractorPt.ofFace hQ x = AttractorPt.push f w at hxw
  have hloc : ∀ b, ∃ u : AttractorPt actU N (openObj ((SCH).map w.toPoint ⁻¹ᵁ V b)),
      AttractorPt.push f u = AttractorPt.baseChange (openJ _) x ∧
      AttractorPt.ofFace hQ u = AttractorPt.baseChange (openJ _) w := by
    intro b
    let J₀ := openJ ((SCH).map w.toPoint ⁻¹ᵁ V b)
    obtain ⟨w', hw'⟩ := exists_piece_lift hV b (AttractorPt.baseChange J₀ w) (fun q => by
      rw [AttractorPt.toPoint_baseChange]
      change (SCH).map (J₀ ≫ w.toPoint) q ∈ V b
      rw [Functor.map_comp]
      exact q.2)
    obtain ⟨u', hu'⟩ := (H b _).2 ⟨(AttractorPt.baseChange J₀ x, w'), by
      change AttractorPt.ofFace hQ (AttractorPt.baseChange J₀ x) =
        AttractorPt.push f (AttractorPt.push (pieceJ (hV.stable b)) w')
      rw [hw']
      exact congrArg (AttractorPt.baseChange J₀) hxw⟩
    have h₁ : AttractorPt.push ((pieceJ (hV.stable b)).comp f) u' = AttractorPt.baseChange J₀ x :=
      congrArg (fun p => p.1.1) hu'
    have h₂ : AttractorPt.ofFace hQ u' = w' := congrArg (fun p => p.1.2) hu'
    refine ⟨AttractorPt.push (pieceJ (hV.stable b)) u', h₁, ?_⟩
    rw [← hw', ← h₂]
    rfl
  choose u hu₁ hu₂ using hloc
  have hsf : (Presieve.ofArrows _ (fun b => openJ ((SCH).map w.toPoint ⁻¹ᵁ V b))).IsSheafFor
      (attractor actU N) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hshU _ (cover_mem hV w.toPoint)
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf u (by
    intro i j Z gi gj hij
    apply hinj Z
    · change AttractorPt.baseChange gi (AttractorPt.push f (u i)) =
        AttractorPt.baseChange gj (AttractorPt.push f (u j))
      rw [hu₁, hu₁, ← bc83_comp, ← bc83_comp, hij]
    · change AttractorPt.baseChange gi (AttractorPt.ofFace hQ (u i)) =
        AttractorPt.baseChange gj (AttractorPt.ofFace hQ (u j))
      rw [hu₂, hu₂, ← bc83_comp, ← bc83_comp, hij])
  refine ⟨t, Subtype.ext (Prod.ext ?_ ?_)⟩
  · refine (hshX _ (cover_mem hV w.toPoint)).isSeparatedFor.ext fun W g hg => ?_
    obtain ⟨_, r, s', ⟨b⟩, rfl⟩ := hg
    have e : AttractorPt.baseChange (openJ _) (AttractorPt.push f t) =
        AttractorPt.baseChange (openJ ((SCH).map w.toPoint ⁻¹ᵁ V b)) x :=
      (congrArg (AttractorPt.push f) (ht b)).trans (hu₁ b)
    exact congrArg (AttractorPt.baseChange r) e
  · refine (hshUQ _ (cover_mem hV w.toPoint)).isSeparatedFor.ext fun W g hg => ?_
    obtain ⟨_, r, s', ⟨b⟩, rfl⟩ := hg
    have e : AttractorPt.baseChange (openJ _) (AttractorPt.ofFace hQ t) =
        AttractorPt.baseChange (openJ ((SCH).map w.toPoint ⁻¹ᵁ V b)) w :=
      (congrArg (AttractorPt.ofFace hQ) (ht b)).trans (hu₂ b)
    exact congrArg (AttractorPt.baseChange r) e

/-- The composite of the inclusion of a piece with an étale atlas is étale. -/
lemma isEtale_piece_comp {W : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    {g : yoneda.obj U ⟶ X}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (SCH)) g)) :
    Space.IsEtale B S hS (yoneda.map (openJ W) ≫ g) := by
  intro T φ hφ
  have hJ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (openJ W)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 (inferInstanceAs (Etale (iV W)))
  rw [← Category.assoc]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.comp_mem _ _ _ hφ hJ) he

end Face

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Main

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {A : Type u} {V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}

omit [AddGroup.FG M] in
/-- A closed subscheme of `U` is `S`-affine over a piece. -/
lemma isAffineHom_preimage_piece (hV : IsAffineDecomposition actU V) (b : A) {W : BigFppfOver B S hS}
    (j : W ⟶ U) (hj : IsClosedImmersion ((SCH).map j)) :
    IsAffineHom (((SCH).map j ⁻¹ᵁ V b).ι ≫ structMap W) := by
  have hA := hV.isAffineHom b
  have e : ((SCH).map j ⁻¹ᵁ V b).ι ≫ structMap W =
      ((SCH).map j ∣_ V b) ≫ (V b).ι ≫ structMap U := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    congr 1
    exact (congrArg B.inclusion.map (Over.w j)).symm
  rw [e]
  infer_instance

/-- The natural map `U^N → U^{N^×}` is affine (Theorem 3.20, with the pieces of the atlas not mixing). -/
theorem isAffineHom_limit (hV : IsAffineDecomposition actU V) (N : AddSubmonoid M) (rN : ChartAttr actU N)
    (Wz : BigFppfOver B S hS) (jz : Wz ⟶ U) (l : rN.W ⟶ Wz)
    (hjz : IsClosedImmersion ((SCH).map jz))
    (hlv : ∀ {T : BigFppfOver B S hS} (v : T ⟶ rN.W),
        v ≫ l ≫ jz = (AttractorPt.ofFace (isFace_unitsSub N) (rN.r.equiv T v)).toPoint) :
    IsAffineHom ((SCH).map l) := by
  have hsup : (⨆ b, (SCH).map jz ⁻¹ᵁ V b) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV.iSup_eq_top]
    rfl
  have _hzl : IsZariskiLocalAtTarget (@AlgebraicGeometry.IsAffineHom.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsAffineHom) (f := (SCH).map l) _ hsup).2
    fun b => ?_
  have h1 := isAffineHom_preimage_piece hV b jz hjz
  have h2 := isAffineHom_preimage_piece hV b rN.j rN.closed
  have hO : (SCH).map l ⁻¹ᵁ ((SCH).map jz ⁻¹ᵁ V b) = (SCH).map rN.j ⁻¹ᵁ V b := by
    refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
    have e1 := hlv (𝟙 rN.W)
    rw [Category.id_comp] at e1
    have e2 := rN.toPoint_r rN.W (𝟙 _)
    rw [Category.id_comp] at e2
    have e3 := toPoint_ofFace_mem_iff hV b (isFace_unitsSub N) (rN.r.equiv rN.W (𝟙 _)) x
    rw [← e1, e2, Functor.map_comp] at e3
    exact e3
  have h3 : IsAffineHom (((SCH).map l ⁻¹ᵁ ((SCH).map jz ⁻¹ᵁ V b)).ι ≫ structMap rN.W) := by
    rw [hO]
    exact h2
  have h4 : (((SCH).map l) ∣_ ((SCH).map jz ⁻¹ᵁ V b)) ≫ ((SCH).map jz ⁻¹ᵁ V b).ι ≫ structMap Wz =
      ((SCH).map l ⁻¹ᵁ ((SCH).map jz ⁻¹ᵁ V b)).ι ≫ structMap rN.W := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    congr 1
    exact congrArg B.inclusion.map (Over.w l)
  have h5 : IsAffineHom ((((SCH).map l) ∣_ ((SCH).map jz ⁻¹ᵁ V b)) ≫
      ((SCH).map jz ⁻¹ᵁ V b).ι ≫ structMap Wz) := by
    rw [h4]; exact h3
  exact .of_comp _ (((SCH).map jz ⁻¹ᵁ V b).ι ≫ structMap Wz)

/-- **Theorem 8.3, representability and (i).** Let `M` be a finitely generated abelian group, `N ⊆ M` a
magnet, `X` an algebraic space over `S` with an action of `D(M)_S` and with a `N^×`-FPR atlas. If `X`
is separated, and `N` is finitely generated or `X` is limit preserving, then `X^N` is an algebraic space
and `X^N → X^{N^×}` is affine; moreover `X^{N^×}` is a closed subspace of `X`. -/
theorem thm83_repr (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (N : AddSubmonoid M)
    (hat : ExistsZFPRAtlas actX (unitsSub N)) (hb : N.FG ∨ IsLimitPreserving X) :
    Nonempty (Thm83Repr actX N) := by
  obtain ⟨U, actU, g, hg⟩ := hat
  obtain ⟨A, V, hV⟩ := hg.atlas.decomposition
  let f : EquivariantHom actU actX := ⟨g, fun {T} h x => hg.atlas.equivariant h x⟩
  obtain ⟨rN⟩ := exists_chartAttr hV N
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  refine thm83_core hX N f hg rN ?_ ?_
  · refine isFaceCartesian_of_pieces hsh hV f _ fun b => ?_
    have hA : IsAffineHom (openObj (V b)).hom.hom := hV.isAffineHom b
    have he : Space.IsEtale B S hS ((pieceJ (hV.stable b)).comp f).hom :=
      isEtale_piece_comp hg.atlas.etale
    rcases hb with hN | hl
    · exact isFaceCartesian_of_fg hX hsep _ he _ hN
    · exact isFaceCartesian_of_separated hX hsep hl _ he _
  · intro Wz jz l hjz _ hlv
    exact isAffineHom_limit hV N rN Wz jz l hjz hlv

end Main

end AlgMag


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Props

variable {A Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A representable morphism whose base changes are separated is separated. -/
lemma isSeparated_of_presheaf {P : MorphismProperty Scheme.{u}}
    (hP : ∀ {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂), P g → AlgebraicGeometry.IsSeparated g)
    (hA : IsAlgebraicSpace B S hS A) {f : A ⟶ Y}
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage P (SCH))) f) :
    Space.IsSeparated B S hS f := by
  refine (Space.isSeparated_iff_forall_pullback B S hS hA f).2 fun T g => ?_
  let R := hf.rep
  have hpb := R.isPullback g
  have hs : AlgebraicGeometry.IsSeparated ((SCH).map (R.snd g)) := hP _ (hf.property_snd g)
  have hy := (Space.isSeparated_yoneda_map_iff B S hS (R.snd g)).2 hs
  have hiso : IsPullback hpb.isoPullback.hom (yoneda.map (R.snd g)) (pullback.snd f g) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_hom_snd]⟩
  have e : pullback.snd f g = hpb.isoPullback.inv ≫ yoneda.map (R.snd g) := by
    rw [IsPullback.isoPullback_inv_snd]
  rw [e]
  exact Space.isSeparated_comp B S hS _ _ (Space.isSeparated_of_isIso B S hS _) hy

/-- A morphism whose base changes are quasi-compact pulls back the quasi-compactness of the target. -/
lemma isQuasiCompactSpace_of_presheaf {P : MorphismProperty Scheme.{u}}
    (hP : ∀ {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂), P g → QuasiCompact g) {f : A ⟶ Y}
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage P (SCH))) f)
    (hY : Space.IsQuasiCompactSpace B S hS Y) : Space.IsQuasiCompactSpace B S hS A := by
  obtain ⟨a, φ, hc, hs, hE⟩ := hY
  have he := Space.presheaf_etale_of_isEtale B S hS hE
  let R := hf.rep
  have hpb := R.isPullback φ
  have hq : QuasiCompact ((SCH).map (R.snd φ)) := hP _ (hf.property_snd φ)
  refine ⟨R.pullback φ, R.fst φ, ?_, ?_, ?_⟩
  · exact QuasiCompact.compactSpace_of_compactSpace ((SCH).map (R.snd φ))
  · exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb.flip hs
  · exact Space.isEtale_of_presheaf_etale B S hS
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb.flip he)

end Props

section Thm

open Space

attribute [local instance] countable_of_fg83

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}

/-- **Theorem 8.3**, for `M` finitely generated. Let `N ⊆ M` be a magnet, `X` an algebraic space over
`S` with an action of `D(M)_S` and a `N^×`-FPR atlas. Assume `X` separated, and `N` finitely generated
or `X` limit preserving. Then `X^N` is represented by an algebraic space `r.P`, and:
(i) `X^N → X^{N^×}` is affine (`r.affine_c`, with `X^{N^×}` closed in `X`);
(ii) `X^N/S` is quasi-separated; (iii) `X^N/S` is separated;
(v) if `X/S` is quasi-compact then `X^N/S` is quasi-compact. -/
theorem thm83 (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (N : AddSubmonoid M)
    (hat : ExistsZFPRAtlas actX (unitsSub N)) (hb : N.FG ∨ IsLimitPreserving X) :
    ∃ r : Thm83Repr actX N,
      Space.IsQuasiSeparated B S hS (toBase r.P) ∧
      IsSeparatedOver r.P ∧
      (Space.IsQuasiCompactSpace B S hS X → Space.IsQuasiCompactSpace B S hS r.P) := by
  obtain ⟨r⟩ := thm83_repr hX hsep N hat hb
  have hc : Space.IsSeparated B S hS r.c :=
    isSeparated_of_presheaf (P := @AlgebraicGeometry.IsAffineHom) (fun g _ => inferInstance) r.algP r.affine_c
  have hi : Space.IsSeparated B S hS r.i :=
    isSeparated_of_presheaf (P := @IsClosedImmersion) (fun g _ => inferInstance) r.algY r.closed_i
  have hs : IsSeparatedOver r.P := by
    have e : toBase r.P = r.c ≫ r.i ≫ toBase X := by
      ext T x
      exact Over.mkIdTerminal.hom_ext _ _
    change Space.IsSeparated B S hS (toBase r.P)
    rw [e]
    exact Space.isSeparated_comp B S hS _ _ hc (Space.isSeparated_comp B S hS _ _ hi hsep)
  refine ⟨r, Space.isQuasiSeparated_of_isSeparated B S hS hs, hs, fun hq => ?_⟩
  exact isQuasiCompactSpace_of_presheaf (P := @AlgebraicGeometry.IsAffineHom) (fun g _ => inferInstance) r.affine_c
    (isQuasiCompactSpace_of_presheaf (P := @IsClosedImmersion) (fun g _ => inferInstance) r.closed_i hq)

/-- **Theorem 8.3 (vii).** If `X` is a scheme, under the same hypotheses, then `X^N` is a scheme. -/
theorem thm83_vii {T₀ : BigFppfOver B S hS} {act : AAction (fppfO B S hS) M (yoneda.obj T₀)}
    (hsep : IsSeparatedOver (yoneda.obj T₀)) (N : AddSubmonoid M)
    (hat : ExistsZFPRAtlas act (unitsSub N)) (hb : N.FG ∨ IsLimitPreserving (yoneda.obj T₀)) :
    ∃ W : BigFppfOver B S hS, Nonempty (RepresentsAttractor act N (yoneda.obj W)) := by
  obtain ⟨r⟩ := thm83_repr (isAlgebraicSpace_yoneda B S hS T₀) hsep N hat hb
  let R₁ := r.closed_i.rep
  have hp₁ := R₁.isPullback (𝟙 (yoneda.obj T₀))
  have hiso₁ : IsIso (R₁.fst (𝟙 (yoneda.obj T₀))) := hp₁.isIso_fst_of_isIso
  let R₂ := r.affine_c.rep
  have hp₂ := R₂.isPullback (R₁.fst (𝟙 (yoneda.obj T₀)))
  have hiso₂ : IsIso (R₂.fst (R₁.fst (𝟙 (yoneda.obj T₀)))) := hp₂.isIso_fst_of_isIso
  let φ := R₂.fst (R₁.fst (𝟙 (yoneda.obj T₀)))
  have hbij : ∀ T' : (BigFppfOver B S hS)ᵒᵖ, Function.Bijective (φ.app T') := fun T' =>
    (isIso_iff_bijective _).1 inferInstance
  refine ⟨_, ⟨fun T' => (Equiv.ofBijective _ (hbij (op T'))).trans (r.rP.equiv T'), fun s z => ?_⟩⟩
  refine (congrArg (r.rP.equiv _) ?_).trans (r.rP.naturality s _)
  exact NatTrans.naturality_apply φ s.op z

/-- **Proposition 12.1**, the representability assumption discharged by Theorem 8.3: under a `N^×`-FPR
atlas, with `N` finitely generated and `X` separated, `X^N → X^{N^×}` between algebraic spaces induces a
bijection on connected components, for any topologies as in `AlgMag.bijective_connectedComponents_repFace`. -/
theorem prop121_of_atlas (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) {N : AddSubmonoid M}
    (hN : N.FG) (hat : ExistsZFPRAtlas actX (unitsSub N)) :
    ∃ r : Thm83Repr actX N,
      ∀ (τN : TopologicalSpace (points B S hS r.P)) (τL : TopologicalSpace (points B S hS r.Y))
        (_ : SchemeContinuous τN)
        (hr : Continuous (pointsMap B S hS _ (repFace r.rP r.rY (isFace_unitsSub N))))
        (_ : Continuous (pointsMap B S hS _ (repMagnet r.rP r.rY (isFace_unitsSub N).le))),
        Function.Bijective hr.connectedComponentsMap := by
  obtain ⟨r⟩ := thm83_repr hX hsep N hat (Or.inl hN)
  exact ⟨r, fun τN τL hτ hr hi =>
    bijective_connectedComponents_repFace (isFace_unitsSub N) hN r.rP r.rY τN τL hτ hr hi⟩

/-- **Proposition 14.4**, the representability assumption discharged by Theorem 8.3: if each term of the
presentation is separated with a `N^×`-FPR atlas, and `N` is finitely generated or each term is limit
preserving, the attractor functor of the ind-algebraic space is an ind-algebraic space. -/
theorem prop144_of_atlas {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
    {Xi : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P Xi}
    (a : IndAction M p) (N : AddSubmonoid M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i)) (hsep : ∀ i, IsSeparatedOver (p.obj i))
    (hat : ∀ i, ExistsZFPRAtlas (a.act i) (unitsSub N))
    (hb : ∀ i, N.FG ∨ IsLimitPreserving (p.obj i)) :
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) := by
  let r := fun i => (thm83_repr (hX i) (hsep i) N (hat i) (hb i)).some
  exact isIndAlgebraicSpace_attractor a N (fun i => (r i).rP) (fun i => (r i).algP)

end Thm

end AlgMag

#print axioms AlgMag.thm83_repr
#print axioms AlgMag.thm83
#print axioms AlgMag.thm83_vii
#print axioms AlgMag.exists_chartAttr
#print axioms AlgMag.app_mem_iff
#print axioms AlgMag.isFaceCartesian_of_pieces
#print axioms AlgMag.prop121_of_atlas
#print axioms AlgMag.prop144_of_atlas
