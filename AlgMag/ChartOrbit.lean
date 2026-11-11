/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartBridge
import AlgMag.ChartIdealPow
import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent

/-!
# The orbit and its thickenings (chart-lemma proof, §§1–2)

* `AlgMag.ChartMain.AffineTower`: a tower of affine `D(M)`-equivariant thickenings of the orbit.
* `AlgMag.ChartMain.AffineTower.toOrbitTower`, `toThickeningSystem`: the §2 inverse system.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

namespace AlgMag.ChartMain

section Thick

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A closed immersion of presheaves on the site. -/
abbrev ClosedP (o : P ⟶ X) : Prop :=
  MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) o

/-- The kernel of a base change of a closed immersion, for any pullback square. -/
lemma ker_eq_comap_of_isPullback {Z' W Z Y : Scheme.{u}} {i' : Z' ⟶ W} {m : Z' ⟶ Z} {f : W ⟶ Y}
    {i : Z ⟶ Y} [IsClosedImmersion i] (sq : IsPullback i' m f i) :
    i'.ker = i.ker.comap f := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← sq.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

variable {o : P ⟶ X} (ho : ClosedP o)

/-- The ideal sheaf of `T ×_X O` in `T`, for `t : T → X`. -/
noncomputable def idealOf {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ X) :
    ((SCH).obj T).IdealSheafData :=
  ((SCH).map (ho.rep.snd t)).ker

lemma snd_closed {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ X) :
    IsClosedImmersion ((SCH).map (ho.rep.snd t)) :=
  ho.property_snd t

/-- The ideal of `T ×_X O` is compatible with base change. -/
theorem idealOf_comp {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (t : yoneda.obj T ⟶ X) :
    idealOf ho (yoneda.map g ≫ t) = (idealOf ho t).comap ((SCH).map g) := by
  have s1 := ho.rep.isPullback t
  have s2 := ho.rep.isPullback (yoneda.map g ≫ t)
  have hc : (ho.rep.fst (yoneda.map g ≫ t)) ≫ o =
      yoneda.map (ho.rep.snd (yoneda.map g ≫ t) ≫ g) ≫ t := by
    rw [s2.w, Functor.map_comp, Category.assoc]
  let m : ho.rep.pullback (yoneda.map g ≫ t) ⟶ ho.rep.pullback t :=
    ho.rep.lift (ho.rep.fst (yoneda.map g ≫ t)) (ho.rep.snd (yoneda.map g ≫ t) ≫ g) hc
  have hm : m ≫ ho.rep.snd t = ho.rep.snd (yoneda.map g ≫ t) ≫ g := ho.rep.lift_snd _ _ _
  have hm' : yoneda.map m ≫ ho.rep.fst t = ho.rep.fst (yoneda.map g ≫ t) := ho.rep.lift_fst _ _ _
  have sq : IsPullback (yoneda.map m) (yoneda.map (ho.rep.snd (yoneda.map g ≫ t)))
      (yoneda.map (ho.rep.snd t)) (yoneda.map g) := by
    refine IsPullback.of_right (h₁₂ := ho.rep.fst t) (v₁₃ := o) (h₂₂ := t) ?_ ?_ s1
    · rw [hm']; exact s2
    · rw [← Functor.map_comp, ← Functor.map_comp, hm]
  have sq' : IsPullback m (ho.rep.snd (yoneda.map g ≫ t)) (ho.rep.snd t) g :=
    IsPullback.of_map yoneda (by rw [hm]) sq
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have := snd_closed ho t
  have sq'' := sq'.map (SCH)
  exact ker_eq_comap_of_isPullback sq''.flip

/-- `ℐ^{n+1}` on the chart, as a subobject: the chart of `X_n`. -/
noncomputable def chartZ {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X) (n : ℕ) :
    Subobject ((SCH).obj U) :=
  Subobject.mk ((idealOf ho φ) ^ (n + 1)).subschemeι

lemma pullback_mk_subscheme {A W : Scheme.{u}} (f : A ⟶ W) (I : W.IdealSheafData) :
    (Subobject.pullback f).obj (Subobject.mk I.subschemeι) =
      Subobject.mk (I.comap f).subschemeι := by
  refine Subobject.pullback_obj_mk (f' := (I.comapIso f).hom ≫ Limits.pullback.snd _ _) ?_
  have h := (IsPullback.of_hasPullback f I.subschemeι).flip
  refine IsPullback.of_iso h (I.comapIso f).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> try simp
  rw [Iso.eq_inv_comp, Scheme.IdealSheafData.comapIso_hom_snd]

/-- The chart of `X_n` is invariant under the relation `U ×_X U`. -/
theorem chartZ_invariant {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ) (n : ℕ) :
    Space.IsInvariantSubscheme B S hS hs (chartZ ho φ n) := by
  have hw : yoneda.map (Space.atlasRelationTarget B S hS hs) ≫ φ =
      yoneda.map (Space.atlasRelationSource B S hS hs) ≫ φ := by
    simpa using hs.rep.w φ
  have e := (idealOf_comp ho (Space.atlasRelationTarget B S hS hs) φ).symm.trans
    ((congrArg (idealOf ho) hw).trans (idealOf_comp ho (Space.atlasRelationSource B S hS hs) φ))
  dsimp only [Space.IsInvariantSubscheme]
  rw [chartZ, pullback_mk_subscheme, pullback_mk_subscheme, IdealPow.comap_pow,
    IdealPow.comap_pow, e]

/-- **§2**: `X_n`, the `n`-th thickening of `O` in `X`, as a subfunctor of `X`: the subspace cut out
by the invariant subscheme `V(ℐ^{n+1})` of a surjective étale chart. -/
noncomputable def thickening {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X) (n : ℕ) :
    Subfunctor X :=
  Space.invariantSubspace B S hS φ (chartZ ho φ n)

lemma mk_arrow_closed {A W : Scheme.{u}} (i : A ⟶ W) [Mono i] [IsClosedImmersion i] :
    IsClosedImmersion (Subobject.mk i).arrow := by
  have hr : MorphismProperty.RespectsIso (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have e : Arrow.mk (Subobject.mk i).arrow ≅ Arrow.mk i :=
    Arrow.isoMk (Subobject.underlyingIso i) (Iso.refl _) (by simp)
  exact (MorphismProperty.arrow_mk_iso_iff
    (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) e).2 inferInstance

lemma chartZ_arrow_closed {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X) (n : ℕ) :
    IsClosedImmersion (chartZ ho φ n).arrow :=
  mk_arrow_closed _

/-- **§2**: `X_n` is a closed subspace of `X`. -/
theorem isClosedSubspace_thickening (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ) (n : ℕ) :
    Space.IsClosedSubspace B S hS (thickening ho φ n) := by
  have hci := chartZ_arrow_closed ho φ n
  have him : AlgebraicGeometry.IsImmersion (chartZ ho φ n).arrow := inferInstance
  have hinv := chartZ_invariant ho hs n
  have hA := Space.isAlgebraicSpace_and_presheaf_invariantSubspace B S hS hs he
    (Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hX _ him hci hinv
  have hloc := Stacks.Descent.isClosedImmersion_isLocalAtTarget_fpqc
  exact ⟨hA.1, Space.presheaf_invariantSubspace_of_isLocalAtTarget B S hS hs he _ him hci hinv
    hA.2.rep⟩

end Thick

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- §2: the affine objects `X_n`, equivariant closed immersions `X_n → X_{n+1}`, and the ideal
conditions of the thickenings of the orbit `X_0 = O`. -/
structure AffineTower (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : Type u) [AddCommGroup M] [AddMonoid.FG M] where
  /-- `X_n` -/
  U : ℕ → BigFppfOver B S hS
  aff : ∀ n, IsAffine ((BigFppfOver.toScheme B S hS).obj (U n))
  /-- the action on `X_n` -/
  act : ∀ n, AAction (fppfO B S hS) M (yoneda.obj (U n))
  /-- `X_n → X_{n+1}` -/
  j : ∀ n, U n ⟶ U (n + 1)
  closed : ∀ n, IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (j n))
  equivariant : ∀ n, IsEquivariant (act n) (act (n + 1)) (yoneda.map (j n))
  /-- `O → X_n` -/
  incl : ∀ n, U 0 ⟶ U n
  incl_zero : incl 0 = 𝟙 _
  incl_succ : ∀ n, incl (n + 1) = incl n ≫ j n
  /-- `I_n^{n+1} = 0`, for `I_n` the ideal of `O` in `X_n`. -/
  nil : ∀ n, RingHom.ker ((BigFppfOver.toScheme B S hS).map (incl n)).appTop.hom ^ (n + 1) = ⊥
  /-- `X_n` is the `n`-th thickening of `O` in `X_{n+1}`. -/
  ker_j : ∀ n, RingHom.ker ((BigFppfOver.toScheme B S hS).map (j n)).appTop.hom =
    RingHom.ker ((BigFppfOver.toScheme B S hS).map (incl (n + 1))).appTop.hom ^ (n + 1)
  /-- `I/I²` is finite. -/
  I_fg : (RingHom.ker ((BigFppfOver.toScheme B S hS).map (incl 1)).appTop.hom).FG

namespace AffineTower

variable (Y : AffineTower B S hS M)

instance (n : ℕ) : IsAffine ((SCH).obj (Y.U n)) := Y.aff n

/-- **§2**: the rings `O_n = Γ(X_n)` of an affine tower, graded by the action. -/
noncomputable def toOrbitTower : OrbitTower M where
  O n := RT (Y.U n)
  𝒜 n := homog (Y.act n)
  gr n := gradedRingOfAction (Y.act n)
  π n := ((SCH).map (Y.j n)).appTop.hom
  π_mem n d y hy := map_mem_homog (Y.act n) (Y.act (n + 1)) (Y.equivariant n) hy
  π_surj n := by
    have := Y.closed n
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map (Y.j n))).2
  toO n := ((SCH).map (Y.incl n)).appTop.hom
  toO_zero := by
    rw [Y.incl_zero]; simp; rfl
  toO_succ n := by
    rw [Y.incl_succ, Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
  nil := Y.nil
  ker_π := Y.ker_j
  I_fg := Y.I_fg

/-- **§2**: the `ThickeningSystem` of an affine tower. -/
noncomputable def toThickeningSystem : ChartGraded.ThickeningSystem M :=
  Y.toOrbitTower.toThickeningSystem

end AffineTower

end Tower

end AlgMag.ChartMain

#print axioms AlgMag.ChartMain.AffineTower.toThickeningSystem
#print axioms AlgMag.ChartMain.isClosedSubspace_thickening
