/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesLimitView
import AlgMag.SpacesLimitOrbit
import AlgMag.ChartAtlas
import AlgMag.ChartThm68
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputQuasiCompact

/-!
# A stable quasi-compact open over an affine open of the base

Mayeux, *Algebraic Magnetism*, proofs of Theorems A.1 and A.2: "the assumptions and conclusion being
local over `S`, we may assume that `S` is affine ... We may replace `X` by one such orbit".

For `X` locally of finite presentation and quasi-separated over `S`, `W'` a stable quasi-compact open
lying over an affine open `O` of `S`:

* `restrictAct`, `ι_equivariant`: the action on `W'`.
* `openBase`, `toBase`, `toBase_invariant`: the object `A` of the site given by `O`, `p : W' ⟶ A`.
* `isFinitePresentation_toBase`, `isSeparated_toBase`.
* `zObj`, `viewBase`, `isFinitePresentation_viewBase`, `viewBase_invariant`, `isSeparated_viewBase`:
  the same over `Spec ℤ`.
* `isStronglyFPR_comp_mono`, `isStronglyFPR_mono_comp`, `isEtale_comp_ι`: going back to `X`.
* `exists_atlas_of_fp`: Theorem 6.8 (i) for `p : Y ⟶ A` of finite presentation, separated, invariant.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.LimThm

open LimAct LimOrbit LimView

attribute [local instance] Space.pointTopology

noncomputable section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The structure morphism of a presheaf, to `S` as an object of its own site. -/
def toT1 (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : X ⟶ yoneda.obj (T1 B S hS) :=
  (isTerminal_T1 B S hS).from X

lemma toT1_ext {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : Y ⟶ yoneda.obj (T1 B S hS)) : a = b :=
  (isTerminal_T1 B S hS).hom_ext a b

/-! ### (a) The restricted action -/

section Restrict

variable (act : AAction (fppfO B S hS) M X) {W : Subfunctor X}
  (hst : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (k : APt (fppfO B S hS) M T) (x : X.obj T),
    x ∈ W.obj T → act.smul k x ∈ W.obj T)

/-- **(a)** The action on a stable subfunctor. -/
def restrictAct : AAction (fppfO B S hS) M W.toFunctor where
  smul {T} k x := ⟨act.smul k x.1, hst T k x.1 x.2⟩
  one_smul {T} x := Subtype.ext (act.one_smul x.1)
  mul_smul {T} g h x := Subtype.ext (act.mul_smul g h x.1)
  map_smul {T T'} f k x := Subtype.ext (act.map_smul f k x.1)

lemma ι_equivariant : IsEquivariant (restrictAct act hst) act W.ι := fun _ _ => rfl

lemma ι_injective (T : (BigFppfOver B S hS)ᵒᵖ) : Function.Injective (W.ι.app T) :=
  fun _ _ h => Subtype.ext h

end Restrict

/-! ### (f) Going back to `X` -/

section Back

variable {U Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actU : AAction (fppfO B S hS) M U}
  {actY : AAction (fppfO B S hS) M Y} {actY' : AAction (fppfO B S hS) M Y'}

/-- Composition of equivariant morphisms. -/
lemma isEquivariant_comp {f : U ⟶ Y} {g : Y ⟶ Y'} (hf : IsEquivariant actU actY f)
    (hg : IsEquivariant actY actY' g) : IsEquivariant actU actY' (f ≫ g) := by
  intro T h x
  change g.app T (f.app T (actU.smul h x)) = actY'.smul h (g.app T (f.app T x))
  rw [hf, hg]

/-- **(f)** A point of `Y` fixed in `Y'` is fixed in `Y`, along an injection: strongly-FPR for
`U ⟶ Y` gives strongly-FPR for `U ⟶ Y'`. -/
theorem isStronglyFPR_comp_mono {f : U ⟶ Y} {g : Y ⟶ Y'} (hf : IsEquivariant actU actY f)
    (hg : IsEquivariant actY actY' g) (hi : ∀ T, Function.Injective (g.app T))
    (H : IsStronglyFPR hf) : IsStronglyFPR (isEquivariant_comp hf hg) := by
  intro Z
  refine (isFPR_iff (IsEquivariant.comap (isEquivariant_comp hf hg) (QuotientAddGroup.mk' Z))).mpr fun T x hx => ?_
  refine (isFPR_iff (hf.comap (QuotientAddGroup.mk' Z))).mp (H Z) T x ?_
  intro T' s k
  refine hi T' ?_
  have h1 := hx s k
  have e : ∀ y : Y.obj T, g.app T' (Y.map s y) = Y'.map s (g.app T y) := fun y =>
    NatTrans.naturality_apply g s y
  change g.app T' (actY.smul _ (Y.map s (f.app T x))) = g.app T' (Y.map s (f.app T x))
  rw [hg, e]
  exact h1

/-- Precomposition with an injective equivariant morphism keeps strongly-FPR. -/
theorem isStronglyFPR_mono_comp {f : U ⟶ Y} {g : Y ⟶ Y'} (hf : IsEquivariant actU actY f)
    (hg : IsEquivariant actY actY' g) (hi : ∀ T, Function.Injective (f.app T))
    (H : IsStronglyFPR hg) : IsStronglyFPR (isEquivariant_comp hf hg) := by
  intro Z
  refine (isFPR_iff (IsEquivariant.comap (isEquivariant_comp hf hg) (QuotientAddGroup.mk' Z))).mpr fun T x hx => ?_
  have h2 : f.app T x ∈ (fixedPoints (AAction.comap (QuotientAddGroup.mk' Z) actY)).obj T :=
    (isFPR_iff (hg.comap (QuotientAddGroup.mk' Z))).mp (H Z) T (f.app T x) (by exact hx)
  intro T' s k
  refine hi T' ?_
  have e : ∀ y : U.obj T, f.app T' (U.map s y) = Y.map s (f.app T y) := fun y =>
    NatTrans.naturality_apply f s y
  have h3 := h2 s k
  change f.app T' (actU.smul _ (U.map s x)) = f.app T' (U.map s x)
  rw [hf, e]
  exact h3

/-- **(f)** `yoneda V ⟶ W' ⟶ X` is étale. -/
theorem isEtale_comp_ι {W : Subfunctor X} (hW : Space.IsOpenSubspace B S hS W)
    {V : BigFppfOver B S hS} {v : yoneda.obj V ⟶ W.toFunctor}
    (hv : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) v) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (v ≫ W.ι) := by
  have hmap := Space.isMultiplicative_presheaf_etale B S hS
  exact MorphismProperty.comp_mem _ _ _ hv (Space.presheaf_etale_of_isOpenImmersion B S hS hW.2)

end Back

/-! ### (b) The object of the site given by an open of `S` -/

section Base

/-- The open `O` of `S` as an object of the site. -/
def openBase (O : S.Opens) : BigFppfOver B S hS :=
  openObj (U := T1 B S hS) (show ((SCH).obj (T1 B S hS)).Opens from O)

/-- Its inclusion in `S`. -/
def openBaseι (O : S.Opens) : openBase (B := B) (hS := hS) O ⟶ T1 B S hS :=
  openJ (U := T1 B S hS) (show ((SCH).obj (T1 B S hS)).Opens from O)

instance (O : S.Opens) : IsOpenImmersion ((SCH).map (openBaseι (B := B) (hS := hS) O)) :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι O))

instance (O : S.Opens) : Mono (openBaseι (B := B) (hS := hS) O) :=
  StronglyFPR.mono_openJ

lemma isAffine_openBase {O : S.Opens} (hO : IsAffineOpen O) :
    IsAffine ((SCH).obj (openBase (B := B) (hS := hS) O)) := hO

lemma structMap_toT1 {T : BigFppfOver B S hS} (k : T ⟶ T1 B S hS) (t : (SCH).obj T) :
    (SCH).map k t = structMap T t := by
  have hw : (SCH).map k ≫ structMap (T1 B S hS) = structMap T := congrArg (B.inclusion.map) (Over.w k)
  rw [← hw]
  rfl

/-- A site object over `O` maps to `openBase O`. -/
lemma exists_lift_openBase {O : S.Opens} (T : BigFppfOver B S hS)
    (h : ∀ t : (SCH).obj T, structMap T t ∈ O) :
    ∃ l : T ⟶ openBase (B := B) (hS := hS) O, True := by
  obtain ⟨k⟩ : Nonempty (T ⟶ T1 B S hS) := ⟨Over.homMk T.hom (Category.comp_id _)⟩
  obtain ⟨l, -⟩ := exists_factor_open (openBaseι (B := B) (hS := hS) O) k (by
      rintro _ ⟨t, rfl⟩
      rw [structMap_toT1]
      have hr : Set.range ((SCH).map (openBaseι (B := B) (hS := hS) O)) =
          (show ((SCH).obj (T1 B S hS)).Opens from O : Set _) :=
        StronglyFPR.range_openJ
      rw [hr]
      exact h t)
  exact ⟨l, trivial⟩

lemma openBase_ext {O : S.Opens} {T : BigFppfOver B S hS} (a b : T ⟶ openBase (B := B) (hS := hS) O) :
    a = b :=
  (cancel_mono (openBaseι (B := B) (hS := hS) O)).mp (t1_ext _ _)

variable {W : Subfunctor X} {O : S.Opens}

/-- **(b)** `p : W' ⟶ A`, for `W'` lying over `O`, `A` the object of the site given by `O`. -/
def toBase (hO : LiesOver W O) : W.toFunctor ⟶ yoneda.obj (openBase (B := B) (hS := hS) O) where
  app T := ↾fun x => (exists_lift_openBase (O := O) (unop T) (hO T ⟨x.1, x.2⟩)).choose
  naturality T T' f := by
    ext x
    exact openBase_ext _ _

/-- **(b)** `p` is invariant: there is at most one morphism to `A`. -/
lemma toBase_invariant (hO : LiesOver W O) (act : AAction (fppfO B S hS) M W.toFunctor)
    {T : (BigFppfOver B S hS)ᵒᵖ} (a : APt (fppfO B S hS) M T) (y : W.toFunctor.obj T) :
    (toBase hO).app T (act.smul a y) = (toBase hO).app T y :=
  openBase_ext _ _

/-- `p` followed by the inclusion of `O` in `S` is the structure morphism of `W'`. -/
lemma toBase_comp (hO : LiesOver W O) :
    toBase hO ≫ yoneda.map (openBaseι (B := B) (hS := hS) O) = W.ι ≫ toT1 X :=
  toT1_ext _ _

end Base

/-! ### (c), (e) Finite presentation and separatedness of `p` -/

section FP

variable {W : Subfunctor X} {O : S.Opens}

/-- **(c)** `p : W' ⟶ A` is of finite presentation. -/
theorem isFinitePresentation_toBase (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X))
    (hW : Space.IsOpenSubspace B S hS W) (hq : Space.IsQuasiCompactSpace B S hS W.toFunctor)
    (hO : LiesOver W O) (hOa : IsAffineOpen O) :
    Space.IsFinitePresentation B S hS (toBase (B := B) (hS := hS) hO) := by
  have hT := isAlgebraicSpace_yoneda B S hS (T1 B S hS)
  have hA := isAlgebraicSpace_yoneda B S hS (openBase (B := B) (hS := hS) O)
  have hg : Space.IsLocallyOfFinitePresentation B S hS
      (yoneda.map (openBaseι (B := B) (hS := hS) O)) :=
    Space.isLocallyOfFinitePresentation_yoneda_map B S hS _ inferInstance
  have hcomp : Space.IsLocallyOfFinitePresentation B S hS (W.ι ≫ toT1 X) :=
    Space.isLocallyOfFinitePresentation_comp B S hS hW.1 hX hT _ _
      (Space.isLocallyOfFinitePresentation_of_isEtale B S hS
        (Space.isEtale_of_isOpenImmersion B S hS hW.2)) hlfp
  refine ⟨Space.isLocallyOfFinitePresentation_of_comp B S hS hW.1 hA hT _ _ ?_
    (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hg), ?_, ?_⟩
  · rw [toBase_comp]; exact hcomp
  · exact Space.isQuasiCompact_of_isQuasiCompactSpace_of_isAffine hW.1 hq _
      (isAffine_openBase hOa) _
  · exact Space.isQuasiCompact_of_isPullback B S hS
      (ChartStratum.isPullback_diagonal_of_mono W.ι (toBase hO) (toT1 X)
        (toT1 _) (toT1_ext _ _)) hqs

/-- **(e)** `p : W' ⟶ A` is separated when `X` is separated over `S`. -/
theorem isSeparated_toBase (hsep : Space.IsSeparatedOver B S hS X) (hO : LiesOver W O) :
    Space.IsSeparated B S hS (toBase (B := B) (hS := hS) hO) := by
  have he : Space.IsSeparated B S hS (toT1 X) :=
    (Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS (isTerminal_T1 B S hS) _).1 hsep
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (ChartStratum.isPullback_diagonal_of_mono W.ι (toBase hO) (toT1 X)
      (toT1 _) (toT1_ext _ _)) he

end FP

/-! ### (d), (e) Over `Spec ℤ` -/

section Z

variable (hZ : B.Contains (⊤_ Scheme.{u}))

lemma isAffine_top : IsAffine (⊤_ Scheme.{u}) :=
  .of_isIso (terminalIsoIsTerminal specULiftZIsTerminal).hom

/-- **(d)** An affine object `A` of the `S`-site, as an affine object of the site of `Spec ℤ`. -/
def zObj (A : BigFppfOver B S hS) (hA : IsAffine ((SCH).obj A)) :
    BigAffineFppf B (⊤_ Scheme.{u}) hZ :=
  ⟨jo (hZ := hZ) A, hA⟩

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : BigFppfOver B S hS}

/-- **(d)** `viewMap p`, with target the Yoneda object of `zObj`. -/
def viewBase (hA : IsAffine ((SCH).obj A)) (p : Y ⟶ yoneda.obj A) :
    view hZ Y ⟶ yoneda.obj ((BigAffineFppf.inclusion _ _ hZ).obj (zObj hZ A hA)) :=
  viewMap (hZ := hZ) p

theorem isFinitePresentation_viewBase (hA : IsAffine ((SCH).obj A)) (p : Y ⟶ yoneda.obj A)
    (hp : Space.IsFinitePresentation B S hS p) :
    Space.IsFinitePresentation B (⊤_ Scheme.{u}) hZ (viewBase hZ hA p) :=
  isFinitePresentation_viewMap (hZ := hZ) p hp

/-- **(e)** Separatedness over `Spec ℤ`, in the form asked by `strongAtlas_of_limit`. -/
theorem isSeparated_viewBase (hA : IsAffine ((SCH).obj A)) {p : Y ⟶ yoneda.obj A}
    (hp : Space.IsSeparated B S hS p) :
    Space.IsSeparated B (⊤_ Scheme.{u}) hZ
      (viewBase hZ hA p ≫ (LimFin.limitDataZ hZ (zObj hZ A hA)).e.inv) := by
  refine Space.isSeparated_comp B _ hZ _ _ ?_ (Space.isSeparated_of_isIso B _ hZ _)
  have hi : IsIso ((OverShriek.relocalizeYonedaIso (toZ hZ hS)).app A).hom := Iso.isIso_hom _
  exact Space.isSeparated_comp B _ hZ _ _
    (Space.isSeparated_relocalize B S hS hZ (toZ hZ hS) hp) (@Space.isSeparated_of_isIso B _ hZ _ _ _ hi)

end Z

/-! ### Theorem 6.8 (i) for a morphism to an affine object -/

/-- The conclusion for one space: an equivariant, étale, surjective, strongly-FPR morphism from an
object of the site, which is a disjoint union of stable affine opens. Affine means here an affine
scheme: it is `S`-affine only if `S` is separated or the like. -/
structure AffineAtlas (act : AAction (fppfO B S hS) M X) (V : BigFppfOver B S hS) where
  actV : AAction (fppfO B S hS) M (yoneda.obj V)
  v : yoneda.obj V ⟶ X
  equivariant : IsEquivariant actV act v
  etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) v
  surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) v
  strong : IsStronglyFPR equivariant
  I : Type u
  piece : I → ((SCH).obj V).Opens
  disjoint : Pairwise (Function.onFun Disjoint piece)
  iSup_eq_top : iSup piece = ⊤
  stable : ∀ a, IsStableOpen actV (piece a)
  affine : ∀ a, IsAffine (piece a).toScheme

section Atlas

variable (hZ : B.Contains (⊤_ Scheme.{u})) [AddGroup.FG M]

/-- **Theorem 6.8 (i)** for `p : Y ⟶ A` separated, of finite presentation, invariant, `A` an affine
object of the site of `S`, `S` arbitrary: `strongAtlas_of_limit` on the site of `Spec ℤ`, for the
view of `p`, and `exists_chart_of_view`. -/
theorem exists_atlas_of_fp
    (h5 : ∀ [AddMonoid.FG M] [DecidableEq M],
      ChartAssembly.Section5FromEffectivity B (⊤_ Scheme.{u}) hZ M)
    (hM : B.Contains (Spec (ZMon M))) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {A : BigFppfOver B S hS} (hA : IsAffine ((SCH).obj A))
    (p : Y ⟶ yoneda.obj A) (hfp : Space.IsFinitePresentation B S hS p)
    (hsep : Space.IsSeparated B S hS p) (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (a : APt (fppfO B S hS) M T) (y : Y.obj T),
      p.app T (act.smul a y) = p.app T y) :
    ∃ V : BigFppfOver B S hS, Nonempty (AffineAtlas act V) := by
  have hfg : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  have htop : IsAffine (⊤_ Scheme.{u}) := isAffine_top
  have hSft : LocallyOfFiniteType (terminal.from (⊤_ Scheme.{u})) := by
    have : IsIso (terminal.from (⊤_ Scheme.{u})) :=
      ⟨terminal.from _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    infer_instance
  obtain ⟨V', actV', v', hs⟩ := strongAtlas_of_limit (S := ⊤_ Scheme.{u}) (hS := hZ) hSft h5
    (LimFin.limitDataZ hZ (zObj hZ A hA)) (isAlgebraicSpace_yoneda B _ hZ _) (LimFin.actGoodZ hZ hM)
    (viewBase hZ hA p) (view_isAlgebraicSpace (hZ := hZ) hY)
    (isFinitePresentation_viewBase hZ hA p hfp) (isSeparated_viewBase hZ hA hsep)
    (viewAct act) (fun a y => viewMap_invariant (hZ := hZ) (fun a y => hinv a y) a y)
  have hv' : IsEquivariant actV' (viewAct act) v' := hs.atlas.equivariant
  obtain ⟨I, Vs, hdec⟩ := hs.atlas.decomposition
  refine ⟨LimView.chartObj v', ⟨⟨LimView.chartAct actV' hv', LimView.chartMap v',
    LimView.chartMap_equivariant hv',
    LimView.chartMap_etale v' hs.atlas.etale, LimView.chartMap_surjective v' hs.atlas.surjective,
    chart_isStronglyFPR hv' hs.isStronglyFPR, I, Vs, hdec.disjoint, hdec.iSup_eq_top,
    fun a => chart_isStableOpen hv' (hdec.stable a), fun a => ?_⟩⟩⟩
  have h1 : IsAffineHom ((Vs a).ι ≫ structMap V') := hdec.isAffineHom a
  have h2 : IsAffine (Vs a).toScheme := by
    have : IsAffine (Scheme.Opens.toScheme (Vs a)) := isAffine_of_isAffineHom ((Vs a).ι ≫ structMap V')
    exact this
  exact h2

end Atlas

end

end AlgMag.LimThm

#print axioms AlgMag.LimThm.isFinitePresentation_toBase
#print axioms AlgMag.LimThm.isSeparated_toBase
#print axioms AlgMag.LimThm.isSeparated_viewBase
#print axioms AlgMag.LimThm.isStronglyFPR_comp_mono
#print axioms AlgMag.LimThm.exists_atlas_of_fp
