/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalCorAtlas

/-!
# Theorem 6.8 (i), one atlas for `X` not quasi-compact

The coproduct of the charts lies in the site, with no assumption on the site. One chart at each point of an atlas `W` of `X`
suffices. A chart is affine and locally of finite type over `S`, so its size is at most `size S`, uniformly
(`Scheme.size_le_of_locallyOfFiniteType`), and `#W ≤ 2 ^ size W`. This removes `HasSiteCoproducts` from `FinalThm68Single`,
`FinalCorAtlas`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal

universe v u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A scheme has at most `2 ^ size` points: it is `T₀` and the affine opens are a basis. -/
theorem mk_scheme_le (Y : Scheme.{u}) : #Y ≤ 2 ^ Y.size := by
  have inj : Function.Injective (fun x : Y => {V : Y.affineOpens | x ∈ V.1}) := by
    intro x y h
    refine Inseparable.eq (inseparable_iff_forall_isOpen.2 fun O hO => ?_)
    have key : ∀ {a b : Y}, {V : Y.affineOpens | a ∈ V.1} = {V : Y.affineOpens | b ∈ V.1} →
        a ∈ O → b ∈ O := by
      intro a b e ha
      obtain ⟨_, ⟨W, hW, rfl⟩, hx, hsub⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open ha hO
      have : (⟨W, hW⟩ : Y.affineOpens) ∈ {V : Y.affineOpens | a ∈ V.1} := hx
      rw [e] at this
      exact hsub this
    exact ⟨key h, key h.symm⟩
  calc #Y ≤ #(Set Y.affineOpens) := Cardinal.mk_le_of_injective inj
    _ = 2 ^ #Y.affineOpens := Cardinal.mk_set
    _ ≤ 2 ^ Y.size := Cardinal.power_le_power_left two_ne_zero Y.mk_affineOpens_le_size

/-- A family of site objects indexed by at most `μ` elements, each of size at most `μ`, with `μ` below the cutoff, has a
coproduct in the site. -/
theorem exists_cofan_of_size {A : Type u} (U : A → BigFppfOver B S hS) {μ : Cardinal.{u}}
    (hμ : μ < B.cutoff) (hA : #A ≤ μ) (hU : ∀ a, ((SCH).obj (U a)).size ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V), Nonempty (IsColimit (Cofan.mk V j)) := by
  let Y : A → Scheme.{u} := fun a => (SCH).obj (U a)
  have hC : B.Contains (∐ Y) :=
    (schemeSize_coproduct_le Y (max ℵ₀ μ) (le_max_left _ _) (hA.trans (le_max_right _ _))
      fun a => (hU a).trans (le_max_right _ _)).trans_lt (max_lt B.aleph0_lt_cutoff hμ)
  let f : ∐ Y ⟶ S := Sigma.desc fun a => (U a).hom.hom
  let V : BigFppfOver B S hS := siteObject B S hS hC f
  let j : ∀ a, U a ⟶ V := fun a => siteHom (Sigma.ι Y a) (Sigma.ι_desc _ _)
  refine ⟨V, j, ⟨mkCofanColimit _ (fun s => siteHom (Sigma.desc fun a => (SCH).map (s.inj a)) ?_)
    (fun s a => ?_) (fun s m hm => ?_)⟩⟩
  · refine Sigma.hom_ext _ _ fun a => ?_
    rw [Sigma.ι_desc_assoc]
    have h1 : (SCH).map (s.inj a) ≫ s.pt.hom.hom = (U a).hom.hom :=
      congrArg (fun k => k.hom) (Over.w (s.inj a))
    exact h1.trans (Sigma.ι_desc (fun a => (U a).hom.hom) a).symm
  · exact site_hom_ext (Sigma.ι_desc _ _)
  · refine site_hom_ext (Sigma.hom_ext _ _ fun a => ?_)
    have := congrArg (SCH).map (hm a)
    exact this.trans (Sigma.ι_desc (fun a => (SCH).map (s.inj a)) a).symm

/-- One chart for each point of an atlas `W`: a chart family whose coproduct exists in the site. -/
theorem exists_small_charts [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (A : Type u) (U : A → BigFppfOver B S hS) (_ : ChartFamily act A U)
      (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V), Nonempty (IsColimit (Cofan.mk V j)) := by
  obtain ⟨A₀, U₀, ⟨L⟩⟩ := exists_charts hZ section5FromEffectivity hM hX hlfp hsep act
  obtain ⟨W, g, hs, -⟩ := hX.exists_atlas
  have hit := fun u : (SCH).obj W =>
    L.hit (Space.pointsMap B S hS _ g ((Space.pointsEquivScheme B S hS W).symm u))
  choose c hc using hit
  let A : Type u := (SCH).obj W
  let U : A → BigFppfOver B S hS := fun u => U₀ (c u)
  have hft := chartsOfFiniteType_of_lfp ((lfp_toT1_iff hX).1 hlfp)
  have hsize : ∀ a, ((SCH).obj (U a)).size ≤ S.size := fun a => by
    haveI : LocallyOfFiniteType (U a).hom.hom := hft _ _ (L.etale (c a))
    haveI : CompactSpace ((SCH).obj (U a)) :=
      have := L.affine (c a); inferInstance
    exact Scheme.size_le_of_locallyOfFiniteType (U a).hom.hom
  have hμ : max (2 ^ ((SCH).obj W).size) S.size < B.cutoff :=
    max_lt (B.cutoff_isStrongPrelimit W.left.property) hS
  obtain ⟨V, j, hV⟩ := exists_cofan_of_size U hμ ((mk_scheme_le _).trans (le_max_left _ _))
    fun a => (hsize a).trans (le_max_right _ _)
  refine ⟨A, U, ⟨fun a => L.actU (c a), fun a => L.f (c a), fun a => L.equivariant (c a),
    fun a => L.etale (c a), fun a => L.strong (c a), fun a => L.affine (c a), fun x => ?_⟩, V, j, hV⟩
  obtain ⟨y, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS g hs x
  refine ⟨Space.pointsToScheme B S hS W y, ?_⟩
  have e : (Space.pointsEquivScheme B S hS W).symm (Space.pointsToScheme B S hS W y) = y :=
    (Space.pointsEquivScheme B S hS W).symm_apply_apply y
  have := hc (Space.pointsToScheme B S hS W y)
  rwa [e] at this

/-- **Theorem 6.8 (i)**: `X` separated, locally of finite presentation, not necessarily quasi-compact, `S` separated: one
strongly-FPR atlas, with no assumption on the site. -/
theorem thm68_atlas [S.IsSeparated] [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) M (yoneda.obj V))
      (v : yoneda.obj V ⟶ X), IsStronglyFPRAtlas actV act v ∧
        ∀ Z : AddSubgroup M, IsZFPRAtlas actV act v Z := by
  obtain ⟨A, U, L, V, j, ⟨hV⟩⟩ := exists_small_charts hZ hM hX hlfp hsep act
  let E := L.toEtale fun a => isAffineHom_structMap (L.affine a)
  obtain ⟨v, hv, hat⟩ := exists_atlas_of_family hX E hV
  have h : IsStronglyFPRAtlas (coprodAction E.act hV) act v :=
    ⟨hat, fun Z => isZFPR_coprod hV E hv hat.equivariant fun a => L.strong a Z⟩
  exact ⟨V, _, v, h, h.isZFPRAtlas⟩

variable [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- A `Z`-FPR atlas for all `Z`. -/
theorem existsZFPRAtlas_nonqc [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (Z : AddSubgroup M) : ExistsZFPRAtlas act Z := by
  obtain ⟨V, actV, v, -, h2⟩ := thm68_atlas hZ hM hX ((lfp_toT1_iff hX).2 hfp) hsep act
  exact ⟨V, actV, v, h2 Z⟩

include hZ in
/-- **Theorem 8.3** for `X` separated, locally of finite presentation, not necessarily quasi-compact, arbitrary magnet `N`,
no atlas in the hypotheses, `S` separated. -/
theorem thm83_nonqc [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    ∃ r : Thm83Repr act N,
      Space.IsQuasiSeparated B S hS (toBase r.P) ∧ IsSeparatedOver r.P ∧
      (Space.IsQuasiCompactSpace B S hS X → Space.IsQuasiCompactSpace B S hS r.P) ∧
      Space.IsLocallyOfFinitePresentation B S hS (terminal.from r.P) :=
  thm83_of_lfp hX (isSeparatedOver_iff_space.1 hsep) hfp N
    (existsZFPRAtlas_nonqc hZ hM hX hsep hfp act _)

include hZ in
/-- **Proposition 14.4**, terms separated, locally of finite presentation, not necessarily quasi-compact, `S` separated. -/
theorem prop144_nonqc [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
    {Xi : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P Xi}
    (a : IndAction M p) (N : AddSubmonoid M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i))
    (hsep : ∀ i, Space.IsSeparatedOver B S hS (p.obj i))
    (hfp : ∀ i, Space.IsLocallyOfFinitePresentation B S hS (terminal.from (p.obj i))) :
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) :=
  prop144_of_atlas a N hX (fun i => isSeparatedOver_iff_space.1 (hsep i))
    (fun i => existsZFPRAtlas_nonqc hZ hM (hX i) (hsep i) (hfp i) (a.act i) _)
    (fun i => Or.inr (isLimitPreserving_of_lfp (hX i) (hfp i)))

end AlgMag.Final

#print axioms AlgMag.Final.thm68_atlas
#print axioms AlgMag.Final.thm83_nonqc
#print axioms AlgMag.Final.prop144_nonqc
