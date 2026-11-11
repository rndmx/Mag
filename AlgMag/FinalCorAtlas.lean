/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalCorBridge

/-!
# Fact 3.34 (ii), Theorem 15.3, Propositions 14.4, 8.5, Theorem 8.3: the atlas discharged

`X` separated and locally of finite presentation over a separated `S`, `M` a finitely generated abelian group, `X` quasi-compact
(atlas from `thm68_qc_spaces`). For Theorem 8.3 and Proposition 14.4 the `S`-affine atlas is not used, and `X` not quasi-compact is
allowed under `HasSiteCoproducts` (`thm68_single`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u

namespace AlgMag.Final

open AlgMag.ChartAssembly

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- **Fact 3.34 (ii)**, arbitrary family, no atlas in the hypotheses: `X` separated, locally of finite presentation, quasi-compact. -/
theorem fact334_free [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X)
    {s : Set (AddSubmonoid M)} (y) (hne : s.Nonempty) (hy : ∀ N ∈ s, attractorImage act N = y) :
    attractorImage act (sInf s) = y := by
  obtain ⟨V, actV, v, h1, -, h3⟩ := thm68_qc_spaces hZ hM hX ((lfp_toT1_iff hX).2 hfp) hsep hq act
  haveI := (hasFiniteAffineDecomposition_iff _).mp h3.2
  haveI : LocallyOfFiniteType V.hom.hom := chartsOfFiniteType_of_lfp hfp V v h1.atlas.etale
  exact fact334_strong hX (isSeparatedOver_iff_space.1 hsep) (isLimitPreserving_of_lfp hX hfp) h1.atlas
    (fun _ _ _ _ => h1.isStronglyFPR _) y hne hy

include hZ in
/-- The order conclusion of Fact 3.34 and Proposition 3.29 for the same `X`. -/
theorem attractorOrder_free [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) :
    AttractorOrder (attractorImage act) where
  monotone := attractorImage_monotone act
  sInf_of_const _ y hne hy := fact334_free hZ hM hX hsep hfp hq act y hne hy

include hZ in
/-- **Theorem 15.3**, no atlas in the hypotheses: pure magnets are in bijection with attractors. -/
noncomputable def thm153_free [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) :
    pureMagnets (attractorImage act) ≃ Set.range (attractorImage act) :=
  pureEquivRange (attractorOrder_free hZ hM hX hsep hfp hq act)

include hZ in
/-- **Proposition 8.5**, no atlas in the hypotheses, one form of each hypothesis. -/
theorem prop85_atlasFree [S.IsSeparated] [CompactSpace S] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    ∃ (Nc : AddSubmonoid M) (hc : Nc ≤ N), Nc.FG ∧ unitsSub Nc = unitsSub N ∧
      ∀ T : BigFppfOver B S hS, Function.Bijective (AttractorPt.ofLE (act := act) (T := T) hc) :=
  prop85_free hZ hM hX (isSeparatedOver_iff_space.1 hsep) hsep ((lfp_toT1_iff hX).2 hfp) hfp hq act N

include hZ in
/-- The `N^×`-FPR atlas for `X` quasi-compact. -/
theorem existsZFPRAtlas_of_qc [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) (Z : AddSubgroup M) :
    ExistsZFPRAtlas act Z := by
  obtain ⟨V, actV, v, -, h2, -⟩ := thm68_qc_spaces hZ hM hX ((lfp_toT1_iff hX).2 hfp) hsep hq act
  exact ⟨V, actV, v, h2 Z⟩

/-- Coproducts of site objects indexed by `Type u` stay in the site. -/
def HasSiteCoproducts (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ (A : Type u) (U : A → BigFppfOver B S hS),
    ∃ (V : BigFppfOver B S hS) (j : ∀ a, U a ⟶ V), Nonempty (IsColimit (Cofan.mk V j))

include hZ in
/-- The `N^×`-FPR atlas, `X` not necessarily quasi-compact, coproducts in the site. -/
theorem existsZFPRAtlas_of_coproducts [S.IsSeparated] (hco : HasSiteCoproducts B S hS)
    (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (Z : AddSubgroup M) :
    ExistsZFPRAtlas act Z := by
  obtain ⟨V, actV, v, -, h2⟩ := thm68_single hZ hco hM hX ((lfp_toT1_iff hX).2 hfp) hsep act
  exact ⟨V, actV, v, h2 Z⟩

private theorem thm83_aux (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) (hat : ExistsZFPRAtlas act (unitsSub N)) :
    ∃ r : Thm83Repr act N,
      Space.IsQuasiSeparated B S hS (toBase r.P) ∧ IsSeparatedOver r.P ∧
      (Space.IsQuasiCompactSpace B S hS X → Space.IsQuasiCompactSpace B S hS r.P) ∧
      Space.IsLocallyOfFinitePresentation B S hS (terminal.from r.P) :=
  thm83_of_lfp hX (isSeparatedOver_iff_space.1 hsep) hfp N hat

include hZ in
/-- **Theorem 8.3**, no atlas in the hypotheses, `X` quasi-compact, arbitrary magnet `N`. -/
theorem thm83_free [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    ∃ r : Thm83Repr act N,
      Space.IsQuasiSeparated B S hS (toBase r.P) ∧ IsSeparatedOver r.P ∧
      Space.IsQuasiCompactSpace B S hS r.P ∧
      Space.IsLocallyOfFinitePresentation B S hS (terminal.from r.P) := by
  obtain ⟨r, a, b, c, d⟩ := thm83_aux hX hsep hfp act N (existsZFPRAtlas_of_qc hZ hM hX hsep hfp hq act _)
  exact ⟨r, a, b, c hq, d⟩

include hZ in
/-- **Theorem 8.3**, no atlas in the hypotheses, `X` not necessarily quasi-compact, coproducts in the site. -/
theorem thm83_free_of_coproducts [S.IsSeparated] (hco : HasSiteCoproducts B S hS)
    (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    ∃ r : Thm83Repr act N,
      Space.IsQuasiSeparated B S hS (toBase r.P) ∧ IsSeparatedOver r.P ∧
      (Space.IsQuasiCompactSpace B S hS X → Space.IsQuasiCompactSpace B S hS r.P) ∧
      Space.IsLocallyOfFinitePresentation B S hS (terminal.from r.P) :=
  thm83_aux hX hsep hfp act N (existsZFPRAtlas_of_coproducts hZ hco hM hX hsep hfp act _)

include hZ in
/-- **Proposition 14.4**, no atlas in the hypotheses: each term separated, locally of finite presentation, quasi-compact. -/
theorem prop144_free [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
    {Xi : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P Xi}
    (a : IndAction M p) (N : AddSubmonoid M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i)) (hsep : ∀ i, Space.IsSeparatedOver B S hS (p.obj i))
    (hfp : ∀ i, Space.IsLocallyOfFinitePresentation B S hS (terminal.from (p.obj i)))
    (hq : ∀ i, Space.IsQuasiCompactSpace B S hS (p.obj i)) :
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) :=
  prop144_of_atlas a N hX (fun i => isSeparatedOver_iff_space.1 (hsep i))
    (fun i => existsZFPRAtlas_of_qc hZ hM (hX i) (hsep i) (hfp i) (hq i) (a.act i) _)
    (fun i => Or.inr (isLimitPreserving_of_lfp (hX i) (hfp i)))

include hZ in
/-- **Proposition 14.4**, terms not necessarily quasi-compact, coproducts in the site. -/
theorem prop144_free_of_coproducts [S.IsSeparated] (hco : HasSiteCoproducts B S hS)
    (hM : B.Contains (Spec (ZMon M)))
    {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
    {Xi : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P Xi}
    (a : IndAction M p) (N : AddSubmonoid M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i)) (hsep : ∀ i, Space.IsSeparatedOver B S hS (p.obj i))
    (hfp : ∀ i, Space.IsLocallyOfFinitePresentation B S hS (terminal.from (p.obj i))) :
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) :=
  prop144_of_atlas a N hX (fun i => isSeparatedOver_iff_space.1 (hsep i))
    (fun i => existsZFPRAtlas_of_coproducts hZ hco hM (hX i) (hsep i) (hfp i) (a.act i) _)
    (fun i => Or.inr (isLimitPreserving_of_lfp (hX i) (hfp i)))

end AlgMag.Final

#print axioms AlgMag.Final.fact334_free
#print axioms AlgMag.Final.thm153_free
#print axioms AlgMag.Final.prop85_atlasFree
#print axioms AlgMag.Final.thm83_free
#print axioms AlgMag.Final.thm83_free_of_coproducts
#print axioms AlgMag.Final.prop144_free
#print axioms AlgMag.Final.prop144_free_of_coproducts
