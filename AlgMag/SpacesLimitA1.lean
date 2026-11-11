/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesLimitThm68
import AlgMag.SpacesLimitStage
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationLocalAtTarget

/-!
# Theorem A.1 for a general base

Mayeux, *Algebraic Magnetism*, Theorem A.1 for `D(M)` with connected fibres (`TorsionResidue M S`).

The printed proof: local over `S`, replace `X` by an orbit, descend to a noetherian stage, and there
`X^G = X_0 := ⋂ X^{F_n}`.

* `mem_fixed_of_site_stage`: `X_0 ⊆ X^G` on the site of a noetherian stage `T₀`.
* `exists_stage_local`: the descent of a stable quasi-compact open over an affine open of `S`.
* `mem_fixed_of_fnAll_local`: `X_0 ⊆ X^G` for that open.
* `a1_closed_local`: `W^G → W` is a closed immersion of finite presentation.
* `fixedPoints_eq_fnAll`: `X^G = X_0` for `X` locally of finite presentation, quasi-separated.
* `a1_closed`: Theorem A.1 (ii), `X^G → X` is a closed immersion of finite presentation.
* `a1_isFPR`, `a1_isStronglyFPR`: Theorem A.1 (ii), étale equivariant morphisms reflect fixed points.
* `a1_closed_noetherian`, `a1_isFPR_noetherian`: Theorem A.1 (i).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.LimThm

open LimAct LimOrbit LimView LimStage AppA3 AppR

attribute [local instance] Space.pointTopology

noncomputable section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-! ### Transport of `X_0` -/

/-- An equivariant morphism maps `X^{F_n}` to `Y^{F_n}`. -/
lemma fnFixed_map {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {P : Type u}
    [AddCommGroup P] {Y Y' : Cᵒᵖ ⥤ Type u} {a : AAction 𝒪 P Y} {a' : AAction 𝒪 P Y'}
    {f : Y ⟶ Y'} (hf : IsEquivariant a a' f) {E : Set P} {n : ℕ} {T : Cᵒᵖ} {x : Y.obj T}
    (hx : x ∈ (fnFixed a E n).obj T) : f.app T x ∈ (fnFixed a' E n).obj T := by
  intro T' s h hh
  rw [← NatTrans.naturality_apply f s x, ← hf, hx s h hh]

section Stage

variable {T₀ : BigFppfOver B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : Y ⟶ yoneda.obj T₀}
  {act : AAction (fppfO B S hS) M Y}

/-- **Theorem A.1, proof**: `X_0 ⊆ X^G` on the site of a noetherian `T₀`. -/
theorem mem_fixed_of_site_stage [AddGroup.FG M] [IsLocallyNoetherian T₀.left.1]
    (hY : IsAlgebraicSpace B S hS Y) (hC : ChartsOfFiniteType Y)
    (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T), p.app T (act.smul h x) = p.app T x)
    (hT : TorsionResidue M T₀.left.1) {E : Set M} (hE : ∀ n, InfinitesimalE E n)
    (hfr : ∀ n, ∀ (A : Type u) [CommRing A], Module.Free A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A M ⧸ Jn A E n))
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : Y.obj T) (hx : x ∈ (fnAll act E).obj T) :
    x ∈ (fixedPoints act).obj T := by
  obtain ⟨ψ, hψ, s, rfl⟩ := exists_fib (p := p) (W := T.unop) x
  have hs1 : s.1 ∈ (fnAll act E).obj (op ((Over.map T₀.hom).obj (Over.mk ψ))) := by
    have h1 : Y.map (OverShriek.overMapMkIso T₀.hom hψ).inv.op
        (Y.map (OverShriek.overMapMkIso T₀.hom hψ).hom.op s.1) ∈
        (fnAll act E).obj (op ((Over.map T₀.hom).obj (Over.mk ψ))) :=
      (fnAll act E).map (OverShriek.overMapMkIso T₀.hom hψ).inv.op hx
    rwa [OverShriek.map_overMapMkIso_inv_hom] at h1
  have hs2 : s ∈ (fnAll (descAct act hinv) E).obj (op (Over.mk ψ)) := by
    intro n hn T₂ r h hh
    exact Subtype.ext (hs1 n hn ((Over.map T₀.hom).map r.unop).op (cv h) hh)
  have hs3 : s ∈ (fixedPoints (descAct act hinv)).obj (op (Over.mk ψ)) := by
    intro _ r k
    exact mem_fixedPoints_of_fnAll (isAlgebraicSpace_fib p hY) (charts_fib p hC)
      (descAct act hinv) hE hT hfr s hs2 r k
  have hs4 : s.1 ∈ (fixedPoints act).obj (op ((Over.map T₀.hom).obj (Over.mk ψ))) :=
    (mem_fix_iff hinv s).mp hs3
  have hs5 : Y.map (OverShriek.overMapMkIso T₀.hom hψ).hom.op s.1 ∈ (fixedPoints act).obj T :=
    (fixedPoints act).map _ hs4
  exact @hs5

end Stage

/-- A section `(ψ, s)` of the view lies in `X^{F_n}` if `s` does. -/
theorem sec_mem_fnFixed (hZ : B.Contains (⊤_ Scheme.{u})) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {act : AAction (fppfO B S hS) M X} {E : Set M} {n : ℕ} {W : ZSite (B := B) hZ}
    {ψ : W.left ⟶ B.obj hS} {s : X.obj (op (Over.mk ψ))}
    (hs : s ∈ (fnFixed act E n).obj (op (Over.mk ψ))) :
    sec W ψ s ∈ (fnFixed (viewAct (hZ := hZ) act) E n).obj (op W) := by
  intro W' f a ha
  let r : Over.mk (f.unop.left ≫ ψ) ⟶ Over.mk ψ := Over.homMk f.unop.left rfl
  exact Subtype.ext (congrArg (Sigma.mk _) (hs r.op (LimView.ptS (W := W'.unop) _ a) ha))

/-! ### The stage of a stable open -/

section Local

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : Subfunctor X} {O : S.Opens}

/-- The torsion hypothesis on `Spec Γ(O)`. -/
lemma torsionResidue_of_affine {A : BigFppfOver B S hS} (hA : IsAffine ((SCH).obj A))
    (hT : TorsionResidue M S) : TorsionResidue M (Spec (.of Γ((SCH).obj A, ⊤))) :=
  torsionResidue_of_hom (((SCH).obj A).isoSpec.inv ≫ A.hom.hom) hT

/-- The descent to a noetherian stage of `W`, stable over the affine open `O`, seen on the site of
`Spec ℤ`. -/
theorem exists_stage_local [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hTor : TorsionResidue M S) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X)
    (hst : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (k : APt (fppfO B S hS) M T) (x : X.obj T),
      x ∈ W.obj T → act.smul k x ∈ W.obj T)
    (hW : Space.IsOpenSubspace B S hS W) (hq : Space.IsQuasiCompactSpace B S hS W.toFunctor)
    (hL : LiesOver W O) (hOa : IsAffineOpen O) :
    ∃ (T₀ : ZSite (B := B) hZ) (_ : IsLocallyNoetherian T₀.left.1)
      (Wk : (ZSite (B := B) hZ)ᵒᵖ ⥤ Type u) (pk : Wk ⟶ yoneda.obj T₀)
      (actK : AAction (fppfO B (⊤_ Scheme.{u}) hZ) M Wk)
      (q : view hZ W.toFunctor ⟶ Wk)
      (hq' : IsEquivariant (viewAct (hZ := hZ) (restrictAct act hst)) actK q),
      IsAlgebraicSpace B _ hZ Wk ∧ ChartsOfFiniteType Wk ∧
      (∀ {T} (h : APt (fppfO B (⊤_ Scheme.{u}) hZ) M T) (x : Wk.obj T),
        pk.app T (actK.smul h x) = pk.app T x) ∧
      TorsionResidue M T₀.left.1 ∧ IsFPR hq' := by
  have hcount : Countable M := countable_of_fg M
  have hM : B.Contains (Spec (ZMon M)) := contains_zmon_of_countable hS M
  have hfg : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  have hA := isAffine_openBase (B := B) (hS := hS) hOa
  have hfp := isFinitePresentation_toBase hX hlfp hqs hW hq hL hOa
  obtain ⟨k, Wk, m, hWk, hWfp, mu, mm⟩ := exists_stage (LimFin.limitDataZ hZ (zObj hZ _ hA))
    (isAlgebraicSpace_yoneda B _ hZ _) (LimFin.actGoodZ hZ hM) (viewBase hZ hA (toBase hL))
    (view_isAlgebraicSpace (hZ := hZ) hW.1)
    (isFinitePresentation_viewBase hZ hA _ hfp) (viewAct (restrictAct act hst))
    (fun a y => viewMap_invariant (hZ := hZ) (fun a y => toBase_invariant hL _ a y) a y)
  let R := Space.affineRing hZ (zObj hZ _ hA)
  let k' : (Finset R)ᵒᵖ := k
  have hE : IsEquivariant (viewAct (restrictAct act hst)) (m.toAct mu mm) m.q :=
    m.equivariant mu mm
  refine ⟨(BigAffineFppf.inclusion _ _ hZ).obj (Space.finsetStage hZ R k'), ?_, Wk.left, Wk.hom,
    m.toAct mu mm, m.q, hE, hWk, (LimFin.limitDataZ hZ (zObj hZ _ hA)).stageCharts k Wk hWk hWfp,
    fun h x => m.invariant mu mm h x, ?_, ?_⟩
  · have h1 : Algebra.FiniteType ℤ (Algebra.adjoin ℤ ((k'.unop : Finset R) : Set R)) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset _)
    have h2 : IsNoetherianRing (Algebra.adjoin ℤ ((k'.unop : Finset R) : Set R)) :=
      Algebra.FiniteType.isNoetherianRing ℤ _
    exact inferInstanceAs (IsLocallyNoetherian
      (Spec (CommRingCat.of (Algebra.adjoin ℤ ((k'.unop : Finset R) : Set R)))))
  · exact torsionResidue_of_injective (Algebra.adjoin ℤ ((k'.unop : Finset R) : Set R)).val.toRingHom
      Subtype.val_injective
      (torsionResidue_of_affine (S := S) (hS := hS) (A := openBase O) hA hTor)
  · exact (isFPR_iff hE).2 fun T x hx => m.fixed_iff mu mm x hx

/-- **Theorem A.1, proof**: `X_0 ⊆ X^G` for `W`, stable over the affine open `O` of `S`. -/
theorem mem_fixed_of_fnAll_local [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hTor : TorsionResidue M S) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X)
    (hst : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (k : APt (fppfO B S hS) M T) (x : X.obj T),
      x ∈ W.obj T → act.smul k x ∈ W.obj T)
    (hW : Space.IsOpenSubspace B S hS W) (hq : Space.IsQuasiCompactSpace B S hS W.toFunctor)
    (hL : LiesOver W O) (hOa : IsAffineOpen O) {E : Set M} (hE : ∀ n, InfinitesimalE E n)
    (hfr : ∀ n, ∀ (A : Type u) [CommRing A], Module.Free A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A M ⧸ Jn A E n))
    {T : BigFppfOver B S hS} (y : W.toFunctor.obj (op T))
    (hy : y ∈ (fnAll (restrictAct act hst) E).obj (op T)) :
    y ∈ (fixedPoints (restrictAct act hst)).obj (op T) := by
  obtain ⟨T₀, hN, Wk, pk, actK, q, hq', hWk, hC, hinv, hTk, hfpr⟩ :=
    exists_stage_local hZ hTor hX hlfp hqs act hst hW hq hL hOa
  have h1 : sec (jo (hZ := hZ) T) T.hom y ∈
      (fixedPoints (viewAct (hZ := hZ) (restrictAct act hst))).obj (op (jo (hZ := hZ) T)) := by
    refine (isFPR_iff hq').1 hfpr _ _ ?_
    refine mem_fixed_of_site_stage (p := pk) hWk hC hinv hTk hE hfr _ fun n hn => ?_
    exact fnFixed_map hq' (sec_mem_fnFixed hZ (hy n hn))
  intro T' r a
  exact mem_fixed_of_sec (W := jo (hZ := hZ) T) (ψ := T.hom) h1 r a

/-- **Theorem A.1, on a stable open**: `W^G → W` is a closed immersion of finite presentation, for
`W` stable quasi-compact over the affine open `O`. -/
theorem a1_closed_local [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hTor : TorsionResidue M S) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X)
    (hst : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (k : APt (fppfO B S hS) M T) (x : X.obj T),
      x ∈ W.obj T → act.smul k x ∈ W.obj T)
    (hW : Space.IsOpenSubspace B S hS W) (hq : Space.IsQuasiCompactSpace B S hS W.toFunctor)
    (hL : LiesOver W O) (hOa : IsAffineOpen O) :
    Space.IsClosedImmersion B S hS (fixedPoints (restrictAct act hst)).ι ∧
      Space.IsFinitePresentation B S hS (fixedPoints (restrictAct act hst)).ι := by
  obtain ⟨T₀, hN, Wk, pk, actK, q, hq', hWk, hC, hinv, hTk, hfpr⟩ :=
    exists_stage_local hZ hTor hX hlfp hqs act hst hW hq hL hOa
  have hcl := closed_of_site_stage pk hWk hC actK hinv hTk
  have hfp := fixedPoints_fp_of_site_stage pk hWk hC actK hinv hTk
  have hview : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)))
      (fixedPoints (viewAct (hZ := hZ) (restrictAct act hst))).ι :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hfpr hcl
  have hvY := view_isAlgebraicSpace (hZ := hZ) hW.1
  have hF₁ := isAlgebraicSpace_of_relativelyRepresentable B _ hZ _ hcl.rep hWk
  have hF₂ := isAlgebraicSpace_of_relativelyRepresentable B _ hZ _ hview.rep hvY
  exact ⟨closed_of_view hview, isFinitePresentation_of_view
    (Space.IsFinitePresentation.of_isPullback B _ hZ hF₂ hF₁ hvY hWk hfpr hfp)⟩

/-! ### Global statements -/

/-- A `T`-point of `X` lies, locally on `T`, in a stable open over an affine open of `S`. -/
theorem exists_cover_point [AddMonoid.FG M] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (act : AAction (fppfO B S hS) M X)
    {T : BigFppfOver B S hS} (x : X.obj (op T)) (t : (SCH).obj T) :
    ∃ (O : S.Opens) (W : Subfunctor X), IsAffineOpen O ∧ Space.IsOpenSubspace B S hS W ∧
      Space.IsQuasiCompactSpace B S hS W.toFunctor ∧
      (∀ (T : (BigFppfOver B S hS)ᵒᵖ) (k : APt (fppfO B S hS) M T) (y : X.obj T),
        y ∈ W.obj T → act.smul k y ∈ W.obj T) ∧
      LiesOver W O ∧ ∃ (V : BigFppfOver B S hS) (j : V ⟶ T), IsOpenImmersion ((SCH).map j) ∧
        X.map j.op x ∈ W.obj (op V) ∧ t ∈ Set.range ((SCH).map j) := by
  let g : yoneda.obj T ⟶ X := yonedaEquiv.symm x
  obtain ⟨w, hw⟩ := Space.surjective_pointsToScheme B S hS T t
  obtain ⟨O, W, hOa, hW, hq, hst, hL, z, hz⟩ :=
    exists_stable_open hM hX act (Space.pointsMap B S hS _ g w)
  let rep := hW.2.rep
  have hpb := rep.isPullback g
  obtain ⟨v, -, hv⟩ := Space.exists_points_of_isPullback B S hS hpb z w hz
  refine ⟨O, W, hOa, hW, hq, hst, hL, rep.pullback g, rep.snd g, hW.2.property_snd g, ?_,
    Space.pointsToScheme B S hS _ v, ?_⟩
  · have hw' := congrArg (fun q => q.app (op (rep.pullback g)) (𝟙 _)) hpb.w
    have e : X.map (rep.snd g).op x = ((rep.fst g).app (op (rep.pullback g)) (𝟙 _)).1 := by
      refine Eq.trans ?_ hw'.symm
      change _ = g.app (op (rep.pullback g)) (𝟙 (rep.pullback g) ≫ rep.snd g)
      rw [Category.id_comp]
      simp [g, yonedaEquiv]
    rw [e]
    exact ((rep.fst g).app (op (rep.pullback g)) (𝟙 _)).2
  · rw [← hw, ← hv, Space.pointsToScheme_pointsMap]

/-- **Theorem A.1, proof**: `X^G = X_0 = ⋂ X^{F_n}`, for `X` locally of finite presentation and
quasi-separated, by the stage of each stable open. -/
theorem mem_fixed_of_fnAll [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hTor : TorsionResidue M S) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X)
    {E : Set M} (hE : ∀ n, InfinitesimalE E n)
    (hfr : ∀ n, ∀ (A : Type u) [CommRing A], Module.Free A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A M ⧸ Jn A E n))
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : X.obj T) (hx : x ∈ (fnAll act E).obj T) :
    x ∈ (fixedPoints act).obj T := by
  obtain ⟨T⟩ := T
  have hcount : Countable M := countable_of_fg M
  have hM : B.Contains (Spec (ZMon M)) := contains_zmon_of_countable hS M
  have hfg : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  choose O W hOa hW hq hst hL V j hj hmem hr using exists_cover_point hM hX act x
  have hc := BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS j hj
    (fun t => ⟨t, hr t⟩)
  suffices hs : ∀ {W₁ : BigFppfOver B S hS} (f : W₁ ⟶ T), (Sieve.ofArrows V j) f →
      X.map f.op x ∈ (fixedPoints act).obj (op W₁) by
    intro T₁ s k
    exact mem_fixedPoints_of_cover hX.isSheaf act x hc hs s k
  rintro W₁ f ⟨Z, h, r, ⟨t⟩, rfl⟩
  let y : (W t).toFunctor.obj (op (V t)) := ⟨X.map (j t).op x, hmem t⟩
  have hy : y ∈ (fnAll (restrictAct act (hst t)) E).obj (op (V t)) := by
    intro n hn T' s k hk
    exact Subtype.ext ((fnAll act E).map (j t).op hx n hn s k hk)
  have h1 : y ∈ (fixedPoints (restrictAct act (hst t))).obj (op (V t)) := by
    intro _ s k
    exact mem_fixed_of_fnAll_local hZ hTor hX hlfp hqs act (hst t) (hW t) (hq t) (hL t) (hOa t)
      hE hfr y hy s k
  have h2 : X.map (j t).op x ∈ (fixedPoints act).obj (op (V t)) := by
    intro _ s k
    exact congrArg Subtype.val (h1 s k)
  have h3 : X.map h.op (X.map (j t).op x) ∈ (fixedPoints act).obj (op W₁) :=
    (fixedPoints act).map h.op h2
  have e : X.map (h ≫ j t).op x = X.map h.op (X.map (j t).op x) := by
    rw [op_comp, Functor.map_comp_apply]
  rw [e]
  exact @h3

/-- **Theorem A.1 (ii)**, proof: `X^G = X_0`. -/
theorem fixedPoints_eq_fnAll [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hTor : TorsionResidue M S) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X)
    {E : Set M} (hE : ∀ n, InfinitesimalE E n)
    (hfr : ∀ n, ∀ (A : Type u) [CommRing A], Module.Free A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A M ⧸ Jn A E n)) :
    fixedPoints act = fnAll act E := by
  refine le_antisymm ?_ ?_
  · intro T x hx n _
    exact fixedPoints_le_fnFixed act E n T hx
  · intro T x hx _ s k
    exact mem_fixed_of_fnAll hZ hTor hX hlfp hqs act hE hfr x hx s k

/-- **Theorem A.1 (ii)**, closedness: `X^G → X` is a closed immersion, for `X` locally of finite
presentation and quasi-separated over an arbitrary `S`, `D(M)` with connected fibres. -/
theorem a1_isClosedImmersion [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hTor : TorsionResidue M S) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X) :
    Space.IsClosedImmersion B S hS (fixedPoints act).ι := by
  obtain ⟨E, hE⟩ := exists_E M
  have hA := fun n => (hE n).1
  have hF := fun n => (hE n).2
  rw [fixedPoints_eq_fnAll hZ hTor hX hlfp hqs act hA hF]
  exact presheaf_fnAll_ι hX act hA hTor hF

/-- `W^G` is the base change of `X^G` to the stable subfunctor `W`. -/
lemma isPullback_fixed_restrict (act : AAction (fppfO B S hS) M X)
    (hst : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (k : APt (fppfO B S hS) M T) (x : X.obj T),
      x ∈ W.obj T → act.smul k x ∈ W.obj T) :
    IsFPR (ι_equivariant act hst) := by
  refine (isFPR_iff (ι_equivariant act hst)).2 fun _ x hx _ s k => ?_
  exact Subtype.ext (hx s k)

/-- **Theorem A.1 (ii)**: `X^G → X` is a closed immersion of finite presentation, for `X` locally of
finite presentation and quasi-separated over an arbitrary `S`, `D(M)` with connected fibres. -/
theorem a1_closed [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))
    (hTor : TorsionResidue M S) (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X) :
    Space.IsClosedImmersion B S hS (fixedPoints act).ι ∧
      Space.IsFinitePresentation B S hS (fixedPoints act).ι := by
  have hcl := a1_isClosedImmersion hZ hTor hX hlfp hqs act
  refine ⟨hcl, ?_⟩
  have hcount : Countable M := countable_of_fg M
  have hM : B.Contains (Spec (ZMon M)) := contains_zmon_of_countable hS M
  have hfg : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  have hF := isAlgebraicSpace_of_relativelyRepresentable B S hS _ hcl.rep hX
  obtain ⟨U, f, hs, -⟩ := hX.exists_atlas
  let c : (SCH).obj U → Space.points B S hS X := fun u =>
    Space.pointsMap B S hS _ f (Function.surjInv (Space.surjective_pointsToScheme B S hS U) u)
  choose O W hOa hW hq hst hL hr using fun u => exists_stable_open hM hX act (c u)
  have hcov : Space.IsZariskiCover B S hS ((SCH).obj U) W := by
    refine (Space.isZariskiCover_iff_iUnion_points B S hS X hX _ W hW).2
      (Set.eq_univ_of_forall fun x => ?_)
    obtain ⟨y, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS f hs x
    refine Set.mem_iUnion.2 ⟨Space.pointsToScheme B S hS U y, ?_⟩
    have e : Function.surjInv (Space.surjective_pointsToScheme B S hS U)
        (Space.pointsToScheme B S hS U y) = y :=
      Space.injective_pointsToScheme B S hS U
        (Function.surjInv_eq (Space.surjective_pointsToScheme B S hS U) _)
    have := hr (Space.pointsToScheme B S hS U y)
    simp only [c, e] at this
    exact this
  refine Space.isFinitePresentation_of_zariskiCover B S hS hF hX _ hcov fun u => ?_
  have hPb : IsPullback _ _ _ _ := isPullback_fixed_restrict (W := W u) act (hst u)
  have hloc := a1_closed_local hZ hTor hX hlfp hqs act (hst u) (hW u) (hq u) (hL u) (hOa u)
  have hR := isAlgebraicSpace_of_relativelyRepresentable B S hS _ hloc.1.rep (hW u).1
  have hP : IsAlgebraicSpace B S hS (pullback (fixedPoints act).ι (W u).ι) :=
    isAlgebraicSpace_pullback B S hS _ _ hF (hW u).1 hX
  refine Space.IsFinitePresentation.of_isPullback B S hS hP hR (hW u).1 (hW u).1
    (a := hPb.isoPullback.inv) (b := pullback.snd _ _) (f := (fixedPoints _).ι) (g := 𝟙 _)
    (IsPullback.of_horiz_isIso (CommSq.mk ?_)) hloc.2
  rw [Category.comp_id, hPb.isoPullback_inv_snd]

/-- **Theorem A.1 (ii)**: étale equivariant morphisms are fixed point reflecting, for `U` locally of
finite presentation and quasi-separated over an arbitrary `S`, `D(M)` with connected fibres. -/
theorem a1_isFPR [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u})) (hTor : TorsionResidue M S)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 U))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 U))
    {actU : AAction (fppfO B S hS) M U} {actX : AAction (fppfO B S hS) M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f) : IsFPR hf := by
  obtain ⟨E, hE⟩ := exists_E M
  have hA := fun n => (hE n).1
  have hF := fun n => (hE n).2
  refine (isFPR_iff hf).2 fun T x hx _ s k =>
    mem_fixed_of_fnAll hZ hTor hU hlfp hqs actU hA hF x (fun n _ => ?_) s k
  exact mem_fnFixed_of_etale (hA n) hTor hf het x (fixedPoints_le_fnFixed actX E n T hx)

/-- **Theorem A.2 (ii)** input: `H = D(M/Z)` with connected fibres: étale equivariant morphisms are
`Z`-FPR. -/
theorem a1_isZFPR (hZ : B.Contains (⊤_ Scheme.{u})) [AddGroup.FG M] (Z : AddSubgroup M)
    (hTor : TorsionResidue (M ⧸ Z) S)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 U))
    (hqs : Space.IsQuasiSeparated B S hS (toT1 U))
    {actU : AAction (fppfO B S hS) M U} {actX : AAction (fppfO B S hS) M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f) : IsZFPR hf Z :=
  a1_isFPR hZ hTor hU hlfp hqs (hf.comap (QuotientAddGroup.mk' Z)) het

/-! ### Case (i) -/

/-- Charts of a space locally of finite presentation over `S` are of finite type over `S`. -/
theorem chartsOfFiniteType_of_lfp (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X)) :
    ChartsOfFiniteType X := by
  intro V φ he
  have h : LocallyOfFinitePresentation ((SCH).map (Over.homMk V.hom rfl : V ⟶ T1 B S hS)) :=
    hlfp V (T1 B S hS) φ (𝟙 _) _ he
      (have := Space.isMultiplicative_presheaf_etale B S hS; MorphismProperty.id_mem _ _) (toT1_ext _ _)
  exact inferInstanceAs (LocallyOfFiniteType ((SCH).map (Over.homMk V.hom rfl : V ⟶ T1 B S hS)))

/-- **Theorem A.1 (i)**: for `S` locally noetherian, `X` locally of finite presentation, `D(M)` with
connected fibres, `X^G → X` is a closed immersion of finite presentation. -/
theorem a1_closed_noetherian [AddGroup.FG M] [IsLocallyNoetherian S] (hTor : TorsionResidue M S)
    (hX : IsAlgebraicSpace B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 X))
    (act : AAction (fppfO B S hS) M X) :
    Space.IsClosedImmersion B S hS (fixedPoints act).ι ∧
      Space.IsFinitePresentation B S hS (fixedPoints act).ι := by
  have hC := chartsOfFiniteType_of_lfp hlfp
  have hcl := thmA1_closed hX hC act hTor
  have : IsLocallyNoetherian (T1 B S hS).left.1 := inferInstanceAs (IsLocallyNoetherian S)
  exact ⟨hcl, fp_of_closed_noetherian (T₀ := T1 B S hS) (toT1 X) hX hC _ hcl⟩

/-- **Theorem A.1 (i)**: étale equivariant morphisms are fixed point reflecting. -/
theorem a1_isFPR_noetherian [AddGroup.FG M] [IsLocallyNoetherian S] (hTor : TorsionResidue M S)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 U))
    {actU : AAction (fppfO B S hS) M U} {actX : AAction (fppfO B S hS) M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f) : IsFPR hf :=
  thmA1_isFPR hU (chartsOfFiniteType_of_lfp hlfp) hTor hf het

end Local

end

end AlgMag.LimThm

#print axioms AlgMag.LimThm.a1_closed_local
#print axioms AlgMag.LimThm.fixedPoints_eq_fnAll
#print axioms AlgMag.LimThm.a1_closed
#print axioms AlgMag.LimThm.a1_isFPR
#print axioms AlgMag.LimThm.a1_isZFPR
#print axioms AlgMag.LimThm.a1_closed_noetherian
#print axioms AlgMag.LimThm.a1_isFPR_noetherian
