/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCClauses
import AlgMag.AppendixA
import AlgMag.FinalCorBridge

/-!
# Separated ind-algebraic spaces, and Proposition 14.4 with "`X` separated" as printed

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §14. After Definition 14.3 the print says
that a map of ind-algebraic spaces has a property `P` if it is representable and all its pullbacks along
schemes `T → Y` have `P`. For the diagonal `X → X ×_S X` and `P` = closed immersion, with `X` a functor on
`(Aff/S)`, this is `IsSeparatedInd`: for an affine `T` and `x, y ∈ X(T)` the locus `{x = y}` is represented,
on affine test schemes, by a closed subscheme of `T`.

* `isSeparatedInd_iff`: for an algebraic space this is the usual separatedness.
* `isSeparatedOver_term`: every term of a presentation of a separated ind-algebraic space is separated (the
  maps `X_i → X` are monomorphisms, since the transition maps are closed immersions).
* `prop144_sep`, `prop144_scheme_sep`: Proposition 14.4, first and second assertions, alternative "`X` separated".
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u w

namespace AlgMag.Unrestrict

open AlgMag AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


variable (B S hS) in
/-- **Separated ind-algebraic space** (§14, the diagonal `X → X ×_S X` has the property "closed immersion" in
the sense following Definition 14.3): for an affine `T` and `x, y ∈ X(T)` there is a closed immersion
`W → T` through which an affine `T' → T` factors exactly when `x` and `y` agree on `T'`. -/
def IsSeparatedInd (X : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (T : BigAffineFppf B S hS) (x y : X.obj (op T)), ∃ (W : BigFppfOver B S hS) (p : W ⟶ (BigAffineFppf.inclusion B S hS).obj T),
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p) ∧
      ∀ (T' : BigAffineFppf B S hS) (t : T' ⟶ T), (X.map t.op x = X.map t.op y ↔ ∃ l : (BigAffineFppf.inclusion B S hS).obj T' ⟶ W, l ≫ p = (BigAffineFppf.inclusion B S hS).map t)

section Lemmas

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Factorization through a closed immersion, from affine test objects to all test objects (affine cover and
gluing in the sheaf `yoneda W`). -/
lemma factor_of_affine {Z W : BigFppfOver B S hS} (p : W ⟶ Z) (hp : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p))
    {a b : F.obj (op Z)}
    (h : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) → ∀ r : V ⟶ Z, F.map r.op a = F.map r.op b → ∃ l, l ≫ p = r)
    (V : BigFppfOver B S hS) (r : V ⟶ Z) (hr : F.map r.op a = F.map r.op b) : ∃ l, l ≫ p = r := by
  have hmono : Mono p := ⟨fun g g' e => site_hom_ext (by
    have := congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) e
    simp only [Functor.map_comp] at this
    exact (cancel_mono _).1 this)⟩
  obtain ⟨I, U, π, hU, hcov⟩ := exists_affine_cover V
  have hl : ∀ k, ∃ l, l ≫ p = π k ≫ r := fun k => h _ (hU k) _ (by
    simp only [op_comp, Functor.map_comp_apply, hr])
  choose l hl using hl
  have hY : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj W) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp (isAlgebraicSpace_yoneda B S hS W).isSheaf
  have hZs : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj Z) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp (isAlgebraicSpace_yoneda B S hS Z).isSheaf
  have hsf := (Presieve.isSheafFor_iff_generate _).mpr (hY _ hcov)
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf l (by
    intro i j U' gi gj e
    change gi ≫ l i = gj ≫ l j
    refine hmono.right_cancellation _ _ ?_
    rw [Category.assoc, Category.assoc, hl, hl, ← Category.assoc, ← Category.assoc, e])
  refine ⟨t, ?_⟩
  have hsZ := (Presieve.isSheafFor_iff_generate _).mpr (hZs _ hcov)
  obtain ⟨t', -, hu⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsZ (fun k => π k ≫ r) (by
    intro i j U' gi gj e
    change gi ≫ π i ≫ r = gj ≫ π j ≫ r
    rw [← Category.assoc, ← Category.assoc, e])
  have h1 : t ≫ p = t' := hu _ fun k => by
    change π k ≫ t ≫ p = π k ≫ r
    have := ht k
    change π k ≫ t = l k at this
    rw [← Category.assoc, this, hl]
  have h2 : r = t' := hu _ fun k => rfl
  exact h1.trans h2.symm

/-- The pullback of the diagonal along `(a, b) : Z → F ×_S F` is the subobject through which exactly the
`r` with `a|_r = b|_r` factor. -/
lemma isPullback_diag {Z W : BigFppfOver B S hS} (p : W ⟶ Z) (hp : Mono p) {a b : F.obj (op Z)}
    (hpab : F.map p.op a = F.map p.op b)
    (hfac : ∀ (V : BigFppfOver B S hS) (r : V ⟶ Z), F.map r.op a = F.map r.op b → ∃ l, l ≫ p = r)
    (g : yoneda.obj Z ⟶ pullback (toBase F) (toBase F))
    (h1 : g ≫ pullback.fst _ _ = yonedaEquiv.symm a) (h2 : g ≫ pullback.snd _ _ = yonedaEquiv.symm b) :
    IsPullback (yonedaEquiv.symm (F.map p.op a)) (yoneda.map p) (pullback.diagonal (toBase F)) g := by
  have hq : yoneda.map p ≫ yonedaEquiv.symm a = yonedaEquiv.symm (F.map p.op a) := yoneda_map_comp_symm p a
  have hq' : yoneda.map p ≫ yonedaEquiv.symm b = yonedaEquiv.symm (F.map p.op a) := by
    rw [yoneda_map_comp_symm, hpab]
  have comm : yonedaEquiv.symm (F.map p.op a) ≫ pullback.diagonal (toBase F) = yoneda.map p ≫ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h1, hq, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, h2, hq', pullback.diagonal_snd, Category.comp_id]
  have pt : ∀ (s : PullbackCone (pullback.diagonal (toBase F)) g) (V : (BigFppfOver B S hS)ᵒᵖ) (x : s.pt.obj V),
      F.map (s.snd.app V x).op a = F.map (s.snd.app V x).op b := by
    intro s V x
    have e1 : s.fst = s.snd ≫ yonedaEquiv.symm a := by
      have := s.condition =≫ pullback.fst _ _
      rwa [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, h1] at this
    have e2 : s.fst = s.snd ≫ yonedaEquiv.symm b := by
      have := s.condition =≫ pullback.snd _ _
      rwa [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, h2] at this
    have := ConcreteCategory.congr_hom (NatTrans.congr_app (e1.symm.trans e2) V) x
    simpa [yonedaEquiv_symm_app_apply] using this
  let L : ∀ s : PullbackCone (pullback.diagonal (toBase F)) g, s.pt ⟶ yoneda.obj W := fun s =>
    { app := fun V => ↾ fun x => Classical.choose (hfac V.unop _ (pt s V x))
      naturality := fun V V' f => by
        ext1
        refine DFunLike.ext _ _ fun x => ?_
        refine hp.right_cancellation _ _ ?_
        change Classical.choose (hfac V'.unop _ (pt s V' _)) ≫ p =
          (f.unop ≫ Classical.choose (hfac V.unop _ (pt s V x))) ≫ p
        rw [Category.assoc, Classical.choose_spec (hfac _ _ (pt s V' _)),
          Classical.choose_spec (hfac _ _ (pt s V x))]
        exact ConcreteCategory.congr_hom (s.snd.naturality f) x }
  have hL : ∀ s V x, (L s).app V x ≫ p = s.snd.app V x := fun s V x =>
    Classical.choose_spec (hfac V.unop _ (pt s V x))
  have fr : ∀ s, L s ≫ yoneda.map p = s.snd := fun s => by
    ext V x
    exact hL s V x
  refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm L (fun s => ?_) fr (fun s m _ hm => ?_)⟩⟩
  · have e1 : s.fst = s.snd ≫ yonedaEquiv.symm a := by
      have := s.condition =≫ pullback.fst _ _
      rwa [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, h1] at this
    rw [e1, ← fr s, Category.assoc, hq]
  · ext V x
    refine hp.right_cancellation _ _ ?_
    have := ConcreteCategory.congr_hom (NatTrans.congr_app hm V) x
    change (m.app V x) ≫ p = s.snd.app V x at this
    exact this.trans (hL s V x).symm

/-- A presheaf `F` on the site whose affine points inject naturally into a separated ind-algebraic space is
separated, if it is an algebraic space. -/
theorem isSeparatedOver_of_inj {X : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type w} (hX : IsSeparatedInd B S hS X)
    (hF : IsAlgebraicSpace B S hS F) (φ : ∀ T : BigAffineFppf B S hS, F.obj (op ((BigAffineFppf.inclusion B S hS).obj T)) → X.obj (op T))
    (hφ : ∀ T, Function.Injective (φ T))
    (hnat : ∀ {T T' : BigAffineFppf B S hS} (t : T' ⟶ T) (x : F.obj (op ((BigAffineFppf.inclusion B S hS).obj T))),
      φ T' (F.map ((BigAffineFppf.inclusion B S hS).map t).op x) = X.map t.op (φ T x)) :
    AlgMag.IsSeparatedOver F := by
  have hFs : Presieve.IsSheaf (BigFppfOver.topology B S hS) F :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hF.isSheaf
  have hG : IsAlgebraicSpace B S hS (pullback (toBase F) (toBase F)) :=
    isAlgebraicSpace_pullback B S hS _ _ hF hF (isAlgebraicSpace_yoneda B S hS _)
  refine Space.presheaf_of_affineBaseChange B S hS (P := @AlgebraicGeometry.IsClosedImmersion) inferInstance
    hF hG fun Z hZ g => ?_
  let T : BigAffineFppf B S hS := ⟨Z, hZ⟩
  let a : F.obj (op Z) := yonedaEquiv (g ≫ pullback.fst _ _)
  let b : F.obj (op Z) := yonedaEquiv (g ≫ pullback.snd _ _)
  obtain ⟨W, p, hp, hiff⟩ := hX T (φ T a) (φ T b)
  have := hp
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map p)
  have hmono : Mono p := ⟨fun g g' e => site_hom_ext (by
    have := congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) e
    simp only [Functor.map_comp] at this
    exact (cancel_mono _).1 this)⟩
  have key : ∀ (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (r : V ⟶ Z),
      F.map r.op a = F.map r.op b ↔ ∃ l, l ≫ p = r := by
    intro V hV r
    let t : (⟨V, hV⟩ : BigAffineFppf B S hS) ⟶ T := ObjectProperty.homMk r
    have := hiff ⟨V, hV⟩ t
    rw [← hnat t a, ← hnat t b] at this
    exact ((hφ _).eq_iff).symm.trans this
  have hpab : F.map p.op a = F.map p.op b := (key W inferInstance p).2 ⟨𝟙 _, Category.id_comp _⟩
  refine ⟨W, p, yonedaEquiv.symm (F.map p.op a), isPullback_diag p hmono hpab
    (fun V r hr => factor_of_affine p hp (fun V hV r hr => (key V hV r).1 hr) V r hr) g
    (by simp [a]) (by simp [b]), hp⟩

end Lemmas

variable (B S hS) in
/-- The ind-algebraic space underlying an algebraic space: its restriction to `(Aff/S)`. -/
abbrev restrictAff (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u := (BigAffineFppf.inclusion B S hS).op ⋙ F

/-- For an algebraic space, `IsSeparatedInd` of its restriction to `(Aff/S)` is separatedness. -/
theorem isSeparatedInd_iff {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    IsSeparatedInd B S hS (restrictAff B S hS F) ↔ Space.IsSeparatedOver B S hS F := by
  rw [isSeparatedOver_iff_space]
  constructor
  · intro h
    exact isSeparatedOver_of_inj h hF (fun _ x => x) (fun _ => Function.injective_id) (fun _ _ => rfl)
  · intro h T x y
    obtain ⟨E, e, he, hxy, hfac⟩ := exists_equalizer h x y
    refine ⟨E, e, he, fun T' t => ⟨fun h' => hfac _ h', ?_⟩⟩
    rintro ⟨l, hl⟩
    change F.map ((BigAffineFppf.inclusion B S hS).map t).op x = F.map ((BigAffineFppf.inclusion B S hS).map t).op y
    rw [← hl, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hxy]

section Prop144

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {Xi : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P Xi}

/-- The terms of a presentation of a separated ind-algebraic space are separated: `X_i(T) → X(T)` is injective
because the transition maps are closed immersions. -/
theorem isSeparatedOver_term (hsep : IsSeparatedInd B S hS Xi) (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i))
    (i : p.I) : Space.IsSeparatedOver B S hS (p.obj i) := by
  refine isSeparatedOver_iff_space.2 (isSeparatedOver_of_inj hsep (hX i) (p.π i) (fun T x x' h => ?_)
    (fun t x => p.π_map i t x))
  obtain ⟨j, hij, he⟩ := p.inj i T x x' h
  exact isClosedImm_injective (p.closed hij) he

/-- **Proposition 14.4**, first and second assertions, alternative "`X` separated", as printed: `M` a finitely
generated abelian group, `X = colim X_i` a separated ind-algebraic space with an ind-action of `D(M)`, terms
locally of finite presentation, `S` arbitrary, `N` an arbitrary magnet. Then the attractor functor is the
ind-algebraic space `colim X_i^N`, and `X^N → X` is representable by algebraic spaces. -/
theorem prop144_sep (a : IndAction M p) (N : AddSubmonoid M) (hsep : IsSeparatedInd B S hS Xi)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i))
    (hfp : ∀ i, Space.IsLocallyOfFinitePresentation B S hS (terminal.from (p.obj i))) :
    haveI : Countable M := countable_of_fg83
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) ∧
      IndAttractorMapHasPropNat a N (fun {Z' _} _ => IsAlgebraicSpace B S hS Z') :=
  haveI : Countable M := countable_of_fg83
  ⟨prop144_general B.contains_terminal (contains_zmon_of_countable hS M) a N hX (isSeparatedOver_term hsep hX) hfp,
    prop144_rep_general B.contains_terminal (contains_zmon_of_countable hS M) a hX (isSeparatedOver_term hsep hX)
      hfp N⟩

/-- **Proposition 14.4**, resp. ind-schemes, first and second assertions, alternative "`X` separated", as
printed. -/
theorem prop144_scheme_sep (a : IndAction M p) (N : AddSubmonoid M) (hsep : IsSeparatedInd B S hS Xi)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i))
    (hfp : ∀ i, Space.IsLocallyOfFinitePresentation B S hS (terminal.from (p.obj i)))
    (hS' : ∀ i, ∃ U : BigFppfOver B S hS, Nonempty (p.obj i ≅ yoneda.obj U)) :
    haveI : Countable M := countable_of_fg83
    IsIndScheme.{u, v} (attractor a.toAction N) ∧
      IndAttractorMapHasPropNat a N
        (fun {Z' _} _ => ∃ U : BigFppfOver B S hS, Nonempty (Z' ≅ yoneda.obj U)) :=
  haveI : Countable M := countable_of_fg83
  prop144_scheme_general B.contains_terminal (contains_zmon_of_countable hS M) a hX (isSeparatedOver_term hsep hX)
    hfp N hS'

end Prop144

end AlgMag.Unrestrict

#print axioms AlgMag.Unrestrict.isSeparatedInd_iff
#print axioms AlgMag.Unrestrict.prop144_sep
#print axioms AlgMag.Unrestrict.prop144_scheme_sep
