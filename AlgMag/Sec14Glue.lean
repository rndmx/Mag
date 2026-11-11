/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec14Final
import StacksFrontier.AlgebraicGeometry.Spaces.AtlasLocalAtSource
import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
import StacksFrontier.AlgebraicGeometry.Descent.ZariskiCoverSizeBound
import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic

/-!
# Algebraic Magnetism, Remark 14.2: closure under fibre products, by gluing

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Remark 14.2: "The categories of
ind-algebraic spaces and ind-schemes are closed under fiber product."

Without quasi-compactness a term `X_i` need not map to one `Z_k`. The term of the fibre product is
then the locus `W_{ij} ⊆ X_i ×_S Y_j` where the two maps to `Z` agree on affine schemes. On an affine
chart of `X_i ×_S Y_j` the two maps do land in one `Z_k`, so `W_{ij}` is there represented through the
diagonal of `Z_k`; these pieces are glued in a disjoint union, which is an atlas of `W_{ij}`.

* `AlgMag.isAlgebraicSpace_eqLocus`: the locus is an algebraic space.
* `AlgMag.isIndAlgebraicSpace_fibreProduct_of_gluing`, `AlgMag.isIndScheme_fibreProduct_of_gluing`:
  Remark 14.2, with no quasi-compactness.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "AFF" => BigAffineFppf B S hS
local notation "incl" => BigAffineFppf.inclusion B S hS
local notation "SITE" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS

section EqLocus

variable {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {Z : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u}
  {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (φ ψ : ∀ A : (BigAffineFppf B S hS),
    G.obj (op ((BigAffineFppf.inclusion B S hS).obj A)) → Z.obj (op A))

/-- `x ∈ G(T)` lies in the equality locus: `φ` and `ψ` agree on all affine schemes over `T`. -/
def EqAt {T : SITE} (x : G.obj (op T)) : Prop :=
  ∀ (A : AFF) (s : (incl).obj A ⟶ T), φ A (G.map s.op x) = ψ A (G.map s.op x)

variable {φ ψ} in
lemma EqAt.res {T T' : SITE} {x : G.obj (op T)} (h : EqAt φ ψ x) (g : T' ⟶ T) :
    EqAt φ ψ (G.map g.op x) := by
  intro A s
  have := h A (s ≫ g)
  rwa [op_comp, Functor.map_comp] at this

/-- The equality locus of `φ` and `ψ`, a subfunctor of `G`. -/
def eqLocus : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj T := {x : G.obj T // EqAt φ ψ (T := unop T) x}
  map {T T'} g := ↾ fun x => ⟨G.map g x.1, x.2.res g.unop⟩
  map_id T := by
    ext x
    change G.map (𝟙 T) x.1 = x.1
    simp
  map_comp f g := by
    ext x
    change G.map (f ≫ g) x.1 = G.map g (G.map f x.1)
    simp

/-- The inclusion of the equality locus. -/
def eqLocusι : eqLocus φ ψ ⟶ G where
  app _ := ↾ fun x => x.1
  naturality _ _ _ := rfl

instance : Mono (eqLocusι φ ψ) :=
  (NatTrans.mono_iff_mono_app _).2 fun _ =>
    (mono_iff_injective _).2 fun _ _ h => Subtype.ext h

variable (pZ : IndPresentation.{u, v, u} P Z)
  (hZ : ∀ k, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pZ.obj k))
  {φ ψ}
  (hφ : ∀ {A A' : BigAffineFppf B S hS} (s : A' ⟶ A)
    (x : G.obj (op ((BigAffineFppf.inclusion B S hS).obj A))),
    φ A' (G.map ((BigAffineFppf.inclusion B S hS).map s).op x) = Z.map s.op (φ A x))
  (hψ : ∀ {A A' : BigAffineFppf B S hS} (s : A' ⟶ A)
    (x : G.obj (op ((BigAffineFppf.inclusion B S hS).obj A))),
    ψ A' (G.map ((BigAffineFppf.inclusion B S hS).map s).op x) = Z.map s.op (ψ A x))

include hZ hφ hψ in
/-- Comparison in one term: over `A` affine, lifts `a`, `b` of `φ(x)`, `ψ(x)` to `Z_k`. For `t : T → A`,
`x|_T` lies in the locus iff `a|_T = b|_T`. -/
theorem eqAt_iff {A : AFF} (x : G.obj (op ((incl).obj A))) {k : pZ.I}
    {a b : (pZ.obj k).obj (op ((incl).obj A))} (ha : pZ.π k A a = φ A x) (hb : pZ.π k A b = ψ A x)
    {T : SITE} (t : T ⟶ (incl).obj A) :
    EqAt φ ψ (G.map t.op x) ↔ (pZ.obj k).map t.op a = (pZ.obj k).map t.op b := by
  have key : ∀ (A' : AFF) (s : (incl).obj A' ⟶ T),
      φ A' (G.map s.op (G.map t.op x)) = pZ.π k A' ((pZ.obj k).map (s ≫ t).op a) ∧
      ψ A' (G.map s.op (G.map t.op x)) = pZ.π k A' ((pZ.obj k).map (s ≫ t).op b) := by
    intro A' s
    have e : G.map s.op (G.map t.op x) = G.map ((incl).map (indAffHom (s ≫ t))).op x := by
      change _ = G.map (s ≫ t).op x
      rw [op_comp, Functor.map_comp]
      rfl
    rw [e, hφ, hψ, ← ha, ← hb, ← pZ.π_map, ← pZ.π_map]
    exact ⟨rfl, rfl⟩
  constructor
  · intro h
    refine ind_sep_affine (hZ k) fun A' s => ind_π_injective pZ k A' ?_
    have e₁ := (key A' s).1
    have e₂ := (key A' s).2
    rw [op_comp, Functor.map_comp] at e₁ e₂
    exact e₁.symm.trans ((h A' s).trans e₂)
  · intro h A' s
    rw [(key A' s).1, (key A' s).2, op_comp, Functor.map_comp]
    exact congrArg _ (congrArg ((pZ.obj k).map s.op) h)

include hZ hφ hψ in
/-- The locus is local on the site. -/
theorem eqAt_of_cover {T : SITE} (x : G.obj (op T)) {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T)
    (h : ∀ {W : SITE} (g : W ⟶ T), R g → EqAt φ ψ (G.map g.op x)) : EqAt φ ψ x := by
  intro A s
  obtain ⟨i, a₀, ha₀⟩ := pZ.surj A (φ A (G.map s.op x))
  obtain ⟨j, b₀, hb₀⟩ := pZ.surj A (ψ A (G.map s.op x))
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have ha : pZ.π k A ((pZ.tr hik).app _ a₀) = _ := (pZ.π_tr hik A _).trans ha₀
  have hb : pZ.π k A ((pZ.tr hjk).app _ b₀) = _ := (pZ.π_tr hjk A _).trans hb₀
  have e : (pZ.tr hik).app _ a₀ = (pZ.tr hjk).app _ b₀ := by
    refine (hZ k _ ((BigFppfOver.topology B S hS).pullback_stable s hR)).isSeparatedFor.ext ?_
    intro W g hg
    have h₀ := h (g ≫ s) hg
    have e₀ : G.map (g ≫ s).op x = G.map g.op (G.map s.op x) := by
      rw [op_comp, Functor.map_comp]
      rfl
    rw [e₀] at h₀
    exact (eqAt_iff pZ hZ hφ hψ _ ha hb g).1 h₀
  rw [← ha, ← hb, e]

include hZ hφ hψ in
theorem isSheaf_eqLocus (hG : Presieve.IsSheaf (BigFppfOver.topology B S hS) G) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) (eqLocus φ ψ) := by
  intro T R hR fam hfam
  let fam' : Presieve.FamilyOfElements G R := fun W g hg => (fam g hg).1
  have hc : fam'.Compatible := fun Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ comm =>
    congrArg Subtype.val (hfam g₁ g₂ h₁ h₂ comm)
  let t := (hG _ hR).amalgamate fam' hc
  have ht : ∀ {W : SITE} (g : W ⟶ T) (hg : R g), G.map g.op t = (fam g hg).1 :=
    fun g hg => (hG _ hR).valid_glue hc g hg
  have hm : EqAt φ ψ t := eqAt_of_cover pZ hZ hφ hψ t hR fun g hg => by
    rw [ht g hg]
    exact (fam g hg).2
  refine ⟨⟨t, hm⟩, fun W g hg => Subtype.ext (ht g hg), ?_⟩
  rintro y hy
  refine Subtype.ext ((hG _ hR).isSeparatedFor.ext fun W g hg => ?_)
  exact (congrArg Subtype.val (hy g hg)).trans (ht g hg).symm

include hZ hφ hψ in
/-- The chart `V → A` of the locus over an affine `x : A → G`. -/
theorem exists_eqLocus_chart
    (hZa : ∀ k, yoneda.relativelyRepresentable (Limits.diag (pZ.obj k)))
    {A : AFF} (x : G.obj (op ((incl).obj A))) :
    ∃ (V : SITE) (m : V ⟶ (incl).obj A), Mono m ∧ ∀ {T : SITE} (t : T ⟶ (incl).obj A),
      EqAt φ ψ (G.map t.op x) ↔ ∃ l : T ⟶ V, l ≫ m = t := by
  obtain ⟨i, a₀, ha₀⟩ := pZ.surj A (φ A x)
  obtain ⟨j, b₀, hb₀⟩ := pZ.surj A (ψ A x)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have ha : pZ.π k A ((pZ.tr hik).app _ a₀) = _ := (pZ.π_tr hik A _).trans ha₀
  have hb : pZ.π k A ((pZ.tr hjk).app _ b₀) = _ := (pZ.π_tr hjk A _).trans hb₀
  set a := (pZ.tr hik).app _ a₀
  set b := (pZ.tr hjk).app _ b₀
  let g : yoneda.obj ((incl).obj A) ⟶ pZ.obj k ⨯ pZ.obj k :=
    prod.lift (yonedaEquiv.symm a) (yonedaEquiv.symm b)
  have hsq := (hZa k).isPullback g
  let m := (hZa k).snd g
  have hmono : Mono (yoneda.map m) := by
    haveI : Mono (Limits.diag (pZ.obj k)) := by
      dsimp [Limits.diag]
      infer_instance
    exact ⟨fun h₁ h₂ e => hsq.hom_ext ((cancel_mono (Limits.diag (pZ.obj k))).1 (by
      rw [Category.assoc, Category.assoc, hsq.w, ← Category.assoc, ← Category.assoc, e])) e⟩
  refine ⟨(hZa k).pullback g, m, yoneda.mono_of_mono_map hmono, fun {T} t => ?_⟩
  rw [eqAt_iff pZ hZ hφ hψ x ha hb t]
  have ev : ∀ {T' : SITE} (t' : T' ⟶ (incl).obj A) (c : (pZ.obj k).obj (op ((incl).obj A))),
      yoneda.map t' ≫ yonedaEquiv.symm c = yonedaEquiv.symm ((pZ.obj k).map t'.op c) := fun t' c => by
    rw [yonedaEquiv_symm_naturality_left]
  constructor
  · intro e
    have w : yonedaEquiv.symm ((pZ.obj k).map t.op a) ≫ Limits.diag (pZ.obj k) = yoneda.map t ≫ g := by
      apply Limits.prod.hom_ext
      · simp [Limits.diag, g, ev t]
      · simp [Limits.diag, g, ev t, e]
    refine ⟨yoneda.preimage (hsq.lift _ _ w), yoneda.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage]
    exact hsq.lift_snd _ _ w
  · rintro ⟨l, rfl⟩
    have w := hsq.w
    have w₁ := congrArg (· ≫ (Limits.prod.fst : pZ.obj k ⨯ pZ.obj k ⟶ _)) w
    have w₂ := congrArg (· ≫ (Limits.prod.snd : pZ.obj k ⨯ pZ.obj k ⟶ _)) w
    simp only [Limits.diag, g, Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id] at w₁ w₂
    have w₃ := w₁.symm.trans w₂
    have w₄ := congrArg (yoneda.map l ≫ ·) w₃
    simp only [← Category.assoc, ← Functor.map_comp] at w₄
    rw [ev (l ≫ m), ev (l ≫ m)] at w₄
    exact yonedaEquiv.symm.injective w₄

include hZ hφ hψ in
/-- **Remark 14.2**, the gluing: from an atlas `p` of `G`, the affine charts of `p` restrict to
charts `k i` of the equality locus, base changes of the charts of `p`, whose disjoint union is
surjective and étale over the locus. -/
theorem exists_eqLocus_gluing (hG : IsAlgebraicSpace B S hS G)
    (hZa : ∀ k, yoneda.relativelyRepresentable (Limits.diag (pZ.obj k)))
    {U₀ : BigFppfOver B S hS} (p : yoneda.obj U₀ ⟶ G)
    (hpS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) p)
    (hpE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) p) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (eqLocus φ ψ) ∧
    yoneda.relativelyRepresentable (Limits.diag (eqLocus φ ψ)) ∧
    ∃ (I : Type u) (W₀ : I → BigFppfOver B S hS) (π₀ : ∀ i, W₀ i ⟶ U₀)
      (V : I → BigFppfOver B S hS) (m : ∀ i, V i ⟶ W₀ i)
      (k : ∀ i, yoneda.obj (V i) ⟶ eqLocus φ ψ) (μ : Cardinal.{u})
      (Y : BigFppfOver B S hS) (c : ∀ i, V i ⟶ Y) (v : yoneda.obj Y ⟶ eqLocus φ ψ),
      Cardinal.mk I < B.cutoff ∧ μ < B.cutoff ∧
      (∀ i, ((BigFppfOver.toScheme B S hS).obj (V i)).size ≤ μ) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (π₀ i))) ∧
      (∀ i, IsPullback (yoneda.map (m i)) (k i) (yoneda.map (π₀ i) ≫ p) (eqLocusι φ ψ)) ∧
      (∀ i, yoneda.map (c i) ≫ v = k i) ∧
      (∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (c i))) ∧
      (∀ z : (BigFppfOver.toScheme B S hS).obj Y,
        ∃ i, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (c i))) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) v ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) v := by
  classical
  have hGs : Presieve.IsSheaf (BigFppfOver.topology B S hS) G :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hG.isSheaf
  have hWs := isSheaf_eqLocus pZ hZ hφ hψ hGs
  have hdiag : yoneda.relativelyRepresentable (Limits.diag (eqLocus φ ψ)) := by
    apply Functor.relativelyRepresentable.diag_of_map_from_obj
    intro a g a' g'
    obtain ⟨b, snd, fst, hpb⟩ := Functor.relativelyRepresentable.of_diag hG.diagonal_representable
      (g ≫ eqLocusι φ ψ) (g' ≫ eqLocusι φ ψ)
    refine ⟨b, snd, fst, ?_⟩
    refine ⟨⟨(cancel_mono (eqLocusι φ ψ)).1 (by simpa using hpb.w)⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => hpb.lift s.fst s.snd (by simp [reassoc_of% s.condition])) ?_ ?_ ?_⟩⟩
    · intro s
      exact hpb.lift_fst _ _ _
    · intro s
      exact hpb.lift_snd _ _ _
    · intro s m h₁ h₂
      exact hpb.hom_ext (h₁.trans (hpb.lift_fst _ _ _).symm) (h₂.trans (hpb.lift_snd _ _ _).symm)
  -- the affine charts of the atlas
  let I : Type u := ((SCH).obj U₀).affineOpens
  have hCI : ∀ i : I, B.Contains (i.1 : Scheme.{u}) := fun i =>
    Scheme.size_lt_of_isOpenImmersion i.1.ι U₀.left.property
  let W : I → SITE := fun i => siteObject B S hS (hCI i) (i.1.ι ≫ U₀.hom.hom)
  let πi : ∀ i, W i ⟶ U₀ := fun i => siteHom i.1.ι rfl
  haveI hWa : ∀ i, IsAffine ((SCH).obj (W i)) := fun i => i.2
  let x₀ : G.obj (op U₀) := yonedaEquiv p
  let xi : ∀ i, G.obj (op ((incl).obj (affOf (W i)))) := fun i => G.map (πi i).op x₀
  choose V m hm hV using fun i => exists_eqLocus_chart pZ hZ hφ hψ hZa (xi i)
  have hvi : ∀ i, EqAt φ ψ (G.map (m i).op (xi i)) := fun i => (hV i (m i)).2 ⟨𝟙 _, by simp⟩
  let vi : ∀ i, (eqLocus φ ψ).obj (op (V i)) := fun i => ⟨G.map (m i).op (xi i), hvi i⟩
  -- the sizes
  have hπmono : ∀ i, Mono (πi i) := fun i => by
    haveI : IsOpenImmersion ((SCH).map (πi i)) := inferInstanceAs (IsOpenImmersion i.1.ι)
    exact (SCH).mono_of_mono_map inferInstance
  have hsize : ∀ i, ((SCH).obj (V i)).size ≤ Space.monoSizeBound B S hS U₀ := fun i => by
    haveI := hm i
    haveI := hπmono i
    exact Space.size_le_monoSizeBound_of_mono B S hS (yoneda.map (m i ≫ πi i)) inferInstance
  let μ : Cardinal.{u} := max (Space.monoSizeBound B S hS U₀) ((SCH).obj U₀).size
  have hμ : μ < B.cutoff := max_lt (Space.monoSizeBound_lt_cutoff B S hS U₀) U₀.left.property
  have hℵ : Cardinal.aleph0 ≤ μ := le_max_of_le_right (Scheme.aleph0_le_size _)
  obtain ⟨Y, c, hco, hdis, hcov⟩ := BigFppfOver.exists_coproduct_of_size_le B S hS V hℵ hμ
    (((SCH).obj U₀).mk_affineOpens_le_size.trans (le_max_right _ _))
    (fun i => (hsize i).trans (le_max_left _ _))
  have hcm : ∀ i, Mono (c i) := fun i => (SCH).mono_of_mono_map (by
    haveI := hco i
    infer_instance)
  -- the map `Y → W`
  have hglue : ∀ {T : SITE} {k k' : I} (a : T ⟶ V k) (a' : T ⟶ V k'), a ≫ c k = a' ≫ c k' →
      (eqLocus φ ψ).map a.op (vi k) = (eqLocus φ ψ).map a'.op (vi k') := by
    intro T k k' a a' e
    by_cases hk : k = k'
    · subst hk
      haveI := hcm k
      rw [(cancel_mono (c k)).1 e]
    · have hemp : IsEmpty ((SCH).obj T) := ⟨fun z => hdis k k' hk ((SCH).map a z) ((SCH).map a' z) (by
        have := congrArg (fun q => (SCH).map q z) e
        simpa using this)⟩
      let E : PEmpty.{u + 1} → SITE := fun e => e.elim
      let fE : ∀ e, E e ⟶ T := fun e => e.elim
      refine (hWs (Sieve.ofArrows E fE) (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS fE
        (fun e => e.elim) (fun z => (hemp.false z).elim))).isSeparatedFor.ext ?_
      rintro _ _ ⟨_, _, _, ⟨e⟩, _⟩
      exact e.elim
  let R : Sieve Y := Sieve.ofArrows V c
  have hR : R ∈ BigFppfOver.topology B S hS Y :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS c hco hcov
  have hval : ∀ {T : SITE} (f : T ⟶ Y), R f → ∃ (k : I) (a : T ⟶ V k), a ≫ c k = f := by
    rintro T f ⟨Z', a, b, ⟨k⟩, rfl⟩
    exact ⟨k, a, rfl⟩
  let fam : Presieve.FamilyOfElements (eqLocus φ ψ) R.arrows := fun T f hf =>
    (eqLocus φ ψ).map (hval f hf).choose_spec.choose.op (vi (hval f hf).choose)
  have hfam : fam.Compatible := by
    intro Y₁ Y₂ T g₁ g₂ f₁ f₂ h₁ h₂ comm
    have s₁ := (hval f₁ h₁).choose_spec.choose_spec
    have s₂ := (hval f₂ h₂).choose_spec.choose_spec
    have := hglue (g₁ ≫ (hval f₁ h₁).choose_spec.choose) (g₂ ≫ (hval f₂ h₂).choose_spec.choose)
      (by rw [Category.assoc, Category.assoc, s₁, s₂, comm])
    rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp] at this
    exact this
  let t := (hWs _ hR).amalgamate fam hfam
  have ht : ∀ {T : SITE} {k : I} (a : T ⟶ V k), (eqLocus φ ψ).map (a ≫ c k).op t =
      (eqLocus φ ψ).map a.op (vi k) := fun {T k} a => by
    have hf : R (a ≫ c k) := ⟨_, a, c k, ⟨k⟩, rfl⟩
    refine ((hWs _ hR).valid_glue hfam _ hf).trans ?_
    exact hglue _ _ (hval _ hf).choose_spec.choose_spec
  let v : yoneda.obj Y ⟶ eqLocus φ ψ := yonedaEquiv.symm t
  have hv : ∀ {T : SITE} (l : T ⟶ Y), (v.app (op T) l) = (eqLocus φ ψ).map l.op t := fun l => rfl
  have hrep : yoneda.relativelyRepresentable v :=
    Functor.relativelyRepresentable.of_diag hdiag v
  have hvk : ∀ k, yoneda.map (c k) ≫ v = yonedaEquiv.symm (vi k) := fun k => by
    rw [yonedaEquiv_symm_naturality_left]
    congr 1
    simpa using ht (𝟙 _)
  have hp : p = yonedaEquiv.symm x₀ := (Equiv.symm_apply_apply _ _).symm
  have hpv : ∀ {T : SITE} (g : T ⟶ U₀), p.app (op T) g = G.map g.op x₀ := fun g => by
    rw [hp]
    rfl
  have hmapc : ∀ {T T' T'' : SITE} (a : T ⟶ T') (b : T' ⟶ T'') (z : G.obj (op T'')),
      G.map (a ≫ b).op z = G.map a.op (G.map b.op z) := fun a b z => by
    rw [op_comp, Functor.map_comp]
    rfl
  -- the pieces are base changes of the affine charts of the atlas
  have hsq : ∀ k, IsPullback (yoneda.map (m k)) (yonedaEquiv.symm (vi k))
      (yoneda.map (πi k) ≫ p) (eqLocusι φ ψ) := fun k => by
    refine IsPullback.of_forall_isPullback_app fun T => ?_
    rw [Types.isPullback_iff]
    have hpt : ∀ u : unop T ⟶ W k, (yoneda.map (πi k) ≫ p).app T u = G.map u.op (xi k) := fun u =>
      (hpv (u ≫ πi k)).trans (hmapc _ _ _)
    refine ⟨?_, ?_, ?_⟩
    · ext a
      exact (hpt (a ≫ m k)).trans (hmapc _ _ _)
    · rintro a a' ⟨e, -⟩
      haveI := hm k
      exact (cancel_mono (m k)).1 e
    · intro u w hw
      have hE : EqAt φ ψ (G.map (Quiver.Hom.unop (op u)).op (xi k)) := by
        have h' : G.map u.op (xi k) = w.1 := (hpt u).symm.trans hw
        change EqAt φ ψ (G.map u.op (xi k))
        rw [h']
        exact w.2
      obtain ⟨l, hl⟩ := (hV k u).1 hE
      refine ⟨l, hl, Subtype.ext ?_⟩
      change G.map l.op (G.map (m k).op (xi k)) = w.1
      rw [← hmapc, hl]
      exact (hpt u).symm.trans hw
  have hce := (Space.isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  have hπe : ∀ k, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (πi k) ≫ p) := fun k => by
    refine MorphismProperty.comp_mem _ _ _ ?_ hpE
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (πi k)).2 ?_
    haveI : IsOpenImmersion ((SCH).map (πi k)) := inferInstanceAs (IsOpenImmersion k.1.ι)
    change Etale ((SCH).map (πi k))
    infer_instance
  have hve : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) v := by
    haveI : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
    refine Space.presheaf_inverseImage_of_isZariskiLocalAtSource B S hS (@Etale.{u}) hrep c hco
      (fun y => hcov y) fun k => ?_
    rw [hvk]
    exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback (hsq k) (hπe k)
  have hvs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) v := by
    refine MorphismProperty.relative_of_snd hrep fun V' ξ => ?_
    change Surjective ((SCH).map (hrep.snd ξ))
    refine ⟨fun t₁ => ?_⟩
    let h := ξ ≫ eqLocusι φ ψ
    let q₀ := hpS.rep.snd h
    let e₀ : hpS.rep.pullback h ⟶ U₀ := yoneda.preimage (hpS.rep.fst h)
    have hq₀ : Surjective ((SCH).map q₀) := hpS.property_snd h
    obtain ⟨t₀, ht₀⟩ := hq₀.surj t₁
    obtain ⟨_, ⟨W', hW', rfl⟩, hx, -⟩ := ((SCH).obj U₀).isBasis_affineOpens.exists_subset_of_mem_open
      (show (SCH).map e₀ t₀ ∈ ((⊤ : ((SCH).obj U₀).Opens) : Set _) from trivial)
      (⊤ : ((SCH).obj U₀).Opens).isOpen
    let i : I := ⟨W', hW'⟩
    let w : (SCH).obj (W i) := ⟨(SCH).map e₀ t₀, hx⟩
    have hw : (SCH).map (πi i) w = (SCH).map e₀ t₀ := rfl
    let _ := B.hasPullbacks_schemes
    let _ := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
    have hsqS := (IsPullback.of_hasPullback (πi i) e₀).map (SCH)
    obtain ⟨z₀, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback w t₀ hw
    let z : (SCH).obj (pullback (πi i) e₀) := hsqS.isoPullback.inv z₀
    have hz₂' : (SCH).map (pullback.snd (πi i) e₀) z = t₀ := by
      rw [← hz₂]
      change (hsqS.isoPullback.inv ≫ (SCH).map (pullback.snd (πi i) e₀)) z₀ = _
      rw [hsqS.isoPullback_inv_snd]
    let u₀ := pullback.fst (πi i) e₀
    let s₀ := pullback.snd (πi i) e₀
    have hc₀ : u₀ ≫ πi i = s₀ ≫ e₀ := pullback.condition
    have hpb : G.map e₀.op x₀ = (ξ.app (op _) q₀).1 := by
      have := congrArg (fun τ => τ.app (op (hpS.rep.pullback h)) (𝟙 _)) (hpS.rep.isPullback h).w
      have hf : hpS.rep.fst h = yoneda.map e₀ := (yoneda.map_preimage _).symm
      rw [hf] at this
      refine ((hpv _).symm.trans ?_).trans this
      simp
    have hmem : G.map u₀.op (xi i) = (ξ.app (op _) (s₀ ≫ q₀)).1 := by
      refine (hmapc _ _ _).symm.trans ?_
      rw [hc₀, hmapc, hpb]
      exact congrArg Subtype.val (hom_naturality_apply ξ s₀.op q₀).symm
    have hE : EqAt φ ψ (G.map u₀.op (xi i)) := by
      rw [hmem]
      exact (ξ.app (op _) (s₀ ≫ q₀)).2
    obtain ⟨l, hl⟩ := (hV i u₀).1 hE
    have hlift : yoneda.map (l ≫ c i) ≫ v = yoneda.map (s₀ ≫ q₀) ≫ ξ := by
      rw [Functor.map_comp, Category.assoc, hvk, yonedaEquiv_symm_naturality_left,
        ← (Equiv.symm_apply_apply yonedaEquiv ξ), yonedaEquiv_symm_naturality_left]
      congr 1
      refine Subtype.ext ?_
      change G.map l.op (G.map (m i).op (xi i)) = _
      rw [← hmapc, hl, hmem]
      have e := hom_naturality_apply ξ (s₀ ≫ q₀).op (𝟙 V')
      refine congrArg Subtype.val (Eq.trans ?_ e)
      congr 1
    let r := yoneda.preimage ((hrep.isPullback ξ).lift _ _ hlift)
    have hr : r ≫ hrep.snd ξ = s₀ ≫ q₀ := yoneda.map_injective (by
      rw [Functor.map_comp, Functor.map_preimage]
      exact (hrep.isPullback ξ).lift_snd _ _ _)
    refine ⟨(SCH).map r z, ?_⟩
    have e := congrArg (fun τ => (SCH).map τ z) hr
    simp only [Functor.map_comp, Scheme.Hom.comp_apply] at e
    rw [e, hz₂', ht₀]
  exact ⟨(isSheaf_iff_isSheaf_of_type _ _).mpr hWs, hdiag, I, W, πi, V, m, _, μ, Y, c, v,
    ((SCH).obj U₀).mk_affineOpens_le_size.trans_lt U₀.left.property, hμ,
    fun i => (hsize i).trans (le_max_left _ _),
    fun i => inferInstanceAs (IsOpenImmersion i.1.ι), hsq, hvk, hco, hcov, hvs, hve⟩

include hZ hφ hψ in
/-- **Remark 14.2**, the gluing: the equality locus of two maps from an algebraic space to an
ind-algebraic space is an algebraic space. -/
theorem isAlgebraicSpace_eqLocus (hG : IsAlgebraicSpace B S hS G)
    (hZa : ∀ k, yoneda.relativelyRepresentable (Limits.diag (pZ.obj k))) :
    IsAlgebraicSpace B S hS (eqLocus φ ψ) := by
  obtain ⟨U₀, p, hpS, hpE⟩ := hG.exists_atlas
  obtain ⟨hs, hd, -, -, -, -, -, -, -, Y, -, v, -, -, -, -, -, -, -, -, hvs, hve⟩ :=
    exists_eqLocus_gluing pZ hZ hφ hψ hG hZa p hpS hpE
  exact ⟨hs, hd, Y, v, hvs, hve⟩

include hZ hφ hψ in
/-- **Remark 14.2** for ind-schemes, the gluing: the equality locus of two maps from a scheme to an
ind-scheme is a scheme, by gluing its affine charts along their open immersions (Stacks 01JJ). -/
theorem representable_eqLocus {U₀ : BigFppfOver B S hS} (e : G ≅ yoneda.obj U₀)
    (hG : IsAlgebraicSpace B S hS G)
    (hZa : ∀ k, yoneda.relativelyRepresentable (Limits.diag (pZ.obj k))) :
    (eqLocus φ ψ).IsRepresentable := by
  classical
  have hyS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (𝟙 U₀)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
      (by change Surjective ((SCH).map (𝟙 U₀)); rw [(SCH).map_id]; infer_instance)
  have hyE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (𝟙 U₀)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2
      (by change Etale ((SCH).map (𝟙 U₀)); rw [(SCH).map_id]; infer_instance)
  have hsq₀ : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ yoneda.obj U₀),
      IsPullback (𝟙 F) (a ≫ e.inv) a e.hom := fun a =>
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hpS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) e.inv := by
    have h := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hsq₀ (yoneda.map (𝟙 U₀))) hyS
    simpa using h
  have hpE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) e.inv := by
    have h := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hsq₀ (yoneda.map (𝟙 U₀))) hyE
    simpa using h
  obtain ⟨hs, -, I, W₀, π₀, V, m, k, μ, Y, c, v, hI, hμ, hsize, hπ, hsq, hvk, hco, hcov, hvs, hve⟩ :=
    exists_eqLocus_gluing pZ hZ hφ hψ hG hZa e.inv hpS hpE
  have hk : ∀ i, Space.IsOpenImmersion B S hS (k i) := fun i => by
    have h₁ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (π₀ i)) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 (hπ i)
    have h₂ := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hsq₀ (yoneda.map (π₀ i))) h₁
    exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback (hsq i) h₂
  have hls := Space.isLocallySurjective_of_presheafSurjective_etale v hvs hve
  have hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k) := by
    refine ⟨fun {T} s => ?_⟩
    refine (BigFppfOver.topology B S hS).transitive (hls.imageSieve_mem s) _ ?_
    rintro T' g ⟨y, hy⟩
    have hR : Sieve.ofArrows V c ∈ BigFppfOver.topology B S hS Y :=
      BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS c hco hcov
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      ((BigFppfOver.topology B S hS).pullback_stable y hR)
    rintro T'' a ⟨_, b, _, ⟨i⟩, hab⟩
    refine ⟨(Sigma.ι (fun i => yoneda.obj (V i)) i).app (op T'') b, ?_⟩
    have e₁ : (Sigma.ι (fun i => yoneda.obj (V i)) i ≫ Sigma.desc k).app (op T'') b = (k i).app _ b := by
      rw [Sigma.ι_desc]
    refine e₁.trans ?_
    have e₂ : (k i).app (op T'') b = v.app (op T'') (b ≫ c i) := by
      rw [← hvk i]
      rfl
    refine e₂.trans ?_
    rw [hab]
    have e₃ := hom_naturality_apply v a.op y
    refine Eq.trans (congrArg _ rfl) (e₃.trans ?_)
    rw [hy, op_comp, Functor.map_comp]
    rfl
  exact isRepresentable_of_zariskiCover_of_size_le B S hS hs hI hμ V hsize k hk hsurj

end EqLocus

section Fibre

/-- The structure morphism to the base `S`, as a representable presheaf. -/
noncomputable def toBaseSpace (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))) where
  app U := ↾ fun _ => Over.mkIdTerminal.from (unop U)
  naturality _ _ _ := by
    ext x
    exact Over.mkIdTerminal.hom_ext _ _

variable {X Y Z : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u}
  {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
  (pX : IndPresentation.{u, v, u} P X)
  (pY : IndPresentation.{u, v, u} P Y)
  (pZ : IndPresentation.{u, v, u} P Z) (f : X ⟶ Z) (g : Y ⟶ Z)

/-- `X_i ×_S Y_j`. -/
noncomputable abbrev prodTerm (q : pX.I × pY.I) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  fibreProduct (toBaseSpace (pX.obj q.1)) (toBaseSpace (pY.obj q.2))

/-- The first map `X_i ×_S Y_j → Z`, on affine schemes. -/
def prodφ (q : pX.I × pY.I) (A : AFF) (x : (prodTerm pX pY q).obj (op ((incl).obj A))) : Z.obj (op A) :=
  f.app _ (pX.π q.1 A x.1.1)

/-- The second map `X_i ×_S Y_j → Z`, on affine schemes. -/
def prodψ (q : pX.I × pY.I) (A : AFF) (x : (prodTerm pX pY q).obj (op ((incl).obj A))) : Z.obj (op A) :=
  g.app _ (pY.π q.2 A x.1.2)

/-- The term `W_{ij} ⊆ X_i ×_S Y_j` of the fibre product. -/
noncomputable abbrev fibreTerm (q : pX.I × pY.I) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  eqLocus (prodφ pX pY f q) (prodψ pX pY g q)

/-- The transition maps of `X_i ×_S Y_j`. -/
noncomputable def prodTr {q q' : pX.I × pY.I} (h : q ≤ q') : prodTerm pX pY q ⟶ prodTerm pX pY q' where
  app W := ↾ fun p => ⟨((pX.tr h.1).app W p.1.1, (pY.tr h.2).app W p.1.2),
    Over.mkIdTerminal.hom_ext _ _⟩
  naturality W W' s := by
    ext p
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact hom_naturality_apply (pX.tr h.1) s p.1.1
    · exact hom_naturality_apply (pY.tr h.2) s p.1.2

lemma eqAt_prodTr_iff {q q' : pX.I × pY.I} (h : q ≤ q') {T : SITE} (x : (prodTerm pX pY q).obj (op T)) :
    EqAt (prodφ pX pY f q') (prodψ pX pY g q') ((prodTr pX pY h).app _ x) ↔
      EqAt (prodφ pX pY f q) (prodψ pX pY g q) x := by
  refine forall₂_congr fun A s => ?_
  have e : (prodTerm pX pY q').map s.op ((prodTr pX pY h).app _ x) =
      (prodTr pX pY h).app _ ((prodTerm pX pY q).map s.op x) :=
    (hom_naturality_apply (prodTr pX pY h) s.op x).symm
  rw [e]
  change f.app _ (pX.π q'.1 A ((pX.tr h.1).app _ _)) = g.app _ (pY.π q'.2 A ((pY.tr h.2).app _ _)) ↔ _
  rw [pX.π_tr, pY.π_tr]
  rfl

/-- The transition maps of the terms. -/
noncomputable def fibreTr {q q' : pX.I × pY.I} (h : q ≤ q') :
    fibreTerm pX pY f g q ⟶ fibreTerm pX pY f g q' where
  app W := ↾ fun p => ⟨(prodTr pX pY h).app W p.1, (eqAt_prodTr_iff pX pY f g h p.1).2 p.2⟩
  naturality W W' s := by
    ext p
    refine Subtype.ext ?_
    exact hom_naturality_apply (prodTr pX pY h) s p.1

theorem isClosedImm_fibreTr {q q' : pX.I × pY.I} (h : q ≤ q') : IsClosedImm (fibreTr pX pY f g h) := by
  have c₀ : IsClosedImm (prodTr pX pY h) :=
    isClosedImm_fibre_map (pX.tr h.1) (pY.tr h.2) (pX.closed h.1) (pY.closed h.2)
      (fun W x y => ⟨fun _ => Over.mkIdTerminal.hom_ext _ _, fun _ => Over.mkIdTerminal.hom_ext _ _⟩)
      _ (fun _ _ => rfl)
  have sq : IsPullback (eqLocusι _ _) (fibreTr pX pY f g h) (prodTr pX pY h) (eqLocusι _ _) := by
    refine IsPullback.of_forall_isPullback_app fun W => ?_
    rw [Types.isPullback_iff]
    refine ⟨rfl, ?_, ?_⟩
    · rintro a a' ⟨e, -⟩
      exact Subtype.ext e
    · intro u w hw
      refine ⟨⟨u, (eqAt_prodTr_iff pX pY f g h u).1 ?_⟩, rfl, Subtype.ext hw⟩
      change EqAt _ _ ((prodTr pX pY h).app W u)
      have hw' : (prodTr pX pY h).app W u = w.1 := hw
      rw [hw']
      exact w.2
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq c₀

lemma prodφ_map (q : pX.I × pY.I) {A A' : AFF} (s : A' ⟶ A)
    (x : (prodTerm pX pY q).obj (op ((incl).obj A))) :
    prodφ pX pY f q A' ((prodTerm pX pY q).map ((incl).map s).op x) =
      Z.map s.op (prodφ pX pY f q A x) := by
  change f.app _ (pX.π q.1 A' ((pX.obj q.1).map _ x.1.1)) = _
  rw [pX.π_map]
  exact hom_naturality_apply f s.op _

lemma prodψ_map (q : pX.I × pY.I) {A A' : AFF} (s : A' ⟶ A)
    (x : (prodTerm pX pY q).obj (op ((incl).obj A))) :
    prodψ pX pY g q A' ((prodTerm pX pY q).map ((incl).map s).op x) =
      Z.map s.op (prodψ pX pY g q A x) := by
  change g.app _ (pY.π q.2 A' ((pY.obj q.2).map _ x.1.2)) = _
  rw [pY.π_map]
  exact hom_naturality_apply g s.op _

/-- The presentation `X ×_Z Y = colim W_{ij}` of the fibre product, for any property `P` holding for
the terms `W_{ij}`. No quasi-compactness is assumed. -/
theorem exists_indPresentation_fibreProduct_of_gluing (hP : ∀ q, P (fibreTerm pX pY f g q)) :
    Nonempty (IndPresentation.{u, v, u} P (fibreProduct f g)) := by
  have : IsDirectedOrder (pX.I × pY.I) := ⟨fun q q' => by
    obtain ⟨i, h₁, h₂⟩ := exists_ge_ge q.1 q'.1
    obtain ⟨j, h₃, h₄⟩ := exists_ge_ge q.2 q'.2
    exact ⟨(i, j), ⟨h₁, h₃⟩, ⟨h₂, h₄⟩⟩⟩
  have hmem : ∀ (q : pX.I × pY.I) (A : AFF) (p : (fibreTerm pX pY f g q).obj (op ((incl).obj A))),
      f.app _ (pX.π q.1 A p.1.1.1) = g.app _ (pY.π q.2 A p.1.1.2) := fun q A p => by
    have := p.2 A (𝟙 _)
    simpa [prodφ, prodψ] using this
  exact ⟨{ I := pX.I × pY.I
           obj := fibreTerm pX pY f g
           prop := hP
           tr := fibreTr pX pY f g
           tr_refl := fun q => by
             ext W p
             refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
             · exact congrArg (fun t => t.app W p.1.1.1) (pX.tr_refl q.1)
             · exact congrArg (fun t => t.app W p.1.1.2) (pY.tr_refl q.2)
           tr_trans := fun h₁ h₂ => by
             ext W p
             refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
             · exact congrArg (fun t => t.app W p.1.1.1) (pX.tr_trans h₁.1 h₂.1)
             · exact congrArg (fun t => t.app W p.1.1.2) (pY.tr_trans h₁.2 h₂.2)
           closed := isClosedImm_fibreTr pX pY f g
           π := fun q A p => ⟨(pX.π q.1 A p.1.1.1, pY.π q.2 A p.1.1.2), hmem q A p⟩
           π_map := fun q {A A'} s p => Subtype.ext (Prod.ext (pX.π_map _ _ _) (pY.π_map _ _ _))
           π_tr := fun h A p => Subtype.ext (Prod.ext (pX.π_tr _ _ _) (pY.π_tr _ _ _))
           surj := fun A p => by
             obtain ⟨i, x, hx⟩ := pX.surj A p.1.1
             obtain ⟨j, y, hy⟩ := pY.surj A p.1.2
             refine ⟨(i, j), ⟨⟨(x, y), Over.mkIdTerminal.hom_ext _ _⟩, fun A' s => ?_⟩,
               Subtype.ext (Prod.ext hx hy)⟩
             change f.app _ (pX.π i A' _) = g.app _ (pY.π j A' _)
             have e₁ := pX.π_map i (indAffHom s) x
             have e₂ := pY.π_map j (indAffHom s) y
             refine (congrArg _ e₁).trans (Eq.trans ?_ (congrArg _ e₂).symm)
             rw [hx, hy]
             exact (hom_naturality_apply f _ _).trans
               ((congrArg _ p.2).trans (hom_naturality_apply g _ _).symm)
           inj := fun q A p p' h => by
             have h₁ : pX.π q.1 A p.1.1.1 = pX.π q.1 A p'.1.1.1 := congrArg (fun r => r.1.1) h
             have h₂ : pY.π q.2 A p.1.1.2 = pY.π q.2 A p'.1.1.2 := congrArg (fun r => r.1.2) h
             obtain ⟨i, hi, e₁⟩ := pX.inj _ A _ _ h₁
             obtain ⟨j, hj, e₂⟩ := pY.inj _ A _ _ h₂
             exact ⟨(i, j), ⟨hi, hj⟩, Subtype.ext (Subtype.ext (Prod.ext e₁ e₂))⟩ }⟩

end Fibre

section Corollaries

variable {X Y Z : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u}

/-- **Remark 14.2**: the category of ind-algebraic spaces is closed under fibre products, with no
quasi-compactness of the terms. -/
theorem isIndAlgebraicSpace_fibreProduct_of_gluing
    (pX : IndPresentation.{u, v, u} (IsAlgebraicSpace B S hS) X)
    (pY : IndPresentation.{u, v, u} (IsAlgebraicSpace B S hS) Y)
    (pZ : IndPresentation.{u, v, u} (IsAlgebraicSpace B S hS) Z) (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIndAlgebraicSpace.{u, v} (fibreProduct f g) := by
  refine exists_indPresentation_fibreProduct_of_gluing pX pY f g fun q => ?_
  have hb := isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))
  exact isAlgebraicSpace_eqLocus pZ
    (fun k => (isSheaf_iff_isSheaf_of_type _ _).mp (pZ.prop k).isSheaf)
    (prodφ_map pX pY f q) (prodψ_map pX pY g q)
    (isAlgebraicSpace_of_isPullback (pX.prop q.1) (pY.prop q.2) hb.isSheaf hb.diagonal_representable
      (isPullback_fibreProduct _ _))
    (fun k => (pZ.prop k).diagonal_representable)

/-- **Remark 14.2**: the category of ind-schemes is closed under fibre products, with no
quasi-compactness of the terms. -/
theorem isIndScheme_fibreProduct_of_gluing
    (pX : IndPresentation.{u, v, u}
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => ∃ U : BigFppfOver B S hS, Nonempty (F ≅ yoneda.obj U)) X)
    (pY : IndPresentation.{u, v, u}
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => ∃ U : BigFppfOver B S hS, Nonempty (F ≅ yoneda.obj U)) Y)
    (pZ : IndPresentation.{u, v, u}
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => ∃ U : BigFppfOver B S hS, Nonempty (F ≅ yoneda.obj U)) Z)
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsIndScheme.{u, v} (fibreProduct f g) := by
  have halg : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
      (∃ U : BigFppfOver B S hS, Nonempty (F ≅ yoneda.obj U)) → IsAlgebraicSpace B S hS F := by
    rintro F ⟨U, ⟨e⟩⟩
    exact isAlgebraicSpace_of_iso B S hS e (isAlgebraicSpace_yoneda B S hS U)
  refine exists_indPresentation_fibreProduct_of_gluing pX pY f g fun q => ?_
  have hb := isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))
  obtain ⟨U₀, ⟨e⟩⟩ := representable_fibreProduct (pX.prop q.1) (pY.prop q.2)
    ⟨_, ⟨Iso.refl _⟩⟩ (toBaseSpace (pX.obj q.1)) (toBaseSpace (pY.obj q.2))
  have hr := representable_eqLocus pZ
    (fun k => (isSheaf_iff_isSheaf_of_type _ _).mp (halg (pZ.prop k)).isSheaf)
    (prodφ_map pX pY f q) (prodψ_map pX pY g q) e (isAlgebraicSpace_of_iso B S hS e
      (isAlgebraicSpace_yoneda B S hS U₀)) (fun k => (halg (pZ.prop k)).diagonal_representable)
  exact ⟨_, ⟨(eqLocus _ _).reprW.symm⟩⟩

end Corollaries

end AlgMag

#print axioms AlgMag.isAlgebraicSpace_eqLocus
#print axioms AlgMag.isIndAlgebraicSpace_fibreProduct_of_gluing
#print axioms AlgMag.isIndScheme_fibreProduct_of_gluing
