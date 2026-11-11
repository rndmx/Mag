/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Final2ExtSieveQuot
import AlgMag.Sec3Rest
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic

/-!
# Proposition 3.35 and Proposition 8.1 for an arbitrary abelian group `M`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, Proposition 3.35 (p. 151) and
Proposition 8.1 (p. 159). Proposition 3.35 is printed for `M` finitely generated; Proposition 8.1 is
printed for an arbitrary abelian group `M` and uses Proposition 3.35. Here, without any finiteness
assumption on `M`, Proposition 3.35 is proved for schemes and for algebraic spaces with a `Z`-FPR atlas,
and Proposition 8.1 is proved as printed.

For an arbitrary `M`, `D(M) → D(Z)` is affine, faithfully flat and surjective, but not of finite
presentation. It is an effective epimorphism of schemes (Mathlib), and an algebraic space is separated
for it (`eq_of_effectiveEpi`, through the representable diagonal). For schemes this gives
`U^Z = U^{D(M/Z)}` directly; for an algebraic space with a `Z`-FPR atlas the attractor points are
built étale locally on the atlas and glued.

## Main results

* `AlgMag.P81G.attractorFixedEquiv`: `X^{D(M/Z)}(T) ≃ X^Z(T)` from uniqueness and existence of values.
* `AlgMag.P81G.eq_of_effectiveEpi`: an algebraic space is separated along effective epimorphisms.
* `AlgMag.P81G.prop81_general`: **Proposition 8.1** for an arbitrary abelian group `M`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u

namespace AlgMag.P81G

open AlgMag

section General

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : Type*} [AddCommGroup M] {F : Cᵒᵖ ⥤ Type u}

/-- `y` is the value at `a ∈ D(Z)(T')` of the attractor point attached to `x`: after every extension
`h` of `a` to `D(M)`, `y` becomes `h • x`. -/
def IsExtValue (act : AAction 𝒪 M F) (Z : AddSubgroup M) {T : C} (x : F.obj (op T)) {T' : C}
    (t : T' ⟶ T) (a : APt 𝒪 Z.toAddSubmonoid (op T')) (y : F.obj (op T')) : Prop :=
  ∀ {T'' : C} (s : T'' ⟶ T') (h : APt 𝒪 M (op T'')),
    APt.toMagnet Z.toAddSubmonoid h = APt.res s.op a →
      F.map s.op y = act.smul h (F.map (s ≫ t).op x)

variable {act : AAction 𝒪 M F} {Z : AddSubgroup M}

/-- Values exist and are unique, for every fixed point. -/
def HasExtValues (act : AAction 𝒪 M F) (Z : AddSubgroup M) : Prop :=
  ∀ {T : C} {x : F.obj (op T)}, x ∈ (fixedPoints (quotientAction act Z)).obj (op T) →
    ∀ {T' : C} (t : T' ⟶ T) (a : APt 𝒪 Z.toAddSubmonoid (op T')), ∃! y, IsExtValue act Z x t a y

/-- An inverse of a point of `D(M)`. -/
def APt.inv' {T : Cᵒᵖ} (h : APt 𝒪 M T) : APt 𝒪 M T := h.comp (invMonoidHom (α := Multiplicative M))

lemma APt.mul_inv' {T : Cᵒᵖ} (h : APt 𝒪 M T) : h * APt.inv' h = 1 := by
  refine MonoidHom.ext fun m => ?_
  change h m * h m⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

lemma APt.toMagnet_mul {T : Cᵒᵖ} (N : AddSubmonoid M) (g h : APt 𝒪 M T) :
    APt.toMagnet N (g * h) = APt.toMagnet N g * APt.toMagnet N h := rfl

/-- Values restrict along morphisms. -/
lemma IsExtValue.restrict {T : C} {x : F.obj (op T)} {T' : C} {t : T' ⟶ T}
    {a : APt 𝒪 Z.toAddSubmonoid (op T')} {y : F.obj (op T')} (hy : IsExtValue act Z x t a y)
    {W : C} (f : W ⟶ T') : IsExtValue act Z x (f ≫ t) (APt.res f.op a) (F.map f.op y) := by
  intro T'' s h e
  rw [← Functor.map_comp_apply, ← op_comp, ← Category.assoc]
  exact hy (s ≫ f) h (by rw [e, ← APt.res_comp, ← op_comp])

variable (hex : HasExtValues act Z)

include hex in
/-- The attractor point attached to a fixed point. -/
noncomputable def attOfFixed {T : C} {x : F.obj (op T)}
    (hx : x ∈ (fixedPoints (quotientAction act Z)).obj (op T)) :
    AttractorPt act Z.toAddSubmonoid T where
  app t a := (hex hx t a).choose
  naturality := by
    intro T' T'' s t a
    refine (hex hx (s ≫ t) (APt.res s.op a)).unique
      (hex hx (s ≫ t) (APt.res s.op a)).choose_spec.1 ?_
    intro W r h e
    rw [← Functor.map_comp_apply, ← op_comp, ← Category.assoc]
    refine (hex hx t a).choose_spec.1 (r ≫ s) h ?_
    rw [e, ← APt.res_comp, ← op_comp]
  equivariant := by
    intro T' t h a
    refine (hex hx t _).unique (hex hx t _).choose_spec.1 ?_
    intro W r k e
    rw [act.map_smul]
    let k' : APt 𝒪 M (op W) := k * APt.inv' (APt.res r.op h)
    have hk' : APt.toMagnet Z.toAddSubmonoid k' = APt.res r.op a := by
      have e1 : APt.toMagnet Z.toAddSubmonoid k = APt.toMagnet Z.toAddSubmonoid (APt.res r.op h) *
          APt.res r.op a := by
        rw [e, APt.res_mul, APt.toMagnet_res]
      change APt.toMagnet Z.toAddSubmonoid k *
        APt.toMagnet Z.toAddSubmonoid (APt.inv' (APt.res r.op h)) = _
      rw [e1, mul_comm (APt.toMagnet Z.toAddSubmonoid (APt.res r.op h)), mul_assoc,
        ← APt.toMagnet_mul, APt.mul_inv']
      exact mul_one _
    rw [(hex hx t a).choose_spec.1 r k' hk', ← act.mul_smul]
    refine smul_eq_of_fixed hx (r ≫ t) ?_
    change APt.toMagnet Z.toAddSubmonoid (APt.res r.op h * (k * APt.inv' (APt.res r.op h))) = _
    rw [mul_comm k, ← mul_assoc, APt.mul_inv', one_mul]

include hex in
/-- **Proposition 3.35**, abstract form: if values exist and are unique, the underlying point is a
bijection `X^{D(M/Z)}(T) ≃ X^Z(T)`. -/
noncomputable def attractorFixedEquiv (T : C) :
    (fixedPoints (quotientAction act Z)).obj (op T) ≃ AttractorPt act Z.toAddSubmonoid T where
  toFun x := attOfFixed hex x.2
  invFun φ := ⟨φ.toPoint, φ.toPoint_mem_fixedPoints⟩
  left_inv x := by
    refine Subtype.ext ?_
    have h := (hex x.2 (𝟙 T) 1).choose_spec.1 (𝟙 T) 1 (by
      ext p; simp [APt.toMagnet])
    have e : F.map (𝟙 T).op (attOfFixed hex x.2).toPoint = _ := h
    simpa [act.one_smul] using e
  right_inv φ := by
    have key : ∀ {T' : C} (t : T' ⟶ T) (a : APt 𝒪 Z.toAddSubmonoid (op T')),
        (attOfFixed hex (act := act) (Z := Z) φ.toPoint_mem_fixedPoints).app t a =
          φ.app t a := by
      intro T' t a
      refine ((hex φ.toPoint_mem_fixedPoints t a).unique
        (hex φ.toPoint_mem_fixedPoints t a).choose_spec.1 ?_)
      intro W s h e
      rw [← φ.naturality, ← e, AttractorPt.app_eq_smul_toPoint]
    refine AttractorPt.ext ?_
    funext T' t a
    exact key t a

include hex in
/-- The bijection of `attractorFixedEquiv` is natural. -/
lemma attractorFixedEquiv_naturality {T T' : C}
    (s : T' ⟶ T) (x : (fixedPoints (quotientAction act Z)).toFunctor.obj (op T)) :
    attractorFixedEquiv hex T' ((fixedPoints (quotientAction act Z)).toFunctor.map s.op x) =
      (attractorFixedEquiv hex T x).baseChange s := by
  apply (attractorFixedEquiv hex T').symm.injective
  refine (Equiv.symm_apply_apply _ _).trans (Subtype.ext ?_)
  change F.map s.op x.1 = ((attractorFixedEquiv hex T x).baseChange s).toPoint
  have h1 : ((attractorFixedEquiv hex T x)).toPoint = x.1 :=
    congrArg Subtype.val ((attractorFixedEquiv hex T).symm_apply_apply x)
  have hnat := (attractorFixedEquiv hex T x).naturality s (𝟙 T) 1
  have hone : APt.res (𝒪 := 𝒪) (P := Z.toAddSubmonoid) s.op 1 = 1 := by
    ext p; simp
  rw [hone, Category.comp_id] at hnat
  change _ = AttractorPt.app (attractorFixedEquiv hex T x) (𝟙 T' ≫ s) 1
  rw [Category.id_comp, hnat, ← h1]
  rfl

end General

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The kernel pair `T' ×_T T'` of a morphism of the site, as an object of the site. -/
noncomputable def kp {T T' : BigFppfOver B S hS} (p : T' ⟶ T) : BigFppfOver B S hS :=
  siteObject B S hS (lt_of_le_of_lt (Scheme.size_pullback_le _ _) (max_lt T'.left.2 T'.left.2))
    (pullback.fst ((SCH).map p) ((SCH).map p) ≫ structMap T')

/-- First projection of the kernel pair. -/
noncomputable def kp₁ {T T' : BigFppfOver B S hS} (p : T' ⟶ T) : kp p ⟶ T' :=
  siteHom (pullback.fst ((SCH).map p) ((SCH).map p)) rfl

/-- Second projection of the kernel pair. -/
noncomputable def kp₂ {T T' : BigFppfOver B S hS} (p : T' ⟶ T) : kp p ⟶ T' :=
  siteHom (pullback.snd ((SCH).map p) ((SCH).map p)) (by
    change pullback.snd ((SCH).map p) ((SCH).map p) ≫ T'.hom.hom =
      pullback.fst ((SCH).map p) ((SCH).map p) ≫ T'.hom.hom
    rw [← site_w p, ← Category.assoc, ← Category.assoc, pullback.condition])

lemma kp_condition {T T' : BigFppfOver B S hS} (p : T' ⟶ T) : kp₁ p ≫ p = kp₂ p ≫ p :=
  site_hom_ext (by
    rw [Functor.map_comp, Functor.map_comp]
    exact pullback.condition)

/-- Morphisms out of a target of an epimorphism of schemes are determined after it. -/
lemma cancel_of_epi {T T' W : BigFppfOver B S hS} (p : T' ⟶ T) [Epi ((SCH).map p)]
    {u v : T ⟶ W} (e : p ≫ u = p ≫ v) : u = v :=
  site_hom_ext ((cancel_epi ((SCH).map p)).1 (by rw [← Functor.map_comp, e, Functor.map_comp]))

/-- Descent of morphisms of the site along an effective epimorphism of schemes. -/
lemma exists_desc {T T' W : BigFppfOver B S hS} (p : T' ⟶ T) [EffectiveEpi ((SCH).map p)]
    (e : T' ⟶ W) (he : kp₁ p ≫ e = kp₂ p ≫ e) : ∃ r : T ⟶ W, p ≫ r = e := by
  let d := EffectiveEpi.desc ((SCH).map p) ((SCH).map e) (fun {Z} g₁ g₂ hg => by
    let l : Z ⟶ (SCH).obj (kp p) := pullback.lift g₁ g₂ hg
    have h1 : l ≫ (SCH).map (kp₁ p) = g₁ := pullback.lift_fst _ _ _
    have h2 : l ≫ (SCH).map (kp₂ p) = g₂ := pullback.lift_snd _ _ _
    rw [← h1, ← h2, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, he])
  have hd : (SCH).map p ≫ d = (SCH).map e := EffectiveEpi.fac _ _ _
  have hw : d ≫ W.hom.hom = T.hom.hom := by
    refine (cancel_epi ((SCH).map p)).1 ?_
    rw [← Category.assoc, hd, site_w e, site_w p]
  exact ⟨siteHom d hw, site_hom_ext (by rw [Functor.map_comp, siteHom_map, hd])⟩

/-- An algebraic space is separated along effective epimorphisms: two points of `X(T)` which agree
after an effective epimorphism `T' → T` agree. The locus where they agree is represented, through
the diagonal, by a monomorphism `E → T` through which `T' → T` factors; by descent it has a
section. -/
theorem eq_of_effectiveEpi {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {T T' : BigFppfOver B S hS} (p : T' ⟶ T) [EffectiveEpi ((SCH).map p)]
    {a b : X.obj (op T)} (h : X.map p.op a = X.map p.op b) : a = b := by
  have hd := hX.diagonal_representable
  let g : yoneda.obj T ⟶ X ⨯ X := prod.lift (yonedaEquiv.symm a) (yonedaEquiv.symm b)
  have hdiag : ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k₁ k₂ : P ⟶ X),
      k₁ ≫ Limits.diag X = k₂ ≫ Limits.diag X → k₁ = k₂ := by
    intro P k₁ k₂ e
    have := congrArg (fun k => k ≫ prod.fst) e
    simpa using this
  have hmono : ∀ {c : BigFppfOver B S hS} (l₁ l₂ : c ⟶ hd.pullback g),
      l₁ ≫ hd.snd g = l₂ ≫ hd.snd g → l₁ = l₂ := by
    intro c l₁ l₂ e
    refine hd.hom_ext (hdiag _ _ ?_) e
    rw [Category.assoc, Category.assoc, hd.w, ← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, e]
  have hi : yonedaEquiv.symm (X.map p.op a) ≫ Limits.diag X = yoneda.map p ≫ g := by
    refine prod.hom_ext ?_ ?_
    · simp [g, yonedaEquiv_symm_naturality_left]
    · simp [g, yonedaEquiv_symm_naturality_left, h]
  let s := hd.lift (yonedaEquiv.symm (X.map p.op a)) p hi
  have hs : s ≫ hd.snd g = p := hd.lift_snd _ _ _
  obtain ⟨r, hr⟩ := exists_desc p s (hmono _ _ (by
    rw [Category.assoc, Category.assoc, hs, kp_condition]))
  have hrs : r ≫ hd.snd g = 𝟙 T :=
    cancel_of_epi p (by rw [← Category.assoc, hr, hs, Category.comp_id])
  have hk : (yoneda.map r ≫ hd.fst g) ≫ Limits.diag X = g := by
    rw [Category.assoc, hd.w, ← Category.assoc, ← Functor.map_comp, hrs, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have h1 := congrArg (fun k => k ≫ prod.fst) hk
  have h2 := congrArg (fun k => k ≫ prod.snd) hk
  simp only [Category.assoc, Limits.diag, prod.lift_fst, prod.lift_snd, Category.comp_id, g] at h1 h2
  exact yonedaEquiv.symm.injective (h1.symm.trans h2)

/-- The base change `P ×_{T'} T''` of `p : P → T'` along `s : T'' → T'`, as an object of the site. -/
noncomputable def bc {P T' T'' : BigFppfOver B S hS} (p : P ⟶ T') (s : T'' ⟶ T') :
    BigFppfOver B S hS :=
  siteObject B S hS (lt_of_le_of_lt (Scheme.size_pullback_le _ _) (max_lt P.left.2 T''.left.2))
    (pullback.snd ((SCH).map p) ((SCH).map s) ≫ structMap T'')

/-- First projection of the base change. -/
noncomputable def bc₁ {P T' T'' : BigFppfOver B S hS} (p : P ⟶ T') (s : T'' ⟶ T') : bc p s ⟶ P :=
  siteHom (pullback.fst ((SCH).map p) ((SCH).map s)) (by
    change pullback.fst ((SCH).map p) ((SCH).map s) ≫ P.hom.hom =
      pullback.snd ((SCH).map p) ((SCH).map s) ≫ T''.hom.hom
    rw [← site_w p, ← site_w s, ← Category.assoc, ← Category.assoc, pullback.condition])

/-- Second projection of the base change. -/
noncomputable def bc₂ {P T' T'' : BigFppfOver B S hS} (p : P ⟶ T') (s : T'' ⟶ T') : bc p s ⟶ T'' :=
  siteHom (pullback.snd ((SCH).map p) ((SCH).map s)) rfl

lemma bc_condition {P T' T'' : BigFppfOver B S hS} (p : P ⟶ T') (s : T'' ⟶ T') :
    bc₁ p s ≫ p = bc₂ p s ≫ s :=
  site_hom_ext (by
    rw [Functor.map_comp, Functor.map_comp]
    exact pullback.condition)

lemma effectiveEpi_bc₂ {P T' T'' : BigFppfOver B S hS} (p : P ⟶ T') (s : T'' ⟶ T')
    [Flat ((SCH).map p)] [Surjective ((SCH).map p)] [QuasiCompact ((SCH).map p)] :
    EffectiveEpi ((SCH).map (bc₂ p s)) := by
  have : Flat (pullback.snd ((SCH).map p) ((SCH).map s)) := inferInstance
  have : Surjective (pullback.snd ((SCH).map p) ((SCH).map s)) := inferInstance
  have : QuasiCompact (pullback.snd ((SCH).map p) ((SCH).map s)) := inferInstance
  exact inferInstanceAs (EffectiveEpi (pullback.snd ((SCH).map p) ((SCH).map s)))

end Site

section Values

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M]

/-- Every point `a` of `D(Z)` extends to a point of `D(M)` after the base change
`T ×_{D(Z)} D(M) → T`, which is affine, faithfully flat and surjective (no finiteness on `M`). -/
theorem exists_univ_ext (Z : AddSubgroup M) (hAZ : B.Contains (GB.AZ M)) {T : BigFppfOver B S hS}
    (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)) :
    ∃ (P : BigFppfOver B S hS) (p : P ⟶ T) (h : APt (fppfO B S hS) M (op P)),
      APt.toMagnet Z.toAddSubmonoid h = APt.res p.op a ∧
      Flat ((SCH).map p) ∧ Surjective ((SCH).map p) ∧ QuasiCompact ((SCH).map p) := by
  let φ := Z.toAddSubmonoid.subtype
  let f : (SCH).obj T ⟶ GB.AZ Z.toAddSubmonoid := (GB.ptsZ _).symm a
  let W : Scheme.{u} := pullback f (GB.AZmap φ)
  have hW : B.Contains W := lt_of_le_of_lt (Scheme.size_pullback_le _ _) (max_lt T.left.2 hAZ)
  let P : BigFppfOver B S hS := siteObject B S hS hW (pullback.fst f (GB.AZmap φ) ≫ structMap T)
  let q : P ⟶ T := Over.homMk (ObjectProperty.homMk (pullback.fst f (GB.AZmap φ))) rfl
  have hfl : Flat (GB.AZmap φ) := GB.flat_AZmap φ (flat_of_isFreeAlong ℤ (isFreeAlong_subtype Z))
  have hsu : Surjective (GB.AZmap φ) := ⟨comap_mapDomain_surjective Z ℤ⟩
  have hqc : QuasiCompact (GB.AZmap φ) := inferInstance
  refine ⟨P, q, GB.ptsZ _ (pullback.snd f (GB.AZmap φ)), ?_,
    inferInstanceAs (Flat (pullback.fst f (GB.AZmap φ))),
    inferInstanceAs (Surjective (pullback.fst f (GB.AZmap φ))),
    inferInstanceAs (QuasiCompact (pullback.fst f (GB.AZmap φ)))⟩
  have e := GB.ptsZ_AZmap φ (pullback.snd f (GB.AZmap φ))
  rw [← pullback.condition, GB.ptsZ_comp] at e
  have hf : GB.ptsZ _ f = a := (GB.ptsZ _).apply_symm_apply a
  rw [hf] at e
  exact e.symm

/-- **Proposition 3.35 for schemes, values.** For a scheme `U` of the site with an action of `D(M)_S`,
`M` an arbitrary abelian group, values of attractor points at fixed points exist and are unique:
they are obtained by descent along `T ×_{D(Z)} D(M) → T`. -/
theorem hasExtValues_yoneda (Z : AddSubgroup M) (hAZ : B.Contains (GB.AZ M))
    {U : BigFppfOver B S hS} (actU : AAction (fppfO B S hS) M (yoneda.obj U)) :
    HasExtValues actU Z := by
  intro T x hx T' t a
  obtain ⟨P, p, h, hh, hfl, hsu, hqc⟩ := exists_univ_ext Z hAZ a
  let e : P ⟶ U := actU.smul h ((yoneda.obj U).map (p ≫ t).op x)
  have hext : ∀ {W : BigFppfOver B S hS} (q : W ⟶ P), (yoneda.obj U).map q.op e =
      actU.smul (APt.res q.op h) ((yoneda.obj U).map (q ≫ p ≫ t).op x) := by
    intro W q
    rw [actU.map_smul, ← Functor.map_comp_apply, ← op_comp]
  have he : kp₁ p ≫ e = kp₂ p ≫ e := by
    change (yoneda.obj U).map (kp₁ p).op e = (yoneda.obj U).map (kp₂ p).op e
    rw [hext, hext, ← Category.assoc (kp₂ p), ← kp_condition p, Category.assoc]
    refine smul_eq_of_fixed hx _ ?_
    rw [APt.toMagnet_res, APt.toMagnet_res, hh, ← APt.res_comp, ← APt.res_comp, ← op_comp,
      ← op_comp, kp_condition]
  obtain ⟨r, hr⟩ := exists_desc p e he
  refine ⟨r, ?_, ?_⟩
  · intro T'' s k hk
    have := effectiveEpi_bc₂ p s
    refine cancel_of_epi (bc₂ p s) ?_
    change (yoneda.obj U).map (bc₂ p s).op ((yoneda.obj U).map s.op r) =
      (yoneda.obj U).map (bc₂ p s).op (actU.smul k ((yoneda.obj U).map (s ≫ t).op x))
    rw [← Functor.map_comp_apply, ← op_comp, ← bc_condition, actU.map_smul,
      ← Functor.map_comp_apply, ← op_comp, op_comp, Functor.map_comp_apply]
    change (yoneda.obj U).map (bc₁ p s).op (p ≫ r) = _
    rw [hr, hext, ← Category.assoc (bc₁ p s), bc_condition, Category.assoc]
    refine smul_eq_of_fixed hx _ ?_
    rw [APt.toMagnet_res, APt.toMagnet_res, hh, hk, ← APt.res_comp, ← APt.res_comp, ← op_comp,
      ← op_comp, bc_condition]
  · intro y hy
    refine cancel_of_epi p ?_
    rw [hr]
    exact hy p h hh

/-- **Proposition 3.35 for an algebraic space with a `Z`-FPR atlas, values.** For an arbitrary
abelian group `M`, values of attractor points at fixed points exist and are unique. Uniqueness is
`eq_of_effectiveEpi`; existence holds étale locally, where a fixed point lifts to a fixed point of
the atlas (`Z`-FPR) and `hasExtValues_yoneda` applies, and the local values glue. -/
theorem hasExtValues_of_atlas (Z : AddSubgroup M) (hAZ : B.Contains (GB.AZ M))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {actX : AAction (fppfO B S hS) M X} {U : BigFppfOver B S hS}
    {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {g : yoneda.obj U ⟶ X}
    (hg : IsZFPRAtlas actU actX g Z) : HasExtValues actX Z := by
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hU : HasExtValues actU Z := hasExtValues_yoneda Z hAZ actU
  have hfpr := (isFPR_iff (IsEquivariant.comap hg.atlas.equivariant (QuotientAddGroup.mk' Z))).mp hg.isZFPR
  have hloc := Space.isLocallySurjective_of_presheafSurjective_etale g hg.atlas.surjective
    hg.atlas.etale
  intro T x hx
  have huniq : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (a : APt (fppfO B S hS)
      Z.toAddSubmonoid (op T')) (y y' : X.obj (op T')), IsExtValue actX Z x t a y →
        IsExtValue actX Z x t a y' → y = y' := by
    intro T' t a y y' hy hy'
    obtain ⟨P, p, h, hh, hfl, hsu, hqc⟩ := exists_univ_ext Z hAZ a
    exact eq_of_effectiveEpi hX p ((hy p h hh).trans (hy' p h hh).symm)
  have hlocal : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T)
      (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T')), ∃ y, IsExtValue actX Z x t a y := by
    intro T' t a
    let R : Sieve T' := (Presheaf.imageSieve g x).pullback t
    have hR : R ∈ BigFppfOver.topology B S hS T' :=
      (BigFppfOver.topology B S hS).pullback_stable t (hloc.imageSieve_mem x)
    have hex_r : ∀ {W : BigFppfOver B S hS} (r : W ⟶ T'), R.arrows r →
        ∃ y, IsExtValue actX Z x (r ≫ t) (APt.res r.op a) y := by
      intro W r hr
      obtain ⟨v, hv⟩ := hr
      have hvfix : v ∈ (fixedPoints (quotientAction actU Z)).obj (op W) := by
        refine hfpr (op W) v ?_
        rw [hv]
        exact (fixedPoints (quotientAction actX Z)).map (r ≫ t).op hx
      obtain ⟨yU, hyU, -⟩ := hU hvfix (𝟙 W) (APt.res r.op a)
      refine ⟨g.app _ yU, ?_⟩
      intro W'' s k hk
      rw [← NatTrans.naturality_apply g s.op yU, hyU s k hk, hg.atlas.equivariant,
        NatTrans.naturality_apply, Category.comp_id, hv, ← Functor.map_comp_apply, ← op_comp]
    let fam : Presieve.FamilyOfElements X R.arrows := fun W r hr => (hex_r r hr).choose
    have hc : fam.Compatible := by
      intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ comm
      have e1 : IsExtValue actX Z x (g₁ ≫ f₁ ≫ t) (APt.res g₁.op (APt.res f₁.op a))
          (X.map g₁.op (fam f₁ h₁)) := IsExtValue.restrict (hex_r f₁ h₁).choose_spec g₁
      have e2 : IsExtValue actX Z x (g₂ ≫ f₂ ≫ t) (APt.res g₂.op (APt.res f₂.op a))
          (X.map g₂.op (fam f₂ h₂)) := IsExtValue.restrict (hex_r f₂ h₂).choose_spec g₂
      have ht : g₁ ≫ f₁ ≫ t = g₂ ≫ f₂ ≫ t := by
        rw [← Category.assoc, comm, Category.assoc]
      have ha : APt.res g₁.op (APt.res f₁.op a) = APt.res g₂.op (APt.res f₂.op a) := by
        rw [← APt.res_comp, ← APt.res_comp, ← op_comp, ← op_comp, comm]
      rw [ht, ha] at e1
      exact huniq _ _ _ _ e1 e2
    refine ⟨(hsh R hR).amalgamate fam hc, ?_⟩
    intro T'' s k hk
    have sh := hsh _ ((BigFppfOver.topology B S hS).pullback_stable s hR)
    refine sh.isSeparatedFor.ext fun W f hf => ?_
    rw [← Functor.map_comp_apply, ← op_comp, (hsh R hR).valid_glue hc (f ≫ s) hf, actX.map_smul,
      ← Functor.map_comp_apply, ← op_comp]
    have hf' := (hex_r (f ≫ s) hf).choose_spec (𝟙 W) (APt.res f.op k) (by
      rw [APt.toMagnet_res, hk, ← APt.res_comp, ← op_comp, op_id, APt.res_id])
    rw [op_id, CategoryTheory.Functor.map_id_apply, Category.id_comp] at hf'
    refine hf'.trans ?_
    rw [Category.assoc]
  intro T' t a
  obtain ⟨y, hy⟩ := hlocal t a
  exact ⟨y, hy, fun y' hy' => huniq t a y' y hy' hy⟩

/-- **Proposition 3.35 for schemes, for an arbitrary abelian group `M`**: for a scheme `U` of the
site with an action of `D(M)_S`, the underlying point is a natural bijection
`U^{D(M/Z)}(T) ≃ U^Z(T)`. -/
noncomputable def prop335_scheme (Z : AddSubgroup M) (hAZ : B.Contains (GB.AZ M))
    {U : BigFppfOver B S hS} (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (T : BigFppfOver B S hS) :
    (fixedPoints (quotientAction actU Z)).obj (op T) ≃ AttractorPt actU Z.toAddSubmonoid T :=
  attractorFixedEquiv (hasExtValues_yoneda Z hAZ actU) T

/-- **Proposition 3.35 for an algebraic space with a `Z`-FPR atlas, for an arbitrary abelian group
`M`**: the underlying point is a natural bijection `X^{D(M/Z)}(T) ≃ X^Z(T)`. -/
noncomputable def prop335_of_atlas (Z : AddSubgroup M) (hAZ : B.Contains (GB.AZ M))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {actX : AAction (fppfO B S hS) M X} (hat : ExistsZFPRAtlas actX Z) (T : BigFppfOver B S hS) :
    (fixedPoints (quotientAction actX Z)).obj (op T) ≃ AttractorPt actX Z.toAddSubmonoid T :=
  attractorFixedEquiv (hasExtValues_of_atlas Z hAZ hX hat.choose_spec.choose_spec.choose_spec) T

end Values

/-- **Proposition 8.1 for an arbitrary abelian group `M`** (as printed, Semigroup Forum 113 (2026),
p. 159). If `X` has a `Z`-FPR atlas under `D(M)_S`, then the attractor `X^Z` is represented by a
closed subspace of `X`, namely the fixed points of `D(M/Z)`. The hypotheses `hAZ`, `hM`, `hQ` say that
`𝔸(M)`, `Spec ℤ[M]` and `Spec ℤ[M/Z]` are objects of the site (size cutoffs, automatic for `M`
countable). -/
theorem prop81_general {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (M : Type u)
    [AddCommGroup M] (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (actX : AAction (fppfO B S hS) M X) (Z : AddSubgroup M)
    (hAZ : B.Contains (GB.AZ M)) (hM : B.Contains (Spec (ZMon M)))
    (hQ : B.Contains (Spec (ZMon (M ⧸ Z)))) :
    ExistsZFPRAtlas actX Z → AttractorIsClosedSubspace actX Z := by
  rintro ⟨U, actU, g, hg⟩
  have hex : HasExtValues actX Z := hasExtValues_of_atlas Z hAZ hX hg
  let Y := (fixedPoints (quotientAction actX Z)).toFunctor
  let i : Y ⟶ X := (fixedPoints (quotientAction actX Z)).ι
  have hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y := isSheaf_fixedPoints hX.isSheaf actX Z
  obtain ⟨W, j, hj, hiff⟩ := exists_closed_fixed hM hg.atlas.decomposition hQ
  have hι := presheaf_fixed_ι j hj hiff
  have hpb : IsPullback (fixedMap (IsEquivariant.comap (actU := actU) (actX := actX) (f := g)
        hg.atlas.equivariant (QuotientAddGroup.mk' Z)))
      (fixedPoints (quotientAction actU Z)).ι i g := hg.isZFPR
  have hsq : IsPullback hpb.isoPullback.inv (pullback.snd i g)
      (fixedPoints (quotientAction actU Z)).ι (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩
  have hV := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hι
  have hres := Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hYs hX
    hg.atlas.surjective hg.atlas.etale hV
  refine ⟨Y, i, ⟨fun T => attractorFixedEquiv hex T, fun s z =>
    attractorFixedEquiv_naturality hex s z⟩, hres.1, hres.2, fun T y => ?_⟩
  exact (congrArg Subtype.val ((attractorFixedEquiv hex T).symm_apply_apply y)).symm

end AlgMag.P81G

#print axioms AlgMag.P81G.eq_of_effectiveEpi
#print axioms AlgMag.P81G.prop335_scheme
#print axioms AlgMag.P81G.prop335_of_atlas
#print axioms AlgMag.P81G.prop81_general
