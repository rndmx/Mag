/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCAtlas
import AlgMag.Sec3Final
import AlgMag.Sec3IntersectionsWeak

/-!
# Propositions 3.31 (ii) and 3.32 (ii), `X` separated

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §3. The case `X` separated, by reduction to the
chart through a fixed-point-reflecting atlas (Proposition 5.1, Theorem 6.8). The case `X` not separated has another proof.

For 3.31 (ii) the atlas is `f⁻¹(Y^×)`-FPR for `D(M)`. The vertex of `ψ ∈ X^Y(T)` is fixed by `D(Z/Y^×)`, hence by
`D(M/f⁻¹(Y^×))`, because `D(Z/Y^×) → D(M/f⁻¹(Y^×))` is an fppf cover (`mem_fixed_comap`). So it lifts to a point of the chart
fixed by `D(Z/Y^×)`, `ψ` lifts to the chart by Proposition 5.1, and on the chart the statement is `prop331_ii`.

## Main results

* `prop331_atlas`, `prop332_atlas`: `S` arbitrary, with the atlas in the hypotheses.
* `prop331_separated`, `prop332_separated`: no atlas in the hypotheses, `X` locally of finite presentation, `S` separated. These
  use the atlas of `thm68_atlas`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.SepProp33

open AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
local notation "SCH" => BigFppfOver.toScheme B S hS
attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {M Z : Type u} [AddCommGroup M] [AddCommGroup Z]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The subgroup `f(M) + Q` of `Z`. -/
def rangeAdd (f : M →+ Z) (Q : AddSubgroup Z) : AddSubgroup Z where
  carrier := {z | ∃ m, z - f m ∈ Q}
  zero_mem' := ⟨0, by simp [Q.zero_mem]⟩
  add_mem' := by
    rintro a b ⟨m, h1⟩ ⟨n, h2⟩
    refine ⟨m + n, ?_⟩
    have := Q.add_mem h1 h2
    rwa [show a - f m + (b - f n) = a + b - f (m + n) by rw [map_add]; abel] at this
  neg_mem' := by
    rintro a ⟨m, h1⟩
    refine ⟨-m, ?_⟩
    have := Q.neg_mem h1
    rwa [show -(a - f m) = -a - f (-m) by rw [map_neg]; abel] at this

/-- `D(Z/Q) → D(M/f⁻¹(Q))` is an fppf cover: a point of `X` fixed by `D(Z/Q)`, acting through `f`, is fixed by `D(M/f⁻¹(Q))`.
This is the translation between the two groups in Theorem A of the reduction. -/
theorem mem_fixed_comap [AddGroup.FG Z] (f : M →+ Z) (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
    {act : AAction (fppfO B S hS) M X} {Q : AddSubgroup Z} {T : (BigFppfOver B S hS)ᵒᵖ} {x : X.obj T}
    (hx : x ∈ (fixedPoints (quotientAction (actAlong f act) Q)).obj T) :
    x ∈ (fixedPoints (quotientAction act (Q.comap f))).obj T := by
  classical
  rw [mem_fixedPoints_quotient_iff] at hx ⊢
  intro T' s h hh
  have hwd : ∀ m m' : M, f m - f m' ∈ Q → h (Multiplicative.ofAdd m) = h (Multiplicative.ofAdd m') := by
    intro m m' e
    have e' : m - m' ∈ Q.comap f := by
      rw [AddSubgroup.mem_comap, map_sub]; exact e
    have h0 : h (Multiplicative.ofAdd (m - m')) = 1 :=
      DFunLike.congr_fun hh (Multiplicative.ofAdd (⟨m - m', e'⟩ : (Q.comap f).toAddSubmonoid))
    have : Multiplicative.ofAdd m = Multiplicative.ofAdd (m - m') * Multiplicative.ofAdd m' := by
      rw [← ofAdd_add]; simp
    rw [this, map_mul, h0, one_mul]
  let D := rangeAdd f Q
  have hkey : ∀ (p : Z) (hp : p ∈ D) (m : M), p - f m ∈ Q →
      h (Multiplicative.ofAdd (Exists.choose hp)) = h (Multiplicative.ofAdd m) := by
    intro p hp m a
    refine hwd _ _ ?_
    have := Q.sub_mem a (Exists.choose_spec hp)
    rwa [show p - f m - (p - f (Exists.choose hp)) = f (Exists.choose hp) - f m by abel] at this
  let a : APt (fppfO B S hS) D.toAddSubmonoid T' :=
    { toFun := fun p => h (Multiplicative.ofAdd
        (Exists.choose (show ((Multiplicative.toAdd p).1 : Z) ∈ D from (Multiplicative.toAdd p).2)))
      map_one' := by
        refine (hkey 0 D.zero_mem 0 (by simp [Q.zero_mem])).trans ?_
        exact map_one h
      map_mul' := by
        intro p q
        have hp : ((Multiplicative.toAdd p).1 : Z) ∈ D := (Multiplicative.toAdd p).2
        have hq : ((Multiplicative.toAdd q).1 : Z) ∈ D := (Multiplicative.toAdd q).2
        have hpq : ((Multiplicative.toAdd (p * q)).1 : Z) ∈ D := (Multiplicative.toAdd (p * q)).2
        refine (hkey _ hpq (Exists.choose hp + Exists.choose hq) ?_).trans ?_
        · have := Q.add_mem (Exists.choose_spec hp) (Exists.choose_spec hq)
          rwa [show ((Multiplicative.toAdd p).1 : Z) - f (Exists.choose hp) +
            (((Multiplicative.toAdd q).1 : Z) - f (Exists.choose hq)) =
            ((Multiplicative.toAdd (p * q)).1 : Z) - f (Exists.choose hp + Exists.choose hq) by
              simp only [toAdd_mul, AddSubmonoid.coe_add, map_add]; abel] at this
        · rw [ofAdd_add, map_mul] }
  have ha : ∀ (p : Z) (hp : p ∈ D) (m : M), p - f m ∈ Q →
      a (Multiplicative.ofAdd (⟨p, hp⟩ : D.toAddSubmonoid)) = h (Multiplicative.ofAdd m) :=
    fun p hp m e => hkey p hp m e
  have hmem := extSieve_mem D (T := unop T') a
  refine (hF _ hmem).isSeparatedFor.ext fun {W} i hi => ?_
  obtain ⟨c, hc⟩ := hi
  have hcv : ∀ (p : Z) (hp : p ∈ D) (m : M), p - f m ∈ Q →
      c (Multiplicative.ofAdd p) = APt.res i.op h (Multiplicative.ofAdd m) := by
    intro p hp m e
    have := DFunLike.congr_fun hc (Multiplicative.ofAdd (⟨p, hp⟩ : D.toAddSubmonoid))
    refine this.trans ?_
    simp only [APt.res_apply]
    exact congrArg _ (ha p hp m e)
  have hres0 : APt.res i.op h (Multiplicative.ofAdd (0 : M)) = 1 := map_one _
  have tc : TrivialOn Q c := by
    refine MonoidHom.ext fun n => ?_
    obtain ⟨z, hz, ez⟩ : ∃ z : Z, z ∈ Q ∧ z = ((Multiplicative.toAdd n).1 : Z) :=
      ⟨_, (Multiplicative.toAdd n).2, rfl⟩
    change c (Multiplicative.ofAdd ((Multiplicative.toAdd n).1 : Z)) = 1
    rw [← ez, hcv z ⟨0, by simpa using hz⟩ 0 (by simpa using hz), hres0]
  have hprod : APt.res i.op h = c.comp (AddMonoidHom.toMultiplicative f) := by
    refine MonoidHom.ext fun m => ?_
    exact (hcv (f (Multiplicative.toAdd m)) ⟨Multiplicative.toAdd m, by simp [Q.zero_mem]⟩
      (Multiplicative.toAdd m) (by simp [Q.zero_mem])).symm
  have hms := act.map_smul i.op h (X.map s x)
  change X.map i.op (act.smul h (X.map s x)) = X.map i.op (X.map s x)
  rw [hms, hprod]
  have e := hx (s ≫ i.op) c tc
  rw [Functor.map_comp_apply] at e
  exact e

/-- A point fixed by `D(M/f⁻¹(Q))` is fixed by `D(Z/Q)` acting through `f`. -/
theorem mem_fixed_along (f : M →+ Z) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {act : AAction (fppfO B S hS) M F} {Q : AddSubgroup Z} {T : (BigFppfOver B S hS)ᵒᵖ} {x : F.obj T}
    (hx : x ∈ (fixedPoints (quotientAction act (Q.comap f))).obj T) :
    x ∈ (fixedPoints (quotientAction (actAlong f act) Q)).obj T := by
  rw [mem_fixedPoints_quotient_iff] at hx ⊢
  intro T' s h hh
  refine hx s (h.comp (AddMonoidHom.toMultiplicative f)) ?_
  refine MonoidHom.ext fun n => ?_
  exact DFunLike.congr_fun hh (Multiplicative.ofAdd
    (⟨f ((Multiplicative.toAdd n).1 : M), (Multiplicative.toAdd n).2⟩ : Q.toAddSubmonoid))

variable [AddGroup.FG M] [AddGroup.FG Z] {f : M →+ Z} {Y : AddSubmonoid Z}
  {aX : AAction (fppfO B S hS) M X}

/-- The core of **Proposition 3.31 (ii)**: `ψ ∈ X^Y(T)`, `u : T → U` a point of an `S`-affine scheme étale and equivariant over `X`,
lifting the vertex of `ψ` and fixed by `D(M/f⁻¹(Y^×))`. -/
theorem exists_along_core {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
    {aU : AAction (fppfO B S hS) M (yoneda.obj U)} (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (F : EquivariantHom aU aX) (he : Space.IsEtale B S hS F.hom)
    (hb : Y.FG ∨ IsLimitPreserving X) {T : BigFppfOver B S hS} (ψ : AttractorPt (actAlong f aX) Y T)
    (u : T ⟶ U) (hu : F.hom.app (op T) u = (AttractorPt.ofFace (isFace_units Y) ψ).toPoint)
    (hfix : u ∈ (fixedPoints (quotientAction aU ((unitsSubgroup Y).comap f))).obj (op T)) :
    ∃ χ : AttractorPt aX (Y.comap f) T, χ.toPoint = ψ.toPoint := by
  have : AddMonoid.FG Z := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  have : Countable M := countable_of_fg M
  let F₂ : EquivariantHom (actAlong f aU) (actAlong f aX) := ⟨F.hom, fun h x => F.map_smul _ x⟩
  let Q := unitsSubgroup Y
  have hQ : IsFace Q.toAddSubmonoid Y := isFace_units Y
  have hcov : ∀ {W : BigFppfOver B S hS} (a : APt (fppfO B S hS) Q.toAddSubmonoid (op W)),
      extSieve (fppfO B S hS) Q a ∈ BigFppfOver.topology B S hS W :=
    fun a => extSieve_mem Q a
  have hfix₂ : u ∈ (fixedPoints (quotientAction (actAlong f aU) Q)).obj (op T) :=
    mem_fixed_along f (act := aU) (Q := Q) (T := op T) (x := u) @hfix
  let wZ : AttractorPt (actAlong f aU) Q.toAddSubmonoid T :=
    attractorFixedEquivOfCover (BigFppfOver.isSheaf_of_type_yoneda_obj U) hcov T ⟨u, hfix₂⟩
  have hwZ : wZ.toPoint = u := congrArg Subtype.val
    ((attractorFixedEquivOfCover (act := actAlong f aU) (BigFppfOver.isSheaf_of_type_yoneda_obj U)
      hcov T).symm_apply_apply ⟨u, hfix₂⟩)
  have hpush : AttractorPt.ofFace hQ ψ = AttractorPt.push F₂ wZ := by
    apply attractor_toPoint_injective_sep hX hsep
    change _ = F.hom.app (op T) wZ.toPoint
    rw [hwZ, hu]
  have hcart : IsFaceCartesian F₂ hQ := by
    rcases hb with hY | hl
    · exact isFaceCartesian_of_fg hX hsep F₂ he hQ hY
    · exact isFaceCartesian_of_separated hX hsep hl F₂ he hQ
  obtain ⟨w, hw⟩ := (hcart T).2 ⟨(ψ, wZ), hpush⟩
  have hw' : AttractorPt.push F₂ w = ψ := congrArg (fun p => p.1.1) hw
  obtain ⟨v, hv⟩ := (prop331_ii (f := f) (Y := Y) (aX := aU) T).2 w
  refine ⟨AttractorPt.push F v, ?_⟩
  rw [← hw']
  change F.hom.app (op T) v.toPoint = F.hom.app (op T) w.toPoint
  rw [← hv, toPoint_ptAlong]

/-- The step of **Proposition 3.31 (ii)**: a point of `X^Y` for `D(Z)` has its underlying point in `X^{f⁻¹(Y)}`. The atlas may be any
disjoint union of `S`-affine stable pieces, as in Definition 6.1 (iv). -/
theorem exists_along (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : ExistsZFPRAtlas aX ((unitsSubgroup Y).comap f)) (hb : Y.FG ∨ IsLimitPreserving X)
    {T : BigFppfOver B S hS} (ψ : AttractorPt (actAlong f aX) Y T) :
    ∃ χ : AttractorPt aX (Y.comap f) T, χ.toPoint = ψ.toPoint := by
  have : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  have : AddMonoid.FG Z := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  obtain ⟨U, aU, g, hat⟩ := hat
  obtain ⟨A, V, hV⟩ := hat.atlas.decomposition
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hinj := fun T => attractor_toPoint_injective_sep (aX := aX) hX hsep (Y.comap f) T
  let F : EquivariantHom aU aX := ⟨g, hat.atlas.equivariant⟩
  let Q := unitsSubgroup Y
  have hQ : IsFace Q.toAddSubmonoid Y := isFace_units Y
  let x₀ : AttractorPt (actAlong f aX) Q.toAddSubmonoid T := AttractorPt.ofFace hQ ψ
  let g₀ : yoneda.obj T ⟶ X := yonedaEquiv.symm x₀.toPoint
  let rep := hat.atlas.etale.rep
  let T' := rep.pullback g₀
  let q : T' ⟶ T := rep.snd g₀
  let u : T' ⟶ U := rep.fst' g₀
  have hu : g.app (op T') u = X.map q.op x₀.toPoint := by
    have h2 : yoneda.map u ≫ g = yoneda.map q ≫ g₀ := by
      rw [Functor.relativelyRepresentable.map_fst']
      exact rep.w g₀
    have h3 := congrArg (fun k => k.app (op T') (𝟙 T')) h2
    have h4 : (yoneda.map u ≫ g).app (op T') (𝟙 T') = g.app (op T') u := by
      change g.app (op T') (𝟙 T' ≫ u) = _
      rw [Category.id_comp]
    have h5 : (yoneda.map q ≫ g₀).app (op T') (𝟙 T') = X.map q.op x₀.toPoint := by
      change g₀.app (op T') (𝟙 T' ≫ q) = _
      rw [Category.id_comp]
      simp [g₀, yonedaEquiv_symm_app_apply]
    exact h4.symm.trans (h3.trans h5)
  have hfixZ : X.map q.op x₀.toPoint ∈
      (fixedPoints (quotientAction (actAlong f aX) Q)).obj (op T') := by
    rw [← AttractorPt.toPoint_baseChange]
    exact (AttractorPt.baseChange q x₀).toPoint_mem_fixedPoints
  have hfixU : u ∈ (fixedPoints (quotientAction aU (Q.comap f))).obj (op T') := by
    refine (isFPR_iff (IsEquivariant.comap (actU := aU) (actX := aX) (f := g) hat.atlas.equivariant
      (QuotientAddGroup.mk' _))).mp hat.isZFPR (op T') u ?_
    rw [hu]
    exact mem_fixed_comap f hsX hfixZ
  have hlocal : ∃ χ : AttractorPt aX (Y.comap f) T',
      χ.toPoint = (AttractorPt.baseChange q ψ).toPoint := by
    refine exists_toPoint_of_sieve hsX hinj _ _ (cover_mem hV u) ?_
    rintro W₀ r₀ ⟨W, r, s', ⟨b⟩, rfl⟩
    let J₀ := openJ ((SCH).map u ⁻¹ᵁ V b)
    obtain ⟨u', hu'⟩ := exists_lift_open (V := V b) (J₀ ≫ u) (fun p => by
      change (SCH).map (J₀ ≫ u) p ∈ V b
      rw [Functor.map_comp]
      exact p.2)
    have hA : IsAffineHom (openObj (V b)).hom.hom := hV.isAffineHom b
    have hfix' : u' ∈ (fixedPoints (quotientAction (pieceAct (hV.stable b)) (Q.comap f))).obj (op _) := by
      refine mem_fixed_piece hV b u' ?_
      rw [hu']
      exact (fixedPoints _).map J₀.op hfixU
    have he : Space.IsEtale B S hS ((pieceJ (hV.stable b)).comp F).hom :=
      isEtale_piece_comp hat.atlas.etale
    obtain ⟨χ, hχ⟩ := exists_along_core hX hsep ((pieceJ (hV.stable b)).comp F) he hb
      (AttractorPt.baseChange (J₀ ≫ q) ψ) u' (by
        refine (congrArg (g.app (op _)) hu').trans ?_
        refine (NatTrans.naturality_apply g J₀.op u).trans ?_
        rw [hu, ← Functor.map_comp_apply]
        exact (AttractorPt.toPoint_baseChange (J₀ ≫ q) x₀).symm) hfix'
    refine ⟨AttractorPt.baseChange r χ, ?_⟩
    rw [AttractorPt.toPoint_baseChange, hχ, AttractorPt.toPoint_baseChange,
      AttractorPt.toPoint_baseChange, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
    rfl
  obtain ⟨χ', hχ'⟩ := hlocal
  refine exists_toPoint_of_sieve hsX hinj _ _
    (Space.sieve_generate_singleton_mem_topology_over B S hS q
      (hat.atlas.surjective.property_snd g₀) (hat.atlas.etale.property_snd g₀)) ?_
  rintro W r ⟨W', a, b, ⟨⟩, rfl⟩
  refine ⟨AttractorPt.baseChange a χ', ?_⟩
  rw [AttractorPt.toPoint_baseChange, hχ', AttractorPt.toPoint_baseChange,
    ← Functor.map_comp_apply, ← op_comp]

/-- **Proposition 3.31 (ii)**, `X` separated, `S` arbitrary, with an `f⁻¹(Y^×)`-FPR atlas: `X^{f⁻¹(Y)}_M = X^Y_Z`. `M`, `Z` are finitely
generated abelian groups, `Y ⊆ Z` a submonoid, finitely generated or `X` limit preserving. -/
theorem prop331_atlas (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : ExistsZFPRAtlas aX ((unitsSubgroup Y).comap f)) (hb : Y.FG ∨ IsLimitPreserving X)
    (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong aX : AttractorPt aX (Y.comap f) T → AttractorPt (actAlong f aX) Y T) := by
  haveI : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  haveI : AddMonoid.FG Z := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  constructor
  · intro χ χ' h
    apply attractor_toPoint_injective_sep hX hsep
    rw [← toPoint_ptAlong χ, ← toPoint_ptAlong χ', h]
  · intro ψ
    obtain ⟨χ, hχ⟩ := exists_along hX hsep hat hb ψ
    refine ⟨χ, ?_⟩
    apply attractor_toPoint_injective_sep hX hsep
    rw [toPoint_ptAlong, hχ]

/-- **Proposition 3.32 (ii)**, `X` separated, `S` arbitrary, with an `(N ∩ L)^×`-FPR atlas: `X^{N ∩ L} = (X^N)^L`. -/
theorem prop332_atlas (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) {N L : AddSubmonoid M}
    (hat : ExistsZFPRAtlas aX (unitsSubgroup (N ⊓ L))) (hb : (N.FG ∧ L.FG) ∨ IsLimitPreserving X)
    (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T) :=
  haveI : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  prop332_weak hX hsep hat hb T

variable (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- **Proposition 3.31 (ii)**, `X` separated: `X` locally of finite presentation over a separated `S`, not necessarily quasi-compact, no
atlas in the hypotheses. `M`, `Z` finitely generated abelian groups, `f : M → Z`, `Y ⊆ Z` an arbitrary submonoid. -/
theorem prop331_separated [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (f : M →+ Z) (Y : AddSubmonoid Z) (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong act : AttractorPt act (Y.comap f) T → AttractorPt (actAlong f act) Y T) :=
  prop331_atlas hX (isSeparatedOver_iff_space.1 hsep) (existsZFPRAtlas_nonqc hZ hM hX hsep hfp act _)
    (Or.inr (isLimitPreserving_of_lfp hX hfp)) T

include hZ in
/-- **Proposition 3.32 (ii)**, `X` separated: `X` locally of finite presentation over a separated `S`, not necessarily quasi-compact, no
atlas in the hypotheses. `M` a finitely generated abelian group, `N`, `L ⊆ M` arbitrary submonoids. -/
theorem prop332_separated [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (N L : AddSubmonoid M) (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt act (N ⊓ L) T → IterPt act N L T) :=
  prop332_atlas hX (isSeparatedOver_iff_space.1 hsep) (existsZFPRAtlas_nonqc hZ hM hX hsep hfp act _)
    (Or.inr (isLimitPreserving_of_lfp hX hfp)) T

end AlgMag.SepProp33

#print axioms AlgMag.SepProp33.prop331_atlas
#print axioms AlgMag.SepProp33.prop332_atlas
#print axioms AlgMag.SepProp33.prop331_separated
#print axioms AlgMag.SepProp33.prop332_separated
