/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12Topology

/-!
# Ind-algebraic spaces

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §14.

An ind-algebraic space is a functor on the big affine fppf category over `S`. Filtered colimits of
sets are expressed by their elementwise description (`IndPresentation.surj`, `IndPresentation.inj`).
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u v w

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "AFF" => BigAffineFppf B S hS
local notation "incl" => BigAffineFppf.inclusion B S hS
local notation "SITE" => BigFppfOver B S hS

variable (B S hS) in
/-- The ring functor on the big affine fppf category over `S`. -/
noncomputable abbrev affineO : AFFᵒᵖ ⥤ CommRingCat.{u} := (incl).op ⋙ fppfO B S hS

/-- **Definition 14.1.** A presentation `X = colim_i X_i` of a functor on `(Aff/S)` as a filtered
colimit of functors with property `P` (algebraic spaces, or schemes) along closed immersions. -/
structure IndPresentation (P : (SITEᵒᵖ ⥤ Type u) → Prop) (X : AFFᵒᵖ ⥤ Type w) where
  /-- The index set. -/
  I : Type v
  [preorder : Preorder I]
  [directed : IsDirectedOrder I]
  [nonempty : Nonempty I]
  /-- The terms of the presentation. -/
  obj : I → SITEᵒᵖ ⥤ Type u
  prop : ∀ i, P (obj i)
  /-- The transition maps. -/
  tr : ∀ {i j : I}, i ≤ j → (obj i ⟶ obj j)
  tr_refl : ∀ i, tr (le_refl i) = 𝟙 _
  tr_trans : ∀ {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k), tr (h₁.trans h₂) = tr h₁ ≫ tr h₂
  closed : ∀ {i j : I} (h : i ≤ j), IsClosedImm (tr h)
  /-- The morphisms to the colimit. -/
  π : ∀ (i : I) (T : AFF), (obj i).obj (op ((incl).obj T)) → X.obj (op T)
  π_map : ∀ (i : I) {T T' : AFF} (s : T' ⟶ T) (x : (obj i).obj (op ((incl).obj T))),
    π i T' ((obj i).map ((incl).map s).op x) = X.map s.op (π i T x)
  π_tr : ∀ {i j : I} (h : i ≤ j) (T : AFF) (x : (obj i).obj (op ((incl).obj T))),
    π j T ((tr h).app _ x) = π i T x
  surj : ∀ (T : AFF) (x : X.obj (op T)), ∃ i x', π i T x' = x
  inj : ∀ (i : I) (T : AFF) (x x' : (obj i).obj (op ((incl).obj T))), π i T x = π i T x' →
    ∃ (j : I) (h : i ≤ j), (tr h).app _ x = (tr h).app _ x'

attribute [instance] IndPresentation.preorder IndPresentation.directed IndPresentation.nonempty

/-- **Definition 14.1.** `X` is an ind-algebraic space over `S`. -/
def IsIndAlgebraicSpace (X : AFFᵒᵖ ⥤ Type w) : Prop :=
  Nonempty (IndPresentation.{u, v, w} (IsAlgebraicSpace B S hS) X)

/-- **Definition 14.1.** `X` is an ind-scheme over `S`. -/
def IsIndScheme (X : AFFᵒᵖ ⥤ Type w) : Prop :=
  Nonempty (IndPresentation.{u, v, w}
    (fun F : SITEᵒᵖ ⥤ Type u => ∃ U : SITE, Nonempty (F ≅ yoneda.obj U)) X)

section Action

variable {M : Type*} [AddCommMonoid M] {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {X : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type w}
variable (p : IndPresentation.{u, v, w} P X)

variable (M) in
/-- **Definition 14.3 (ii).** A collection of actions on the `X_i` compatible with the transition
maps. Here `G = D(M)`, the only group needed in the sequel. -/
structure IndAction where
  /-- The actions on the terms. -/
  act : ∀ i, AAction (fppfO B S hS) M (p.obj i)
  tr_smul : ∀ {i j : p.I} (h : i ≤ j) {U : SITEᵒᵖ} (g : APt (fppfO B S hS) M U)
    (x : (p.obj i).obj U), (p.tr h).app U ((act i).smul g x) = (act j).smul g ((p.tr h).app U x)

variable {p}

/-- The action of `g` on a class is well defined. -/
lemma IndAction.smul_wd (a : IndAction M p) {T : AFF}
    (g : APt (affineO B S hS) M (op T)) {i j : p.I} {x : (p.obj i).obj (op ((incl).obj T))}
    {y : (p.obj j).obj (op ((incl).obj T))} (hxy : p.π i T x = p.π j T y) :
    p.π i T ((a.act i).smul g x) = p.π j T ((a.act j).smul g y) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have h : p.π k T ((p.tr hik).app _ x) = p.π k T ((p.tr hjk).app _ y) := by
    rw [p.π_tr, p.π_tr, hxy]
  obtain ⟨l, hkl, e⟩ := p.inj k T _ _ h
  rw [← p.π_tr (hik.trans hkl), ← p.π_tr (hjk.trans hkl), a.tr_smul, a.tr_smul, p.tr_trans hik hkl,
    p.tr_trans hjk hkl]
  congr 2

/-- **Definition 14.3 (ii).** An ind-action gives birth to a categorical action on `X`
(Definition 14.3 (i)). -/
noncomputable def IndAction.toAction (a : IndAction M p) : AAction (affineO B S hS) M X where
  smul {U} g x :=
    p.π (p.surj (unop U) x).choose (unop U)
      (((a.act _).smul g (p.surj (unop U) x).choose_spec.choose))
  one_smul {U} x := by
    have h := (p.surj (unop U) x).choose_spec.choose_spec
    rw [(a.act _).one_smul]
    exact h
  mul_smul {U} g g' x := by
    have h := (p.surj (unop U) x).choose_spec.choose_spec
    set i := (p.surj (unop U) x).choose
    set y := (p.surj (unop U) x).choose_spec.choose
    rw [(a.act i).mul_smul]
    refine a.smul_wd g ?_
    exact (p.surj _ _).choose_spec.choose_spec.symm
  map_smul {U V} f g x := by
    have h := (p.surj (unop U) x).choose_spec.choose_spec
    set i := (p.surj (unop U) x).choose
    set y := (p.surj (unop U) x).choose_spec.choose
    have e := p.π_map i f.unop ((a.act i).smul g y)
    refine e.symm.trans ?_
    have e2 := (a.act i).map_smul ((incl).map f.unop).op g y
    refine (congrArg (p.π i (unop V)) e2).trans ?_
    refine a.smul_wd _ ?_
    rw [p.π_map, h]
    exact (p.surj _ _).choose_spec.choose_spec.symm

lemma IndAction.π_smul (a : IndAction M p) (i : p.I) {T : AFF}
    (g : APt (affineO B S hS) M (op T)) (x : (p.obj i).obj (op ((incl).obj T))) :
    p.π i T ((a.act i).smul g x) = a.toAction.smul g (p.π i T x) :=
  a.smul_wd g (p.surj _ _).choose_spec.choose_spec.symm

end Action

section Attractor

variable {M : Type u} [AddCommMonoid M] [Countable M] {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
variable {X : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P X}
variable (a : IndAction M p) (N : AddSubmonoid M)

/-- An affine object from an object of the site. -/
abbrev affOf (U : SITE) [h : IsAffine ((BigFppfOver.toScheme B S hS).obj U)] : AFF := ⟨U, h⟩

/-- A morphism of affine objects from a morphism of the site. -/
abbrev indAffHom {T T' : AFF} (f : (incl).obj T' ⟶ (incl).obj T) : T' ⟶ T := ObjectProperty.homMk f

/-- The canonical map `X_i^N(T) → X^N(T)`. -/
noncomputable def indPt (i : p.I) {T : AFF} (φ : AttractorPt (a.act i) N ((incl).obj T)) :
    AttractorPt a.toAction N T where
  app {T'} t b := p.π i T' (φ.app ((incl).map t) b)
  naturality {T' T''} s t b := by
    rw [← p.π_map]
    congr 1
    exact φ.naturality ((incl).map s) ((incl).map t) b
  equivariant {T'} t g b := by
    rw [← a.π_smul]
    congr 1
    exact φ.equivariant ((incl).map t) g b

lemma map_map_op {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A A' A'' : SITE} (f : A' ⟶ A'') (g : A ⟶ A')
    (x : F.obj (op A'')) : F.map g.op (F.map f.op x) = F.map (g ≫ f).op x := by
  rw [op_comp, Functor.map_comp_apply]

instance (T : AFF) : IsAffine ((BigFppfOver.toScheme B S hS).obj ((incl).obj T)) := T.property

/-- `φ ∈ X_i^N(T)` is determined by the value at the universal point. -/
lemma indPt_app_universal (i : p.I) (T : AFF) (ψ : AttractorPt (a.act i) N ((incl).obj T))
    (ψ' : AttractorPt (a.act i) N ((incl).obj T))
    (h : ψ.app (specUniversal N ((incl).obj T)).π (specUniversal N ((incl).obj T)).u =
      ψ'.app (specUniversal N ((incl).obj T)).π (specUniversal N ((incl).obj T)).u) : ψ = ψ' := by
  refine AttractorPt.ext ?_
  funext T' t b
  rw [ψ.app_eq_of_universal (specUniversal N _), ψ'.app_eq_of_universal (specUniversal N _), h]

/-- **Proposition 14.4**, first assertion, surjectivity: the attractor functor of `X` on `(Aff/S)`
is the colimit of the `X_i^N`: every point comes from some `X_j^N`. -/
theorem exists_indPt_eq {T : AFF} (ψ : AttractorPt a.toAction N T) :
    ∃ (j : p.I) (φ : AttractorPt (a.act j) N ((incl).obj T)), indPt a N j φ = ψ := by
  let U := specUniversal N ((incl).obj T)
  let Pa : AFF := affOf (specObj N ((incl).obj T))
  let Pr : Pa ⟶ T := indAffHom U.π
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj U.P) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj (specObj N ((incl).obj T))))
  have appc : ∀ {A : AFF} {f f' : A ⟶ T} {c c' : APt (affineO B S hS) N (op A)}, f = f' → c = c' →
      ψ.app f c = ψ.app f' c' := by
    rintro _ _ _ _ _ rfl rfl
    rfl
  obtain ⟨i, x, hx⟩ := p.surj Pa (ψ.app Pr U.u)
  let R : SITE := specObj M (specObj N ((incl).obj T))
  let Ra : AFF := affOf R
  let prR : R ⟶ U.P := specPr M (specObj N ((incl).obj T))
  let hU : APt (fppfO B S hS) M (op R) := specPt M (specObj N ((incl).obj T))
  let a₀ : APt (fppfO B S hS) N (op R) := APt.res prR.op U.u
  let l₀ : R ⟶ U.P := U.lift (prR ≫ U.π) (APt.toMagnet N hU * a₀)
  have hl₀ : APt.res l₀.op U.u = APt.toMagnet N hU * a₀ := U.res_lift _ _
  have hl₀π : l₀ ≫ U.π = prR ≫ U.π := U.lift_π _ _
  -- equality in the colimit
  have key : p.π i Ra ((p.obj i).map l₀.op x) =
      p.π i Ra ((a.act i).smul hU ((p.obj i).map prR.op x)) := by
    rw [a.π_smul]
    have e₁ := p.π_map i (T := Pa) (T' := Ra) (indAffHom l₀) x
    have e₂ := p.π_map i (T := Pa) (T' := Ra) (indAffHom prR) x
    refine e₁.trans ?_
    refine Eq.trans ?_ (congrArg (a.toAction.smul (U := op Ra) hU) e₂.symm)
    rw [hx]
    have e₃ : indAffHom (T := Pa) (T' := Ra) l₀ ≫ Pr = indAffHom (T := Pa) (T' := Ra) prR ≫ Pr := ObjectProperty.hom_ext _ hl₀π
    refine (ψ.naturality (indAffHom (T := Pa) (T' := Ra) l₀) Pr U.u).symm.trans ?_
    refine Eq.trans ?_ (congrArg (a.toAction.smul (U := op Ra) hU)
      (ψ.naturality (indAffHom (T := Pa) (T' := Ra) prR) Pr U.u))
    exact (appc e₃ hl₀).trans (ψ.equivariant (indAffHom (T := Pa) (T' := Ra) prR ≫ Pr) hU a₀)
  obtain ⟨j, hij, ej⟩ := p.inj i Ra _ _ key
  let xj := (p.tr hij).app _ x
  have hmain : (p.obj j).map l₀.op xj = (a.act j).smul hU ((p.obj j).map prR.op xj) :=
    (hom_naturality_apply (p.tr hij) l₀.op x).symm.trans (ej.trans ((a.tr_smul hij hU _).trans
      (congrArg ((a.act j).smul hU) (hom_naturality_apply (p.tr hij) prR.op x))))
  have hcond : ∀ {T' : SITE} (t : T' ⟶ (incl).obj T) (g : APt (fppfO B S hS) M (op T'))
      (b : APt (fppfO B S hS) N (op T')),
      (p.obj j).map (U.lift t (APt.toMagnet N g * b)).op xj =
        (a.act j).smul g ((p.obj j).map (U.lift t b).op xj) := by
    intro T' t g b
    let ℓ : T' ⟶ R := specLift (V := specObj N ((incl).obj T)) (U.lift t b) g
    have hℓ : ℓ ≫ prR = U.lift t b := specLift_pr _ _
    have hg : APt.res ℓ.op hU = g := res_specLift _ _
    have hlift : ℓ ≫ l₀ = U.lift t (APt.toMagnet N g * b) := by
      refine U.uniq _ _ _ ?_ ?_
      · rw [Category.assoc, hl₀π, ← Category.assoc, hℓ, U.lift_π]
      · have ha : APt.res ℓ.op a₀ = b := by
          refine (APt.res_comp prR.op ℓ.op U.u).symm.trans ?_
          have : prR.op ≫ ℓ.op = (U.lift t b).op := by rw [← op_comp, hℓ]
          rw [this]
          exact U.res_lift _ _
        rw [op_comp, APt.res_comp, hl₀, APt.res_mul, ha]
        rw [← APt.toMagnet_res, hg]
    have h3 := congrArg ((p.obj j).map ℓ.op) hmain
    have h4 := (a.act j).map_smul ℓ.op hU ((p.obj j).map prR.op xj)
    rw [hg] at h4
    rw [← hlift]
    refine (map_map_op l₀ ℓ xj).symm.trans (h3.trans (h4.trans ?_))
    refine congrArg _ ((map_map_op prR ℓ xj).trans ?_)
    rw [hℓ]
  let φ : AttractorPt (a.act j) N ((incl).obj T) :=
    (attractorPtEquivOfUniversal U).symm ⟨xj, fun t g b => hcond t g b⟩
  refine ⟨j, φ, AttractorPt.ext ?_⟩
  funext T' t b
  change p.π j T' ((p.obj j).map (U.lift ((incl).map t) b).op xj) = ψ.app t b
  refine (congrArg (p.π j T') (hom_naturality_apply (p.tr hij)
    (U.lift ((incl).map t) b).op x).symm).trans ((p.π_tr hij T' _).trans ?_)
  have e₁ := p.π_map i (T := Pa) (T' := T') (indAffHom (U.lift ((incl).map t) b)) x
  refine e₁.trans ?_
  rw [hx]
  have e₂ : indAffHom (T := Pa) (T' := T') (U.lift ((incl).map t) b) ≫ Pr = t :=
    ObjectProperty.hom_ext _ (U.lift_π _ _)
  refine (ψ.naturality (indAffHom (T := Pa) (T' := T') (U.lift ((incl).map t) b)) Pr U.u).symm.trans ?_
  exact appc e₂ (U.res_lift _ _)

/-- **Proposition 14.4**, first assertion, injectivity: two points of `X_i^N(T)` with the same
image in `X^N(T)` agree in some `X_j^N(T)`. -/
theorem exists_indPt_inj {T : AFF} (i : p.I) (φ φ' : AttractorPt (a.act i) N ((incl).obj T))
    (h : indPt a N i φ = indPt a N i φ') :
    ∃ (j : p.I) (hij : i ≤ j), φ.push ⟨p.tr hij, a.tr_smul hij⟩ = φ'.push ⟨p.tr hij, a.tr_smul hij⟩ := by
  let U := specUniversal N ((incl).obj T)
  let Pa : AFF := affOf (specObj N ((incl).obj T))
  let Pr : Pa ⟶ T := indAffHom U.π
  have e := congrArg (fun k : AttractorPt a.toAction N T => k.app Pr U.u) h
  obtain ⟨j, hij, ej⟩ := p.inj i Pa _ _ e
  exact ⟨j, hij, indPt_app_universal a N j T _ _ ej⟩

/-- **Proposition 14.4**, "`X^N → X` is representable by algebraic spaces" in the form used in the
paper's proof: for `T` affine and `x : T → X_i → X`, one has `T ×_X X^N = T ×_{X_i} X_i^N`. -/
theorem existsUnique_indPt_of_toPoint {T : AFF} (i : p.I) (x : (p.obj i).obj (op ((incl).obj T)))
    (ψ : AttractorPt a.toAction N T) (hψ : ψ.toPoint = p.π i T x) :
    ∃! φ : AttractorPt (a.act i) N ((incl).obj T), indPt a N i φ = ψ ∧ φ.toPoint = x := by
  obtain ⟨j₀, φ₀, h₀⟩ := exists_indPt_eq a N ψ
  obtain ⟨k₀, hik₀, hjk₀⟩ := exists_ge_ge i j₀
  -- bring both to a common stage where the base points agree
  let tφ := φ₀.push ⟨p.tr hjk₀, a.tr_smul hjk₀⟩
  have hbase : p.π k₀ T ((p.tr hik₀).app _ x) = p.π k₀ T tφ.toPoint := by
    rw [p.π_tr, ← hψ, ← h₀]
    exact (p.π_tr hjk₀ T _).symm
  obtain ⟨k, hk₀k, ek⟩ := p.inj k₀ T _ _ hbase
  have hik : i ≤ k := hik₀.trans hk₀k
  let f : EquivariantHom (a.act i) (a.act k) := ⟨p.tr hik, a.tr_smul hik⟩
  let tψ := tφ.push ⟨p.tr hk₀k, a.tr_smul hk₀k⟩
  have hx : f.hom.app _ x = tψ.toPoint := by
    change (p.tr hik).app _ x = _
    rw [p.tr_trans hik₀ hk₀k]
    exact ek
  have hcl : IsClosedImm f.hom := p.closed hik
  obtain ⟨φ, ⟨h₁, h₂⟩, huniq⟩ := existsUnique_attractorPt_of_isClosedImm f hcl N tψ x hx
  have himg : indPt a N i φ = ψ := by
    rw [← h₀]
    refine AttractorPt.ext ?_
    funext T' t b
    have c₁ := congrArg (fun q : AttractorPt (a.act k) N ((incl).obj T) =>
      q.app ((incl).map t) b) h₁
    have c₂ : p.π k T' (tψ.app ((incl).map t) b) = p.π j₀ T' (φ₀.app ((incl).map t) b) :=
      (p.π_tr hk₀k T' _).trans (p.π_tr hjk₀ T' _)
    refine ((p.π_tr hik T' _).symm.trans ?_).trans c₂
    exact congrArg (p.π k T') c₁
  refine ⟨φ, ⟨himg, h₂⟩, ?_⟩
  rintro φ' ⟨h₁', h₂'⟩
  refine huniq φ' ⟨?_, h₂'⟩
  -- two points of `X_k^N` with the same image agree: use closed immersions from a later stage
  obtain ⟨l, hkl, el⟩ := exists_indPt_inj a N k (φ'.push f) tψ (by
    rw [← h₁]
    refine AttractorPt.ext ?_
    funext T' t b
    have c₁ : p.π k T' ((p.tr hik).app _ (φ'.app ((incl).map t) b)) = _ := p.π_tr hik T' _
    have c₂ : p.π k T' ((p.tr hik).app _ (φ.app ((incl).map t) b)) = _ := p.π_tr hik T' _
    refine c₁.trans (Eq.trans ?_ c₂.symm)
    have e := himg.trans h₁'.symm
    exact (congrArg (fun q : AttractorPt a.toAction N T => q.app t b) e).symm)
  refine AttractorPt.ext ?_
  funext T' t' b
  refine isClosedImm_injective (p.closed hkl) ?_
  exact congrArg (fun q : AttractorPt (a.act l) N ((incl).obj T) => q.app t' b) el

/-- **Proposition 14.4**, transition maps: if the `X_i^N` are represented, by Proposition 12.2 the
transition maps `X_i^N → X_j^N` are closed immersions. -/
theorem isClosedImm_indAttractor {Z : p.I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : ∀ i, RepresentsAttractor (a.act i) N (Z i)) {i j : p.I} (h : i ≤ j) :
    IsClosedImm (repAttractorMap ⟨p.tr h, a.tr_smul h⟩ N (r i) (r j)) :=
  isClosedImm_repAttractorMap _ (p.closed h) N (r i) (r j)

/-- **Proposition 14.4**, main assertion. Suppose that each `X_i^N` is represented by an algebraic
space `Z_i`. Then the attractor functor `T ↦ Hom_{D(M)_T}(𝔸(N)_T, X_T)` on `(Aff/S)` is the
ind-algebraic space `colim_i Z_i`. -/
theorem isIndAlgebraicSpace_attractor {Z : p.I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r : ∀ i, RepresentsAttractor (a.act i) N (Z i)) (hZ : ∀ i, IsAlgebraicSpace B S hS (Z i)) :
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) := by
  refine ⟨{ I := p.I, obj := Z, prop := hZ
            tr := fun h => repAttractorMap ⟨p.tr h, a.tr_smul h⟩ N (r _) (r _)
            tr_refl := fun i => ?_
            tr_trans := fun h₁ h₂ => ?_
            closed := fun h => isClosedImm_indAttractor a N r h
            π := fun i T z => indPt a N i (((r i).equiv _) z)
            π_map := fun i T T' s z => ?_
            π_tr := fun h T z => ?_
            surj := fun T ψ => ?_
            inj := fun i T z z' e => ?_ }⟩
  · ext T z
    change ((r i).equiv (unop T)).symm (((r i).equiv (unop T) z).push ⟨p.tr (le_refl i), _⟩) = z
    refine ((r i).equiv (unop T)).symm_apply_eq.mpr ?_
    refine AttractorPt.ext ?_
    funext T' t b
    change (p.tr (le_refl i)).app _ _ = _
    rw [p.tr_refl]
    rfl
  · rename_i i j k
    ext T z
    change ((r k).equiv (unop T)).symm (((r i).equiv (unop T) z).push ⟨p.tr (h₁.trans h₂), _⟩) =
      ((r k).equiv (unop T)).symm (((r j).equiv (unop T) (((r j).equiv (unop T)).symm
        (((r i).equiv (unop T) z).push ⟨p.tr h₁, _⟩))).push ⟨p.tr h₂, _⟩)
    rw [Equiv.apply_symm_apply]
    congr 1
    refine AttractorPt.ext ?_
    funext T' t b
    change (p.tr (h₁.trans h₂)).app _ _ = (p.tr h₂).app _ ((p.tr h₁).app _ _)
    rw [p.tr_trans h₁ h₂]
    rfl
  · refine AttractorPt.ext ?_
    funext T'' t b
    change p.π i T'' (((r i).equiv _ ((Z i).map ((incl).map s).op z)).app ((incl).map t) b) =
      p.π i T'' (((r i).equiv _ z).app ((incl).map (t ≫ s)) b)
    rw [(r i).naturality]
    rfl
  · rename_i i j
    refine AttractorPt.ext ?_
    funext T'' t b
    change p.π j T'' (((r j).equiv _ (((r j).equiv _).symm (((r i).equiv _ z).push ⟨p.tr h, _⟩))).app
      ((incl).map t) b) = p.π i T'' (((r i).equiv _ z).app ((incl).map t) b)
    rw [Equiv.apply_symm_apply]
    exact p.π_tr h T'' _
  · obtain ⟨j, φ, h⟩ := exists_indPt_eq a N ψ
    exact ⟨j, ((r j).equiv _).symm φ, by
      change indPt a N j (((r j).equiv _) (((r j).equiv _).symm φ)) = ψ
      rw [Equiv.apply_symm_apply, h]⟩
  · obtain ⟨j, hij, e'⟩ := exists_indPt_inj a N i _ _ e
    exact ⟨j, hij, congrArg ((r j).equiv _).symm e'⟩

end Attractor

end AlgMag

#print axioms AlgMag.exists_indPt_eq
#print axioms AlgMag.exists_indPt_inj
#print axioms AlgMag.existsUnique_indPt_of_toPoint
#print axioms AlgMag.isIndAlgebraicSpace_attractor
