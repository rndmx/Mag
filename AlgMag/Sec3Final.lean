/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBaseCor
import AlgMag.GeneralBasePushout
import AlgMag.Prop222
import AlgMag.Sec3SchemeQuotient
import AlgMag.Sec3Remaining

/-!
# Algebraic Magnetism, §3: the last statements

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), §3.

## Main results

* `AlgMag.GB.prop331_i`: Proposition 3.31 (i), `S` arbitrary, `Z` any monoid.
* `AlgMag.prop331_ii`: Proposition 3.31 (ii), `X` a scheme. Printed proof repaired: the action is not free
  unless `Y^gp ⊆ f(M)`, the fpqc quotient is replaced by the descent `AlgMag.SQ.exists_desc`.
* `AlgMag.GB.prop332_i`: Proposition 3.32 (i), `S` arbitrary.
* `AlgMag.prop332_iii_gp`, `AlgMag.prop332_iii_scheme`, `AlgMag.prop332_iii_atlas`: Proposition 3.32 (iii).
* `AlgMag.GB.fact334_i`, `AlgMag.fact334_iii_gp`, `AlgMag.fact334_iii_finite_scheme`, `AlgMag.fact334_iii_atlas`: Fact 3.34.
* `AlgMag.isFace_inf36`, `AlgMag.GB.prop336_i`, `AlgMag.GB.prop336_ii`: Proposition 3.36.
-/

universe u

section

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical


namespace AlgMag

section AlongGeneral

variable {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M Z : Type u} [AddCommMonoid M] [AddCommMonoid Z] {F : Cᵒᵖ ⥤ Type u}

/-- `f` restricted to `f⁻¹(Y) → Y`, for a monoid `Z`. -/
def comapHom (f : M →+ Z) (Y : AddSubmonoid Z) : Y.comap f →+ Y where
  toFun n := ⟨f n, n.2⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : M) (b : M))

/-- **Proposition 3.31**: the canonical map `X^N_M → X^Y_Z`, `N = f⁻¹(Y)`, precomposition with
`𝔸(Y) → 𝔸(N)`. -/
def AttractorPt.along (f : M →+ Z) (Y : AddSubmonoid Z) {act : AAction 𝒪 M F} {T : C}
    (φ : AttractorPt act (Y.comap f) T) : AttractorPt (act.comap f) Y T where
  app t a := φ.app t (a.comp (AddMonoidHom.toMultiplicative (comapHom f Y)))
  naturality s t a := φ.naturality s t (a.comp (AddMonoidHom.toMultiplicative (comapHom f Y)))
  equivariant t h a := by
    refine Eq.trans (congrArg (φ.app t) (MonoidHom.ext fun _ => rfl))
      (φ.equivariant t (h.comp (AddMonoidHom.toMultiplicative f))
        (a.comp (AddMonoidHom.toMultiplicative (comapHom f Y))))

lemma AttractorPt.toPoint_along (f : M →+ Z) (Y : AddSubmonoid Z) {act : AAction 𝒪 M F} {T : C}
    (φ : AttractorPt act (Y.comap f) T) : (φ.along f Y).toPoint = φ.toPoint := by
  change φ.app (𝟙 T) ((1 : APt 𝒪 Y (op T)).comp _) = φ.app (𝟙 T) 1
  rw [MonoidHom.one_comp]

end AlongGeneral

namespace GB

attribute [local instance] gradedAlgebraOf

variable {S : Scheme.{u}} {M Z : Type u} [AddCommMonoid M] [AddCommMonoid Z]
variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))

/-- The grading of `act.comap f` is the push-forward along `f`: `A_m ⊆ A_{f(m)}`. -/
lemma mem_gradingOf_along (f : M →+ Z) {U : S.Opens} (hU : IsAffineOpen U) {m : M} {a : Aalg X U}
    (ha : a ∈ gradingOf hU act m) : a ∈ gradingOf hU (act.comap f) (f m) :=
  mem_gradingOf_of_forall hU (act.comap f) fun hT h x =>
    ptX_smul_of_mem hU act hT (h.comp (AddMonoidHom.toMultiplicative f)) x ha

/-- The ideal `J_{f⁻¹(Y)}` for the `M`-grading lies in `J_Y` for the `Z`-grading. -/
lemma magnetIdeal_comap_le (f : M →+ Z) (Y : AddSubmonoid Z) {U : S.Opens} (hU : IsAffineOpen U) :
    magnetIdeal (gradingOf hU act) (Y.comap f) ≤ magnetIdeal (gradingOf hU (act.comap f)) Y := by
  rw [magnetIdeal, Ideal.span_le]
  simp only [Set.iUnion_subset_iff]
  intro m hm x hx
  exact mem_magnetIdeal_of_notMem (m := f m) hm (mem_gradingOf_along act f hU hx)

/-- Key step of **Proposition 3.31 (i)**: a point of `X^Y_Z` has a point of `X^{f⁻¹(Y)}_M` with the same
underlying point. -/
theorem exists_comap_of_along (f : M →+ Z) (Y : AddSubmonoid Z) {T : Over S}
    (ψ : AttractorPt (act.comap f) Y T) :
    ∃ φ : AttractorPt act (Y.comap f) T, φ.toPoint = ψ.toPoint := by
  refine exists_att_of_local act ψ.toPoint fun {W} s U hW => ?_
  refine (exists_att_iff_kills act U.2 hW _).2 fun a ha => ?_
  have h := toPoint_kills U.2 (act.comap f) Y hW (ψ.baseChange s)
    (magnetIdeal_comap_le act f Y U.2 ha)
  rwa [toPoint_baseChange] at h

/-- **Proposition 3.31 (i)**, over an arbitrary scheme `S`. `X` affine over `S`, `f : M → Z` a morphism
of monoids, `Y` a magnet of `Z`: the canonical map `X^{f⁻¹(Y)}_M → X^Y_Z` is bijective on `T`-points
for every scheme `T` over `S`. -/
theorem prop331_i (f : M →+ Z) (Y : AddSubmonoid Z) (T : Over S) :
    Function.Bijective (AttractorPt.along f Y : AttractorPt act (Y.comap f) T → _) := by
  constructor
  · intro φ φ' h
    apply toPoint_injective_global
    have := congrArg AttractorPt.toPoint h
    rwa [AttractorPt.toPoint_along, AttractorPt.toPoint_along] at this
  · intro ψ
    obtain ⟨φ, hφ⟩ := exists_comap_of_along act f Y ψ
    refine ⟨φ, toPoint_injective_global ?_⟩
    rw [AttractorPt.toPoint_along, hφ]

/-- **Proposition 3.32 (i)**, over an arbitrary scheme `S`. `X` affine over `S`, `M` any commutative
monoid: `(X^N)^L = X^{N ∩ L}`. The map `f ↦ F = f ∘ m` is bijective. Theorem 3.20 is used through
Proposition 3.31 (i) for the diagonal `M → M × M`, whose preimage of `N × L` is `N ∩ L`. -/
theorem prop332_i (N L : AddSubmonoid M) (T : Over S) :
    Function.Bijective fun χ : AttractorPt act (N ⊓ L) T =>
      (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L)
        fun _ hk => ⟨(AddSubmonoid.mem_inf.mp hk).1, (AddSubmonoid.mem_inf.mp hk).2⟩) := by
  constructor
  · intro χ χ' h
    apply toPoint_injective_global
    have := congrArg AttractorPt.toPoint ((iterEquivBi T).symm.injective h)
    exact (AttractorPt.toPoint_toBi _ χ).symm.trans (this.trans (AttractorPt.toPoint_toBi _ χ'))
  · intro Ψ
    obtain ⟨φ, hφ⟩ := exists_comap_of_along act (diagHom M) (N.prod L)
      (show AttractorPt (act.comap (diagHom M)) (N.prod L) T from Ψ.toBi)
    have hle : (N.prod L).comap (diagHom M) ≤ N ⊓ L := fun m hm =>
      AddSubmonoid.mem_inf.mpr ⟨hm.1, hm.2⟩
    refine ⟨attIncl hle φ, ?_⟩
    apply (iterEquivBi T).injective
    rw [Equiv.apply_symm_apply]
    refine toPoint_injective_global (act := act.comap (diagHom M)) ?_
    refine (AttractorPt.toPoint_toBi _ _).trans ?_
    rw [toPoint_attIncl, hφ]
    rfl

/-- **Fact 3.34 (i)**, over an arbitrary scheme `S` and for an arbitrary family. `X` affine over `S`:
if the `X^{N}`, `N ∈ s`, are all the same subfunctor `y` of `X`, then `X^{⋂ N} = y`. -/
theorem fact334_i {s : Set (AddSubmonoid M)} (y : ∀ T : Over S, Set (T ⟶ X)) (hne : s.Nonempty)
    (hy : ∀ N ∈ s, attractorImage act N = y) : attractorImage act (sInf s) = y := by
  obtain ⟨N₀, hN₀⟩ := hne
  funext T
  ext x
  rw [sInf_eq_iInf']
  constructor
  · rintro ⟨φ, rfl⟩
    rw [← hy N₀ hN₀]
    exact (exists_toPoint_iInf_iff act (fun N : s => (N : AddSubmonoid M)) φ.toPoint).1 ⟨φ, rfl⟩
      ⟨N₀, hN₀⟩
  · intro hx
    exact (exists_toPoint_iInf_iff act (fun N : s => (N : AddSubmonoid M)) x).2 fun N => by
      have : x ∈ attractorImage act (N : AddSubmonoid M) T := by rw [hy N N.2]; exact hx
      exact this

end GB

end AlgMag

end

section

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical


namespace AlgMag

/-- `FaceCond` from `IsFace`. -/
lemma IsFace.faceCond {M : Type*} [AddCommMonoid M] {F N : AddSubmonoid M} (h : IsFace F N) :
    FaceCond F N := fun _ hx _ hy hxy => h.mem_of_add_mem hx hy hxy

/-- **Proposition 3.36**, first assertion: if `L` is a face of `L'`, `N' ⊆ L'` and `N = L ∩ N'`, then
`N` is a face of `N'`. -/
theorem isFace_inf36 {M : Type*} [AddCommMonoid M] {N N' L L' : AddSubmonoid M} (hL : IsFace L L')
    (hN'L' : N' ≤ L') (hN : N = L ⊓ N') : IsFace N N' := by
  subst hN
  refine ⟨inf_le_right, fun hx hy hxy => ?_⟩
  have hL' := AddSubmonoid.mem_inf.mp hxy
  obtain ⟨h1, h2⟩ := hL.mem_of_add_mem (hN'L' hx) (hN'L' hy) hL'.1
  exact ⟨AddSubmonoid.mem_inf.mpr ⟨h1, hx⟩, AddSubmonoid.mem_inf.mpr ⟨h2, hy⟩⟩

section Square

variable {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommMonoid M]
  {F : Cᵒᵖ ⥤ Type u} {N N' L L' : AddSubmonoid M}

lemma restrict_faceExt_square (hN'L' : N' ≤ L') (hNL : N ≤ L) (hL : IsFace L L') (hN : IsFace N N')
    (hc : ∀ x ∈ N', x ∈ L → x ∈ N) {U : Cᵒᵖ} (a : APt 𝒪 L U) :
    APt.restrict hN'L' (APt.faceExt hL a) = APt.faceExt hN (APt.restrict hNL a) := by
  refine MonoidHom.ext fun n => ?_
  by_cases h : ((Multiplicative.toAdd n : N') : M) ∈ N
  · rw [APt.faceExt_pos hN _ h]
    exact APt.faceExt_pos hL a (n := AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hN'L') n)
      (hNL h)
  · rw [APt.faceExt_neg hN _ h]
    exact APt.faceExt_neg hL a (n := AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hN'L') n)
      fun h' => h (hc _ (Multiplicative.toAdd n).2 h')

variable {act : AAction 𝒪 M F}

/-- **Proposition 3.36**: the square `X^{N'} → X^{L'} ×_{X^L} X^N` commutes, on `T`-points. -/
def cart36 (hN'L' : N' ≤ L') (hNL : N ≤ L) (hL : IsFace L L') (hN : IsFace N N')
    (hc : ∀ x ∈ N', x ∈ L → x ∈ N) {T : C} (x : AttractorPt act N' T) :
    {p : AttractorPt act L' T × AttractorPt act N T //
      AttractorPt.ofFace hL p.1 = AttractorPt.ofLE hNL p.2} :=
  ⟨(AttractorPt.ofLE hN'L' x, AttractorPt.ofFace hN x), by
    refine AttractorPt.ext ?_
    funext T' t a
    exact congrArg (x.app t) (restrict_faceExt_square hN'L' hNL hL hN hc a)⟩

end Square

namespace GB

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]

section Legs

/-- The universal point on `𝔸(E)_T`. -/
local notation "𝐔" => universalPoint

lemma lift_left_eq {E G : AddSubmonoid M} (T : Over S) (g : A E T.left ⟶ A G T.left)
    (a : APt (overO S) G (op (𝐔 E T).P))
    (h : ptsZ (A E T.left).left (g.left ≫ toAZ G T.left) = a) :
    ((𝐔 G T).lift (𝐔 E T).π a).left = g.left := by
  refine pullback.hom_ext ?_ ?_
  · refine (pullback.lift_fst _ _ _).trans ?_
    exact (Over.w g).symm
  · refine (pullback.lift_snd _ _ _).trans ?_
    apply (ptsZ _).injective
    exact ((ptsZ _).apply_symm_apply a).trans h.symm

variable {N L L' : AddSubmonoid M} (hNL : N ≤ L) (hL : IsFace L L')

/-- `N'`. -/
local notation "𝐍" => gluedMagnet hNL (IsFace.faceCond hL)

lemma isFace_glued : IsFace N (gluedMagnet hNL hL.faceCond) :=
  ⟨le_gluedMagnet hNL hL.le hL.faceCond, fun hx hy h =>
    faceCond_gluedMagnet hNL hL.faceCond _ hx _ hy h⟩

/-- `𝔸(L')_T → 𝔸(N')_T`. -/
def aO (T : Over S) : (𝐔 L' T).P ⟶ (𝐔 𝐍 T).P :=
  (𝐔 𝐍 T).lift (𝐔 L' T).π (APt.restrict (gluedMagnet_le hNL hL.faceCond) (𝐔 L' T).u)

/-- `𝔸(N)_T → 𝔸(N')_T`. -/
def cO (T : Over S) : (𝐔 N T).P ⟶ (𝐔 𝐍 T).P :=
  (𝐔 𝐍 T).lift (𝐔 N T).π (APt.faceExt (isFace_glued hNL hL) (𝐔 N T).u)

/-- `𝔸(L)_T → 𝔸(L')_T`. -/
def bA (T : Over S) : (𝐔 L T).P ⟶ (𝐔 L' T).P :=
  (𝐔 L' T).lift (𝐔 L T).π (APt.faceExt hL (𝐔 L T).u)

/-- `𝔸(L)_T → 𝔸(N)_T`. -/
def bC (T : Over S) : (𝐔 L T).P ⟶ (𝐔 N T).P :=
  (𝐔 N T).lift (𝐔 L T).π (APt.restrict hNL (𝐔 L T).u)

lemma pts_self (E : AddSubmonoid M) (R : Scheme.{u}) :
    pts (A E R) (𝟙 _) = ptsZ (A E R).left (toAZ E R) := by
  have h : ∀ f : A E R ⟶ A E R, f = 𝟙 _ →
      ptsZ (A E R).left (f.left ≫ toAZ E R) = ptsZ (A E R).left (toAZ E R) := by
    rintro f rfl
    simp
  exact h _ rfl

lemma aO_left (T : Over S) : (aO hNL hL T).left = (aMor (S := T.left) hNL hL.faceCond).left := by
  refine lift_left_eq T _ _ ?_
  have h := pts_comp_Amap (S := T.left) (AddSubmonoid.inclusion (gluedMagnet_le hNL hL.faceCond))
    (𝟙 (A L' T.left))
  rw [Category.id_comp, pts_self] at h
  exact h

lemma bC_left (T : Over S) : (bC hNL T).left = (bCMor (S := T.left) hNL).left := by
  refine lift_left_eq T _ _ ?_
  have h := pts_comp_Amap (S := T.left) (AddSubmonoid.inclusion hNL) (𝟙 (A L T.left))
  rw [Category.id_comp, pts_self] at h
  exact h

lemma faceA_left {E G : AddSubmonoid M} (h : IsFace E G) (T : Over S) :
    ((𝐔 G T).lift (𝐔 E T).π (APt.faceExt h (𝐔 E T).u)).left =
      (faceA T.left h.faceCond).left := by
  refine lift_left_eq T _ _ ?_
  have e := pts_comp_faceA (S := T.left) h.faceCond (𝟙 (A E T.left))
  rw [Category.id_comp, pts_self] at e
  exact e

lemma cO_left (T : Over S) : (cO hNL hL T).left = (cMor (S := T.left) hNL hL.faceCond).left :=
  faceA_left (isFace_glued hNL hL) T

lemma bA_left (T : Over S) : (bA hL T).left = (bAMor (S := T.left) hL.faceCond).left :=
  faceA_left hL T

theorem po36 (T : Over S) : IsPushout (bA hL T).left (bC hNL T).left (aO hNL hL T).left
    (cO hNL hL T).left := by
  rw [aO_left, bC_left, cO_left, bA_left]
  exact isPushout_glued hNL hL.le hL.faceCond

lemma po_ext (T : Over S) {W : Over S} {w w' : (𝐔 𝐍 T).P ⟶ W}
    (h1 : aO hNL hL T ≫ w = aO hNL hL T ≫ w') (h2 : cO hNL hL T ≫ w = cO hNL hL T ≫ w') : w = w' :=
  Over.OverMorphism.ext ((po36 hNL hL T).hom_ext (congrArg (fun k => k.left) h1)
    (congrArg (fun k => k.left) h2))

lemma exists_po_desc (T : Over S) {W : Over S} (wf : (𝐔 L' T).P ⟶ W) (wg : (𝐔 N T).P ⟶ W)
    (h : bA hL T ≫ wf = bC hNL T ≫ wg) :
    ∃ w : (𝐔 𝐍 T).P ⟶ W, aO hNL hL T ≫ w = wf ∧ cO hNL hL T ≫ w = wg := by
  have hp := po36 hNL hL T
  let d := hp.desc wf.left wg.left (congrArg (fun k => k.left) h)
  have ha : (aO hNL hL T).left ≫ d = wf.left := hp.inl_desc _ _ _
  have hc : (cO hNL hL T).left ≫ d = wg.left := hp.inr_desc _ _ _
  have hw : d ≫ W.hom = (𝐔 𝐍 T).P.hom := by
    refine hp.hom_ext ?_ ?_
    · rw [← Category.assoc, ha, Over.w wf]
      exact (Over.w (aO hNL hL T)).symm
    · rw [← Category.assoc, hc, Over.w wg]
      exact (Over.w (cO hNL hL T)).symm
  exact ⟨Over.homMk d hw, Over.OverMorphism.ext ha, Over.OverMorphism.ext hc⟩

end Legs

section Main

local notation "𝐔" => universalPoint

variable {N L L' : AddSubmonoid M} (hNL : N ≤ L) (hL : IsFace L L')
variable {X : Over S} {act : AAction (overO S) M (yoneda.obj X)}

local notation "𝐍" => gluedMagnet hNL (IsFace.faceCond hL)

lemma lift_restrict {E G : AddSubmonoid M} (h : E ≤ G) (T : Over S) {T' : Over S} (t : T' ⟶ T)
    (b : APt (overO S) G (op T')) :
    (𝐔 E T).lift t (APt.restrict h b) =
      (𝐔 G T).lift t b ≫ (𝐔 E T).lift (𝐔 G T).π (APt.restrict h (𝐔 G T).u) := by
  symm
  refine (𝐔 E T).uniq _ _ _ ?_ ?_
  · rw [Category.assoc, UniversalPoint.lift_π, UniversalPoint.lift_π]
  · rw [op_comp, APt.res_comp, UniversalPoint.res_lift, ← APt.restrict_res,
      UniversalPoint.res_lift]

lemma lift_faceExt {E G : AddSubmonoid M} (h : IsFace E G) (T : Over S) {T' : Over S} (t : T' ⟶ T)
    (b : APt (overO S) E (op T')) :
    (𝐔 G T).lift t (APt.faceExt h b) =
      (𝐔 E T).lift t b ≫ (𝐔 G T).lift (𝐔 E T).π (APt.faceExt h (𝐔 E T).u) := by
  symm
  refine (𝐔 G T).uniq _ _ _ ?_ ?_
  · rw [Category.assoc, UniversalPoint.lift_π, UniversalPoint.lift_π]
  · rw [op_comp, APt.res_comp, UniversalPoint.res_lift, ← APt.faceExt_res,
      UniversalPoint.res_lift]

/-- The equivariance identity for a morphism `w : 𝔸(N')_T → X`, at a point. -/
def EqvAt (T : Over S) (w : (𝐔 𝐍 T).P ⟶ X) {Q : Over S} (t : Q ⟶ T) (h : APt (overO S) M (op Q))
    (b : APt (overO S) 𝐍 (op Q)) : Prop :=
  (𝐔 𝐍 T).lift t (APt.toMagnet 𝐍 h * b) ≫ w = act.smul h ((𝐔 𝐍 T).lift t b ≫ w)

/-- **Proposition 3.36 (i)**, the step *the lower rectangle commutes*: `w` is equivariant as soon as
it is on the two legs of the push-out. -/
theorem eqvAt_of_legs (T : Over S) (w : (𝐔 𝐍 T).P ⟶ X)
    (h1 : ∀ {Q : Over S} (t : Q ⟶ T) (h : APt (overO S) M (op Q)) (b : APt (overO S) L' (op Q)),
      EqvAt (act := act) hNL hL T w t h (APt.restrict (gluedMagnet_le hNL hL.faceCond) b))
    (h2 : ∀ {Q : Over S} (t : Q ⟶ T) (h : APt (overO S) M (op Q)) (b : APt (overO S) N (op Q)),
      EqvAt (act := act) hNL hL T w t h (APt.faceExt (isFace_glued hNL hL) b))
    {T' : Over S} (t : T' ⟶ T) (h : APt (overO S) M (op T')) (a : APt (overO S) 𝐍 (op T')) :
    EqvAt (act := act) hNL hL T w t h a := by
  let U' := 𝐔 𝐍 T'
  let tP : U'.P ⟶ T := U'.π ≫ t
  let hP : APt (overO S) M (op U'.P) := APt.res U'.π.op h
  have key : ∀ {Q : Over S} (s : Q ⟶ U'.P),
      s ≫ (𝐔 𝐍 T).lift tP (APt.toMagnet 𝐍 hP * U'.u) ≫ w =
        s ≫ act.smul hP ((𝐔 𝐍 T).lift tP U'.u ≫ w) ↔
      EqvAt (act := act) hNL hL T w (s ≫ tP) (APt.res s.op hP) (APt.res s.op U'.u) := by
    intro Q s
    have e1 := UniversalPoint.lift_comp (𝐔 𝐍 T) s tP (APt.toMagnet 𝐍 hP * U'.u)
    have e2 := UniversalPoint.lift_comp (𝐔 𝐍 T) s tP U'.u
    have e3 : s ≫ act.smul hP ((𝐔 𝐍 T).lift tP U'.u ≫ w) =
        act.smul (APt.res s.op hP) (s ≫ (𝐔 𝐍 T).lift tP U'.u ≫ w) :=
      act.map_smul s.op hP _
    have e4 : APt.res s.op (APt.toMagnet 𝐍 hP * U'.u) =
        APt.toMagnet 𝐍 (APt.res s.op hP) * APt.res s.op U'.u := by
      rw [APt.res_mul]
      rfl
    rw [e3, EqvAt, ← e4, e1, e2, Category.assoc, Category.assoc]
  have hall : (𝐔 𝐍 T).lift tP (APt.toMagnet 𝐍 hP * U'.u) ≫ w =
      act.smul hP ((𝐔 𝐍 T).lift tP U'.u ≫ w) := by
    refine po_ext hNL hL T' ?_ ?_
    · refine (key _).2 ?_
      have e : APt.res (aO hNL hL T').op U'.u =
          APt.restrict (gluedMagnet_le hNL hL.faceCond) (𝐔 L' T').u := UniversalPoint.res_lift _ _ _
      rw [e]
      exact h1 _ _ _
    · refine (key _).2 ?_
      have e : APt.res (cO hNL hL T').op U'.u =
          APt.faceExt (isFace_glued hNL hL) (𝐔 N T').u := UniversalPoint.res_lift _ _ _
      rw [e]
      exact h2 _ _ _
  let ξ : T' ⟶ U'.P := U'.lift (𝟙 T') a
  have hξ : ξ ≫ U'.π = 𝟙 T' := U'.lift_π _ _
  have e0 := (key ξ).1 (congrArg (ξ ≫ ·) hall)
  have e1 : ξ ≫ tP = t := by
    change ξ ≫ U'.π ≫ t = t
    rw [← Category.assoc, hξ, Category.id_comp]
  have e2 : APt.res ξ.op hP = h := by
    change APt.res ξ.op (APt.res U'.π.op h) = h
    rw [← APt.res_comp, ← op_comp, hξ]
    exact APt.res_id h
  have e3 : APt.res ξ.op U'.u = a := U'.res_lift _ _
  rwa [e1, e2, e3] at e0

variable (act) in
/-- The point of `X^{N'}` given by `w`. -/
def ptOfW (T : Over S) (w : (𝐔 𝐍 T).P ⟶ X)
    (he : ∀ {T' : Over S} (t : T' ⟶ T) (h : APt (overO S) M (op T')) (a : APt (overO S) 𝐍 (op T')),
      EqvAt (act := act) hNL hL T w t h a) : AttractorPt act 𝐍 T where
  app t a := (𝐔 𝐍 T).lift t a ≫ w
  naturality s t a := by
    rw [UniversalPoint.lift_comp, Category.assoc]
    rfl
  equivariant t h a := he t h a

/-- **Proposition 3.36 (i)**, push-out form: `X^{N'}(T) = X^{L'}(T) ×_{X^L(T)} X^N(T)`. -/
theorem cart36_glued_bijective (T : Over S) :
    Function.Bijective (cart36 (act := act) (T := T) (gluedMagnet_le hNL hL.faceCond) hNL hL
      (isFace_glued hNL hL) (fun _ hx hxL => by
        by_contra hn
        exact hx.2 ⟨hxL, hn⟩)) := by
  have hLU : ∀ {E : AddSubmonoid M} (φ : AttractorPt act E T) {T' : Over S} (t : T' ⟶ T)
      (a : APt (overO S) E (op T')), (𝐔 E T).lift t a ≫ φ.app (𝐔 E T).π (𝐔 E T).u = φ.app t a :=
    fun φ _ t a => (φ.app_eq_of_universal (𝐔 _ T) t a).symm
  constructor
  · intro x x' h
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg (fun p => p.1.2) h
    have hu : x.app (𝐔 𝐍 T).π (𝐔 𝐍 T).u = x'.app (𝐔 𝐍 T).π (𝐔 𝐍 T).u := by
      refine po_ext hNL hL T ?_ ?_
      · rw [aO, hLU, hLU]
        exact congrArg (fun φ : AttractorPt act L' T => φ.app (𝐔 L' T).π (𝐔 L' T).u) h1
      · rw [cO, hLU, hLU]
        exact congrArg (fun φ : AttractorPt act N T => φ.app (𝐔 N T).π (𝐔 N T).u) h2
    refine AttractorPt.ext ?_
    funext T' t a
    rw [← hLU x, ← hLU x', hu]
  · rintro ⟨⟨f, g⟩, hfg⟩
    have hfg' : AttractorPt.ofFace hL f = AttractorPt.ofLE hNL g := hfg
    have hcomp : bA hL T ≫ f.app (𝐔 L' T).π (𝐔 L' T).u = bC hNL T ≫ g.app (𝐔 N T).π (𝐔 N T).u := by
      rw [bA, bC, hLU, hLU]
      exact congrArg (fun φ : AttractorPt act L T => φ.app (𝐔 L T).π (𝐔 L T).u) hfg'
    obtain ⟨w, ha, hc⟩ := exists_po_desc hNL hL T _ _ hcomp
    have hf : ∀ {Q : Over S} (t : Q ⟶ T) (b : APt (overO S) L' (op Q)),
        (𝐔 𝐍 T).lift t (APt.restrict (gluedMagnet_le hNL hL.faceCond) b) ≫ w = f.app t b := by
      intro Q t b
      rw [lift_restrict, Category.assoc]
      change _ ≫ aO hNL hL T ≫ w = _
      rw [ha, hLU]
    have hg : ∀ {Q : Over S} (t : Q ⟶ T) (b : APt (overO S) N (op Q)),
        (𝐔 𝐍 T).lift t (APt.faceExt (isFace_glued hNL hL) b) ≫ w = g.app t b := by
      intro Q t b
      rw [lift_faceExt, Category.assoc]
      change _ ≫ cO hNL hL T ≫ w = _
      rw [hc, hLU]
    have he : ∀ {T' : Over S} (t : T' ⟶ T) (h : APt (overO S) M (op T'))
        (a : APt (overO S) 𝐍 (op T')), EqvAt (act := act) hNL hL T w t h a :=
      fun t h a => eqvAt_of_legs (act := act) hNL hL T w
      (fun t h b => by
        have e : APt.toMagnet (gluedMagnet hNL hL.faceCond) h *
            APt.restrict (gluedMagnet_le hNL hL.faceCond) b =
            APt.restrict (gluedMagnet_le hNL hL.faceCond) (APt.toMagnet L' h * b) := rfl
        rw [EqvAt, hf t b, e, hf t, f.equivariant])
      (fun t h b => by
        rw [EqvAt, hg t b, ← APt.faceExt_mul, hg t, g.equivariant]) t h a
    refine ⟨ptOfW hNL hL act T w he, Subtype.ext (Prod.ext ?_ ?_)⟩
    · refine AttractorPt.ext ?_
      funext T' t b
      exact hf t b
    · refine AttractorPt.ext ?_
      funext T' t b
      exact hg t b

/-- **Proposition 3.36 (i)**. `M` any commutative monoid, `X` any scheme over any `S`, `T` any scheme
over `S`. If `L ⊆ L'` is a face, `N' ⊆ L'`, `N = L ∩ N'` and `N' = L' \ (L \ N)`, then `X^{N'}` is the
fibre product `X^{L'} ×_{X^L} X^N` on `T`-points, along `ι_{N',L'}`, `p_{N,N'}`, `p_{L,L'}`, `ι_{N,L}`. -/
theorem prop336_i {N' : AddSubmonoid M} (hN : IsFace N N') (hN'L' : N' ≤ L')
    (hc : ∀ x ∈ N', x ∈ L → x ∈ N)
    (hi : ∀ x, x ∈ N' ↔ x ∈ L' ∧ ¬ (x ∈ L ∧ x ∉ N)) (T : Over S) :
    Function.Bijective (cart36 (act := act) (T := T) hN'L' hNL hL hN hc) := by
  have e : N' = gluedMagnet hNL hL.faceCond := AddSubmonoid.ext hi
  subst e
  exact cart36_glued_bijective hNL hL T

end Main

end GB

end AlgMag

end

section

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical


namespace AlgMag.GB

attribute [local instance] gradedAlgebraOf

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]
variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))
variable {U : S.Opens} (hU : IsAffineOpen U)

/-- A point of `X^E`, evaluated at the point `a` of `𝔸(E)`, on `b ∈ A_m`: it is `a(m) x(b)`. The graded
map `f : A → Γ(T, ⊤)[E]` sends `b` to `f(b) = x(b) X^m`. -/
lemma ptX_app_of_mem {E : AddSubmonoid M} {T : Over S} (hT : LiesOver T U)
    (φ : AttractorPt act E T) (a : APt (overO S) E (op T)) {m : M} (hm : m ∈ E) {b : Aalg X U}
    (hb : b ∈ gradingOf hU act m) :
    ptX X hU T hT (φ.app (𝟙 T) a) b =
      toGa hU hT a (Multiplicative.ofAdd (⟨m, hm⟩ : E)) * ptX X hU T hT φ.toPoint b := by
  obtain ⟨F, rfl⟩ := (localEquiv hU act E hT).symm.surjective φ
  change ptX X hU T hT (grVal hU act E hT (𝟙 T) a _) b =
    _ * ptX X hU T hT (grVal hU act E hT (𝟙 T) 1 _) b
  rw [grVal, grVal, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  obtain ⟨c, hc⟩ := exists_single_of_mem_magnetGrading hm
    ((attractorEquiv (gradingOf hU act) E _ F).map_mem hb)
  simp only [AlgHom.comp_apply]
  erw [hc, evalAlg_single, evalAlg_single]
  rw [mul_comm]
  have h1 : toGa hU (hT.of_hom (𝟙 T)) (1 : APt (overO S) E (op T)) = 1 := MonoidHom.ext fun _ => rfl
  rw [h1]
  simp
  exact congrArg _ (mul_one (c : Ga hU T hT)).symm

variable {N N' L L' : AddSubmonoid M}

/-- **Proposition 3.36 (ii)**. `X` affine over the affine open `U` of `S` (the printed case: `S` affine,
`U = S`, `T` arbitrary), `L ⊆ L'` a face, `N', L ⊆ L'`, `N = L ∩ N'` (that is `hNL`, `hN` and `hc`), `L' = L + N'`, and `A_l A_{n'} = A_{l+n'}`
for all `l ∈ L \ N`, `n' ∈ N'`. Then `X^{N'}` is the fibre product `X^{L'} ×_{X^L} X^N` on points over `U`. -/
theorem prop336_ii (hNL : N ≤ L) (hL : IsFace L L') (hN : IsFace N N') (hN'L' : N' ≤ L')
    (hsum : L' = L ⊔ N')
    (hA : ∀ l ∈ L, l ∉ N → ∀ n ∈ N', gradingOf hU act l * gradingOf hU act n =
      gradingOf hU act (l + n))
    {T : Over S} (hT : LiesOver T U) (hc : ∀ x ∈ N', x ∈ L → x ∈ N) :
    Function.Bijective (cart36 (act := act) (T := T) hN'L' hNL hL hN hc) := by
  constructor
  · intro x x' h
    apply toPoint_injective_global
    have h1 := congrArg (fun p => (p.1.1 : AttractorPt act L' T).toPoint) h
    exact h1
  · rintro ⟨⟨f, g⟩, hfg⟩
    have hfg' : AttractorPt.ofFace hL f = AttractorPt.ofLE hNL g := hfg
    -- on `A_l`, `l ∈ L`, the points `f` and `g` of `X` agree
    have hLeq : ∀ {l : M} (hl : l ∈ L) {b : Aalg X U}, b ∈ gradingOf hU act l →
        ptX X hU T hT f.toPoint b = ptX X hU T hT g.toPoint b := by
      intro l hl b hb
      have e1 : (AttractorPt.ofFace hL f).toPoint = (AttractorPt.ofLE hNL g).toPoint := by
        rw [hfg']
      have e2 : (AttractorPt.ofLE hNL g).toPoint = g.toPoint := rfl
      have e3 := ptX_app_of_mem act hU hT f (APt.faceExt hL 1) (hL.le hl) hb
      have e4 : toGa hU hT (APt.faceExt hL (1 : APt (overO S) L (op T)))
          (Multiplicative.ofAdd (⟨l, hL.le hl⟩ : L')) = 1 :=
        APt.faceExt_pos hL (1 : APt (overO S) L (op T))
          (n := Multiplicative.ofAdd (⟨l, hL.le hl⟩ : L')) hl
      rw [e4, one_mul] at e3
      rw [← e3, ← e2, ← e1]
      rfl
    -- `f` kills `J_{N'}`
    have hkill : ∀ a ∈ magnetIdeal (gradingOf hU act) N', ptX X hU T hT f.toPoint a = 0 := by
      have hle : magnetIdeal (gradingOf hU act) N' ≤
          RingHom.ker (ptX X hU T hT f.toPoint : Aalg X U →+* Ga hU T hT) := by
        rw [magnetIdeal, Ideal.span_le]
        simp only [Set.iUnion_subset_iff]
        intro m hm a ha
        by_cases hmL : m ∈ L'
        · rw [hsum] at hmL
          obtain ⟨l, hl, n, hn, rfl⟩ := AddSubmonoid.mem_sup.mp hmL
          have hlN : l ∉ N := fun h => hm (N'.add_mem (hN.le h) hn)
          rw [← hA l hl hlN n hn] at ha
          refine Submodule.mul_induction_on ha (fun b hb c _ => ?_) (fun u v hu hv => ?_)
          · change ptX X hU T hT f.toPoint (b * c) = 0
            rw [map_mul, hLeq hl hb,
              toPoint_kills hU act N hT g (mem_magnetIdeal_of_notMem hlN hb), zero_mul]
          · exact Ideal.add_mem _ hu hv
        · exact toPoint_kills hU act L' hT f (mem_magnetIdeal_of_notMem hmL ha)
      exact fun a ha => hle ha
    obtain ⟨φ, hφ⟩ := (exists_att_iff_kills act hU hT f.toPoint).2 hkill
    refine ⟨φ, Subtype.ext (Prod.ext ?_ ?_)⟩
    · apply toPoint_injective_global
      exact hφ
    · apply toPoint_injective_global
      apply (ptX X hU T hT).injective
      refine algHom_ext_of_homogeneous (D := Ga hU T hT) (gradingOf hU act) fun m b hb => ?_
      by_cases hm : m ∈ N
      · have e3 := ptX_app_of_mem act hU hT φ (APt.faceExt hN 1) (hN.le hm) hb
        have e4 : toGa hU hT (APt.faceExt hN (1 : APt (overO S) N (op T)))
            (Multiplicative.ofAdd (⟨m, hN.le hm⟩ : N')) = 1 :=
          APt.faceExt_pos hN (1 : APt (overO S) N (op T))
            (n := Multiplicative.ofAdd (⟨m, hN.le hm⟩ : N')) hm
        rw [e4, one_mul, hφ, hLeq (hNL hm) hb] at e3
        exact e3
      · refine (toPoint_kills hU act N hT (AttractorPt.ofFace hN φ)
          (mem_magnetIdeal_of_notMem hm hb)).trans ?_
        exact (toPoint_kills hU act N hT g (mem_magnetIdeal_of_notMem hm hb)).symm

end AlgMag.GB

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

open SQ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section P331

variable {M Z : Type u} [AddCommMonoid M] [AddCommGroup Z]

/-- `(m, y) ↦ f(m) - y`: the grading of `R[M × Y]`. -/
def dl (f : M →+ Z) (Y : AddSubmonoid Z) : M × Y →+ Z :=
  f.comp (AddMonoidHom.fst M Y) - Y.subtype.comp (AddMonoidHom.snd M Y)

/-- `n ↦ (n, f(n))`, dual to `D(M) × 𝔸(Y) → 𝔸(N)`, `(g, x) ↦ g x`. -/
def jn (f : M →+ Z) (Y : AddSubmonoid Z) : Y.comap f →+ M × Y :=
  AddMonoidHom.prod (Y.comap f).subtype (linMagnetHom f Y)

lemma jn_inj (f : M →+ Z) (Y : AddSubmonoid Z) : Function.Injective (jn f Y) := fun _ _ h =>
  Subtype.ext (congrArg Prod.fst h)

lemma dl_eq_zero (f : M →+ Z) (Y : AddSubmonoid Z) (p : M × Y) :
    dl f Y p = 0 ↔ p ∈ Set.range (jn f Y) := by
  constructor
  · intro h
    have e : f p.1 = (p.2 : Z) := sub_eq_zero.1 h
    refine ⟨⟨p.1, show f p.1 ∈ Y by rw [e]; exact p.2.2⟩, Prod.ext rfl (Subtype.ext e)⟩
  · rintro ⟨k, rfl⟩
    exact sub_self (f k)

variable [Countable M] [Countable Z] [AddMonoid.FG Z] {f : M →+ Z} {Y : AddSubmonoid Z}
variable {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}

/-- `G(c) = c|_M • ψ(c|_Y)`, the map `(g, x) ↦ g • ψ(x)` of the printed proof, at a point `c`. -/
noncomputable def gVal {T : BigFppfOver B S hS} (ψ : AttractorPt (actAlong f aX) Y T)
    {T' : BigFppfOver B S hS}
    (t : T' ⟶ T) (c : APt (fppfO B S hS) (M × Y) (op T')) : T' ⟶ U :=
  aX.smul (APt.along (AddMonoidHom.inl M Y) c) (ψ.app t (APt.along (AddMonoidHom.inr M Y) c))

omit [Countable M] [Countable Z] [AddMonoid.FG Z] in
lemma gVal_res {T : BigFppfOver B S hS} (ψ : AttractorPt (actAlong f aX) Y T)
    {T' T'' : BigFppfOver B S hS} (s : T'' ⟶ T') (t : T' ⟶ T)
    (c : APt (fppfO B S hS) (M × Y) (op T')) :
    gVal ψ (s ≫ t) (APt.res s.op c) = s ≫ gVal ψ t c := by
  have e := aX.map_smul s.op (APt.along (AddMonoidHom.inl M Y) c)
    (ψ.app t (APt.along (AddMonoidHom.inr M Y) c))
  have hn := ψ.naturality s t (APt.along (AddMonoidHom.inr M Y) c)
  refine Eq.trans ?_ e.symm
  exact congrArg (aX.smul _) hn

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The morphism `F : D(M)_T × 𝔸(Y)_T → X` of the printed proof. -/
noncomputable def gX (ψ : AttractorPt (actAlong f aX) Y T) : specObj (M × Y) T ⟶ U :=
  gVal ψ (specPr _ T) (specPt _ T)

lemma lift_gX (ψ : AttractorPt (actAlong f aX) Y T) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (c : APt (fppfO B S hS) (M × Y) (op T')) : specLift t c ≫ gX ψ = gVal ψ t c := by
  have h := gVal_res ψ (specLift t c) (specPr _ T) (specPt _ T)
  rw [specLift_pr, res_specLift] at h
  exact h.symm

/-- `F` is invariant under `D(Z)`: the group `D(Z)` acts by `k (g, x) = (g k, k⁻¹ x)`. The printed proof
restricts to `D(f(M) + Y^gp)` and claims that this action is free, which fails unless `Y^gp ⊆ f(M)`;
freeness is not used here. -/
theorem isInvariant_gX (ψ : AttractorPt (actAlong f aX) Y T) :
    IsInvariantF (monCoact (R := Γ((SCH).obj T, ⊤)) (dl f Y)) ((SCH).map (gX ψ)) := by
  let A := gRing (M × Y) T
  let ρ : RT T →+* AddMonoidAlgebra A Z := (cC A Z).comp (algebraMap _ _)
  have hC : B.Contains (Spec (.of (AddMonoidAlgebra A Z))) := contains_M (contains_spec _ T)
  let t := spToT T ρ hC
  let σ : A →+* AddMonoidAlgebra A Z := (monCoact (R := Γ((SCH).obj T, ⊤)) (dl f Y)).σ
  have hσ : σ.comp (algebraMap _ _) = ρ := by
    refine RingHom.ext fun r => ?_
    change monσ _ (AddMonoidAlgebra.single 0 r) = _
    rw [monσ_single, map_zero]
    rfl
  let a₁ := spPt (T := T) (ρ := ρ) (hC := hC) (σ.toMonoidHom.comp (AddMonoidAlgebra.of _ _))
  let a₂ := spPt (T := T) (ρ := ρ) (hC := hC) ((cC A Z).toMonoidHom.comp (AddMonoidAlgebra.of _ _))
  let E : Multiplicative Z →* AddMonoidAlgebra A Z := AddMonoidAlgebra.of _ _
  let e := spPt (T := T) (ρ := ρ) (hC := hC) E
  have ha : ∀ p : Multiplicative (M × Y),
      a₁ p = e (Multiplicative.ofAdd (dl f Y (Multiplicative.toAdd p))) * a₂ p := by
    intro p
    change spSec T ρ hC (σ (AddMonoidAlgebra.single (Multiplicative.toAdd p) 1)) =
      spSec T ρ hC _ * spSec T ρ hC _
    rw [← map_mul]
    congr 1
    change monσ _ _ = _
    rw [monσ_single]
    simp [E, cC, AddMonoidAlgebra.single_mul_single]
    rfl
  let k : APt (fppfO B S hS) M (op (spObj T ρ hC)) := e.comp (AddMonoidHom.toMultiplicative f)
  have hl : APt.along (AddMonoidHom.inl M Y) a₁ = k * APt.along (AddMonoidHom.inl M Y) a₂ := by
    refine MonoidHom.ext fun m => ?_
    refine (ha _).trans ?_
    have : dl f Y (Multiplicative.toAdd m, 0) = f (Multiplicative.toAdd m) := by simp [dl]
    change e (Multiplicative.ofAdd (dl f Y (Multiplicative.toAdd m, 0))) * _ = _
    rw [this]
    rfl
  have hr : APt.along (AddMonoidHom.inr M Y) a₂ =
      APt.toMagnet Y e * APt.along (AddMonoidHom.inr M Y) a₁ := by
    refine MonoidHom.ext fun y => ?_
    change _ = e (Multiplicative.ofAdd ((Multiplicative.toAdd y : Y) : Z)) *
      a₁ (Multiplicative.ofAdd (0, Multiplicative.toAdd y))
    rw [ha]
    have h0 : dl f Y (0, Multiplicative.toAdd y) = -((Multiplicative.toAdd y : Y) : Z) := by
      simp [dl]
    change _ = e _ * (e (Multiplicative.ofAdd (dl f Y (0, Multiplicative.toAdd y))) * _)
    rw [h0, ← mul_assoc, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one, one_mul]
    rfl
  have heq : gVal ψ t a₁ = gVal ψ t a₂ := by
    change aX.smul _ _ = aX.smul _ (ψ.app t _)
    rw [hl, hr, ψ.equivariant, mul_comm k]
    exact aX.mul_smul _ k _
  rw [← lift_gX, ← lift_gX] at heq
  have h1 := congrArg (fun w => (SCH).map w) heq
  simp only [Functor.map_comp] at h1
  rw [map_specLift_spPt σ hσ, map_specLift_spPt (cC A Z) rfl] at h1
  exact h1

/-- **The descent**: `F` factors through `(g, x) ↦ g x`, `D(M)_T × 𝔸(Y)_T → 𝔸(N)_T`. -/
theorem exists_x₁ (ψ : AttractorPt (actAlong f aX) Y T) :
    ∃ x₀ : specObj (Y.comap f) T ⟶ U, specAlong T (jn f Y) ≫ x₀ = gX ψ := by
  let R := Γ((SCH).obj T, ⊤)
  have hι := monCoact_isInv (R := R) (δ := dl f Y) (jn_inj f Y) (dl_eq_zero f Y)
  obtain ⟨g, hg⟩ := exists_desc (R := R) (dl f Y) (jn_inj f Y) (dl_eq_zero f Y) (isInvariant_gX ψ)
  refine ⟨overHom g ?_, toScheme_map_injective ?_⟩
  · refine desc_unique hι.isSplit ?_
    have e1 : sp (monι (jn f Y) R) ≫ specPrS (Y.comap f) T = specPrS (M × Y) T := by
      rw [sp_specPrS, monι_comp_algebraMap]
      rfl
    have e2 : (SCH).map (gX ψ) ≫ U.hom.hom = specPrS (M × Y) T ≫ T.hom.hom := site_w (gX ψ)
    change sp (monι (jn f Y) R) ≫ g ≫ U.hom.hom = sp (monι (jn f Y) R) ≫ specPrS (Y.comap f) T ≫ T.hom.hom
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.hom.hom) hg).trans (e2.trans
      ((congrArg (· ≫ T.hom.hom) e1).symm.trans (Category.assoc _ _ _))))
  · rw [Functor.map_comp]
    exact hg

lemma lift_x₁ {ψ : AttractorPt (actAlong f aX) Y T} {x₀ : specObj (Y.comap f) T ⟶ U}
    (hx : specAlong T (jn f Y) ≫ x₀ = gX ψ) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (c : APt (fppfO B S hS) (M × Y) (op T')) :
    specLift t (APt.along (jn f Y) c) ≫ x₀ = gVal ψ t c := by
  rw [specLift_along, Category.assoc, hx, lift_gX]

/-- The induced map `𝔸(N)_T → X_T` is `D(M)_T`-equivariant. -/
theorem equivariant_x₁ {ψ : AttractorPt (actAlong f aX) Y T} {x₀ : specObj (Y.comap f) T ⟶ U}
    (hx : specAlong T (jn f Y) ≫ x₀ = gX ψ) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (h : APt (fppfO B S hS) M (op T')) (a : APt (fppfO B S hS) (Y.comap f) (op T')) :
    specLift t (APt.toMagnet (Y.comap f) h * a) ≫ x₀ = aX.smul h (specLift t a ≫ x₀) := by
  let R := Γ((SCH).obj T, ⊤)
  let N := Y.comap f
  let P₂ := ↥N × M
  let Pm := (M × Y) × M
  let Q := specObj P₂ T
  let tQ : Q ⟶ T := specPr P₂ T
  let aU : APt (fppfO B S hS) ↥N (op Q) := APt.along (AddMonoidHom.inl _ _) (specPt P₂ T)
  let hU : APt (fppfO B S hS) M (op Q) := APt.along (AddMonoidHom.inr _ _) (specPt P₂ T)
  let jh : P₂ →+ Pm := (jn f Y).prodMap (AddMonoidHom.id M)
  let δh : Pm →+ Z := (dl f Y).comp (AddMonoidHom.fst _ _)
  have hι : (monCoact (R := R) δh).IsInv (monι jh R) := monCoact_isInv
    (Function.Injective.prodMap (jn_inj f Y) Function.injective_id) (fun p => by
      constructor
      · intro hp
        obtain ⟨k, hk⟩ := (dl_eq_zero f Y p.1).1 hp
        exact ⟨(k, p.2), Prod.ext hk rfl⟩
      · rintro ⟨k, rfl⟩
        exact (dl_eq_zero f Y _).2 ⟨k.1, rfl⟩)
  let π : specObj Pm T ⟶ Q := specAlong T jh
  let tm : specObj Pm T ⟶ T := specPr Pm T
  let ch : APt (fppfO B S hS) (M × Y) (op (specObj Pm T)) :=
    APt.along (AddMonoidHom.inl _ _) (specPt Pm T)
  let eh : APt (fppfO B S hS) M (op (specObj Pm T)) :=
    APt.along (AddMonoidHom.inr _ _) (specPt Pm T)
  have hπt : π ≫ tQ = tm := specAlong_pr T jh
  have hra : APt.res π.op aU = APt.along (jn f Y) ch := by
    have e := res_specAlong T jh
    refine MonoidHom.ext fun p => ?_
    exact congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ _) p)) e
  have hrh : APt.res π.op hU = eh := by
    have e := res_specAlong T jh
    refine MonoidHom.ext fun p => ?_
    refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inr _ _) p)) e).trans ?_
    have e0 : jh (0, Multiplicative.toAdd p) = (0, Multiplicative.toAdd p) :=
      Prod.ext (map_zero (jn f Y)) rfl
    exact congrArg (fun q => specPt Pm T (Multiplicative.ofAdd q)) e0
  let sh : APt (fppfO B S hS) (M × Y) (op (specObj Pm T)) :=
    eh.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M Y)) * ch
  have hmag : APt.along (jn f Y) sh = APt.toMagnet N eh * APt.along (jn f Y) ch :=
    MonoidHom.ext fun p => rfl
  have hφsm : gVal ψ tm sh = aX.smul eh (gVal ψ tm ch) := by
    have e1 : APt.along (AddMonoidHom.inl M Y) sh = eh * APt.along (AddMonoidHom.inl M Y) ch :=
      MonoidHom.ext fun p => rfl
    have e2 : APt.along (AddMonoidHom.inr M Y) sh = APt.along (AddMonoidHom.inr M Y) ch := by
      refine MonoidHom.ext fun y => ?_
      change eh (Multiplicative.ofAdd 0) * _ = _
      have : eh (Multiplicative.ofAdd (0 : M)) = 1 := map_one eh
      rw [this, one_mul]
      rfl
    change aX.smul _ (ψ.app tm _) = _
    rw [e1, e2, aX.mul_smul]
    rfl
  have huniv : specLift tQ (APt.toMagnet N hU * aU) ≫ x₀ = aX.smul hU (specLift tQ aU ≫ x₀) := by
    apply toScheme_map_injective
    refine desc_unique hι.isSplit ?_
    have e0 : ∀ w : Q ⟶ U, sp (monι jh R) ≫ (SCH).map w = (SCH).map (π ≫ w) := fun w => by
      rw [Functor.map_comp]
      rfl
    rw [e0, e0]
    congr 1
    have e1 : π ≫ specLift tQ (APt.toMagnet N hU * aU) = specLift tm (APt.along (jn f Y) sh) := by
      rw [← specLift_comp, hπt, hmag, APt.res_mul, hra, ← APt.toMagnet_res, hrh]
    have e2 : π ≫ specLift tQ aU = specLift tm (APt.along (jn f Y) ch) := by
      rw [← specLift_comp, hπt, hra]
    have e3 : (yoneda.obj U).map π.op (aX.smul hU (specLift tQ aU ≫ x₀)) =
        aX.smul (APt.res π.op hU) ((yoneda.obj U).map π.op (specLift tQ aU ≫ x₀)) :=
      aX.map_smul π.op hU _
    change _ = (yoneda.obj U).map π.op (aX.smul hU (specLift tQ aU ≫ x₀))
    rw [e3, hrh]
    change _ = aX.smul eh (π ≫ specLift tQ aU ≫ x₀)
    have eL : π ≫ specLift tQ (APt.toMagnet N hU * aU) ≫ x₀ = aX.smul eh (gVal ψ tm ch) := by
      rw [← Category.assoc, e1, lift_x₁ hx, hφsm]
    have eR : π ≫ specLift tQ aU ≫ x₀ = gVal ψ tm ch := by
      rw [← Category.assoc, e2, lift_x₁ hx]
    rw [eL, eR]
  let pt : APt (fppfO B S hS) P₂ (op T') :=
    APt.along (AddMonoidHom.fst _ _) a * APt.along (AddMonoidHom.snd _ _) h
  let ξ : T' ⟶ Q := specLift t pt
  have hξt : ξ ≫ tQ = t := specLift_pr t pt
  have hξa : APt.res ξ.op aU = a := by
    refine MonoidHom.ext fun p => ?_
    have e := res_specLift t pt
    refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ _) p)) e).trans ?_
    change a p * h (Multiplicative.ofAdd 0) = a p
    have : h (Multiplicative.ofAdd (0 : M)) = 1 := map_one h
    rw [this, mul_one]
  have hξh : APt.res ξ.op hU = h := by
    refine MonoidHom.ext fun p => ?_
    have e := res_specLift t pt
    refine (congrArg (fun z => z (AddMonoidHom.toMultiplicative (AddMonoidHom.inr _ _) p)) e).trans ?_
    change a (Multiplicative.ofAdd 0) * h p = h p
    have : a (Multiplicative.ofAdd (0 : ↥N)) = 1 := map_one a
    rw [this, one_mul]
  have e1 := congrArg (fun w => ξ ≫ w) huniv
  have e3 : (yoneda.obj U).map ξ.op (aX.smul hU (specLift tQ aU ≫ x₀)) =
      aX.smul (APt.res ξ.op hU) ((yoneda.obj U).map ξ.op (specLift tQ aU ≫ x₀)) :=
    aX.map_smul ξ.op hU _
  have e4 : ξ ≫ specLift tQ (APt.toMagnet N hU * aU) = specLift t (APt.toMagnet N h * a) := by
    rw [← specLift_comp, hξt, APt.res_mul, hξa, ← APt.toMagnet_res, hξh]
  have e5 : ξ ≫ specLift tQ aU = specLift t a := by
    rw [← specLift_comp, hξt, hξa]
  simp only at e1
  rw [← Category.assoc, e4] at e1
  refine e1.trans ?_
  refine Eq.trans e3 ?_
  rw [hξh]
  change aX.smul h (ξ ≫ specLift tQ aU ≫ x₀) = _
  rw [← Category.assoc, e5]

/-- The point of `X^N` given by the descent. -/
noncomputable def chi₁ {ψ : AttractorPt (actAlong f aX) Y T} {x₀ : specObj (Y.comap f) T ⟶ U}
    (hx : specAlong T (jn f Y) ≫ x₀ = gX ψ) : AttractorPt aX (Y.comap f) T where
  app t a := specLift t a ≫ x₀
  naturality s t a := by
    rw [specLift_comp, Category.assoc]
    rfl
  equivariant t h a := equivariant_x₁ hx t h a

/-- A point `φ` of `X^N` over `ψ` satisfies `φ(g x) = g ψ(x)`. -/
lemma specAlong_app (φ : AttractorPt aX (Y.comap f) T) :
    specAlong T (jn f Y) ≫ φ.app (specPr _ T) (specPt _ T) = gX (ptAlong aX φ) := by
  have h := φ.naturality (specAlong T (jn f Y)) (specPr _ T) (specPt _ T)
  rw [specAlong_pr, res_specAlong] at h
  refine h.symm.trans ?_
  let u := specPt (M × Y) T
  have e : APt.along (jn f Y) u = APt.toMagnet (Y.comap f) (APt.along (AddMonoidHom.inl M Y) u) *
      (APt.along (AddMonoidHom.inr M Y) u).comp (AddMonoidHom.toMultiplicative (linMagnetHom f Y)) := by
    refine MonoidHom.ext fun n => ?_
    change u _ = u _ * u _
    rw [← map_mul]
    refine congrArg u (congrArg Multiplicative.ofAdd (Prod.ext ?_ ?_))
    · exact (add_zero _).symm
    · exact (zero_add _).symm
  rw [e]
  exact φ.equivariant _ _ _

/-- **Proposition 3.31 (ii)**, `T` affine. -/
theorem existsUnique_ptAlong_affine (ψ : AttractorPt (actAlong f aX) Y T) :
    ∃! φ : AttractorPt aX (Y.comap f) T, ptAlong aX φ = ψ := by
  obtain ⟨x₀, hx⟩ := exists_x₁ ψ
  refine ⟨chi₁ hx, ?_, fun φ hφ => ?_⟩
  · refine AttractorPt.ext ?_
    funext T' t a
    let c : APt (fppfO B S hS) (M × Y) (op T') :=
      a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd M Y))
    have e1 : APt.along (jn f Y) c = a.comp (AddMonoidHom.toMultiplicative (linMagnetHom f Y)) := rfl
    have e2 : APt.along (AddMonoidHom.inl M Y) c = 1 := by
      refine MonoidHom.ext fun m => ?_
      exact map_one a
    have e3 : APt.along (AddMonoidHom.inr M Y) c = a := MonoidHom.ext fun y => rfl
    change specLift t (a.comp (AddMonoidHom.toMultiplicative (linMagnetHom f Y))) ≫ x₀ = ψ.app t a
    rw [← e1, lift_x₁ hx, gVal, e2, e3, aX.one_smul]
  · refine AttractorPt.ext ?_
    funext T' t a
    have hι := monCoact_isInv (R := Γ((SCH).obj T, ⊤)) (δ := dl f Y) (jn_inj f Y) (dl_eq_zero f Y)
    have e2 : φ.app (specPr _ T) (specPt _ T) = x₀ := by
      apply toScheme_map_injective
      refine desc_unique hι.isSplit ?_
      have e0 : ∀ w : specObj (Y.comap f) T ⟶ U,
          sp (monι (jn f Y) Γ((SCH).obj T, ⊤)) ≫ (SCH).map w =
            (SCH).map (specAlong T (jn f Y) ≫ w) := fun w => by
        rw [Functor.map_comp]
        rfl
      rw [e0, e0, hx]
      have hφ' : ptAlong aX φ = ψ := hφ
      exact congrArg _ ((specAlong_app φ).trans (by rw [hφ']))
    have e1 := φ.app_eq_of_universal (specUniversal (Y.comap f) T) t a
    exact e1.trans (congrArg (specLift t a ≫ ·) e2)

end P331

section Glue331

variable {M Z : Type u} [AddCommMonoid M] [Countable M] [AddCommGroup Z] [AddMonoid.FG Z]
  {f : M →+ Z} {Y : AddSubmonoid Z}
  {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}

lemma ptAlong_baseChange {T W : BigFppfOver B S hS} (s : W ⟶ T)
    (φ : AttractorPt aX (Y.comap f) T) :
    ptAlong aX (AttractorPt.baseChange s φ) = AttractorPt.baseChange s (ptAlong aX φ) := rfl

theorem ptAlong_injective (T : BigFppfOver B S hS) :
    Function.Injective (ptAlong aX : AttractorPt aX (Y.comap f) T → _) := by
  have : AddGroup.FG Z := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  have : Countable Z := countable_of_fg Z
  intro χ χ' h
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  have hsh := isSheaf_attractor aX (Y.comap f) _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  refine (hsh _ hcov).isSeparatedFor.ext ?_
  rintro W g ⟨W', a, b, ⟨i⟩, rfl⟩
  have := hV i
  have e : AttractorPt.baseChange (π i) χ = AttractorPt.baseChange (π i) χ' :=
    (existsUnique_ptAlong_affine (AttractorPt.baseChange (π i) (ptAlong aX χ))).unique
      (ptAlong_baseChange _ _) ((ptAlong_baseChange _ _).trans (congrArg _ h.symm))
  change AttractorPt.baseChange (a ≫ π i) χ = AttractorPt.baseChange (a ≫ π i) χ'
  rw [baseChange_comp', baseChange_comp', e]

theorem ptAlong_surjective (T : BigFppfOver B S hS) :
    Function.Surjective (ptAlong aX : AttractorPt aX (Y.comap f) T → _) := by
  have : AddGroup.FG Z := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  have : Countable Z := countable_of_fg Z
  intro φ
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  have hsh := isSheaf_attractor aX (Y.comap f) _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  have hshB := isSheaf_attractor (actAlong f aX) Y _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  have key : ∀ {W : BigFppfOver B S hS} (g : W ⟶ T), (Sieve.ofArrows V π) g →
      ∃ χ : AttractorPt aX (Y.comap f) W, ptAlong aX χ = AttractorPt.baseChange g φ := by
    rintro W g ⟨W', a, b, ⟨i⟩, rfl⟩
    have := hV i
    obtain ⟨χ, hχ, -⟩ := existsUnique_ptAlong_affine (AttractorPt.baseChange (π i) φ)
    refine ⟨AttractorPt.baseChange a χ, ?_⟩
    rw [ptAlong_baseChange, hχ, baseChange_comp']
  choose x hx using @key
  have hcomp : Presieve.FamilyOfElements.Compatible (P := attractor aX (Y.comap f))
      (R := (Sieve.ofArrows V π).arrows) (fun _ g hg => x g hg) := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ comm
    apply ptAlong_injective W
    change ptAlong aX (AttractorPt.baseChange g₁ (x f₁ h₁)) =
      ptAlong aX (AttractorPt.baseChange g₂ (x f₂ h₂))
    rw [ptAlong_baseChange, ptAlong_baseChange, hx, hx, ← baseChange_comp', ← baseChange_comp', comm]
  have hamal := (hsh _ hcov).isAmalgamation hcomp
  let t : AttractorPt aX (Y.comap f) T := (hsh _ hcov).amalgamate _ hcomp
  refine ⟨t, (hshB _ hcov).isSeparatedFor.ext ?_⟩
  intro W g hg
  have e : AttractorPt.baseChange g t = x g hg := hamal g hg
  exact (ptAlong_baseChange g t).symm.trans ((congrArg (ptAlong aX) e).trans (hx g hg))

/-- **Proposition 3.31 (ii)**. `X` a scheme over an arbitrary `S`, `f : M → Z`, `Z` a finitely generated
abelian group, `M` countable (`M` a finitely generated group is the printed case), `Y` a magnet of `Z`,
`N = f⁻¹(Y)`: `X^N_M = X^Y_Z`. Printed proof repaired: the action of `D(f(M) + Y^gp)` on
`D(M) × 𝔸(Y)` is not free unless `Y^gp ⊆ f(M)` (if `k` fixes the `D(M)` coordinate, nothing forces `k` to be
trivial on `Y`), so the *fpqc quotient* is replaced by the descent `AlgMag.SQ.exists_desc` along the
`Z`-grading `(m, y) ↦ f(m) - y` of `R[M × Y]`, whose degree zero part is `R[N]`. -/
theorem prop331_ii (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong aX : AttractorPt aX (Y.comap f) T → _) :=
  ⟨ptAlong_injective T, ptAlong_surjective T⟩

end Glue331

end AlgMag

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


set_option linter.unusedSectionVars false

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Iter

variable {M Z : Type u} [AddCommMonoid M] [AddCommGroup Z] [AddMonoid.FG Z]
  {f : M →+ Z} (hf : Function.Injective f)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M F}

lemma mem_range_map (N : AddSubmonoid M) : ∀ y ∈ N.map f, ∃ m, f m = y := by
  rintro y ⟨m, -, rfl⟩
  exact ⟨m, rfl⟩

lemma toPoint_ptAlong {Y : AddSubmonoid Z} {T : BigFppfOver B S hS}
    (φ : AttractorPt aX (Y.comap f) T) : (ptAlong aX φ).toPoint = φ.toPoint := by
  change φ.app (𝟙 T) ((1 : APt (fppfO B S hS) Y (op T)).comp _) = φ.app (𝟙 T) 1
  rw [MonoidHom.one_comp]

lemma toPoint_ptOfAlong {Y : AddSubmonoid Z} {T : BigFppfOver B S hS}
    (hY : ∀ y ∈ Y, ∃ m, f m = y) (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hd : HasDensePullback F) (ψ : AttractorPt (actAlong f aX) Y T) :
    (ptOfAlong hf hY hF hd ψ).toPoint = ψ.toPoint := by
  change ψ.app (𝟙 T) ((1 : APt (fppfO B S hS) (Y.comap f) (op T)).comp _) = ψ.app (𝟙 T) 1
  rw [MonoidHom.one_comp]

include hf in
/-- `X^N → X` is a monomorphism for a magnet of a monoid embedded in a finitely generated group,
`X` a separated algebraic space: **Corollary 3.30** for cancellative `M`. -/
theorem toPoint_injective_of_embed (hX : IsAlgebraicSpace B S hS F) (hsep : IsSeparatedOver F)
    (N : AddSubmonoid M) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.toPoint (act := aX) (N := N) (T := T)) := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hd := hasDensePullback_of_separated hsep
  have key : ∀ (P : AddSubmonoid M) (_ : P = (N.map f).comap f),
      Function.Injective (AttractorPt.toPoint (act := aX) (N := P) (T := T)) := by
    rintro P rfl φ φ' h
    apply (prop331_iii hf (mem_range_map N) hF hd T).injective
    apply attractor_toPoint_injective_sep hX hsep
    change (ptAlong aX φ).toPoint = (ptAlong aX φ').toPoint
    rw [toPoint_ptAlong, toPoint_ptAlong, h]
  exact key N (AddSubmonoid.comap_map_eq_of_injective hf N).symm

/-- `f × f`. -/
abbrev f2 (f : M →+ Z) : M × M →+ Z × Z := AddMonoidHom.prodMap f f

include hf in
lemma f2_inj : Function.Injective (f2 f) := Function.Injective.prodMap hf hf

/-- The two actions of `Z × Z` on `X` agree: through `M × M` or through the action of `Z`. -/
def biAlong {Y : AddSubmonoid (Z × Z)} {T : BigFppfOver B S hS}
    (ψ : AttractorPt (actAlong (f2 f) (biAct aX)) Y T) :
    AttractorPt (biAct (actAlong f aX)) Y T where
  app := ψ.app
  naturality := ψ.naturality
  equivariant := ψ.equivariant

lemma hKinf' (N L : AddSubmonoid M) : ∀ k ∈ N ⊓ L, (k, k) ∈ N.prod L :=
  fun _ hk => ⟨(AddSubmonoid.mem_inf.mp hk).1, (AddSubmonoid.mem_inf.mp hk).2⟩

include hf in
/-- **Proposition 3.32 (iii)**, reduction to the group `Z` (the printed chain
`(X^N_M)^L_M = (X^N_{M^gp})^L_{M^gp} = X^{N ∩ L}_{M^gp} = X^{N ∩ L}_M`, three uses of Proposition 3.31 (iii)
and one of Proposition 3.32 (ii)), run on `X^{N × L}_{M × M}`, so that `X^N` need not be assumed
separated. `hZ` is Proposition 3.32 (ii) for `Z`. -/
theorem prop332_iii_of (hX : IsAlgebraicSpace B S hS F) (hsep : IsSeparatedOver F)
    {N L : AddSubmonoid M}
    (hZ : ∀ {T : BigFppfOver B S hS}
      (φ : AttractorPt (biAct (actAlong f aX)) ((N.map f).prod (L.map f)) T),
      ∃ χ : AttractorPt (actAlong f aX) (N.map f ⊓ L.map f) T, χ.toPoint = φ.toPoint)
    (T : BigFppfOver B S hS) :
    Function.Bijective fun χ : AttractorPt aX (N ⊓ L) T =>
      (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L) (hKinf' N L)) := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hd := hasDensePullback_of_separated hsep
  constructor
  · intro χ χ' h
    apply toPoint_injective_of_embed hf hX hsep
    have := congrArg AttractorPt.toPoint ((iterEquivBi T).symm.injective h)
    exact (AttractorPt.toPoint_toBi _ χ).symm.trans (this.trans (AttractorPt.toPoint_toBi _ χ'))
  · intro Ψ
    let Y2 : AddSubmonoid (Z × Z) := (N.map f).prod (L.map f)
    have hc : N.prod L = Y2.comap (f2 f) := by
      ext ⟨a, b⟩
      constructor
      · rintro ⟨ha, hb⟩
        exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
      · rintro ⟨⟨a', ha, ea⟩, ⟨b', hb, eb⟩⟩
        have e1 : a' = a := hf ea
        have e2 : b' = b := hf eb
        subst e1 e2
        exact ⟨ha, hb⟩
    have key : ∀ (P : AddSubmonoid (M × M)) (_ : P = Y2.comap (f2 f))
        (ψ : AttractorPt (biAct aX) P T),
        ∃ ψB : AttractorPt (biAct (actAlong f aX)) Y2 T, ψB.toPoint = ψ.toPoint := by
      rintro P rfl ψ
      exact ⟨biAlong (ptAlong _ ψ), toPoint_ptAlong ψ⟩
    obtain ⟨ψB, hψB⟩ := key _ hc Ψ.toBi
    obtain ⟨χZ, hχZ⟩ := hZ ψB
    have hY : ∀ y ∈ N.map f ⊓ L.map f, ∃ m, f m = y := fun y hy =>
      mem_range_map N y (AddSubmonoid.mem_inf.mp hy).1
    let χ₁ := ptOfAlong hf hY hF hd χZ
    have hle : (N.map f ⊓ L.map f).comap f ≤ N ⊓ L := by
      intro m hm
      obtain ⟨⟨a, ha, ea⟩, ⟨b, hb, eb⟩⟩ := AddSubmonoid.mem_inf.mp hm
      exact AddSubmonoid.mem_inf.mpr ⟨hf ea ▸ ha, hf eb ▸ hb⟩
    refine ⟨AttractorPt.ofLE hle χ₁, ?_⟩
    apply (iterEquivBi T).injective
    rw [Equiv.apply_symm_apply]
    apply toPoint_injective_of_embed (f2_inj hf) hX hsep
    refine (AttractorPt.toPoint_toBi _ _).trans ?_
    change χ₁.toPoint = _
    rw [toPoint_ptOfAlong, hχZ, hψB]
    rfl

include hf in
/-- The attractors for `M` are those for `Z`: Proposition 3.31 (iii) on images in `X`. -/
theorem attractorImage_comap_of_embed (hX : IsAlgebraicSpace B S hS F)
    (hsep : IsSeparatedOver F) {Y : AddSubmonoid Z} (hY : ∀ y ∈ Y, ∃ m, f m = y) :
    attractorImage (actAlong f aX) Y = attractorImage aX (Y.comap f) := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hd := hasDensePullback_of_separated hsep
  funext T
  ext x
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨ptOfAlong hf hY hF hd ψ, toPoint_ptOfAlong hf hY hF hd ψ⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨ptAlong aX φ, toPoint_ptAlong φ⟩

include hf in
/-- **Fact 3.34 (iii)**, reduction to the group `Z`: if the statement holds for the action of `Z` and the
family of the `f(N)`, then it holds for `M`. -/
theorem fact334_iii_of (hX : IsAlgebraicSpace B S hS F) (hsep : IsSeparatedOver F)
    {s : Set (AddSubmonoid M)} (hne : s.Nonempty) (y) (hy : ∀ N ∈ s, attractorImage aX N = y)
    (hZ : (∀ Y ∈ AddSubmonoid.map f '' s, attractorImage (actAlong f aX) Y = y) →
      attractorImage (actAlong f aX) (sInf (AddSubmonoid.map f '' s)) = y) :
    attractorImage aX (sInf s) = y := by
  obtain ⟨N₀, hN₀⟩ := id hne
  have hy' : ∀ Y ∈ AddSubmonoid.map f '' s, attractorImage (actAlong f aX) Y = y := by
    rintro Y ⟨N, hN, rfl⟩
    rw [attractorImage_comap_of_embed hf hX hsep (mem_range_map N),
      AddSubmonoid.comap_map_eq_of_injective hf N]
    exact hy N hN
  have hYr : ∀ z ∈ sInf (AddSubmonoid.map f '' s), ∃ m, f m = z := fun z hz =>
    mem_range_map N₀ z ((AddSubmonoid.mem_sInf.mp hz) _ ⟨N₀, hN₀, rfl⟩)
  have e : (sInf (AddSubmonoid.map f '' s)).comap f = sInf s := by
    ext m
    constructor
    · intro hm
      refine AddSubmonoid.mem_sInf.mpr fun N hN => ?_
      obtain ⟨a, ha, ea⟩ := (AddSubmonoid.mem_sInf.mp hm) _ ⟨N, hN, rfl⟩
      exact hf ea ▸ ha
    · intro hm
      refine AddSubmonoid.mem_sInf.mpr ?_
      rintro _ ⟨N, hN, rfl⟩
      exact ⟨m, (AddSubmonoid.mem_sInf.mp hm) N hN, rfl⟩
  rw [← e, ← attractorImage_comap_of_embed hf hX hsep hYr]
  exact hZ hy'

end Iter

section Schemes

variable {M Z : Type u} [AddCommMonoid M] [AddCommGroup Z] [AddMonoid.FG Z]
  {f : M →+ Z} (hf : Function.Injective f)
  {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}

include hf in
/-- **Proposition 3.32 (iii)**, `X` a separated scheme over an arbitrary `S`: `f : M → Z` an embedding into
a finitely generated abelian group (`M` cancellative with `M^gp` finitely generated, `Z = M^gp`), `N`,
`L` magnets of `M`: `(X^N)^L = X^{N ∩ L}`. No hypothesis on `X^N`. -/
theorem prop332_iii_scheme (hsep : IsSeparatedOver (yoneda.obj U)) (N L : AddSubmonoid M)
    (T : BigFppfOver B S hS) :
    Function.Bijective fun χ : AttractorPt aX (N ⊓ L) T =>
      (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L) (hKinf' N L)) :=
  prop332_iii_of hf (isAlgebraicSpace_yoneda B S hS U) hsep (fun φ => by
    obtain ⟨χ, hχ⟩ := exists_toBi φ
    exact ⟨χ, by rw [← hχ]; exact (AttractorPt.toPoint_toBi _ χ).symm⟩) T

include hf in
/-- **Fact 3.34 (iii)** for a finite family, `X` a separated scheme over an arbitrary `S`, `M` embedded in a
finitely generated abelian group. -/
theorem fact334_iii_finite_scheme (hsep : IsSeparatedOver (yoneda.obj U))
    {s : Set (AddSubmonoid M)} (hfin : s.Finite) (hne : s.Nonempty) (y)
    (hy : ∀ N ∈ s, attractorImage aX N = y) : attractorImage aX (sInf s) = y :=
  fact334_iii_of hf (isAlgebraicSpace_yoneda B S hS U) hsep hne y hy fun h =>
    fact334_finite_scheme hsep (hfin.image _) y (hne.image _) h

end Schemes

section Spaces

variable {M Z : Type u} [AddCommMonoid M] [AddCommGroup Z] [AddMonoid.FG Z]
  {f : M →+ Z} (hf : Function.Injective f)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}

variable {V : BigFppfOver B S hS} [IsAffineHom V.hom.hom]
  {aV : AAction (fppfO B S hS) Z (yoneda.obj V)} {g : yoneda.obj V ⟶ X}

include hf in
/-- **Proposition 3.32 (iii)**, `X` a separated algebraic space with an `S`-affine strongly-FPR atlas for
the action of `Z`, as in `prop332`. -/
theorem prop332_iii_atlas (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : IsStronglyFPRAtlas aV (actAlong f aX) g) {N L : AddSubmonoid M}
    (hb : ((N.map f).FG ∧ (L.map f).FG) ∨ IsLimitPreserving X) (T : BigFppfOver B S hS) :
    Function.Bijective fun χ : AttractorPt aX (N ⊓ L) T =>
      (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L) (hKinf' N L)) :=
  prop332_iii_of hf hX hsep (fun φ => exists_inf_of_bi hX hsep hat hb φ) T

include hf in
/-- **Fact 3.34 (iii)**, arbitrary family, `X` a separated algebraic space with an `S`-affine strongly-FPR
atlas for the action of `Z`, limit preserving, charts of finite type, `S` quasi-compact: the hypotheses
of `fact334`. -/
theorem fact334_iii_atlas [CompactSpace S] (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hat : IsStronglyFPRAtlas aV (actAlong f aX) g)
    (hlim : IsLimitPreserving X) (hft : ChartsOfFiniteType X)
    {s : Set (AddSubmonoid M)} (hne : s.Nonempty) (y)
    (hy : ∀ N ∈ s, attractorImage aX N = y) : attractorImage aX (sInf s) = y :=
  fact334_iii_of hf hX hsep hne y hy fun h =>
    fact334 hX hsep hat hlim hft y (hne.image _) h

end Spaces

end AlgMag

end

section

open CategoryTheory Opposite AlgebraicGeometry
namespace AlgMag
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommMonoid M] [IsCancelAdd M] [AddMonoid.FG (Algebra.GrothendieckAddGroup M)]
  {U : BigFppfOver B S hS} {aX : AAction (fppfO B S hS) M (yoneda.obj U)}

/-- **Proposition 3.32 (iii)** as printed for schemes: `M` cancellative, `M^gp` finitely generated, `X` a
separated scheme. -/
theorem prop332_iii_gp (hsep : IsSeparatedOver (yoneda.obj U)) (N L : AddSubmonoid M)
    (T : BigFppfOver B S hS) :
    Function.Bijective fun χ : AttractorPt aX (N ⊓ L) T =>
      (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L) (hKinf' N L)) :=
  prop332_iii_scheme (f := Algebra.GrothendieckAddGroup.of) Algebra.GrothendieckAddGroup.of_injective hsep N L T

/-- **Fact 3.34 (iii)** as printed, finite family, for schemes. -/
theorem fact334_iii_gp (hsep : IsSeparatedOver (yoneda.obj U))
    {s : Set (AddSubmonoid M)} (hfin : s.Finite) (hne : s.Nonempty) (y)
    (hy : ∀ N ∈ s, attractorImage aX N = y) : attractorImage aX (sInf s) = y :=
  fact334_iii_finite_scheme (f := Algebra.GrothendieckAddGroup.of)
    Algebra.GrothendieckAddGroup.of_injective hsep hfin hne y hy
end AlgMag

end

#print axioms AlgMag.GB.prop331_i
#print axioms AlgMag.prop331_ii
#print axioms AlgMag.GB.prop332_i
#print axioms AlgMag.GB.fact334_i
#print axioms AlgMag.prop332_iii_scheme
#print axioms AlgMag.prop332_iii_atlas
#print axioms AlgMag.prop332_iii_gp
#print axioms AlgMag.fact334_iii_gp
#print axioms AlgMag.fact334_iii_finite_scheme
#print axioms AlgMag.fact334_iii_atlas
#print axioms AlgMag.isFace_inf36
#print axioms AlgMag.GB.prop336_i
#print axioms AlgMag.GB.prop336_ii
