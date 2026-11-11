/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10Deformations
import AlgMag.Sec3Functorial
import AlgMag.Representation
import AlgMag.AlgebraicSpace
import AlgMag.Affine.Attractor

/-!
# Formal étaleness, smoothness and unramifiedness of attractors

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §11.

* Part 1: formal properties of a transformation of functors (Tags 049S, 04G7), and
  Proposition 11.3, Corollary 11.4, for arbitrary functors on the big fppf site of any `S`.
* Part 2: the ring statements behind Fact 11.8, Lemma 11.9, and Propositions 11.1, 11.5, 11.7 when
  `X`, `Y` are affine. Existence of lifts for non-affine `X` needs Proposition 10.1, which is not
  available; see `AlgMag.Sec10Deformations`.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u v w

namespace AlgMag

/-! ### Part 1: formal properties of functors -/

section Functorial

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Formally unramified with respect to a class `Th` of thickenings: at most one lift. -/
def FormallyUnramifiedFor (Th : ∀ {U V : C}, (U ⟶ V) → Prop) {X Y : Cᵒᵖ ⥤ Type w} (f : X ⟶ Y) :
    Prop :=
  ∀ {T₀ T : C} (i : T₀ ⟶ T), Th i → ∀ x y : X.obj (op T),
    X.map i.op x = X.map i.op y → f.app _ x = f.app _ y → x = y

/-- Formally smooth with respect to a class `Th` of thickenings: at least one lift. -/
def FormallySmoothFor (Th : ∀ {U V : C}, (U ⟶ V) → Prop) {X Y : Cᵒᵖ ⥤ Type w} (f : X ⟶ Y) : Prop :=
  ∀ {T₀ T : C} (i : T₀ ⟶ T), Th i → ∀ (x₀ : X.obj (op T₀)) (y : Y.obj (op T)),
    f.app _ x₀ = Y.map i.op y → ∃ x : X.obj (op T), X.map i.op x = x₀ ∧ f.app _ x = y

variable {M : Type*} [AddCommMonoid M] {X Y : Cᵒᵖ ⥤ Type u}
  {aX : AAction 𝒪 M X} {aY : AAction 𝒪 M Y}

/-- **Proposition 11.3**, on any site: if `𝔸(N)` carries `Th` to `Th`, then `f^N` is formally
unramified when `f` is. -/
theorem formallyUnramifiedFor_attractorMap (Th : ∀ {U V : C}, (U ⟶ V) → Prop)
    (f : EquivariantHom aX aY) (N : AddSubmonoid M) (hf : FormallyUnramifiedFor Th f.hom)
    (hU : ∀ {T₀ T : C} (i : T₀ ⟶ T), Th i → ∃ (U₀ : UniversalPoint 𝒪 N T₀)
      (U : UniversalPoint 𝒪 N T), Th (U.lift (U₀.π ≫ i) U₀.u)) :
    FormallyUnramifiedFor Th (attractorMap f N) := by
  intro T₀ T i hi φ ψ h₀ h₁
  obtain ⟨U₀, U, hj⟩ := hU i hi
  have hk : ∀ χ : AttractorPt aX N T, X.map (U.lift (U₀.π ≫ i) U₀.u).op (χ.app U.π U.u) =
      χ.app (U₀.π ≫ i) U₀.u := fun χ => (χ.app_eq_of_universal U _ _).symm
  have key : φ.app U.π U.u = ψ.app U.π U.u := by
    refine hf _ hj _ _ ?_ ?_
    · exact (hk φ).trans ((congrArg (fun χ : AttractorPt aX N T₀ => χ.app U₀.π U₀.u) h₀).trans
        (hk ψ).symm)
    · exact congrArg (fun χ : AttractorPt aY N T => χ.app U.π U.u) h₁
  refine AttractorPt.ext ?_
  funext T' t a
  rw [φ.app_eq_of_universal U, ψ.app_eq_of_universal U, key]

end Functorial

/-! ### The site -/

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A first order thickening of affine schemes over `S` (Tag 05ZK, for affine schemes): the map on
global sections is surjective with square zero kernel. -/
structure IsAffineThickening {T₀ T : BigFppfOver B S hS} (i : T₀ ⟶ T) : Prop where
  affine₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)
  affine : IsAffine ((BigFppfOver.toScheme B S hS).obj T)
  surjective : Function.Surjective ((BigFppfOver.toScheme B S hS).map i).appTop.hom
  sq_zero : ∀ x y, ((BigFppfOver.toScheme B S hS).map i).appTop.hom x = 0 →
    ((BigFppfOver.toScheme B S hS).map i).appTop.hom y = 0 → x * y = 0

/-- Formally unramified transformations of functors (Tag 049S). For algebraic spaces this is
the definition of a formally unramified morphism (Tag 04G7). -/
abbrev IsFormallyUnramified {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} (f : X ⟶ Y) : Prop :=
  FormallyUnramifiedFor (fun {_ _} i => IsAffineThickening i) f

/-- Formally smooth transformations of functors (Tag 049S). -/
abbrev IsFormallySmooth {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} (f : X ⟶ Y) : Prop :=
  FormallySmoothFor (fun {_ _} i => IsAffineThickening i) f

variable {M : Type u} [AddCommMonoid M] (N : AddSubmonoid M)

/-- `R[N]`. -/
noncomputable abbrev magnetRing (T : Scheme.{u}) : CommRingCat.{u} :=
  CommRingCat.of (AddMonoidAlgebra Γ(T, ⊤) N)

/-- The structure map `R → R[N]`. -/
noncomputable def magnetConst (T : Scheme.{u}) : Γ(T, ⊤) ⟶ magnetRing N T :=
  CommRingCat.ofHom (AddMonoidAlgebra.singleZeroRingHom)

/-- `𝔸(N)_T → T`, for `T` affine. -/
noncomputable def magnetπ (T : Scheme.{u}) [IsAffine T] : Spec (magnetRing N T) ⟶ T :=
  Spec.map (magnetConst N T) ≫ T.isoSpec.inv

lemma magnetπ_appTop (T : Scheme.{u}) [IsAffine T] :
    (magnetπ N T).appTop = magnetConst N T ≫ (Scheme.ΓSpecIso _).inv := by
  have h : T.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).inv := by
    have e : T.isoSpec.hom.appTop ≫ T.isoSpec.inv.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
      simp
    have e₁ : T.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).hom := Scheme.toSpecΓ_appTop T
    rw [e₁] at e
    exact (Iso.hom_comp_eq_id _).mp e
  rw [magnetπ, Scheme.Hom.comp_appTop, h, Scheme.ΓSpecIso_inv_naturality]

/-- The universal point of `𝔸(N)_T`. -/
noncomputable def magnetU (T : Scheme.{u}) :
    Multiplicative N →* Γ(Spec (magnetRing N T), ⊤) where
  toFun n := (Scheme.ΓSpecIso _).inv.hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  map_one' := by
    have : AddMonoidAlgebra.single (Multiplicative.toAdd (1 : Multiplicative N)) (1 : Γ(T, ⊤)) = 1 :=
      rfl
    rw [this, map_one]
  map_mul' x y := by
    rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
    rfl

/-- The ring map `R[N] → Γ(X)` of a point of `𝔸(N)` over `t : X → T`. -/
noncomputable def magnetLiftRing {X T : Scheme.{u}} (t : X ⟶ T) (a : Multiplicative N →* Γ(X, ⊤)) :
    magnetRing N T ⟶ Γ(X, ⊤) :=
  CommRingCat.ofHom (AddMonoidAlgebra.liftNCRingHom t.appTop.hom a (fun _ _ => Commute.all _ _))

/-- The morphism `X → 𝔸(N)_T` of a point of `𝔸(N)` over `t : X → T`. -/
noncomputable def magnetLift {X T : Scheme.{u}} (t : X ⟶ T) (a : Multiplicative N →* Γ(X, ⊤)) :
    X ⟶ Spec (magnetRing N T) :=
  ΓSpec.adjunction.homEquiv X (op (magnetRing N T)) (magnetLiftRing N t a).op

lemma magnetLift_appTop {X T : Scheme.{u}} (t : X ⟶ T) (a : Multiplicative N →* Γ(X, ⊤)) :
    (Scheme.ΓSpecIso _).inv ≫ (magnetLift N t a).appTop = magnetLiftRing N t a :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

lemma magnetLift_π {X T : Scheme.{u}} [IsAffine T] (t : X ⟶ T)
    (a : Multiplicative N →* Γ(X, ⊤)) : magnetLift N t a ≫ magnetπ N T = t := by
  refine ext_of_isAffine ?_
  rw [Scheme.Hom.comp_appTop, magnetπ_appTop, Category.assoc, magnetLift_appTop]
  ext r
  simp [magnetConst, magnetLiftRing]

lemma magnetLift_res {X T : Scheme.{u}} (t : X ⟶ T) (a : Multiplicative N →* Γ(X, ⊤))
    (n : Multiplicative N) : (magnetLift N t a).appTop.hom (magnetU N T n) = a n := by
  have h := congrArg (fun k => k.hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1))
    (magnetLift_appTop N t a)
  simpa [magnetLiftRing, magnetU] using h

lemma magnetLift_uniq {X T : Scheme.{u}} [IsAffine T] (t : X ⟶ T)
    (a : Multiplicative N →* Γ(X, ⊤)) (s : X ⟶ Spec (magnetRing N T)) (h₁ : s ≫ magnetπ N T = t)
    (h₂ : ∀ n, s.appTop.hom (magnetU N T n) = a n) : s = magnetLift N t a := by
  refine ext_of_isAffine ?_
  rw [← cancel_epi (Scheme.ΓSpecIso (magnetRing N T)).inv, magnetLift_appTop]
  refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun n => ?_))
  · have e := congrArg (fun k => k.appTop) h₁
    simp only [Scheme.Hom.comp_appTop, magnetπ_appTop] at e
    have this := congrArg (fun k => k.hom r) e
    change s.appTop.hom ((Scheme.ΓSpecIso _).inv.hom (AddMonoidAlgebra.single 0 r)) = _ at this
    change s.appTop.hom ((Scheme.ΓSpecIso _).inv.hom (AddMonoidAlgebra.single 0 r)) =
      (magnetLiftRing N t a).hom (AddMonoidAlgebra.single 0 r)
    rw [this]
    simp [magnetLiftRing]
  · have := h₂ (Multiplicative.ofAdd n)
    simpa [magnetLiftRing, magnetU] using this

/-- `𝔸(N)_T` as an object of the site, for `T` affine, as soon as it is small enough to belong to
the site (Definition 3.1 quantifies over the site). -/
noncomputable def magnetUniversalPoint (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (hN : B.Contains (Spec (magnetRing N ((BigFppfOver.toScheme B S hS).obj T)))) :
    UniversalPoint (fppfO B S hS) N T where
  P := siteObject B S hS hN (magnetπ N _ ≫ T.hom.hom)
  π := Over.homMk (ObjectProperty.homMk (magnetπ N _))
  u := magnetU N _
  lift {T₁} t a := Over.homMk (ObjectProperty.homMk
    (magnetLift N ((BigFppfOver.toScheme B S hS).map t) a)) (by
      have h : (BigFppfOver.toScheme B S hS).map t ≫ T.hom.hom = T₁.hom.hom :=
        congrArg (fun k => k.hom) (Over.w t)
      refine ObjectProperty.hom_ext _ ?_
      have h₂ := magnetLift_π N ((BigFppfOver.toScheme B S hS).map t) a
      exact (congrArg (fun k => k ≫ T.hom.hom) h₂).trans h)
  lift_π t a := by
    refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
    exact magnetLift_π N ((BigFppfOver.toScheme B S hS).map t) a
  res_lift t a := by
    refine MonoidHom.ext fun n => ?_
    exact magnetLift_res N _ a n
  uniq t a s h₁ h₂ := by
    refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
    refine magnetLift_uniq N ((BigFppfOver.toScheme B S hS).map t) a
      ((BigFppfOver.toScheme B S hS).map s) ?_ ?_
    · rw [← h₁]; rfl
    · intro n
      rw [← h₂]; rfl

/-- If `R → R₀` has square zero kernel, the kernel of `R[L] → R₀[L]` has square zero. This is the
computation of Tag 09ZU for `𝔸(N)_T`, and that of Lemma 11.9. -/
lemma magnetAlgebra_mul_eq_zero {R R₀ L : Type*} [CommRing R] [CommRing R₀] [AddMonoid L]
    (φ : R →+* R₀) (hφ : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (x y : AddMonoidAlgebra R L)
    (hx : AddMonoidAlgebra.mapRingHom L φ x = 0) (hy : AddMonoidAlgebra.mapRingHom L φ y = 0) :
    x * y = 0 := by
  have hcx : ∀ a, φ (x.coeff a) = 0 := fun a => by
    have := congrArg (fun z => z.coeff a) hx
    simpa using this
  have hcy : ∀ a, φ (y.coeff a) = 0 := fun a => by
    have := congrArg (fun z => z.coeff a) hy
    simpa using this
  rw [AddMonoidAlgebra.mul_def]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
  change AddMonoidAlgebra.single _ (x.coeff a * y.coeff c) = 0
  rw [hφ _ _ (hcx a) (hcy c), AddMonoidAlgebra.single_zero]

lemma mapRingHom_surjective {R R₀ L : Type*} [CommRing R] [CommRing R₀] [AddMonoid L]
    (φ : R →+* R₀) (hφ : Function.Surjective φ) :
    Function.Surjective (AddMonoidAlgebra.mapRingHom L φ) := by
  intro y
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add p q hp hq =>
    obtain ⟨p₁, rfl⟩ := hp
    obtain ⟨q₁, rfl⟩ := hq
    exact ⟨p₁ + q₁, map_add _ _ _⟩
  | single n r =>
    obtain ⟨s, rfl⟩ := hφ r
    exact ⟨AddMonoidAlgebra.single n s, AddMonoidAlgebra.mapRingHom_single _ _ _⟩

lemma magnetLiftRing_comp {X₀ X : Scheme.{u}} [IsAffine X₀] (e : X₀ ⟶ X)
    (r : AddMonoidAlgebra Γ(X, ⊤) N) :
    (magnetLiftRing N (magnetπ N X₀ ≫ e) (magnetU N X₀)).hom r =
      (Scheme.ΓSpecIso _).inv.hom (AddMonoidAlgebra.mapRingHom N e.appTop.hom r) := by
  have h : (magnetπ N X₀ ≫ e).appTop =
      e.appTop ≫ magnetConst N X₀ ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.comp_appTop, magnetπ_appTop]
  let g₁ : AddMonoidAlgebra Γ(X, ⊤) N →+* Γ(Spec (magnetRing N X₀), ⊤) :=
    (magnetLiftRing N (magnetπ N X₀ ≫ e) (magnetU N X₀)).hom
  let g₂ : AddMonoidAlgebra Γ(X, ⊤) N →+* Γ(Spec (magnetRing N X₀), ⊤) :=
    (Scheme.ΓSpecIso (magnetRing N X₀)).inv.hom.comp (AddMonoidAlgebra.mapRingHom N e.appTop.hom)
  suffices g₁ = g₂ from congrArg (fun k : _ →+* _ => k r) this
  refine AddMonoidAlgebra.ringHom_ext (fun c => ?_) (fun n => ?_)
  · have h₁ : g₁ (AddMonoidAlgebra.single 0 c) = (magnetπ N X₀ ≫ e).appTop.hom c := by
      simp [g₁, magnetLiftRing]
    rw [h₁, h]
    change (Scheme.ΓSpecIso (magnetRing N X₀)).inv.hom
        (AddMonoidAlgebra.single 0 (e.appTop.hom c)) =
      (Scheme.ΓSpecIso (magnetRing N X₀)).inv.hom (AddMonoidAlgebra.mapRingHom N e.appTop.hom
        (AddMonoidAlgebra.single 0 c))
    rw [AddMonoidAlgebra.mapRingHom_single]
  · have h₁ : g₁ (AddMonoidAlgebra.single n 1) = magnetU N X₀ (Multiplicative.ofAdd n) := by
      simp [g₁, magnetLiftRing]
    rw [h₁]
    simp [g₂]
    rfl

/-- The ring computation of Tag 09ZU for `𝔸(N)`. -/
lemma magnetLift_comp_thickening {X₀ X : Scheme.{u}} [IsAffine X₀] (e : X₀ ⟶ X)
    (hs : Function.Surjective e.appTop.hom)
    (hq : ∀ x y, e.appTop.hom x = 0 → e.appTop.hom y = 0 → x * y = 0) :
    Function.Surjective (magnetLift N (magnetπ N X₀ ≫ e) (magnetU N X₀)).appTop.hom ∧
    ∀ x y, (magnetLift N (magnetπ N X₀ ≫ e) (magnetU N X₀)).appTop.hom x = 0 →
      (magnetLift N (magnetπ N X₀ ≫ e) (magnetU N X₀)).appTop.hom y = 0 → x * y = 0 := by
  set j := magnetLift N (magnetπ N X₀ ≫ e) (magnetU N X₀) with hj
  have hring : ∀ r : AddMonoidAlgebra Γ(X, ⊤) N,
      j.appTop.hom ((Scheme.ΓSpecIso _).inv.hom r) =
        (Scheme.ΓSpecIso _).inv.hom (AddMonoidAlgebra.mapRingHom N e.appTop.hom r) := fun r =>
    (congrArg (fun k => k.hom r) (magnetLift_appTop N (magnetπ N X₀ ≫ e) (magnetU N X₀))).trans
      (magnetLiftRing_comp N e r)
  have hinv : ∀ (A : CommRingCat.{u}) (x), (Scheme.ΓSpecIso A).inv.hom
      ((Scheme.ΓSpecIso A).hom.hom x) = x := fun A x => by
    change ((Scheme.ΓSpecIso A).hom ≫ (Scheme.ΓSpecIso A).inv).hom x = x
    simp
  have hinv' : ∀ (A : CommRingCat.{u}) (x), (Scheme.ΓSpecIso A).hom.hom
      ((Scheme.ΓSpecIso A).inv.hom x) = x := fun A x => by
    change ((Scheme.ΓSpecIso A).inv ≫ (Scheme.ΓSpecIso A).hom).hom x = x
    simp
  constructor
  · intro y
    obtain ⟨r, hr⟩ := mapRingHom_surjective (L := N) e.appTop.hom hs
      ((Scheme.ΓSpecIso (magnetRing N X₀)).hom.hom y)
    refine ⟨(Scheme.ΓSpecIso _).inv.hom r, ?_⟩
    rw [hring, hr, hinv]
  · have hzero : ∀ x, j.appTop.hom x = 0 →
        AddMonoidAlgebra.mapRingHom N e.appTop.hom ((Scheme.ΓSpecIso (magnetRing N X)).hom.hom x)
          = 0 := by
      intro x hx
      have h₁ := hring ((Scheme.ΓSpecIso (magnetRing N X)).hom.hom x)
      rw [hinv, hx] at h₁
      have h₂ := congrArg (Scheme.ΓSpecIso (magnetRing N X₀)).hom.hom h₁
      rw [hinv', map_zero] at h₂
      exact h₂.symm
    intro x y hx hy
    have := magnetAlgebra_mul_eq_zero e.appTop.hom hq _ _ (hzero x hx) (hzero y hy)
    rw [← hinv _ x, ← hinv _ y, ← map_mul, this, map_zero]

/-- Tag 09ZU for `𝔸(N)`: base change of a first order thickening of affine schemes along
`𝔸(N)` is one. -/
theorem isAffineThickening_magnet {T₀ T : BigFppfOver B S hS} (i : T₀ ⟶ T)
    (hi : IsAffineThickening i)
    (h₀ : B.Contains (Spec (magnetRing N ((BigFppfOver.toScheme B S hS).obj T₀))))
    (h : B.Contains (Spec (magnetRing N ((BigFppfOver.toScheme B S hS).obj T)))) :
    letI := hi.affine₀
    letI := hi.affine
    IsAffineThickening ((magnetUniversalPoint N T h).lift
      ((magnetUniversalPoint N T₀ h₀).π ≫ i) (magnetUniversalPoint N T₀ h₀).u) := by
  have := hi.affine₀
  have := hi.affine
  obtain ⟨h₁, h₂⟩ := magnetLift_comp_thickening N ((BigFppfOver.toScheme B S hS).map i)
    hi.surjective hi.sq_zero
  exact ⟨by change IsAffine (Spec _); infer_instance, by change IsAffine (Spec _); infer_instance,
    h₁, h₂⟩

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {aY : AAction (fppfO B S hS) M Y}

/-- `𝔸(N)_T` belongs to the site for all affine `T` in the site. This holds if the cutoff of `B` is
large enough with respect to `N`. -/
def MagnetInSite (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    B.Contains (Spec (magnetRing N ((BigFppfOver.toScheme B S hS).obj T)))

/-- **Proposition 11.3.** If `f : X → Y` is formally unramified, so is `f^N : X^N → Y^N`, as a
transformation of functors. `X`, `Y` are arbitrary functors with an action of `𝔸(M)`, over any `S`;
`M` and `N` are arbitrary. -/
theorem isFormallyUnramified_attractorMap (f : EquivariantHom aX aY)
    (hN : MagnetInSite N B S hS) (hf : IsFormallyUnramified f.hom) :
    IsFormallyUnramified (attractorMap f N) := by
  refine formallyUnramifiedFor_attractorMap _ f N hf ?_
  intro T₀ T i hi
  have := hi.affine₀
  have := hi.affine
  exact ⟨_, _, isAffineThickening_magnet N i hi (hN T₀ hi.affine₀) (hN T hi.affine)⟩

/-- **Corollary 11.4.** If `Zx`, `Zy` represent `X^N`, `Y^N` (for instance by algebraic spaces; by
Tag 04G7, a formally unramified morphism of algebraic spaces is one with `IsFormallyUnramified`),
the morphism `Zx → Zy` corresponding to `f^N` is formally unramified. -/
theorem isFormallyUnramified_of_represents (f : EquivariantHom aX aY)
    (hN : MagnetInSite N B S hS) (hf : IsFormallyUnramified f.hom)
    {Zx Zy : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (rx : RepresentsAttractor aX N Zx)
    (ry : RepresentsAttractor aY N Zy) (g : Zx ⟶ Zy)
    (hg : ∀ (T : BigFppfOver B S hS) (z : Zx.obj (op T)),
      ry.equiv T (g.app _ z) = AttractorPt.push f (rx.equiv T z)) :
    IsFormallyUnramified g := by
  intro T₀ T i hi x y h₀ h₁
  apply (rx.equiv T).injective
  refine isFormallyUnramified_attractorMap N f hN hf i hi _ _ ?_ ?_
  · refine (rx.naturality i x).symm.trans ?_
    rw [h₀]
    exact rx.naturality i y
  · change AttractorPt.push f _ = AttractorPt.push f _
    rw [← hg, ← hg, h₁]

end Site

/-! ### Part 2: the affine case -/

section Affine

open Magnetism AlgMag.Deformations

variable {M : Type*} [AddCancelCommMonoid M] [DecidableEq M]

/-- A ring map compatible with gradings commutes with the homogeneous projections. -/
lemma map_proj_of_graded {E E' σ σ' : Type*} [CommRing E] [CommRing E'] [SetLike σ E]
    [AddSubgroupClass σ E] [SetLike σ' E'] [AddSubgroupClass σ' E'] (ℰ : M → σ) [GradedRing ℰ]
    (ℰ' : M → σ') [GradedRing ℰ'] (p : E →+* E') (hp : ∀ m x, x ∈ ℰ m → p x ∈ ℰ' m) (k : M) (x : E) :
    p (GradedRing.proj ℰ k x) = GradedRing.proj ℰ' k (p x) := by
  induction x using DirectSum.Decomposition.inductionOn ℰ with
  | zero => simp
  | @homogeneous i x =>
    simp only [GradedRing.proj_apply]
    by_cases h : i = k
    · subst h
      rw [DirectSum.decompose_of_mem_same ℰ x.2, DirectSum.decompose_of_mem_same ℰ' (hp _ _ x.2)]
    · rw [DirectSum.decompose_of_mem_ne ℰ x.2 h, DirectSum.decompose_of_mem_ne ℰ' (hp _ _ x.2) h,
        map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {N : AddSubmonoid M} {D D' : Type*} [CommRing D] [CommRing D']

lemma map_mem_magnetGrading (φ : D →+* D') {m : M} {x : AddMonoidAlgebra D N}
    (hx : x ∈ magnetGrading N D m) :
    AddMonoidAlgebra.mapRingHom N φ x ∈ magnetGrading N D' m := by
  by_cases hm : m ∈ N
  · obtain ⟨c, rfl⟩ := exists_single_of_mem_magnetGrading hm hx
    rw [AddMonoidAlgebra.mapRingHom_single]
    exact single_mem_magnetGrading (⟨m, hm⟩ : N) _
  · rw [magnetGrading_eq_bot hm, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _

/-- A homogeneous element of `D'[N]` lifts to a homogeneous element of `D[N]` of the same degree. -/
lemma exists_homogeneous_lift (φ : D →+* D') (hφ : Function.Surjective φ) {m : M}
    {y : AddMonoidAlgebra D' N} (hy : y ∈ magnetGrading N D' m) :
    ∃ e ∈ magnetGrading N D m, AddMonoidAlgebra.mapRingHom N φ e = y := by
  by_cases hm : m ∈ N
  · obtain ⟨c, rfl⟩ := exists_single_of_mem_magnetGrading hm hy
    obtain ⟨c', rfl⟩ := hφ c
    exact ⟨_, single_mem_magnetGrading (⟨m, hm⟩ : N) c', AddMonoidAlgebra.mapRingHom_single _ _ _⟩
  · rw [magnetGrading_eq_bot hm, Submodule.mem_bot] at hy
    exact ⟨0, Submodule.zero_mem _, by rw [hy, map_zero]⟩

variable {R₀ A B : Type*} [CommRing R₀] [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B]
  [Algebra B A] [IsScalarTower R₀ B A] [Algebra R₀ D] [Algebra R₀ D']
  (𝒜 : M → Submodule R₀ A) [GradedAlgebra 𝒜] (ℬ : M → Submodule R₀ B) [GradedAlgebra ℬ]

/-- **Proposition 11.1, `X`, `Y` affine.** Let `f : Spec A → Spec B` be equivariant and formally
smooth (`hf` says that `B → A` is graded; `S = Spec R₀`). Then `f^N` is formally smooth: for a first
order thickening `Spec D' → Spec D` (`φ` surjective with square zero kernel), a compatible pair of
points of `X^N(D')`, `Y^N(D)` lifts to a point of `X^N(D)`. No finiteness is assumed. -/
theorem attractor_formallySmooth_affine [Algebra.FormallySmooth B A]
    (hf : ∀ (m : M) (b : B), b ∈ ℬ m → algebraMap B A b ∈ 𝒜 m)
    (φ : D →ₐ[R₀] D') (hφ : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (α : Attractor 𝒜 N D') (β : Attractor ℬ N D)
    (hc : ∀ b, AddMonoidAlgebra.mapRingHom N (φ : D →+* D') (β b) = α (algebraMap B A b)) :
    ∃ γ : Attractor 𝒜 N D, (∀ a, AddMonoidAlgebra.mapRingHom N (φ : D →+* D') (γ a) = α a) ∧
      ∀ b, γ (algebraMap B A b) = β b := by
  let ρ := AddMonoidAlgebra.mapRingHom N (φ : D →+* D')
  have hgr : ∀ m x, x ∈ magnetGrading N D m → ρ x ∈ magnetGrading N D' m :=
    fun m x hx => map_mem_magnetGrading _ hx
  obtain ⟨γ, h₁, h₂, h₃⟩ := exists_graded_lift (𝒜 := 𝒜) (ℰ := magnetGrading N D) (B := B) ρ
    (mapRingHom_surjective _ hφ)
    (magnetAlgebra_mul_eq_zero _ hq)
    (fun k x hx => by
      rw [map_proj_of_graded (magnetGrading N D) (magnetGrading N D') ρ hgr, hx, map_zero])
    (α.toAlgHom : A →+* _) (β.toAlgHom : B →+* _) hc
    (fun m a ha => exists_homogeneous_lift _ hφ (α.map_mem ha))
    (fun b => by
      induction b using DirectSum.Decomposition.inductionOn ℬ with
      | zero => exact AddSubmonoid.zero_mem _
      | @homogeneous i x => exact AddSubmonoid.subset_closure ⟨i, hf i _ x.2, β.map_mem x.2⟩
      | add p q hp hq => exact AddSubmonoid.add_mem _ hp hq)
  refine ⟨{ toAlgHom := { γ with commutes' := fun r => ?_ }, map_mem' := fun {m a} ha => h₃ m a ha },
    h₁, h₂⟩
  change γ (algebraMap R₀ A r) = _
  rw [IsScalarTower.algebraMap_apply R₀ B A, h₂]
  exact β.toAlgHom.commutes r

/-- **Proposition 11.5, `X`, `Y` affine.** If `f` is formally étale, the lift of
`attractor_formallySmooth_affine` is unique, even among all points. -/
theorem attractor_formallyEtale_affine [Algebra.FormallyEtale B A]
    (hf : ∀ (m : M) (b : B), b ∈ ℬ m → algebraMap B A b ∈ 𝒜 m)
    (φ : D →ₐ[R₀] D') (hφ : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (α : Attractor 𝒜 N D') (β : Attractor ℬ N D)
    (hc : ∀ b, AddMonoidAlgebra.mapRingHom N (φ : D →+* D') (β b) = α (algebraMap B A b)) :
    ∃! γ : Attractor 𝒜 N D, (∀ a, AddMonoidAlgebra.mapRingHom N (φ : D →+* D') (γ a) = α a) ∧
      ∀ b, γ (algebraMap B A b) = β b := by
  have : Algebra.FormallySmooth B A := inferInstance
  obtain ⟨γ, hγ⟩ := attractor_formallySmooth_affine 𝒜 ℬ hf φ hφ hq α β hc
  refine ⟨γ, hγ, fun γ' hγ' => ?_⟩
  let ρ := AddMonoidAlgebra.mapRingHom N (φ : D →+* D')
  let _ : Algebra B (AddMonoidAlgebra D N) := (β.toAlgHom : B →+* _).toAlgebra
  let K : Ideal (AddMonoidAlgebra D N) := RingHom.ker ρ
  have hK : K ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    exact fun x hx y hy => (Ideal.mem_bot).2 (magnetAlgebra_mul_eq_zero _ hq x y hx hy)
  let g₁ : A →ₐ[B] AddMonoidAlgebra D N :=
    { (γ'.toAlgHom : A →+* _) with commutes' := hγ'.2 }
  let g₂ : A →ₐ[B] AddMonoidAlgebra D N :=
    { (γ.toAlgHom : A →+* _) with commutes' := hγ.2 }
  have : g₁ = g₂ := Algebra.FormallyUnramified.ext K ⟨2, hK⟩ (fun a => by
    rw [Ideal.Quotient.eq]
    change ρ (γ' a - γ a) = 0
    rw [map_sub]
    exact sub_eq_zero.2 ((hγ'.1 a).trans (hγ.1 a).symm))
  exact GradedAlgHom.ext fun a => congrArg (fun k : A →ₐ[B] _ => k a) this

/-! ### Faces: Fact 11.8, Lemma 11.9, Proposition 11.7 -/

variable {F : AddSubmonoid M}

open Classical in
/-- The ring map `R[N] → R[F]`, `X^n ↦ X^n` if `n ∈ F` and `0` otherwise, for a face `F` of `N`:
the morphism `𝔸(F) → 𝔸(N)` of Fact 2.15. -/
noncomputable def faceRingHom (hF : IsFace F N) (D : Type*) [CommRing D] :
    AddMonoidAlgebra D N →+* AddMonoidAlgebra D F :=
  AddMonoidAlgebra.liftNCRingHom AddMonoidAlgebra.singleZeroRingHom
    { toFun := fun n => if h : ((Multiplicative.toAdd n : N) : M) ∈ F then
        AddMonoidAlgebra.single (⟨_, h⟩ : F) 1 else 0
      map_one' := by
        have h : ((Multiplicative.toAdd (1 : Multiplicative N) : N) : M) ∈ F := F.zero_mem
        rw [dif_pos h]
        rfl
      map_mul' := fun x y => by
        by_cases hx : ((Multiplicative.toAdd x : N) : M) ∈ F
        · by_cases hy : ((Multiplicative.toAdd y : N) : M) ∈ F
          · have hxy : ((Multiplicative.toAdd (x * y) : N) : M) ∈ F := F.add_mem hx hy
            rw [dif_pos hx, dif_pos hy, dif_pos hxy, AddMonoidAlgebra.single_mul_single, one_mul]
            rfl
          · have hxy : ((Multiplicative.toAdd (x * y) : N) : M) ∉ F := fun h =>
              hy (hF.mem_of_add_mem (Multiplicative.toAdd x : N).2 (Multiplicative.toAdd y : N).2 h).2
            rw [dif_neg hy, dif_neg hxy, mul_zero]
        · have hxy : ((Multiplicative.toAdd (x * y) : N) : M) ∉ F := fun h =>
            hx (hF.mem_of_add_mem (Multiplicative.toAdd x : N).2 (Multiplicative.toAdd y : N).2 h).1
          rw [dif_neg hx, dif_neg hxy, zero_mul] }
    (fun _ _ => Commute.all _ _)

open Classical in
lemma faceRingHom_single_pos (hF : IsFace F N) (n : N) (hn : (n : M) ∈ F) (c : D) :
    faceRingHom hF D (AddMonoidAlgebra.single n c) = AddMonoidAlgebra.single ⟨n, hn⟩ c := by
  simp only [faceRingHom, AddMonoidAlgebra.liftNCRingHom_single]
  change AddMonoidAlgebra.single 0 c * (if h : (n : M) ∈ F then
    AddMonoidAlgebra.single (⟨n, h⟩ : F) 1 else 0) = _
  rw [dif_pos hn, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

open Classical in
lemma faceRingHom_single_neg (hF : IsFace F N) (n : N) (hn : (n : M) ∉ F) (c : D) :
    faceRingHom hF D (AddMonoidAlgebra.single n c) = 0 := by
  simp only [faceRingHom, AddMonoidAlgebra.liftNCRingHom_single]
  change AddMonoidAlgebra.single 0 c * (if h : (n : M) ∈ F then
    AddMonoidAlgebra.single (⟨n, h⟩ : F) 1 else 0) = _
  rw [dif_neg hn, mul_zero]

lemma face_comm (hF : IsFace F N) (φ : D →+* D') (x : AddMonoidAlgebra D N) :
    faceRingHom hF D' (AddMonoidAlgebra.mapRingHom N φ x) =
      AddMonoidAlgebra.mapRingHom F φ (faceRingHom hF D x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n c =>
    rw [AddMonoidAlgebra.mapRingHom_single]
    by_cases hn : (n : M) ∈ F
    · rw [faceRingHom_single_pos hF n hn, faceRingHom_single_pos hF n hn,
        AddMonoidAlgebra.mapRingHom_single]
    · rw [faceRingHom_single_neg hF n hn, faceRingHom_single_neg hF n hn, map_zero]

lemma face_mem (hF : IsFace F N) {m : M} {x : AddMonoidAlgebra D N}
    (hx : x ∈ magnetGrading N D m) : faceRingHom hF D x ∈ magnetGrading F D m := by
  by_cases hm : m ∈ N
  · obtain ⟨c, rfl⟩ := exists_single_of_mem_magnetGrading hm hx
    by_cases hmF : m ∈ F
    · rw [faceRingHom_single_pos hF ⟨m, hm⟩ hmF]
      exact single_mem_magnetGrading (⟨m, hmF⟩ : F) _
    · rw [faceRingHom_single_neg hF ⟨m, hm⟩ hmF]
      exact Submodule.zero_mem _
  · rw [magnetGrading_eq_bot hm, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _

/-- The coordinate ring `R[F] ×_{(R/I)[F]} (R/I)[N] = R[F] ⊕ (R/I)[N∖F]` of the push-out
`𝔸(F)_T ⊔_{𝔸(F)_{T'}} 𝔸(N)_{T'}` of **Fact 11.8**. As a subring of a product, it is the fibre
product of rings (the affine form of the universal property of the push-out). -/
def pushoutRing (hF : IsFace F N) (φ : D →+* D') :
    Subring (AddMonoidAlgebra D F × AddMonoidAlgebra D' N) where
  carrier := {p | AddMonoidAlgebra.mapRingHom F φ p.1 = faceRingHom hF D' p.2}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at *
    rw [ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, map_add] at *
    rw [ha, hb]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, map_neg] at *
    rw [ha]

/-- The ring map `R[N] → R[F] ×_{(R/I)[F]} (R/I)[N]` of Lemma 11.9. -/
noncomputable def pushoutMap (hF : IsFace F N) (φ : D →+* D') :
    AddMonoidAlgebra D N →+* pushoutRing hF φ :=
  ((faceRingHom hF D).prod (AddMonoidAlgebra.mapRingHom N φ)).codRestrict _
    (fun x => (face_comm hF φ x).symm)

/-- The inclusion `R[F] → R[N]`. -/
noncomputable def faceInc (hF : IsFace F N) (D : Type*) [CommRing D] :
    AddMonoidAlgebra D F →+ AddMonoidAlgebra D N :=
  (AddMonoidAlgebra.mapDomainRingHom D (AddSubmonoid.inclusion hF.le)).toAddMonoidHom

/-- **Fact 11.8, affine form**: `R[N]` surjects onto the push-out ring. -/
theorem pushoutMap_surjective (hF : IsFace F N) (φ : D →+* D') (hφ : Function.Surjective φ) :
    Function.Surjective (pushoutMap hF φ) := by
  have hinc₁ : ∀ v : AddMonoidAlgebra D F, faceRingHom hF D (faceInc hF D v) = v := by
    intro v
    induction v using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | single n c =>
      have : faceInc hF D (AddMonoidAlgebra.single n c) =
          AddMonoidAlgebra.single (AddSubmonoid.inclusion hF.le n) c := by
        simp [faceInc]
      rw [this, faceRingHom_single_pos hF _ n.2]
      rfl
  have hinc₂ : ∀ v : AddMonoidAlgebra D F, AddMonoidAlgebra.mapRingHom F φ v = 0 →
      AddMonoidAlgebra.mapRingHom N φ (faceInc hF D v) = 0 := by
    intro v hv
    refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun n => ?_)
    by_cases hn : (n : M) ∈ F
    · have h₁ : (faceInc hF D v).coeff n = v.coeff ⟨n, hn⟩ := by
        have hinj : Function.Injective (AddSubmonoid.inclusion hF.le) :=
          AddSubmonoid.inclusion_injective hF.le
        have := Finsupp.mapDomain_apply hinj v.coeff (⟨n, hn⟩ : F)
        rw [show AddSubmonoid.inclusion hF.le (⟨n, hn⟩ : F) = n from rfl] at this
        simpa [faceInc] using this
      have h₂ := congrArg (fun z => z.coeff ⟨n, hn⟩) hv
      simp only [AddMonoidAlgebra.coeff_mapRingHom] at h₂ ⊢
      rw [h₁]
      simpa using h₂
    · have h₁ : (faceInc hF D v).coeff n = 0 := by
        have := Finsupp.mapDomain_notin_range v.coeff n (f := AddSubmonoid.inclusion hF.le)
          (by rintro ⟨w, rfl⟩; exact hn w.2)
        simpa [faceInc] using this
      simp [h₁]
  rintro ⟨⟨u, w⟩, hp⟩
  obtain ⟨x₀, hx₀⟩ := mapRingHom_surjective (L := N) φ hφ w
  let v := u - faceRingHom hF D x₀
  have hv : AddMonoidAlgebra.mapRingHom F φ v = 0 := by
    have hp' : AddMonoidAlgebra.mapRingHom F φ u = faceRingHom hF D' w := hp
    simp only [v, map_sub, hp', ← face_comm, hx₀, sub_self]
  refine ⟨x₀ + faceInc hF D v, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change faceRingHom hF D _ = u
    rw [map_add, hinc₁]
    simp [v]
  · change AddMonoidAlgebra.mapRingHom N φ _ = w
    rw [map_add, hinc₂ v hv, add_zero, hx₀]

/-- **Lemma 11.9.** The morphism from the push-out to `𝔸(N)_T` is a first order thickening: the map
of rings is surjective (`pushoutMap_surjective`), and its kernel has square zero. -/
theorem pushoutMap_mul_eq_zero (hF : IsFace F N) (φ : D →+* D')
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (x y : AddMonoidAlgebra D N)
    (hx : pushoutMap hF φ x = 0) (hy : pushoutMap hF φ y = 0) : x * y = 0 :=
  magnetAlgebra_mul_eq_zero φ hq x y (congrArg (fun p => p.1.2) hx) (congrArg (fun p => p.1.2) hy)

/-- **Lemma 11.9**, the description of the kernel in its proof: `K = I · R[N∖F]`. -/
theorem pushoutMap_eq_zero_iff (hF : IsFace F N) (φ : D →+* D') (x : AddMonoidAlgebra D N) :
    pushoutMap hF φ x = 0 ↔ ∀ n : N, φ (x.coeff n) = 0 ∧ ((n : M) ∈ F → x.coeff n = 0) := by
  have hface : ∀ (n : F) (x : AddMonoidAlgebra D N),
      (faceRingHom hF D x).coeff n = x.coeff (AddSubmonoid.inclusion hF.le n) := by
    intro n x
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    | single k c =>
      classical
      by_cases hk : (k : M) ∈ F
      · rw [faceRingHom_single_pos hF k hk]
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        congr 1
        simp only [Subtype.ext_iff, AddSubmonoid.coe_inclusion]
      · rw [faceRingHom_single_neg hF k hk]
        simp only [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
          Pi.zero_apply, Finsupp.single_apply]
        rw [if_neg]
        intro h
        exact hk (h ▸ n.2)
  constructor
  · intro h n
    have h₁ : AddMonoidAlgebra.mapRingHom N φ x = 0 := congrArg (fun p => p.1.2) h
    have h₂ : faceRingHom hF D x = 0 := congrArg (fun p => p.1.1) h
    refine ⟨?_, fun hn => ?_⟩
    · have := congrArg (fun z => z.coeff n) h₁
      simpa using this
    · have := hface ⟨n, hn⟩ x
      rw [h₂] at this
      exact this.symm
  · intro h
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun n => ?_)
      change (faceRingHom hF D x).coeff n = 0
      rw [hface]
      exact (h _).2 n.2
    · refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun n => ?_)
      change (AddMonoidAlgebra.mapRingHom N φ x).coeff n = 0
      simpa using (h n).1

lemma algebraMap_magnet_eq (L : AddSubmonoid M) {D : Type*} [CommRing D] [Algebra R₀ D] (r : R₀) :
    algebraMap R₀ (AddMonoidAlgebra D L) r = AddMonoidAlgebra.single 0 (algebraMap R₀ D r) := rfl

lemma algebraMap_mem_magnetGrading {L : AddSubmonoid M} {D : Type*} [CommRing D] [Algebra R₀ D]
    (r : R₀) : algebraMap R₀ (AddMonoidAlgebra D L) r ∈ magnetGrading L D 0 :=
  single_mem_magnetGrading (0 : L) _

lemma map_algebraMap_face (hF : IsFace F N) (r : R₀) :
    faceRingHom hF D (algebraMap R₀ _ r) = algebraMap R₀ (AddMonoidAlgebra D F) r := by
  rw [algebraMap_magnet_eq, algebraMap_magnet_eq, faceRingHom_single_pos hF 0 F.zero_mem]
  rfl

lemma map_algebraMap_reduce (φ : D →ₐ[R₀] D') (r : R₀) :
    AddMonoidAlgebra.mapRingHom N (φ : D →+* D') (algebraMap R₀ _ r) =
      algebraMap R₀ (AddMonoidAlgebra D' N) r := by
  rw [algebraMap_magnet_eq, algebraMap_magnet_eq, AddMonoidAlgebra.mapRingHom_single]
  congr 1
  exact φ.commutes r

/-- The homogeneous part of Fact 11.8: a homogeneous element of the push-out ring lifts to a
homogeneous element of `R[N]`. -/
lemma homogeneous_pushout_lift (hF : IsFace F N) (φ : D →+* D') (hφ : Function.Surjective φ)
    {m : M} {w : AddMonoidAlgebra D' N} {u : AddMonoidAlgebra D F}
    (hw : w ∈ magnetGrading N D' m) (hu : u ∈ magnetGrading F D m)
    (hc : AddMonoidAlgebra.mapRingHom F φ u = faceRingHom hF D' w) :
    ∃ e ∈ magnetGrading N D m, (faceRingHom hF D e, AddMonoidAlgebra.mapRingHom N φ e) = (u, w) := by
  by_cases hmF : m ∈ F
  · obtain ⟨c, rfl⟩ := exists_single_of_mem_magnetGrading hmF hu
    have hm : m ∈ N := hF.le hmF
    obtain ⟨c', rfl⟩ := exists_single_of_mem_magnetGrading hm hw
    rw [AddMonoidAlgebra.mapRingHom_single, faceRingHom_single_pos hF ⟨m, hm⟩ hmF] at hc
    have hcc : φ c = c' := by
      have := congrArg (fun z => z.coeff ⟨m, hmF⟩) hc
      simpa using this
    refine ⟨AddMonoidAlgebra.single ⟨m, hm⟩ c, single_mem_magnetGrading (⟨m, hm⟩ : N) c, ?_⟩
    rw [faceRingHom_single_pos hF ⟨m, hm⟩ hmF, AddMonoidAlgebra.mapRingHom_single, hcc]
  · rw [magnetGrading_eq_bot hmF, Submodule.mem_bot] at hu
    subst hu
    obtain ⟨e, he, rfl⟩ := exists_homogeneous_lift φ hφ hw
    refine ⟨e, he, ?_⟩
    have : faceRingHom hF D e = 0 := by
      by_cases hm : m ∈ N
      · obtain ⟨c, rfl⟩ := exists_single_of_mem_magnetGrading hm he
        exact faceRingHom_single_neg hF ⟨m, hm⟩ hmF c
      · rw [magnetGrading_eq_bot hm, Submodule.mem_bot] at he
        rw [he, map_zero]
    rw [this]

/-- **Proposition 11.7, `X` affine.** If `X = Spec A → S = Spec R₀` is formally smooth and `F` is a
face of `N`, then `X^N → X^F` is formally smooth: a point `α` of `X^N(D')` and a point `β` of
`X^F(D)` with the same image in `X^F(D')` lift to a point of `X^N(D)`. -/
theorem attractor_face_formallySmooth_affine [Algebra.FormallySmooth R₀ A] (hF : IsFace F N)
    (φ : D →ₐ[R₀] D') (hφ : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (α : Attractor 𝒜 N D') (β : Attractor 𝒜 F D)
    (hc : ∀ a, AddMonoidAlgebra.mapRingHom F (φ : D →+* D') (β a) =
      faceRingHom hF D' (α a)) :
    ∃ γ : Attractor 𝒜 N D, (∀ a, AddMonoidAlgebra.mapRingHom N (φ : D →+* D') (γ a) = α a) ∧
      ∀ a, faceRingHom hF D (γ a) = β a := by
  let φr : D →+* D' := φ
  let π := pushoutMap hF φr
  let α₀ : A →+* pushoutRing hF φr :=
    ((β.toAlgHom : A →+* _).prod (α.toAlgHom : A →+* _)).codRestrict _ (fun a => by exact hc a)
  let β₀ : R₀ →+* AddMonoidAlgebra D N := algebraMap R₀ _
  have hgrF : ∀ m x, x ∈ magnetGrading N D m → faceRingHom hF D x ∈ magnetGrading F D m :=
    fun m x hx => face_mem hF hx
  have hgrN : ∀ m x, x ∈ magnetGrading N D m →
      AddMonoidAlgebra.mapRingHom N φr x ∈ magnetGrading N D' m :=
    fun m x hx => map_mem_magnetGrading _ hx
  obtain ⟨γ, h₁, h₂, h₃⟩ := exists_graded_lift (𝒜 := 𝒜) (ℰ := magnetGrading N D) (B := R₀) π
    (pushoutMap_surjective hF φr hφ)
    (pushoutMap_mul_eq_zero hF φr hq)
    (fun k x hx => by
      have hx₁ : faceRingHom hF D x = 0 := congrArg (fun p => p.1.1) hx
      have hx₂ : AddMonoidAlgebra.mapRingHom N φr x = 0 := congrArg (fun p => p.1.2) hx
      refine Subtype.ext (Prod.ext ?_ ?_)
      · change faceRingHom hF D _ = 0
        rw [map_proj_of_graded (magnetGrading N D) (magnetGrading F D) _ hgrF, hx₁, map_zero]
      · change AddMonoidAlgebra.mapRingHom N φr _ = 0
        rw [map_proj_of_graded (magnetGrading N D) (magnetGrading N D') _ hgrN, hx₂, map_zero])
    α₀ β₀
    (fun r => by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · change faceRingHom hF D (algebraMap R₀ _ r) = β.toAlgHom (algebraMap R₀ A r)
        rw [β.toAlgHom.commutes]
        exact map_algebraMap_face hF r
      · change AddMonoidAlgebra.mapRingHom N φr (algebraMap R₀ _ r) = α.toAlgHom (algebraMap R₀ A r)
        rw [α.toAlgHom.commutes]
        exact map_algebraMap_reduce φ r)
    (fun m a ha => by
      obtain ⟨e, he, hea⟩ := homogeneous_pushout_lift hF φr hφ (α.map_mem ha) (β.map_mem ha) (hc a)
      exact ⟨e, he, Subtype.ext hea⟩)
    (fun r => AddSubmonoid.subset_closure ⟨0, SetLike.algebraMap_mem_graded 𝒜 r, by
      change algebraMap R₀ _ r ∈ _
      exact algebraMap_mem_magnetGrading r⟩)
  refine ⟨{ toAlgHom := { γ with commutes' := fun r => h₂ r }, map_mem' := fun {m a} ha => h₃ m a ha },
    fun a => congrArg (fun p => p.1.2) (h₁ a), fun a => congrArg (fun p => p.1.1) (h₁ a)⟩

end Affine

end AlgMag
