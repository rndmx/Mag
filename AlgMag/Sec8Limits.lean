/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec8Theorem83
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Sorites

/-!
# Limits: Tag 049J, Theorem 8.3 (iv), (vi), Proposition 8.5

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §§3, 5, 8.

* `AlgMag.isLimitPreserving_of_lfp`: **Tag 049J** in the form `AlgMag.IsLimitPreserving`.
* `AlgMag.prop337`, `AlgMag.prop51_ii`: **Proposition 3.37** (`T` affine) and **Proposition 5.1 (ii)**, for
  `X` separated and locally of finite presentation.
* `AlgMag.limitPreserving_of_represents`, `AlgMag.thm83_iv`, `AlgMag.thm83_vi`, `AlgMag.thm83_of_lfp`:
  **Theorem 8.3 (iv), (vi)**, through `R[N] = colim R_i[N]`.
* `AlgMag.prop85`: **Proposition 8.5**, with `X/S` locally of finite presentation and `S` quasi-compact
  (both needed) and an `S`-affine `N^×`-FPR atlas.
-/

universe u

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgMag

section Rings

/-- The functor `R ↦ R[P]`. -/
noncomputable def algF (P : Type u) [AddCommMonoid P] : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := .of (AddMonoidAlgebra R P)
  map f := CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom P f.hom)
  map_id R := CommRingCat.hom_ext (RingHom.ext fun x => AddMonoidAlgebra.coeff_injective
    (Finsupp.ext fun p => by
      change (AddMonoidAlgebra.mapRingHom P (RingHom.id R) x).coeff p = x.coeff p
      simp))
  map_comp {X Y Z} f g := CommRingCat.hom_ext (RingHom.ext fun x => AddMonoidAlgebra.coeff_injective
    (Finsupp.ext fun p => by
      change (AddMonoidAlgebra.mapRingHom P (g.hom.comp f.hom) x).coeff p =
        (AddMonoidAlgebra.mapRingHom P g.hom (AddMonoidAlgebra.mapRingHom P f.hom x)).coeff p
      simp [AddMonoidAlgebra.coeff_mapRingHom]))

lemma algF_map_coeff (P : Type u) [AddCommMonoid P] {R R' : CommRingCat.{u}} (f : R ⟶ R')
    (x : AddMonoidAlgebra R P) (p : P) :
    (((algF P).map f).hom x : AddMonoidAlgebra R' P).coeff p = f.hom (x.coeff p) := by
  change (AddMonoidAlgebra.mapRingHom P f.hom x).coeff p = _
  simp [AddMonoidAlgebra.coeff_mapRingHom]

lemma algF_map_single (P : Type u) [AddCommMonoid P] {R R' : CommRingCat.{u}} (f : R ⟶ R')
    (p : P) (r : R) :
    ((algF P).map f).hom (AddMonoidAlgebra.single p r) = AddMonoidAlgebra.single p (f.hom r) :=
  AddMonoidAlgebra.mapRingHom_single _ _ _

/-- **`R[P]` commutes with filtered colimits of rings.** This is the identity
`colim (R_i[N]) = (colim R_i)[N]` of the proof of Theorem 8.3. -/
noncomputable def isColimit_algF {J : Type u} [Category.{u} J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
    {c : Cocone F} (hc : IsColimit c) (P : Type u) [AddCommMonoid P] :
    IsColimit ((algF P).mapCocone c) := by
  classical
  have hc' := isColimitOfPreserves (forget CommRingCat.{u}) hc
  have hsurj0 : ∀ r : c.pt, ∃ (j : J) (y : F.obj j), (c.ι.app j).hom y = r := fun r => by
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc' r
    exact ⟨j, y, hy⟩
  have hinj0 : ∀ (j : J) (y : F.obj j), (c.ι.app j).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (F.map f).hom y = 0 := by
    intro j y hy
    have e : ((forget CommRingCat.{u}).mapCocone c).ι.app j y =
        ((forget CommRingCat.{u}).mapCocone c).ι.app j 0 := by
      refine Eq.trans hy ?_
      exact (map_zero (c.ι.app j).hom).symm
    obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' y 0).1 e
    refine ⟨k, f, ?_⟩
    exact Eq.trans hf (map_zero (F.map f).hom)
  haveI : ReflectsColimit (F ⋙ algF P) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    have key : ∀ x : AddMonoidAlgebra c.pt P, ∃ (j : J) (y : AddMonoidAlgebra (F.obj j) P),
        ((algF P).map (c.ι.app j)).hom y = x := by
      intro x
      rw [eq_sum_single x]
      refine Finset.sum_induction _ (fun x : AddMonoidAlgebra c.pt P => ∃ (j : J) (y : AddMonoidAlgebra (F.obj j) P),
        ((algF P).map (c.ι.app j)).hom y = x) ?_ ?_ ?_
      · rintro a b ⟨j, y, rfl⟩ ⟨j', y', rfl⟩
        refine ⟨IsFiltered.max j j', ((algF P).map (F.map (IsFiltered.leftToMax j j'))).hom y +
          ((algF P).map (F.map (IsFiltered.rightToMax j j'))).hom y', ?_⟩
        have hw : ∀ {j j' : J} (f : j ⟶ j') (y : AddMonoidAlgebra (F.obj j) P),
            ((algF P).map (c.ι.app j')).hom (((algF P).map (F.map f)).hom y) =
              ((algF P).map (c.ι.app j)).hom y := by
          intro j j' f y
          have e := (algF P).map_comp (F.map f) (c.ι.app j')
          rw [c.w] at e
          rw [e]
          rfl
        rw [map_add, hw, hw]
        rfl
      · obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
        exact ⟨j, 0, map_zero _⟩
      · intro p _
        obtain ⟨j, y, hy⟩ := hsurj0 (x.coeff p)
        refine ⟨j, AddMonoidAlgebra.single p y, ?_⟩
        rw [algF_map_single, hy]
    obtain ⟨j, y, hy⟩ := key x
    exact ⟨j, y, hy.symm⟩
  · intro j x y h
    let d : AddMonoidAlgebra (F.obj j) P := x - y
    have hd : ((algF P).map (c.ι.app j)).hom d = 0 := by
      have h' : ((algF P).map (c.ι.app j)).hom x = ((algF P).map (c.ι.app j)).hom y := h
      simp [d, map_sub, h']
    have fin : ∀ s : Finset P, ∃ (k : J) (f : j ⟶ k), ∀ p ∈ s, (F.map f).hom (d.coeff p) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨j, 𝟙 j, by simp⟩
      | insert a s _ ih =>
        obtain ⟨k, f, hf⟩ := ih
        have h0 : (c.ι.app j).hom (d.coeff a) = 0 := by
          have := congrArg (fun z : AddMonoidAlgebra c.pt P => z.coeff a) hd
          exact (algF_map_coeff P (c.ι.app j) d a).symm.trans this
        obtain ⟨k', f', hf'⟩ := hinj0 j _ h0
        let t := IsFiltered.coeq (f ≫ IsFiltered.leftToMax k k') (f' ≫ IsFiltered.rightToMax k k')
        let g : j ⟶ t := f ≫ IsFiltered.leftToMax k k' ≫ IsFiltered.coeqHom _ _
        refine ⟨t, g, fun p hp => ?_⟩
        rcases Finset.mem_insert.1 hp with rfl | hp
        · have e : g = f' ≫ IsFiltered.rightToMax k k' ≫ IsFiltered.coeqHom
              (f ≫ IsFiltered.leftToMax k k') (f' ≫ IsFiltered.rightToMax k k') := by
            have := IsFiltered.coeq_condition (f ≫ IsFiltered.leftToMax k k')
              (f' ≫ IsFiltered.rightToMax k k')
            simpa [g, Category.assoc] using this
          rw [e, F.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hf', map_zero]
        · change (F.map (f ≫ _)).hom _ = 0
          rw [F.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hf p hp, map_zero]
    obtain ⟨k, f, hf⟩ := fin d.coeff.support
    refine ⟨k, f, ?_⟩
    change ((algF P).map (F.map f)).hom x = ((algF P).map (F.map f)).hom y
    rw [← sub_eq_zero, ← map_sub]
    refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun p => ?_)
    change (((algF P).map (F.map f)).hom d).coeff p = 0
    rw [algF_map_coeff]
    by_cases hp : p ∈ d.coeff.support
    · exact hf p hp
    · have : d.coeff p = 0 := by simpa using hp
      rw [this, map_zero]

end Rings

end AlgMag

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

section Sys

/-- `Spec R' → Spec R` over a morphism `s : T' → T` of affine objects of the site. -/
noncomputable def sp2 {T' T : BigFppfOver B S hS} [IsAffine ((Sch).obj T')] [IsAffine ((Sch).obj T)]
    {R R' : Type u} [CommRing R] [CommRing R'] {ρ : RT T →+* R} {ρ' : RT T' →+* R'}
    {hC : B.Contains (Spec (.of R))} {hC' : B.Contains (Spec (.of R'))} (s : T' ⟶ T) (g : R →+* R')
    (hg : g.comp ρ = ρ'.comp ((Sch).map s).appTop.hom) : spObj T' ρ' hC' ⟶ spObj T ρ hC :=
  siteHom (Spec.map (CommRingCat.ofHom g)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom ρ) ≫ ((Sch).obj T).isoSpec.inv ≫ T.hom.hom =
      Spec.map (CommRingCat.ofHom ρ') ≫ ((Sch).obj T').isoSpec.inv ≫ T'.hom.hom
    have h1 : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom ρ) =
        Spec.map (CommRingCat.ofHom ρ') ≫ Spec.map ((Sch).map s).appTop := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hg
    rw [← Category.assoc, h1, Category.assoc, ← Category.assoc (Spec.map ((Sch).map s).appTop),
      Scheme.isoSpec_inv_naturality, Category.assoc, site_w])

/-- Functions and `sp2`. -/
lemma sp2_appTop {T' T : BigFppfOver B S hS} [IsAffine ((Sch).obj T')] [IsAffine ((Sch).obj T)]
    {R R' : Type u} [CommRing R] [CommRing R'] {ρ : RT T →+* R} {ρ' : RT T' →+* R'}
    {hC : B.Contains (Spec (.of R))} {hC' : B.Contains (Spec (.of R'))} (s : T' ⟶ T) (g : R →+* R')
    (hg : g.comp ρ = ρ'.comp ((Sch).map s).appTop.hom) (x : R) :
    ((Sch).map (sp2 (hC := hC) (hC' := hC') s g hg)).appTop.hom (spSec T ρ hC x) =
      spSec T' ρ' hC' (g x) :=
  congrArg (fun k => k.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).symm

lemma sp2_toT {T' T : BigFppfOver B S hS} [IsAffine ((Sch).obj T')] [IsAffine ((Sch).obj T)]
    {R R' : Type u} [CommRing R] [CommRing R'] {ρ : RT T →+* R} {ρ' : RT T' →+* R'}
    {hC : B.Contains (Spec (.of R))} {hC' : B.Contains (Spec (.of R'))} (s : T' ⟶ T) (g : R →+* R')
    (hg : g.comp ρ = ρ'.comp ((Sch).map s).appTop.hom) :
    sp2 (hC := hC) (hC' := hC') s g hg ≫ spToT T ρ hC = spToT T' ρ' hC' ≫ s := by
  refine site_hom_ext ?_
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom ρ) ≫ ((Sch).obj T).isoSpec.inv =
    (Spec.map (CommRingCat.ofHom ρ') ≫ ((Sch).obj T').isoSpec.inv) ≫ (Sch).map s
  have h1 : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom ρ) =
      Spec.map (CommRingCat.ofHom ρ') ≫ Spec.map ((Sch).map s).appTop := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hg
  rw [← Category.assoc, h1, Category.assoc, Scheme.isoSpec_inv_naturality, Category.assoc]

/-- All terms of a diagram of the site are affine. -/
class AffDg {I : Type u} [Category.{u} I] (D : I ⥤ BigFppfOver B S hS) : Prop where
  aff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i))

instance {I : Type u} [Category.{u} I] (D : I ⥤ BigFppfOver B S hS) [AffDg D] (i : I) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)) := AffDg.aff i

/-- A functorial ring construction `R ↦ Φ(R)` over `R`, commuting with filtered colimits, staying in the
site: `Φ = (·)[N]` and `Φ = (·)[N][M]`. -/
structure AlgSys (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  Φ : CommRingCat.{u} ⥤ CommRingCat.{u}
  τ : ∀ R : CommRingCat.{u}, R →+* Φ.obj R
  τ_nat : ∀ {R R' : CommRingCat.{u}} (f : R ⟶ R'), (Φ.map f).hom.comp (τ R) = (τ R').comp f.hom
  pres : ∀ {J : Type u} [Category.{u} J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}} {c : Cocone F},
    IsColimit c → Nonempty (IsColimit (Φ.mapCocone c))
  cont : ∀ (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)],
    B.Contains (Spec (Φ.obj (RT T)))

namespace AlgSys

variable (A : AlgSys B S hS)

/-- `Spec Φ(Γ(T))`. -/
noncomputable def ob (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] : BigFppfOver B S hS :=
  spObj T (A.τ (RT T)) (A.cont T)

instance (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] : IsAffine ((Sch).obj (A.ob T)) := by
  unfold ob; infer_instance

/-- The base change map of `Spec Φ(Γ(·))`. -/
noncomputable def mp {T' T : BigFppfOver B S hS} [IsAffine ((Sch).obj T')] [IsAffine ((Sch).obj T)]
    (s : T' ⟶ T) : A.ob T' ⟶ A.ob T :=
  sp2 (hC := A.cont T) (hC' := A.cont T') s (A.Φ.map ((Sch).map s).appTop).hom (A.τ_nat _)

lemma mp_id (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] : A.mp (𝟙 T) = 𝟙 _ := by
  refine site_hom_ext ?_
  change Spec.map (CommRingCat.ofHom (A.Φ.map ((Sch).map (𝟙 T)).appTop).hom) = 𝟙 _
  have : ((Sch).map (𝟙 T)).appTop = 𝟙 _ := by simp
  rw [this, A.Φ.map_id]
  exact Spec.map_id _

lemma mp_comp {T'' T' T : BigFppfOver B S hS} [IsAffine ((Sch).obj T'')] [IsAffine ((Sch).obj T')]
    [IsAffine ((Sch).obj T)] (r : T'' ⟶ T') (s : T' ⟶ T) :
    A.mp (r ≫ s) = A.mp r ≫ A.mp s := by
  refine site_hom_ext ?_
  change Spec.map (CommRingCat.ofHom (A.Φ.map ((Sch).map (r ≫ s)).appTop).hom) =
    Spec.map (CommRingCat.ofHom (A.Φ.map ((Sch).map r).appTop).hom) ≫
      Spec.map (CommRingCat.ofHom (A.Φ.map ((Sch).map s).appTop).hom)
  rw [← Spec.map_comp]
  congr 1
  have : ((Sch).map (r ≫ s)).appTop = ((Sch).map s).appTop ≫ ((Sch).map r).appTop := by
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  rw [this, A.Φ.map_comp]
  rfl

variable {I : Type u} [Category.{u} I] (D : I ⥤ BigFppfOver B S hS) [AffDg D]

/-- The diagram `i ↦ Spec Φ(Γ(D_i))`. -/
noncomputable def dg : I ⥤ BigFppfOver B S hS where
  obj i := A.ob (D.obj i)
  map f := A.mp (D.map f)
  map_id i := by
    rw [D.map_id]; exact A.mp_id _
  map_comp f g := by
    rw [D.map_comp]; exact A.mp_comp _ _

/-- The cone with vertex `Spec Φ(Γ(c))`. -/
noncomputable def cn (c : Cone D) [IsAffine ((Sch).obj c.pt)] : Cone (A.dg D) where
  pt := A.ob c.pt
  π := { app := fun i => A.mp (T' := c.pt) (c.π.app i)
         naturality := fun i j f => by
          refine (Category.id_comp _).trans ?_
          refine Eq.trans ?_ (A.mp_comp (T'' := c.pt) (c.π.app i) (D.map f))
          rw [c.w] }

/-- `Spec Φ` of a limit of affine schemes is the limit of the `Spec Φ`. -/
theorem isLimit_cn [IsCofiltered I] (c : Cone D) [IsAffine ((Sch).obj c.pt)] (h : IsLimit ((Sch).mapCone c)) :
    Nonempty (IsLimit ((Sch).mapCone (A.cn D c))) := by
  have hA : ∀ i, IsAffine ((D ⋙ (Sch)).obj i) := fun i => AffDg.aff i
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ (Sch)).map f) := fun {i j} f =>
    have := hA j
    isAffineHom_of_isAffine _
  have h1 : IsColimit (Scheme.Γ.mapCocone ((Sch).mapCone c).op) :=
    (nonempty_isColimit_Γ_mapCocone (D ⋙ (Sch)) _ h).some
  obtain ⟨h2⟩ := A.pres h1
  have h3 := isLimitConeRightOpOfCocone _ h2
  have h4 := isLimitOfPreserves Scheme.Spec h3
  let G : Iᵒᵖ ⥤ CommRingCat.{u} := (D ⋙ (Sch)).op ⋙ Scheme.Γ ⋙ A.Φ
  let α : G.rightOp ⋙ Scheme.Spec ≅ A.dg D ⋙ (Sch) :=
    NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} f => by
      exact (Category.comp_id _).trans (Eq.trans rfl (Category.id_comp _).symm))
  have h5 := (IsLimit.postcomposeHomEquiv α _).symm h4
  exact ⟨h5.ofIsoLimit (Cone.ext (Iso.refl _) (fun i =>
    Eq.trans ((Category.comp_id _).trans rfl) (Category.id_comp _).symm))⟩

end AlgSys

end Sys

end AlgMag

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

lemma AlgSys.mp_appTop (A : AlgSys B S hS) {T' T : BigFppfOver B S hS} [IsAffine ((Sch).obj T')]
    [IsAffine ((Sch).obj T)] (s : T' ⟶ T) (x : A.Φ.obj (RT T)) :
    ((Sch).map (A.mp s)).appTop.hom (spSec T (A.τ (RT T)) (A.cont T) x) =
      spSec T' (A.τ (RT T')) (A.cont T') ((A.Φ.map ((Sch).map s).appTop).hom x) :=
  sp2_appTop s _ _ x

section Use

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
  (A : AlgSys B S hS)
  {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigFppfOver B S hS) [AffDg D]
  (c : Cone D) [IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt)]
  (h : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))

include hl h

/-- A section of a limit preserving `X` over `Spec Φ(Γ(lim T_i))` comes from a finite level. -/
theorem AlgSys.exists_rep (x : X.obj (op (A.ob c.pt))) :
    ∃ (i : I) (xi : X.obj (op (A.ob (D.obj i)))), X.map (A.mp (T' := c.pt) (c.π.app i)).op xi = x := by
  obtain ⟨hL⟩ := A.isLimit_cn D c h
  obtain ⟨hc⟩ := hl I (A.dg D) (A.cn D c) hL (fun i => inferInstanceAs (IsAffine ((Sch).obj (A.ob (D.obj i)))))
    (inferInstanceAs (IsAffine ((Sch).obj (A.ob c.pt))))
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc x
  exact ⟨j.unop, y, hy⟩

/-- Two sections over a finite level which agree on the limit agree at a further finite level. -/
theorem AlgSys.exists_eq (i : I) (a b : X.obj (op (A.ob (D.obj i))))
    (e : X.map (A.mp (T' := c.pt) (c.π.app i)).op a = X.map (A.mp (T' := c.pt) (c.π.app i)).op b) :
    ∃ (k : I) (f : k ⟶ i), X.map (A.mp (D.map f)).op a = X.map (A.mp (D.map f)).op b := by
  obtain ⟨hL⟩ := A.isLimit_cn D c h
  obtain ⟨hc⟩ := hl I (A.dg D) (A.cn D c) hL (fun i => inferInstanceAs (IsAffine ((Sch).obj (A.ob (D.obj i)))))
    (inferInstanceAs (IsAffine ((Sch).obj (A.ob c.pt))))
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc (i := op i) a b).1 e
  exact ⟨j.unop, f.unop, hf⟩

end Use

section Attr

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]

instance : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance

/-- `Φ = (·)[N]`. -/
noncomputable def algN (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (N : AddSubmonoid M) :
    AlgSys B S hS where
  Φ := algF N
  τ R := AddMonoidAlgebra.singleZeroRingHom
  τ_nat f := RingHom.ext fun r => algF_map_single N f 0 r
  pres hc := ⟨isColimit_algF hc N⟩
  cont T _ := contains_any T N

/-- `Φ = (·)[N][M]`. -/
noncomputable def algNM (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (N : AddSubmonoid M) :
    AlgSys B S hS where
  Φ := algF N ⋙ algF M
  τ R := (jr (AddMonoidAlgebra R N) M).comp AddMonoidAlgebra.singleZeroRingHom
  τ_nat {R R'} f := RingHom.ext fun r =>
    (algF_map_single M ((algF N).map f) 0 _).trans (congrArg _ (algF_map_single N f 0 r))
  pres hc := ⟨isColimit_algF (isColimit_algF hc N) M⟩
  cont T _ := contains_M (contains_any T N)

variable {T' T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

lemma ring_cN (s : T' ⟶ T) (N : AddSubmonoid M) (x : AddMonoidAlgebra (RT T) N) :
    ((algF M).map ((algF N).map ((Sch).map s).appTop)).hom (cN T N x) =
      cN T' N (((algF N).map ((Sch).map s).appTop).hom x) := by
  let γ : RT T →+* RT T' := ((Sch).map s).appTop.hom
  have key : ((AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom N γ)).comp
      (faceCoact (RT T) N)) = (faceCoact (RT T') N).comp (AddMonoidAlgebra.mapRingHom N γ) := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun n => ?_)
    · simp [faceCoact_single, AddMonoidAlgebra.mapRingHom_single]
    · simp [faceCoact_single, AddMonoidAlgebra.mapRingHom_single]
  exact congrArg (fun k : AddMonoidAlgebra (RT T) N →+* _ => k x) key

lemma ring_jr (s : T' ⟶ T) (N : AddSubmonoid M) (x : AddMonoidAlgebra (RT T) N) :
    ((algF M).map ((algF N).map ((Sch).map s).appTop)).hom (jr _ M x) =
      jr _ M (((algF N).map ((Sch).map s).appTop).hom x) :=
  algF_map_single M ((algF N).map ((Sch).map s).appTop) 0 x

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M X} {N : AddSubmonoid M}

/-- The value of a point of `X^N` at the universal point of `𝔸(N)`. -/
noncomputable abbrev univ (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] (φ : AttractorPt act N T) :
    X.obj (op (spObj T (ρN T N) (contains_any T N))) :=
  φ.app (spToT T (ρN T N) (contains_any T N)) (spPt (monN _ N))

/-- Base change on universal values. -/
lemma univ_baseChange (s : T' ⟶ T) (φ : AttractorPt act N T) :
    univ T' (φ.baseChange s) = X.map ((algN B S hS N).mp s).op (univ T φ) := by
  have hn := φ.naturality ((algN B S hS N).mp s) (spToT T (ρN T N) (contains_any T N)) (spPt (monN _ N))
  have e1 : (algN B S hS N).mp s ≫ spToT T (ρN T N) (contains_any T N) =
      spToT T' (ρN T' N) (contains_any T' N) ≫ s := sp2_toT _ _ _
  have e2 : APt.res ((algN B S hS N).mp s).op (spPt (T := T) (ρ := ρN T N) (hC := contains_any T N)
      (monN _ N)) = spPt (T := T') (ρ := ρN T' N) (hC := contains_any T' N) (monN _ N) := by
    refine MonoidHom.ext fun n => ?_
    refine (AlgSys.mp_appTop (algN B S hS N) s (monN _ N n)).trans ?_
    refine congrArg (spSec T' (ρN T' N) (contains_any T' N)) ?_
    refine (algF_map_single N _ _ _).trans ?_
    rw [map_one]
    rfl
  have gen : ∀ {T₁ : BigFppfOver B S hS} {t t' : T₁ ⟶ T} {a a' : APt (fppfO B S hS) N (op T₁)},
      t = t' → a = a' → φ.app t a = φ.app t' a' := by
    rintro _ _ _ _ _ rfl rfl; rfl
  exact (gen e1.symm e2.symm).trans hn

/-- A point of `X^N` on an affine `T` is determined by its universal value. -/
lemma eq_of_univ {φ ψ : AttractorPt act N T} (e : univ T φ = univ T ψ) : φ = ψ := by
  let Uni := spUniversal T N (contains_any T N)
  refine AttractorPt.ext ?_
  funext T₁ t a
  rw [AttractorPt.app_eq_of_universal Uni, ψ.app_eq_of_universal Uni]
  exact congrArg _ e

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
lemma mapMapOp {P Q R : BigFppfOver B S hS} (f : P ⟶ Q) (g : Q ⟶ R) (x : X.obj (op R)) :
    X.map f.op (X.map g.op x) = X.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp_apply]

/-- First side of `IsKey`. -/
noncomputable def kA (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] (N : AddSubmonoid M)
    (x : X.obj (op (spObj T (ρN T N) (contains_any T N)))) :
    X.obj (op (spObj T ((jr _ M).comp (ρN T N)) (contains_M (contains_any T N)))) :=
  X.map (spMap T (hC := contains_any T N) (hC' := contains_M (contains_any T N)) (cN T N) cN_ρN).op x

/-- Second side of `IsKey`. -/
noncomputable def kB (act : AAction (fppfO B S hS) M X) (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)]
    (N : AddSubmonoid M) (x : X.obj (op (spObj T (ρN T N) (contains_any T N)))) :
    X.obj (op (spObj T ((jr _ M).comp (ρN T N)) (contains_M (contains_any T N)))) :=
  act.smul (spPt (eM _ M)) (X.map (spMap T (hC := contains_any T N) (hC' := contains_M (contains_any T N))
    (jr _ M) rfl).op x)

lemma kA_pull (s : T' ⟶ T) (x : X.obj (op (spObj T (ρN T N) (contains_any T N)))) :
    X.map ((algNM B S hS N).mp s).op (kA T N x) = kA T' N (X.map ((algN B S hS N).mp s).op x) := by
  have A : spMap T' (hC := contains_any T' N) (hC' := contains_M (contains_any T' N)) (cN T' N) cN_ρN ≫
      (algN B S hS N).mp s = (algNM B S hS N).mp s ≫
        spMap T (hC := contains_any T N) (hC' := contains_M (contains_any T N)) (cN T N) cN_ρN := by
    refine site_hom_ext ?_
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    exact CommRingCat.hom_ext (RingHom.ext fun y => (ring_cN s N y).symm)
  exact (mapMapOp _ _ _).trans ((congrArg (fun k => X.map (Quiver.Hom.op k) x) A.symm).trans
    (mapMapOp _ _ _).symm)

lemma kB_pull (s : T' ⟶ T) (x : X.obj (op (spObj T (ρN T N) (contains_any T N)))) :
    X.map ((algNM B S hS N).mp s).op (kB act T N x) = kB act T' N (X.map ((algN B S hS N).mp s).op x) := by
  have A : spMap T' (hC := contains_any T' N) (hC' := contains_M (contains_any T' N)) (jr _ M) rfl ≫
      (algN B S hS N).mp s = (algNM B S hS N).mp s ≫
        spMap T (hC := contains_any T N) (hC' := contains_M (contains_any T N)) (jr _ M) rfl := by
    refine site_hom_ext ?_
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    exact CommRingCat.hom_ext (RingHom.ext fun y => (ring_jr s N y).symm)
  have e : APt.res ((algNM B S hS N).mp s).op (spPt (T := T) (ρ := (jr _ M).comp (ρN T N))
      (hC := contains_M (contains_any T N)) (eM _ M)) =
      spPt (T := T') (ρ := (jr _ M).comp (ρN T' N)) (hC := contains_M (contains_any T' N)) (eM _ M) := by
    refine MonoidHom.ext fun n => ?_
    refine (AlgSys.mp_appTop (algNM B S hS N) s (eM _ M n)).trans ?_
    refine congrArg (spSec T' ((jr _ M).comp (ρN T' N)) (contains_M (contains_any T' N))) ?_
    refine (algF_map_single M _ _ _).trans ?_
    rw [map_one]
    rfl
  refine (act.map_smul _ _ _).trans ?_
  refine congr (congrArg _ e) ?_
  exact (mapMapOp _ _ _).trans ((congrArg (fun k => X.map (Quiver.Hom.op k) x) A.symm).trans
    (mapMapOp _ _ _).symm)

/-- **Theorem 8.3 (iv), functor form.** If `X` commutes with limits of affine schemes, then so does the
attractor `X^N`, for every magnet `N`. As in the printed proof: `𝔸(N)_T = lim 𝔸(N)_{T_i}`, since
`R[N] = colim R_i[N]`. -/
theorem limitPreserving_of_represents
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (rP : RepresentsAttractor act N P) :
    LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) P := by
  intro I _ _ D c h haff haffc
  haveI : AffDg D := ⟨haff⟩
  haveI := haffc
  let A₁ := algN B S hS N
  let A₂ := algNM B S hS N
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
  · intro y
    let φ := rP.equiv c.pt y
    obtain ⟨i, xi, hxi⟩ := A₁.exists_rep hl D c h (univ c.pt φ)
    have hkT : kA c.pt N (univ c.pt φ) = kB act c.pt N (univ c.pt φ) := isKey_app N φ
    have e0 : X.map (A₂.mp (T' := c.pt) (c.π.app i)).op (kA (D.obj i) N xi) =
        X.map (A₂.mp (T' := c.pt) (c.π.app i)).op (kB act (D.obj i) N xi) := by
      refine (kA_pull (T' := c.pt) (c.π.app i) xi).trans ?_
      refine Eq.trans ?_ (kB_pull (T' := c.pt) (c.π.app i) xi).symm
      have := hkT
      rw [← hxi] at this
      exact this
    obtain ⟨k, f, hf⟩ := A₂.exists_eq hl D c h i _ _ e0
    have hk : IsKey (act := act) N (X.map (A₁.mp (D.map f)).op xi) :=
      (kA_pull (D.map f) xi).symm.trans (hf.trans (kB_pull (D.map f) xi))
    obtain ⟨φk, hφk⟩ := exists_attractorPt_of_key N _ hk
    refine ⟨op k, (rP.equiv (D.obj k)).symm φk, ?_⟩
    apply (rP.equiv c.pt).injective
    refine Eq.trans ?_ (rP.naturality (c.π.app k) _).symm
    rw [Equiv.apply_symm_apply]
    refine eq_of_univ ?_
    refine Eq.trans hxi.symm ?_
    refine Eq.trans ?_ (univ_baseChange (T' := c.pt) (c.π.app k) φk).symm
    have e1 : univ (D.obj k) φk = X.map (A₁.mp (D.map f)).op xi := hφk
    rw [e1]
    refine Eq.trans ?_ (mapMapOp _ _ _).symm
    have e2 : A₁.mp (T' := c.pt) (c.π.app i) = A₁.mp (T' := c.pt) (c.π.app k) ≫ A₁.mp (D.map f) := by
      rw [← A₁.mp_comp, c.w]
    exact congrArg (fun z => X.map (Quiver.Hom.op z) xi) e2
  · intro i y y' e
    obtain ⟨i⟩ := i
    have hb : (rP.equiv (D.obj i) y).baseChange (c.π.app i) = (rP.equiv (D.obj i) y').baseChange (c.π.app i) :=
      (rP.naturality (c.π.app i) y).symm.trans ((congrArg _ e).trans (rP.naturality (c.π.app i) y'))
    have hu := congrArg (univ c.pt) hb
    rw [univ_baseChange, univ_baseChange] at hu
    obtain ⟨k, f, hf⟩ := A₁.exists_eq hl D c h i _ _ hu
    refine ⟨op k, f.op, ?_⟩
    apply (rP.equiv (D.obj k)).injective
    refine (rP.naturality (D.map f) y).trans (Eq.trans ?_ (rP.naturality (D.map f) y').symm)
    refine eq_of_univ ?_
    rw [univ_baseChange, univ_baseChange]
    exact hf

end Attr

end AlgMag

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

section AdjRings

variable {A R' : Type u} [CommRing A] [CommRing R'] (ρ : A →+* R')

/-- The subring of `R'` generated over `A` by a finite set. -/
irreducible_def adj (s : Finset R') : Subring R' :=
  letI := ρ.toAlgebra
  (Algebra.adjoin A (s : Set R')).toSubring

lemma mem_adj_ρ (s : Finset R') (r : A) : ρ r ∈ adj ρ s := by
  letI := ρ.toAlgebra
  rw [adj_def]
  exact (Algebra.adjoin A (s : Set R')).algebraMap_mem r

/-- The structure map. -/
noncomputable def adjρ (s : Finset R') : A →+* adj ρ s :=
  ρ.codRestrict (adj ρ s) (mem_adj_ρ ρ s)

/-- The inclusion. -/
noncomputable def adjι (s : Finset R') : adj ρ s →+* R' := (adj ρ s).subtype

lemma adjι_comp (s : Finset R') : (adjι ρ s).comp (adjρ ρ s) = ρ := rfl

variable {s t : Finset R'}

lemma adj_mono (h : s ≤ t) : adj ρ s ≤ adj ρ t := by
  letI := ρ.toAlgebra
  rw [adj_def, adj_def]
  exact Algebra.adjoin_mono (R := A) (Finset.coe_subset.2 h)

/-- The transition map. -/
noncomputable def adjT (h : s ≤ t) : adj ρ s →+* adj ρ t :=
  (adjι ρ s).codRestrict (adj ρ t) (fun x => adj_mono ρ h x.2)

lemma adjT_id (h : s ≤ s) : adjT ρ h = RingHom.id _ := RingHom.ext fun _ => Subtype.ext rfl

lemma adjT_comp {r : Finset R'} (h : s ≤ t) (h' : t ≤ r) (h'' : s ≤ r) :
    adjT ρ h'' = (adjT ρ h').comp (adjT ρ h) := RingHom.ext fun _ => Subtype.ext rfl

lemma adjT_ρ (h : s ≤ t) : (adjT ρ h).comp (adjρ ρ s) = adjρ ρ t :=
  RingHom.ext fun _ => Subtype.ext rfl

lemma adjι_T (h : s ≤ t) : (adjι ρ t).comp (adjT ρ h) = adjι ρ s :=
  RingHom.ext fun _ => rfl

/-- The diagram of rings, on the opposite of the opposite of the finite subsets. -/
noncomputable def adjD : (Finset R')ᵒᵖᵒᵖ ⥤ CommRingCat.{u} where
  obj s := .of (adj ρ s.unop.unop)
  map {s t} f := CommRingCat.ofHom (adjT ρ (leOfHom f.unop.unop))
  map_id s := CommRingCat.hom_ext (adjT_id ρ (le_refl s.unop.unop))
  map_comp {X Y Z} f g := CommRingCat.hom_ext (adjT_comp ρ (leOfHom f.unop.unop) (leOfHom g.unop.unop)
    (le_trans (leOfHom f.unop.unop) (leOfHom g.unop.unop)))

/-- `R'` as a cocone. -/
noncomputable def adjC : Cocone (adjD ρ) where
  pt := .of R'
  ι := { app := fun s => CommRingCat.ofHom (adjι ρ s.unop.unop)
         naturality := fun _ _ _ => CommRingCat.hom_ext (RingHom.ext fun _ => rfl) }

/-- `R'` is the filtered union of its subrings of finite type over `A`. -/
noncomputable def isColimit_adjC : IsColimit (adjC ρ) := by
  haveI : ReflectsColimit (adjD ρ) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    have hx : (show R' from x) ∈ adj ρ ({show R' from x} : Finset R') := by
      letI := ρ.toAlgebra
      rw [adj_def]
      exact Algebra.subset_adjoin (R := A) (s := (({show R' from x} : Finset R') : Set R'))
        (Finset.mem_coe.2 (Finset.mem_singleton_self _))
    exact ⟨op (op {show R' from x}), ⟨_, hx⟩, rfl⟩
  · intro s x y h
    have e : x = y := Subtype.ext (a1 := x) (a2 := y) h
    exact ⟨s, 𝟙 s, congrArg _ e⟩

lemma exists_ring_adj {Ri : Type u} [CommRing Ri] (ρi : A →+* Ri) (g : Ri →+* R') (hg : g.comp ρi = ρ)
    (hinj : Function.Injective g) (s : Finset R') (hi : ∀ x ∈ s, x ∈ g.range) :
    ∃ φ : adj ρ s →+* Ri, φ.comp (adjρ ρ s) = ρi ∧ g.comp φ = adjι ρ s := by
  have key : ∀ y : R', (letI := ρ.toAlgebra; y ∈ Algebra.adjoin A (s : Set R')) → ∃ r : Ri, g r = y := by
    letI := ρ.toAlgebra
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => exact hi z hz
    | algebraMap r => exact ⟨ρi r, congrArg (fun k => k r) hg⟩
    | add a b _ _ ha hb =>
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      exact ⟨p + q, by rw [map_add, hp, hq]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨p, hp⟩ := ha
      obtain ⟨q, hq⟩ := hb
      exact ⟨p * q, by rw [map_mul, hp, hq]⟩
  have hlift : ∀ y : adj ρ s, ∃ r : Ri, g r = y := by
    rintro ⟨y, hy⟩
    rw [adj_def] at hy
    exact key y hy
  choose l hl' using hlift
  let φ : adj ρ s →+* Ri :=
    { toFun := l
      map_one' := hinj (by rw [hl', map_one]; rfl)
      map_mul' := fun a b => hinj (by rw [hl', map_mul, hl', hl']; rfl)
      map_zero' := hinj (by rw [hl', map_zero]; rfl)
      map_add' := fun a b => hinj (by rw [hl', map_add, hl', hl']; rfl) }
  refine ⟨φ, RingHom.ext fun r => hinj ?_, RingHom.ext fun y => hl' y⟩
  exact (hl' _).trans (congrArg (fun k => k r) hg).symm

end AdjRings

section Finite

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {R' : Type u} [CommRing R'] (ρ : RT T →+* R') (hC : B.Contains (Spec (.of R')))

lemma adj_contains (s : Finset R') : B.Contains (Spec (.of (adj ρ s))) := by
  letI := ρ.toAlgebra
  haveI : Algebra.FiniteType (RT T) (Algebra.adjoin (RT T) (s : Set R')) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
  rw [adj_def]
  exact contains_ft (RT T) (Algebra.adjoin (RT T) (s : Set R')) (contains_RT T)

lemma spMap_adj_id {s : Finset R'} (h : s ≤ s) :
    spMap T (hC := adj_contains T ρ s) (hC' := adj_contains T ρ s) (adjT ρ h) (adjT_ρ ρ h) = 𝟙 _ := by
  refine site_hom_ext ?_
  change Spec.map (CommRingCat.ofHom (adjT ρ h)) = 𝟙 _
  rw [adjT_id]
  exact Spec.map_id _

lemma spMap_adj_comp {r s t : Finset R'} (h : t ≤ s) (h' : s ≤ r) (h'' : t ≤ r) :
    spMap T (hC := adj_contains T ρ t) (hC' := adj_contains T ρ r) (adjT ρ h'') (adjT_ρ ρ h'') =
      spMap T (hC := adj_contains T ρ s) (hC' := adj_contains T ρ r) (adjT ρ h') (adjT_ρ ρ h') ≫
        spMap T (hC := adj_contains T ρ t) (hC' := adj_contains T ρ s) (adjT ρ h) (adjT_ρ ρ h) := by
  refine site_hom_ext ?_
  change Spec.map (CommRingCat.ofHom (adjT ρ h'')) =
    Spec.map (CommRingCat.ofHom (adjT ρ h')) ≫ Spec.map (CommRingCat.ofHom (adjT ρ h))
  rw [← Spec.map_comp, adjT_comp ρ h h' h'']
  rfl

/-- `spObj` on the diagram. -/
noncomputable def adjS : (Finset R')ᵒᵖ ⥤ BigFppfOver B S hS where
  obj s := spObj T (adjρ ρ s.unop) (adj_contains T ρ s.unop)
  map {s t} f := spMap T (hC := adj_contains T ρ t.unop) (hC' := adj_contains T ρ s.unop)
    (adjT ρ (leOfHom f.unop)) (adjT_ρ ρ _)
  map_id s := spMap_adj_id T ρ _
  map_comp {X Y Z} f g := spMap_adj_comp T ρ (leOfHom g.unop) (leOfHom f.unop) _

/-- The cone with vertex `Spec R'`. -/
noncomputable def adjCn : Cone (adjS T ρ) where
  pt := spObj T ρ hC
  π := { app := fun s => spMap T (hC := adj_contains T ρ s.unop) (hC' := hC) (adjι ρ s.unop) (adjι_comp ρ _)
         naturality := fun i j f => by
          refine (Category.id_comp _).trans (site_hom_ext ?_)
          change Spec.map (CommRingCat.ofHom (adjι ρ j.unop)) =
            Spec.map (CommRingCat.ofHom (adjι ρ i.unop)) ≫ Spec.map (CommRingCat.ofHom (adjT ρ (leOfHom f.unop)))
          rw [← Spec.map_comp, ← adjι_T ρ (leOfHom f.unop)]
          rfl }

instance : AffDg (adjS T ρ) := ⟨fun s => inferInstanceAs (IsAffine ((Sch).obj (spObj T _ _)))⟩

theorem isLimit_adjCn : Nonempty (IsLimit ((Sch).mapCone (adjCn T ρ hC))) := by
  have h3 := isLimitConeRightOpOfCocone _ (isColimit_adjC ρ)
  have h4 := isLimitOfPreserves Scheme.Spec h3
  let α : (adjD ρ).rightOp ⋙ Scheme.Spec ≅ adjS T ρ ⋙ (Sch) :=
    NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} f =>
      (Category.comp_id _).trans (Eq.trans rfl (Category.id_comp _).symm))
  have h5 := (IsLimit.postcomposeHomEquiv α _).symm h4
  exact ⟨h5.ofIsoLimit (Cone.ext (Iso.refl _) (fun i =>
    Eq.trans ((Category.comp_id _).trans rfl) (Category.id_comp _).symm))⟩

end Finite

/-- **Tag 049J in the form used by Proposition 3.37.** A presheaf commuting with limits of affine schemes
is limit preserving in the sense of `AlgMag.IsLimitPreserving`. -/
theorem isLimitPreserving_of_limitPreserving {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X) :
    IsLimitPreserving X := by
  intro T _ R' _ ρ hC ι Ri _ ρi hCi gi hg hinj hun x
  obtain ⟨hL⟩ := isLimit_adjCn T ρ hC
  obtain ⟨hc⟩ := hl (Finset R')ᵒᵖ (adjS T ρ) (adjCn T ρ hC) hL
    (fun s => inferInstanceAs (IsAffine ((Sch).obj (spObj T _ _))))
    (inferInstanceAs (IsAffine ((Sch).obj (spObj T _ _))))
  obtain ⟨s, xs, hxs⟩ := Types.jointly_surjective_of_isColimit hc x
  obtain ⟨i, hi⟩ := hun s.unop.unop
  obtain ⟨φ, hφ, hgφ⟩ := exists_ring_adj ρ (ρi i) (gi i) (hg i) (hinj i) s.unop.unop hi
  refine ⟨i, X.map (spMap T (hC := adj_contains T ρ s.unop.unop) (hC' := hCi i) φ hφ).op xs, ?_⟩
  refine Eq.trans ?_ hxs
  refine (mapMapOp _ _ _).trans ?_
  refine congrArg (fun k => X.map (Quiver.Hom.op k) xs) ?_
  refine site_hom_ext ?_
  change Spec.map (CommRingCat.ofHom (gi i)) ≫ Spec.map (CommRingCat.ofHom φ) =
    Spec.map (CommRingCat.ofHom (adjι ρ s.unop.unop))
  rw [← Spec.map_comp, ← hgφ]
  rfl

end AlgMag

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

namespace AlgMag

section Degrees

variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]

/-- The step of the proof of **Proposition 8.5** on the graded algebra: "consider degrees of a finite set
of generators". There is a finite set `D` of degrees, such that for magnets `N' , N''` with the same
elements of `D`, the ideal of `Spec A^{N'}` lies in the ideal of `Spec A^{N''}`. -/
theorem exists_degrees (ρ : A →ₐ[R] AddMonoidAlgebra A M) [GradedAlgebra (GB.coactGrading ρ)]
    [Algebra.FiniteType R A] :
    ∃ D : Finset M, ∀ N' N'' : AddSubmonoid M, (∀ d ∈ D, d ∈ N'' → d ∈ N') →
      magnetIdeal (GB.coactGrading ρ) N' ≤ magnetIdeal (GB.coactGrading ρ) N'' := by
  obtain ⟨G, hG⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  have hmem : ∀ (a : A) (m : M), (ρ a).coeff m ∈ GB.coactGrading ρ m := by
    intro a m
    have hd : ρ a = ∑ i ∈ (DirectSum.decompose (GB.coactGrading ρ) a).support,
        AddMonoidAlgebra.single i ((DirectSum.decompose (GB.coactGrading ρ) a) i : A) := by
      conv_lhs => rw [← DirectSum.sum_support_decompose (GB.coactGrading ρ) a]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => GB.mem_coactGrading.1 (SetLike.coe_mem _)
    rw [hd, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
    by_cases hm : m ∈ (DirectSum.decompose (GB.coactGrading ρ) a).support
    · rw [Finset.sum_eq_single m]
      · simp [AddMonoidAlgebra.coeff_single, SetLike.coe_mem]
      · intro b _ hb
        simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hb]
      · intro h; exact absurd hm h
    · rw [Finset.sum_eq_zero]
      · exact Submodule.zero_mem _
      · intro b hb
        have : b ≠ m := fun e => hm (e ▸ hb)
        simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, this]
  refine ⟨G.biUnion fun g => (ρ g).coeff.support, fun N' N'' hD => ?_⟩
  set I := magnetIdeal (GB.coactGrading ρ) N'' with hI
  let C := A ⧸ I
  let Ψ : A →+* AddMonoidAlgebra C M :=
    (AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk I)).comp (ρ : A →+* AddMonoidAlgebra A M)
  let Sb : Subring (AddMonoidAlgebra C M) :=
    (AddMonoidAlgebra.mapDomainRingHom C N'.subtype).range
  have hSb : ∀ x : AddMonoidAlgebra C M, (∀ m, m ∉ N' → x.coeff m = 0) → x ∈ Sb := by
    intro x hx
    rw [eq_sum_single x]
    refine Subring.sum_mem _ fun m hm => ?_
    have hmN : m ∈ N' := by
      by_contra h
      exact (Finsupp.mem_support_iff.1 hm) (hx m h)
    refine ⟨AddMonoidAlgebra.single ⟨m, hmN⟩ (x.coeff m), ?_⟩
    simp
  have hSb' : ∀ x ∈ Sb, ∀ m, m ∉ N' → x.coeff m = 0 := by
    rintro _ ⟨y, rfl⟩ m hm
    rw [eq_sum_single y, map_sum, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
    refine Finset.sum_eq_zero fun n _ => ?_
    have : (n : M) ≠ m := fun e => hm (e ▸ n.2)
    simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, this]
  have hall : ∀ a : A, Ψ a ∈ Sb := by
    intro a
    have ha : a ∈ Algebra.adjoin R (G : Set A) := by rw [hG]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem g hg =>
      refine hSb _ fun m hm => ?_
      change AddMonoidAlgebra.coeff (AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk I) (ρ g)) m = 0
      rw [AddMonoidAlgebra.coeff_mapRingHom]
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      by_cases h0 : (ρ g).coeff m = 0
      · rw [h0]; exact I.zero_mem
      · have hmD : m ∈ G.biUnion fun g => (ρ g).coeff.support :=
          Finset.mem_biUnion.2 ⟨g, hg, Finsupp.mem_support_iff.2 h0⟩
        exact mem_magnetIdeal_of_notMem (fun h => hm (hD m hmD h)) (hmem g m)
    | algebraMap r =>
      refine hSb _ fun m hm => ?_
      have hm0 : (0 : M) ≠ m := fun e => hm (e ▸ N'.zero_mem)
      have e : ρ (algebraMap R A r) = AddMonoidAlgebra.single 0 (algebraMap R A r) := by
        rw [AlgHom.commutes]; rfl
      change AddMonoidAlgebra.coeff (AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk I)
        (ρ (algebraMap R A r))) m = 0
      rw [e, AddMonoidAlgebra.mapRingHom_single]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hm0]
    | add x y _ _ hx hy => rw [map_add]; exact Sb.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact Sb.mul_mem hx hy
  refine Ideal.span_le.2 ?_
  intro a ha
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha
  obtain ⟨m, hm, ha⟩ := ha
  have e1 : Ψ a = AddMonoidAlgebra.single m (Ideal.Quotient.mk I a) := by
    change AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk I) (ρ a) = _
    rw [GB.mem_coactGrading.1 ha, AddMonoidAlgebra.mapRingHom_single]
  have e2 := hSb' _ (hall a) m hm
  rw [e1] at e2
  have e3 : Ideal.Quotient.mk I a = 0 := by simpa [AddMonoidAlgebra.coeff_single] using e2
  exact Ideal.Quotient.eq_zero_iff_mem.1 e3

end Degrees

end AlgMag

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism
open scoped Classical

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] GB.gradedAlgebraOf

section Chart

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {A' : Type u} {V : A' → ((BigFppfOver.toScheme B S hS).obj U).Opens}

/-- Gluing points of `U^N` over an open cover of `T`. -/
theorem exists_att_of_opens (hV : IsAffineDecomposition actU V) {N : AddSubmonoid M}
    {T : BigFppfOver B S hS} (y : T ⟶ U) {ι : Type u} (O : ι → ((SCH).obj T).Opens)
    (hO : ∀ x, ∃ i, x ∈ O i)
    (H : ∀ i, ∃ φ : AttractorPt actU N (openObj (O i)), φ.toPoint = openJ (O i) ≫ y) :
    ∃ φ : AttractorPt actU N T, φ.toPoint = y := by
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) (attractor actU N) :=
    isSheaf_attractor actU N _ (BigFppfOver.isSheaf_of_type_yoneda_obj U)
  have hmem : Sieve.ofArrows (fun i => openObj (O i)) (fun i => openJ (O i)) ∈
      BigFppfOver.topology B S hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS _
      (fun i => inferInstanceAs (IsOpenImmersion (iV _))) fun x => ?_
    obtain ⟨c, hc⟩ := hO x
    exact ⟨c, (⟨x, hc⟩ : O c), rfl⟩
  choose φs hφs using H
  have hsf : (Presieve.ofArrows _ (fun i => openJ (O i))).IsSheafFor (attractor actU N) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hsh _ hmem
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf φs (by
    intro i j Z gi gj hij
    apply toPoint_injective_U hV
    change AttractorPt.toPoint (AttractorPt.baseChange gi (φs i)) =
      AttractorPt.toPoint (AttractorPt.baseChange gj (φs j))
    rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, hφs, hφs]
    change gi ≫ _ ≫ y = gj ≫ _ ≫ y
    rw [← Category.assoc, ← Category.assoc, hij])
  refine ⟨t, ?_⟩
  refine (BigFppfOver.isSheaf_of_type_yoneda_obj U _ hmem).isSeparatedFor.ext fun W g hg => ?_
  obtain ⟨_, r, s', ⟨b⟩, rfl⟩ := hg
  have h1 : (AttractorPt.baseChange (openJ (O b)) t).toPoint = (φs b).toPoint :=
    congrArg AttractorPt.toPoint (ht b)
  have h2 : openJ (O b) ≫ t.toPoint = openJ (O b) ≫ y :=
    ((AttractorPt.toPoint_baseChange (openJ (O b)) t).symm.trans h1).trans (hφs b)
  change (r ≫ openJ _) ≫ t.toPoint = (r ≫ openJ _) ≫ y
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun q => r ≫ q) h2

/-- **The step `U^{N_c} = U^{N_i}`** of the proof of **Proposition 8.5**, for `S` covered by the affine
opens `Uk`: if on every chart the ideal of `N'` lies in the ideal of `N''`, then a point of `U^{N''}`
is a point of `U^{N'}`. -/
theorem exists_att_of_ideal_le (hV : IsAffineDecomposition actU V) {κ : Type u} (Uk : κ → S.affineOpens)
    (hUk : ∀ s : S, ∃ k, s ∈ (Uk k).1) {N' N'' : AddSubmonoid M}
    (hle : ∀ b k, haveI : IsAffineHom (openOver (V b)).hom := hV.isAffineHom b
      magnetIdeal (GB.gradingOf (Uk k).2 (overAct (hM_of hS M) (hV.stable b))) N' ≤
        magnetIdeal (GB.gradingOf (Uk k).2 (overAct (hM_of hS M) (hV.stable b))) N'')
    {T : BigFppfOver B S hS} (φ : AttractorPt actU N'' T) :
    ∃ φ' : AttractorPt actU N' T, φ'.toPoint = φ.toPoint := by
  let y := φ.toPoint
  let O : (A' × κ) → ((SCH).obj T).Opens := fun p =>
    (SCH).map y ⁻¹ᵁ V p.1 ⊓ structMap T ⁻¹ᵁ (Uk p.2).1
  refine exists_att_of_opens hV y O ?_ fun p => ?_
  · intro x
    have : (SCH).map y x ∈ iSup V := by rw [hV.iSup_eq_top]; trivial
    obtain ⟨c, hc⟩ := (TopologicalSpace.Opens.mem_iSup).1 this
    obtain ⟨k, hk⟩ := hUk (structMap T x)
    exact ⟨(c, k), hc, hk⟩
  · obtain ⟨b, k⟩ := p
    have hA : IsAffineHom (openOver (V b)).hom := hV.isAffineHom b
    let P := openObj (O (b, k))
    let J : P ⟶ T := openJ (O (b, k))
    obtain ⟨t, ht⟩ := exists_lift_open (V := V b) (J ≫ y) (fun p => by
      rw [Functor.map_comp]
      exact p.2.1)
    obtain ⟨φo, hφo⟩ := exists_over_att hV b (φ.baseChange J) t
      (ht.trans (AttractorPt.toPoint_baseChange J φ).symm)
    have hW : GB.LiesOver (ov P) (Uk k).1 := by
      refine top_le_iff.1 fun p _ => ?_
      exact p.2.2
    have hkill := (GB.exists_att_iff_kills (overAct (hM_of hS M) (hV.stable b)) (Uk k).2 hW (ovMap t)).1
      ⟨φo, hφo⟩
    obtain ⟨φo', hφo'⟩ := (GB.exists_att_iff_kills (N := N') (overAct (hM_of hS M) (hV.stable b))
      (Uk k).2 hW (ovMap t)).2 fun a ha => hkill a (hle b k ha)
    obtain ⟨ψ, hψ⟩ := exists_site_att (hV.stable b) φo'
    refine ⟨ψ, hψ.trans ?_⟩
    rw [hφo']
    exact ht

end Chart

end AlgMag

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- **Tag 049J.** An algebraic space locally of finite presentation over `S` is limit preserving. -/
theorem isLimitPreserving_of_lfp {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) : IsLimitPreserving X :=
  isLimitPreserving_of_limitPreserving
    ((Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS hX).1 hfp)

section Thm

attribute [local instance] countable_of_fg83

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}

/-- **Theorem 8.3 (iv).** If `X/S` is locally of finite presentation, the algebraic space representing
`X^N` is locally of finite presentation over `S`. -/
theorem thm83_iv (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) {N : AddSubmonoid M}
    (r : Thm83Repr actX N) :
    Space.IsLocallyOfFinitePresentation B S hS (terminal.from r.P) :=
  (Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS r.algP).2
    (limitPreserving_of_represents
      ((Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS hX).1 hfp) r.rP)

/-- Separatedness of `X^N`, from the affine and closed maps of `Thm83Repr`. -/
lemma thm83_sep (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) {N : AddSubmonoid M}
    (r : Thm83Repr actX N) : IsSeparatedOver r.P := by
  have hc : Space.IsSeparated B S hS r.c :=
    isSeparated_of_presheaf (P := @AlgebraicGeometry.IsAffineHom) (fun g _ => inferInstance) r.algP r.affine_c
  have hi : Space.IsSeparated B S hS r.i :=
    isSeparated_of_presheaf (P := @IsClosedImmersion) (fun g _ => inferInstance) r.algY r.closed_i
  have e : toBase r.P = r.c ≫ r.i ≫ toBase X := by
    ext T x
    exact Over.mkIdTerminal.hom_ext _ _
  change Space.IsSeparated B S hS (toBase r.P)
  rw [e]
  exact Space.isSeparated_comp B S hS _ _ hc (Space.isSeparated_comp B S hS _ _ hi hsep)

/-- Quasi-compactness over `S` goes up along a representable morphism with quasi-compact base changes. -/
lemma isQuasiCompact_terminal_of_presheaf {P : MorphismProperty Scheme.{u}}
    (hP : ∀ {X₁ X₂ : Scheme.{u}} (g : X₁ ⟶ X₂), P g → QuasiCompact g)
    (hPs : P.IsStableUnderBaseChange)
    {A Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : A ⟶ Y}
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage P (SCH))) f)
    (hq : Space.IsQuasiCompact B S hS (terminal.from Y)) :
    Space.IsQuasiCompact B S hS (terminal.from A) := by
  intro Z hZ hZqc k
  have hW := hq Z hZ hZqc k
  let m : pullback k (terminal.from A) ⟶ pullback k (terminal.from Y) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f) (Subsingleton.elim _ _)
  have hsq : IsPullback m (pullback.snd _ _) (pullback.snd _ _) f := by
    have e : terminal.from A = f ≫ terminal.from Y := Subsingleton.elim _ _
    have h0 := IsPullback.of_hasPullback k (terminal.from A)
    have e2 : m ≫ pullback.fst k (terminal.from Y) = pullback.fst k (terminal.from A) :=
      pullback.lift_fst _ _ _
    refine IsPullback.of_right (h₂₂ := terminal.from Y) (v₁₃ := k) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback k (terminal.from Y))
    rw [e2, ← e]
    exact h0
  exact isQuasiCompactSpace_of_presheaf hP
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip hf) hW

/-- The final presheaf is the Yoneda presheaf of `S/S`. -/
lemma isTerminal_yoneda_top :
    Nonempty (IsTerminal (yoneda.obj (siteTop (B := B) (S := S) (hS := hS)))) :=
  ⟨IsTerminal.ofUniqueHom (fun X => toBase X) (fun X m => by
    ext T x
    exact Over.mkIdTerminal.hom_ext _ _)⟩

instance : IsIso (terminal.from (yoneda.obj (siteTop (B := B) (S := S) (hS := hS)))) := by
  obtain ⟨hT⟩ := isTerminal_yoneda_top (B := B) (S := S) (hS := hS)
  exact ⟨hT.from _, hT.hom_ext _ _, terminalIsTerminal.hom_ext _ _⟩

lemma terminal_from_eq (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    terminal.from X = toBase X ≫ terminal.from (yoneda.obj (siteTop (B := B) (S := S) (hS := hS))) :=
  Subsingleton.elim _ _

/-- **Theorem 8.3 (vi).** If `X/S` is of finite presentation, so is `X^N/S`. -/
theorem thm83_vi (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsFinitePresentation B S hS (terminal.from X)) {N : AddSubmonoid M}
    (r : Thm83Repr actX N) :
    Space.IsFinitePresentation B S hS (terminal.from r.P) := by
  refine ⟨thm83_iv hX hfp.1 r, ?_, ?_⟩
  · exact isQuasiCompact_terminal_of_presheaf (P := @AlgebraicGeometry.IsAffineHom)
      (fun g _ => inferInstance) inferInstance r.affine_c
      (isQuasiCompact_terminal_of_presheaf (P := @IsClosedImmersion)
        (fun g _ => inferInstance) inferInstance r.closed_i hfp.2.1)
  · have hs := thm83_sep hX hsep r
    rw [terminal_from_eq]
    exact Space.isQuasiSeparated_of_isSeparated B S hS
      (Space.isSeparated_comp B S hS _ _ hs (Space.isSeparated_of_isIso B S hS _))

/-- **Theorem 8.3** with its assumption (a): `X` separated (and `X/S` locally of finite presentation in
the case of an arbitrary magnet, by Tag 049J). -/
theorem thm83_of_lfp (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) (N : AddSubmonoid M)
    (hat : ExistsZFPRAtlas actX (unitsSub N)) :
    ∃ r : Thm83Repr actX N,
      Space.IsQuasiSeparated B S hS (toBase r.P) ∧ IsSeparatedOver r.P ∧
      (Space.IsQuasiCompactSpace B S hS X → Space.IsQuasiCompactSpace B S hS r.P) ∧
      Space.IsLocallyOfFinitePresentation B S hS (terminal.from r.P) := by
  obtain ⟨r, h1, h2, h3⟩ := thm83 hX hsep N hat (Or.inr (isLimitPreserving_of_lfp hX hfp))
  exact ⟨r, h1, h2, h3, thm83_iv hX hfp r⟩

/-- **Proposition 3.37**, unconditional form (`T` affine, `M` finitely generated): `X` separated, locally
of finite presentation. -/
theorem prop337 (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) {N P₀ : AddSubmonoid M}
    (h₀ : P₀ ≤ N) (hP₀ : P₀.FG) {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    (φ : AttractorPt actX N T) :
    ∃ (P : AddSubmonoid M) (hP : P ≤ N) (φ' : AttractorPt actX P T), P₀ ≤ P ∧ P.FG ∧
      AttractorPt.ofLE hP φ' = φ :=
  exists_ofLE_eq hsep (isLimitPreserving_of_lfp hX hfp) h₀ hP₀ φ

/-- **Proposition 5.1 (ii)**, unconditional form: `X` separated, locally of finite presentation. -/
theorem prop51_ii (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom] {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
    (f : EquivariantHom aU actX) (hf : Space.IsEtale B S hS f.hom)
    {Q N : AddSubmonoid M} (hQ : IsFace Q N) : IsFaceCartesian f hQ :=
  isFaceCartesian_of_separated hX hsep (isLimitPreserving_of_lfp hX hfp) f hf hQ

end Thm

end AlgMag

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism
open scoped Classical

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] GB.gradedAlgebraOf

section P85

attribute [local instance] countable_of_fg83

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {A' : Type u} {V : A' → ((BigFppfOver.toScheme B S hS).obj U).Opens}

/-- **The descent step** in the proof of **Proposition 8.5**: the morphism `X^{N'} → X^{N''}` is
an isomorphism if `U^{N'} → U^{N''}` is, for `U → X` a `Z`-FPR atlas (`Z` a common face). The printed proof
applies Tag 03I2 to the property "isomorphism"; here the statement is unfolded on `T`-points. -/
theorem exists_ofLE_of_chart (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (g : yoneda.obj U ⟶ X) {Z : AddSubgroup M} (hg : IsZFPRAtlas actU actX g Z)
    (hV : IsAffineDecomposition actU V) {N' N'' : AddSubmonoid M} (h : N' ≤ N'')
    (hF : IsFace Z.toAddSubmonoid N'')
    (hl : IsLimitPreserving X)
    (hstep : ∀ {T : BigFppfOver B S hS} (φ : AttractorPt actU N'' T),
      ∃ φ' : AttractorPt actU N' T, φ'.toPoint = φ.toPoint)
    {T : BigFppfOver B S hS} (ψ : AttractorPt actX N'' T) :
    ∃ ξ : AttractorPt actX N' T, AttractorPt.ofLE h ξ = ψ := by
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hshU : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj U) :=
    BigFppfOver.isSheaf_of_type_yoneda_obj U
  have hcov : ∀ {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)),
      extSieve (fppfO B S hS) Z a ∈ BigFppfOver.topology B S hS T := fun a => extSieve_mem Z a
  let f : EquivariantHom actU actX := ⟨g, fun {T} h x => hg.atlas.equivariant h x⟩
  -- the cartesian squares of Proposition 5.1
  have hc : IsFaceCartesian f hF := by
    refine isFaceCartesian_of_pieces hsh hV f _ fun b => ?_
    have hA : IsAffineHom (openObj (V b)).hom.hom := hV.isAffineHom b
    exact isFaceCartesian_of_separated hX hsep hl _ (isEtale_piece_comp hg.atlas.etale) _
  -- the étale surjective cover of `T`
  let x₀ := (AttractorPt.ofFace hF ψ).toPoint
  let gx : yoneda.obj T ⟶ X := yonedaEquiv.symm x₀
  let R := hg.atlas.etale.rep
  let W := R.pullback gx
  let q : W ⟶ T := R.snd gx
  have hpb := R.isPullback gx
  have hqe : Etale ((SCH).map q) := hg.atlas.etale.property_snd gx
  have hqs : Surjective ((SCH).map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).1
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb hg.atlas.surjective)
  have hmem := Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS q hqs
    (inferInstanceAs (Flat ((SCH).map q))) (inferInstanceAs (LocallyOfFinitePresentation ((SCH).map q)))
  let y : W ⟶ U := (R.fst gx).app (op W) (𝟙 W)
  have hy : g.app (op W) y = X.map q.op x₀ := by
    have := congrArg (fun k => k.app (op W) (𝟙 W)) hpb.w
    simpa [gx, yonedaEquiv] using this
  -- the point of `U^{N^×}`
  let eU := attractorFixedEquivOfCover (act := actU) hshU hcov W
  let eX := attractorFixedEquivOfCover (act := actX) hsh hcov W
  let ψW := ψ.baseChange q
  have hψW : (AttractorPt.ofFace hF ψW).toPoint = X.map q.op x₀ := by
    change (AttractorPt.ofFace hF (AttractorPt.baseChange q ψ)).toPoint = _
    rw [ofFace_baseChange]
    exact AttractorPt.toPoint_baseChange q _
  have hfix : y ∈ (fixedPoints (quotientAction actU Z)).obj (op W) := by
    refine (isFPR_iff (IsEquivariant.comap (actU := actU) (actX := actX) (f := g) hg.atlas.equivariant (QuotientAddGroup.mk' Z))).1 hg.isZFPR (op W) y ?_
    rw [hy, ← hψW]
    exact AttractorPt.toPoint_mem_fixedPoints _
  let w := eU ⟨y, hfix⟩
  have hw : w.toPoint = y := congrArg Subtype.val (eU.symm_apply_apply ⟨y, hfix⟩)
  have hfc : AttractorPt.ofFace hF ψW = AttractorPt.push f w := by
    apply eX.symm.injective
    refine Subtype.ext ?_
    change (AttractorPt.ofFace hF ψW).toPoint = g.app (op W) w.toPoint
    rw [hψW, hw, hy]
  obtain ⟨u, hu⟩ := (hc W).2 ⟨(ψW, w), hfc⟩
  have hu₁ : AttractorPt.push f u = ψW := congrArg (fun p => p.1.1) hu
  obtain ⟨u', hu'⟩ := hstep u
  have hle : AttractorPt.ofLE h u' = u := toPoint_injective_U hV ((AttractorPt.toPoint_ofLE h u').trans hu')
  let ξW := AttractorPt.push f u'
  have hξW : AttractorPt.ofLE h ξW = ψW := by
    refine Eq.trans ?_ hu₁
    rw [← hle]
    exact rfl
  have hshN' := isSheaf_attractor actX N' _ hsh
  have hshN'' := isSheaf_attractor actX N'' _ hsh
  have hsf : (Presieve.ofArrows (fun _ : PUnit.{1} => W) (fun _ => q)).IsSheafFor (attractor actX N') := by
    rw [Presieve.ofArrows_pUnit, Presieve.isSheafFor_iff_generate]
    exact hshN' _ hmem
  obtain ⟨ξ, hξ', -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf (fun _ => ξW) (by
    intro _ _ Y g₁ g₂ e
    apply ofLE_injective hX hsep h Y
    change AttractorPt.baseChange g₁ (AttractorPt.ofLE h ξW) = AttractorPt.baseChange g₂ (AttractorPt.ofLE h ξW)
    rw [hξW]
    change AttractorPt.baseChange (g₁ ≫ q) ψ = AttractorPt.baseChange (g₂ ≫ q) ψ
    rw [e])
  have hξ := hξ' PUnit.unit
  refine ⟨ξ, ?_⟩
  refine (hshN'' _ hmem).isSeparatedFor.ext fun Y p hp => ?_
  obtain ⟨Y', r, s', ⟨⟩, rfl⟩ := hp
  have e : AttractorPt.baseChange q (AttractorPt.ofLE h ξ) = AttractorPt.baseChange q ψ := by
    have : AttractorPt.baseChange q ξ = ξW := hξ
    refine Eq.trans ?_ hξW
    rw [← this]
    rfl
  exact congrArg (AttractorPt.baseChange r) e

omit [AddGroup.FG M] in
/-- `U → S` is locally of finite presentation if `U → X` is étale and `X/S` is. -/
lemma lfp_structMap (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (g : yoneda.obj U ⟶ X)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g) :
    LocallyOfFinitePresentation (structMap U) := by
  let top : BigFppfOver B S hS := siteTop
  let b : yoneda.obj top ⟶ ⊤_ _ := terminal.from _
  have hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) b := by
    have h1 : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map (𝟙 top)) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (𝟙 top)).2 (by
        rw [(SCH).map_id]; infer_instance)
    have hsq : IsPullback (𝟙 _) b (yoneda.map (𝟙 top)) (inv b) :=
      IsPullback.of_vert_isIso ⟨by
        rw [CategoryTheory.Functor.map_id, Category.comp_id, IsIso.hom_inv_id]⟩
    exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq h1
  let h : U ⟶ top := Over.mkIdTerminal.from U
  have := hfp U top g b h he hb (Subsingleton.elim _ _)
  have e : (SCH).map h = structMap U := by
    have := congrArg (fun k => k.hom) (Over.w h)
    simpa [top, siteTop] using this
  rwa [e] at this

omit [AddGroup.FG M] in
lemma finiteType_chart (hfp : LocallyOfFinitePresentation (structMap U))
    (W : ((SCH).obj U).Opens) (hA : IsAffineHom (openOver W).hom) {U₀ : S.Opens}
    (hU₀ : IsAffineOpen U₀) : Algebra.FiniteType Γ(S, U₀) (GB.Aalg (openOver W) U₀) := by
  have h1 : LocallyOfFinitePresentation (openOver W).hom := by
    change LocallyOfFinitePresentation (iV W ≫ structMap U)
    infer_instance
  exact Scheme.Hom.finiteType_appLE (openOver W).hom hU₀ (GB.isAffineOpen_preimage (openOver W) hU₀) le_rfl

set_option maxHeartbeats 2000000 in
/-- The finite set of degrees, for `S` quasi-compact: this is the only place where quasi-compactness of `S`
is used. It cannot be avoided: for `S = ⊔ Spec k` over `k ∈ ℕ` and `X = ⊔ 𝔸¹_{S_k}` with coordinate of degree
`m_k`, where the `m_k` enumerate a magnet `N` that is not finitely generated, no `N_c` exists. -/
theorem exists_finset_degrees [CompactSpace S] (hfp : LocallyOfFinitePresentation (structMap U))
    [Finite A'] (hV : IsAffineDecomposition actU V) :
    ∃ (κ : Type u) (Uk : κ → S.affineOpens) (D : Finset M), (∀ s : S, ∃ k, s ∈ (Uk k).1) ∧
      ∀ N' N'' : AddSubmonoid M, (∀ d ∈ D, d ∈ N'' → d ∈ N') →
      ∀ b k, haveI : IsAffineHom (openOver (V b)).hom := hV.isAffineHom b
        magnetIdeal (GB.gradingOf (Uk k).2 (overAct (hM_of hS M) (hV.stable b))) N' ≤
          magnetIdeal (GB.gradingOf (Uk k).2 (overAct (hM_of hS M) (hV.stable b))) N'' := by
  obtain ⟨t, ht⟩ := (isCompact_univ (X := S)).elim_finite_subcover
    (fun W : S.affineOpens => (W.1 : Set S)) (fun W => W.1.2) (fun s _ => by
      obtain ⟨_, ⟨W, hW, rfl⟩, hs, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ s) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hs⟩)
  let κ : Type u := t
  let Uk : κ → S.affineOpens := fun k => k.1
  have hdeg : ∀ (b : A') (k : κ), ∃ D : Finset M, ∀ N' N'' : AddSubmonoid M, (∀ d ∈ D, d ∈ N'' → d ∈ N') →
      haveI : IsAffineHom (openOver (V b)).hom := hV.isAffineHom b
      magnetIdeal (GB.gradingOf (Uk k).2 (overAct (hM_of hS M) (hV.stable b))) N' ≤
        magnetIdeal (GB.gradingOf (Uk k).2 (overAct (hM_of hS M) (hV.stable b))) N'' := by
    intro b k
    have hA : IsAffineHom (openOver (V b)).hom := hV.isAffineHom b
    have hft := finiteType_chart hfp (V b) hA (Uk k).2
    exact @exists_degrees Γ(S, (Uk k).1) (GB.Aalg (openOver (V b)) (Uk k).1) M _ _ _ _
      (GB.rho (Uk k).2 (overAct (hM_of hS M) (hV.stable b)))
      (GB.gradedAlgebraOf (Uk k).2 (overAct (hM_of hS M) (hV.stable b))) hft
  choose D hD using hdeg
  have : Fintype A' := Fintype.ofFinite A'
  refine ⟨κ, Uk, Finset.univ.biUnion fun b => Finset.univ.biUnion fun k => D b k, fun s => ?_, ?_⟩
  · obtain ⟨W, hW, hs⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ s))
    exact ⟨⟨W, hW⟩, hs⟩
  · intro N' N'' h b k
    exact hD b k N' N'' fun d hd => h d (Finset.mem_biUnion.2 ⟨b, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hd⟩⟩)

end P85

end AlgMag

end

section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism
open scoped Classical

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Chain

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]

lemma fg_unitsSub (N : AddSubmonoid M) : (unitsSub N).toAddSubmonoid.FG := by
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hn : IsNoetherian ℤ M := inferInstance
  have h1 : (AddSubgroup.toIntSubmodule (unitsSub N)).FG := hn.noetherian _
  have h2 : (unitsSub N).FG := (Submodule.fg_iff_addSubgroup_fg _).1 h1
  exact (AddSubgroup.fg_iff_addSubmonoid_fg _).1 h2

/-- The chain of the proof of **Proposition 8.5**: `N_i` is generated by `N^×` and the first elements of
an enumeration of `N`. -/
irreducible_def chainN337 (N : AddSubmonoid M) (ν : ℕ → N) (i : ℕ) : AddSubmonoid M :=
  (unitsSub N).toAddSubmonoid ⊔ AddSubmonoid.closure ((fun j => (ν j : M)) '' Set.Iic i)

lemma chainN337_le (N : AddSubmonoid M) (ν : ℕ → N) (i : ℕ) : chainN337 N ν i ≤ N := by
  rw [chainN337_def]
  exact sup_le (isFace_unitsSub N).le ((AddSubmonoid.closure_le).2 (by
    rintro _ ⟨j, -, rfl⟩
    exact (ν j).2))

lemma chainN337_mono (N : AddSubmonoid M) (ν : ℕ → N) {i j : ℕ} (h : i ≤ j) : chainN337 N ν i ≤ chainN337 N ν j := by
  rw [chainN337_def, chainN337_def]
  exact sup_le_sup_left (AddSubmonoid.closure_mono (Set.image_mono (Set.Iic_subset_Iic.2 h))) _

lemma chainN337_fg (N : AddSubmonoid M) (ν : ℕ → N) (i : ℕ) : (chainN337 N ν i).FG := by
  rw [chainN337_def]
  exact (fg_unitsSub N).sup ⟨((Set.finite_Iic i).image (fun j => (ν j : M))).toFinset, by rw [Set.Finite.coe_toFinset]⟩

/-- The units of a magnet between `N^×` and `N` are `N^×`. -/
lemma unitsSub_of_between {N L : AddSubmonoid M} (h₁ : (unitsSub N).toAddSubmonoid ≤ L) (h₂ : L ≤ N) :
    unitsSub L = unitsSub N := by
  ext x
  exact ⟨fun hx => ⟨h₂ hx.1, h₂ hx.2⟩, fun hx => ⟨h₁ hx, h₁ ((unitsSub N).neg_mem hx)⟩⟩

lemma isFace_between {N L : AddSubmonoid M} (h₁ : (unitsSub N).toAddSubmonoid ≤ L) (h₂ : L ≤ N) :
    IsFace (unitsSub N).toAddSubmonoid L := by
  have := isFace_unitsSub L
  rwa [unitsSub_of_between h₁ h₂] at this

lemma exists_index (N : AddSubmonoid M) (ν : ℕ → N) (hν : Function.Surjective ν) (F : Finset M) :
    ∃ c, ∀ d ∈ F, d ∈ N → d ∈ chainN337 N ν c := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a F _ ih =>
    obtain ⟨c, hc⟩ := ih
    by_cases ha : a ∈ N
    · obtain ⟨j, hj⟩ := hν ⟨a, ha⟩
      refine ⟨max c j, fun d hd hdN => ?_⟩
      rcases Finset.mem_insert.1 hd with rfl | hd
      · rw [chainN337_def]
        refine SetLike.le_def.1 le_sup_right (AddSubmonoid.subset_closure ⟨j, Set.mem_Iic.2 (le_max_right _ _), ?_⟩)
        exact congrArg Subtype.val hj
      · exact chainN337_mono N ν (le_max_left _ _) (hc d hd hdN)
    · refine ⟨c, fun d hd hdN => ?_⟩
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact absurd hdN ha
      · exact hc d hd hdN

/-- A finitely generated `P ≤ N` lies in a member of the chain. -/
lemma exists_le_chain (N : AddSubmonoid M) (ν : ℕ → N) (hν : Function.Surjective ν) {P : AddSubmonoid M}
    (hP : P ≤ N) (hf : P.FG) : ∃ i, P ≤ chainN337 N ν i := by
  obtain ⟨F, rfl⟩ := hf
  obtain ⟨i, hi⟩ := exists_index N ν hν F
  exact ⟨i, (AddSubmonoid.closure_le).2 fun d hd => hi d hd (hP (AddSubmonoid.subset_closure hd))⟩

end Chain

section Main

attribute [local instance] countable_of_fg83

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}

/-- **Proposition 8.5.** Let `M` be a finitely generated abelian group, `N ⊆ M` a magnet, `X` an algebraic
space separated and locally of finite presentation over a quasi-compact scheme `S`, with an action of
`D(M)_S` and an `S`-affine `N^×`-FPR atlas. Then there is a finitely generated submonoid `N_c ⊆ N` with
`N_c^× = N^×` and `X^{N_c} = X^N` (the map `X^{N_c} → X^N` is bijective on points). -/
theorem prop85 [CompactSpace S] (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) (N : AddSubmonoid M)
    (hat : ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (g : yoneda.obj U ⟶ X), IsZFPRAtlas actU actX g (unitsSub N) ∧
        HasFiniteAffineDecomposition actU) :
    ∃ (Nc : AddSubmonoid M) (hc : Nc ≤ N), Nc.FG ∧ unitsSub Nc = unitsSub N ∧
      ∀ T : BigFppfOver B S hS, Function.Bijective (AttractorPt.ofLE (act := actX) (T := T) hc) := by
  obtain ⟨U, actU, g, hg, A', hA', V, hV⟩ := hat
  have hl := isLimitPreserving_of_lfp hX hfp
  have hU := lfp_structMap hfp g hg.atlas.etale
  obtain ⟨κ, Uk, D, hUk, hD⟩ := exists_finset_degrees hU hV
  obtain ⟨ν, hν⟩ := exists_surjective_nat N
  obtain ⟨c, hc⟩ := exists_index N ν hν D
  have hle := chainN337_le N ν c
  have hZ : ∀ i, (unitsSub N).toAddSubmonoid ≤ chainN337 N ν i := fun i => by
    rw [chainN337_def]; exact le_sup_left
  -- `U^{N_c} = U^{N_i}`, then `X^{N_c} = X^{N_i}`, for `i ≥ c`
  have hstep : ∀ {i} (hi : c ≤ i) {T : BigFppfOver B S hS} (ψ : AttractorPt actX (chainN337 N ν i) T),
      ∃ ξ : AttractorPt actX (chainN337 N ν c) T, AttractorPt.ofLE (chainN337_mono N ν hi) ξ = ψ := by
    intro i hi T ψ
    refine exists_ofLE_of_chart hX hsep g hg hV (chainN337_mono N ν hi)
      (isFace_between (hZ i) (chainN337_le N ν i)) hl (fun φ => ?_) ψ
    exact exists_att_of_ideal_le hV Uk hUk
      (hD _ _ fun d hd hdi => hc d hd (chainN337_le N ν i hdi)) φ
  have hshc := isSheaf_attractor actX (chainN337 N ν c) _ ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
  have hshN := isSheaf_attractor actX N _ ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
  refine ⟨chainN337 N ν c, hle, chainN337_fg N ν c, unitsSub_of_between (hZ c) hle, fun T => ?_⟩
  refine ⟨ofLE_injective hX hsep hle T, fun ψ => ?_⟩
  -- `X^N = colim X^{N_i}` by Proposition 3.37
  obtain ⟨I, W, π, hW, hmem⟩ := exists_affine_cover T
  have hloc : ∀ j, ∃ ξ : AttractorPt actX (chainN337 N ν c) (W j),
      AttractorPt.ofLE hle ξ = AttractorPt.baseChange (π j) ψ := by
    intro j
    haveI : IsAffine ((SCH).obj (W j)) := hW j
    obtain ⟨P, hP, φ', hP₀, hPf, hφ'⟩ := prop337 hX hsep hfp hle (chainN337_fg N ν c)
      (AttractorPt.baseChange (π j) ψ)
    obtain ⟨i₀, hi₀⟩ := exists_le_chain N ν hν hP hPf
    let i := max c i₀
    have hPi : P ≤ chainN337 N ν i := hi₀.trans (chainN337_mono N ν (le_max_right _ _))
    obtain ⟨ξ, hξ⟩ := hstep (le_max_left c i₀) (AttractorPt.ofLE hPi φ')
    refine ⟨ξ, ?_⟩
    rw [← hφ']
    have := congrArg (AttractorPt.ofLE (chainN337_le N ν i)) hξ
    exact this
  choose ξ hξ using hloc
  have hsf : (Presieve.ofArrows W π).IsSheafFor (attractor actX (chainN337 N ν c)) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hshc _ hmem
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf ξ (by
    intro a b Y ga gb e
    apply ofLE_injective hX hsep hle Y
    change AttractorPt.baseChange ga (AttractorPt.ofLE hle (ξ a)) =
      AttractorPt.baseChange gb (AttractorPt.ofLE hle (ξ b))
    rw [hξ, hξ]
    change AttractorPt.baseChange (ga ≫ π a) ψ = AttractorPt.baseChange (gb ≫ π b) ψ
    rw [e])
  refine ⟨t, (hshN _ hmem).isSeparatedFor.ext fun Y p hp => ?_⟩
  obtain ⟨_, r, s', ⟨j⟩, rfl⟩ := hp
  have e : AttractorPt.baseChange (π j) (AttractorPt.ofLE hle t) = AttractorPt.baseChange (π j) ψ :=
    (congrArg (AttractorPt.ofLE hle) (ht j)).trans (hξ j)
  exact congrArg (AttractorPt.baseChange r) e

end Main

end AlgMag

end

#print axioms AlgMag.isLimitPreserving_of_limitPreserving
#print axioms AlgMag.isLimitPreserving_of_lfp
#print axioms AlgMag.limitPreserving_of_represents
#print axioms AlgMag.thm83_iv
#print axioms AlgMag.thm83_vi
#print axioms AlgMag.thm83_of_lfp
#print axioms AlgMag.prop337
#print axioms AlgMag.prop51_ii
#print axioms AlgMag.exists_degrees
#print axioms AlgMag.exists_att_of_ideal_le
#print axioms AlgMag.exists_ofLE_of_chart
#print axioms AlgMag.exists_finset_degrees
#print axioms AlgMag.prop85
