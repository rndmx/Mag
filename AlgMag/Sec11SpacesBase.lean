/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11Spaces
import AlgMag.Sec11Schemes
import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSections

/-!
# Spectra in the big fppf site, and Milnor gluing of sections of an algebraic space

Infrastructure for the proof of Corollary 10.3 for algebraic spaces (`AlgMag.Sec11SpacesCore`).
`SR B R` says that `Spec R` is an object of the site, `SM B M` that `#M` is below the cutoff of the
site. Both are size conditions: they are stable under `R ↦ R[M]` and under subrings of products.
`glue` is Stacks 07SY for a Milnor square, on sections of an algebraic space.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB

/-- `Spec R` belongs to the site. -/
class SR (B : BigFppfSite.{u}) (R : Type u) [CommRing R] : Prop where
  contains : B.Contains (Spec (CommRingCat.of R))

/-- The cardinal of `M` is below the cutoff of the site. -/
class SM (B : BigFppfSite.{u}) (M : Type u) : Prop where
  lt : #M < B.cutoff

variable {B : BigFppfSite.{u}}

lemma sr_iff {R : Type u} [CommRing R] : SR B R ↔ #R < B.cutoff := by
  have e : #(Γ(Spec (CommRingCat.of R), ⊤)) = #R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.cardinal_eq
  constructor
  · intro h
    have h₁ := h.contains
    rw [BigFppfSite.Contains, Scheme.size_of_isAffine, e] at h₁
    exact (le_max_right _ _).trans_lt h₁
  · intro h
    refine ⟨?_⟩
    rw [BigFppfSite.Contains, Scheme.size_of_isAffine, e]
    exact max_lt B.aleph0_lt_cutoff h

lemma mk_finsupp_lt {M R : Type u} [Zero R] (hM : #M < B.cutoff) (hR : #R < B.cutoff) :
    #(M →₀ R) < B.cutoff := by
  have ha := B.aleph0_lt_cutoff
  have h₁ : #(M →₀ R) ≤ #(Finset (M × R)) := by
    classical
    exact mk_le_of_injective (Finsupp.graph_injective M R)
  refine h₁.trans_lt ?_
  by_cases hf : Finite (M × R)
  · have : Finite (Finset (M × R)) := inferInstance
    exact (lt_aleph0_of_finite _).trans ha
  · have : Infinite (M × R) := not_finite_iff_infinite.1 hf
    rw [mk_finset_of_infinite, mk_prod, lift_id, lift_id]
    exact mul_lt_of_lt ha.le hM hR

instance srMonoidAlgebra {R M : Type u} [CommRing R] [AddCommMonoid M] [SR B R] [SM B M] :
    SR B (AddMonoidAlgebra R M) := by
  refine sr_iff.2 ?_
  have e : #(AddMonoidAlgebra R M) ≤ #(M →₀ R) :=
    mk_le_of_injective (f := fun x : AddMonoidAlgebra R M => x.coeff) (fun x y h => by
      ext m
      exact DFunLike.congr_fun h m)
  exact e.trans_lt (mk_finsupp_lt SM.lt (sr_iff.1 inferInstance))

instance smSubmonoid {M : Type u} [AddCommMonoid M] [SM B M] (N : AddSubmonoid M) : SM B N :=
  ⟨(mk_subtype_le _).trans_lt (SM.lt (B := B) (M := M))⟩

/-- A subring of a product of rings in the site is in the site. -/
lemma sr_subring {A C : Type u} [CommRing A] [CommRing C] [SR B A] [SR B C] (R : Subring (A × C)) :
    SR B R := by
  refine sr_iff.2 ((mk_subtype_le _).trans_lt ?_)
  rw [mk_prod, lift_id, lift_id]
  exact mul_lt_of_lt B.aleph0_lt_cutoff.le (sr_iff.1 inferInstance) (sr_iff.1 inferInstance)

variable {S : Scheme.{u}} (B) (hS : B.Contains S)

/-- `Spec R` as an object of the site over `S`, with structure morphism `s`. -/
noncomputable abbrev Sv {R : Type u} [CommRing R] [SR B R] (s : Spec (CommRingCat.of R) ⟶ S) :
    BigFppfOver B S hS :=
  siteObject B S hS (SR.contains (B := B) (R := R)) s

/-- `Spec` of a ring map, in the site over `S`. -/
noncomputable def svHom {R R₁ : Type u} [CommRing R] [CommRing R₁] [SR B R] [SR B R₁] (g : R →+* R₁)
    {s : Spec (CommRingCat.of R) ⟶ S} {s₁ : Spec (CommRingCat.of R₁) ⟶ S} (h : sp g ≫ s = s₁) :
    Sv B hS s₁ ⟶ Sv B hS s :=
  Over.homMk (ObjectProperty.homMk (sp g)) (ObjectProperty.hom_ext _ h)

variable {B hS}

lemma site_ext {X Y : BigFppfOver B S hS} {x y : X ⟶ Y}
    (h : (BigFppfOver.toScheme B S hS).map x = (BigFppfOver.toScheme B S hS).map y) : x = y :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ h)

/-- Pull-back of a section. -/
abbrev pb (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {T T₁ : BigFppfOver B S hS} (u : T₁ ⟶ T)
    (x : P.obj (op T)) : P.obj (op T₁) := P.map u.op x

lemma pb_comp (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {T T₁ T₂ : BigFppfOver B S hS}
    (v : T₂ ⟶ T₁) (u : T₁ ⟶ T) (x : P.obj (op T)) : pb P (v ≫ u) x = pb P v (pb P u x) := by
  simp [pb]

lemma pb_id (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {T : BigFppfOver B S hS} (x : P.obj (op T)) :
    pb P (𝟙 T) x = x := by
  simp [pb]

lemma pb_sq (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {W R Q T : BigFppfOver B S hS}
    {u : W ⟶ Q} {v : Q ⟶ T} {w : W ⟶ R} {x : R ⟶ T} (h : u ≫ v = w ≫ x) (z : P.obj (op T)) :
    pb P u (pb P v z) = pb P w (pb P x z) := by
  rw [← pb_comp, h, pb_comp]

lemma isPushout_of_milnor {R' A C D : Type u} [CommRing R'] [CommRing A] [CommRing C] [CommRing D]
    {p : R' →+* A} {q : R' →+* C} {i : A →+* D} {j : C →+* D} (H : MilnorData p q i j)
    (hqs : Function.Surjective q) (hker : ∀ y, i y = 0 → ∃ z, p z = y ∧ q z = 0) :
    IsPushout (sp i) (sp j) (sp p) (sp q) := by
  have hc : sp i ≫ sp p = sp j ≫ sp q :=
    AlgMag.Lifts.sp_sq (RingHom.ext fun z => H.comm z)
  refine ⟨⟨hc⟩, ⟨PushoutCocone.isColimitAux' _ fun s => ?_⟩⟩
  have E := AlgMag.Lifts.milnor_desc H hqs hker s.inl s.inr s.condition
  exact ⟨E.choose, E.choose_spec.1.1, E.choose_spec.1.2, fun {m} h₁ h₂ =>
    E.choose_spec.2 m ⟨h₁, h₂⟩⟩

/-- **Stacks 07SY for a Milnor square**, on sections of an algebraic space. The square
`Spec D → Spec A`, `Spec D → Spec C`, with `Spec D → Spec A` a first order thickening, is a push-out
in schemes, and sections of an algebraic space glue over it uniquely. -/
theorem glue {R' A C D : Type u} [CommRing R'] [CommRing A] [CommRing C] [CommRing D] [SR B R']
    [SR B A] [SR B C] [SR B D]
    {p : R' →+* A} {q : R' →+* C} {i : A →+* D} {j : C →+* D} (H : MilnorData p q i j)
    (hqs : Function.Surjective q) (hker : ∀ y, i y = 0 → ∃ z, p z = y ∧ q z = 0)
    (hiq : ∀ x y, i x = 0 → i y = 0 → x * y = 0)
    {s : Spec (CommRingCat.of R') ⟶ S} {sA : Spec (CommRingCat.of A) ⟶ S}
    {sC : Spec (CommRingCat.of C) ⟶ S} {sD : Spec (CommRingCat.of D) ⟶ S}
    (hp : sp p ≫ s = sA) (hq : sp q ≫ s = sC) (hi : sp i ≫ sA = sD) (hj : sp j ≫ sC = sD)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (f : P.obj (op (Sv B hS sA))) (g : P.obj (op (Sv B hS sC)))
    (h : pb P (svHom B hS i hi) f = pb P (svHom B hS j hj) g) :
    ∃! k : P.obj (op (Sv B hS s)), pb P (svHom B hS p hp) k = f ∧ pb P (svHom B hS q hq) k = g := by
  have hth : Stacks.Thickenings.IsFirstOrderThickening (Spec.map (CommRingCat.ofHom i)) :=
    Stacks.Smooth.isFirstOrderThickening_specMap _ H.surj (by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro x hx z hz
      exact hiq x z hx hz)
  have hth₂ : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (svHom B hS i hi)) :=
    Stacks.Thickenings.isThickening_of_ker_pow_eq_bot _ hth.1 (n := 1) hth.2
  haveI : IsAffineHom ((BigFppfOver.toScheme B S hS).map (svHom B hS j hj)) :=
    inferInstanceAs (IsAffineHom (sp j))
  exact Space.existsUnique_section_of_isThickening_of_isAffineHom B S hS
    (svHom B hS i hi) (svHom B hS j hj) (svHom B hS p hp) (svHom B hS q hq) hth₂
    (isPushout_of_milnor H hqs hker) P hP f g h

end AlgMag.SpacesLift
