/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.AppendixRemaining
import AlgMag.Sec8Representability
import AlgMag.Sec15General
import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth

/-!
# Appendix A (by M. Romagny): Lemma A.3 for spaces and the route through `F_n`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, Appendix A, for `G = D(M)`.

`F_n ⊆ D(M)` is the closed subscheme `V(J_n)`, `J_n = ((X^e - 1)^n, e ∈ E)` of `AppR.lemmaA5`.

Main results, for `D(M)` with connected fibres (`TorsionResidue`):

* `lemmaA3`: **Lemma A.3** for `F_n` acting on an algebraic space, via `exists_lift_nil` (lifting of
  étale sections along nil-thickenings) and `exists_ideal_chart` (closedness of the stabilizer).
* `presheaf_fnAll_ι`: `X_0 = ⋂ X^{F_n}` is closed.
* `mem_fixedPoints_of_fnAll`: `X_0 = X^G` in case (i) of **Theorem A.1**.
* `thmA1_closed`, `thmA1_isFPR`: **Theorem A.1**, case (i), by the printed route through `F_n`.

Case (ii) of Theorem A.1 needs the reduction to noetherian bases by limits and is not treated here.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.AppA3

open AddMonoidAlgebra AppR

section Ring

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]

/-- The evaluation `R[M] → R` at a point `h` of `D(M)`. -/
noncomputable def evPt (h : Multiplicative M →* R) : AddMonoidAlgebra R M →+* R :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id R) h (fun _ _ => mul_comm _ _)

@[simp] lemma evPt_single (h : Multiplicative M →* R) (m : M) (r : R) :
    evPt h (single m r) = r * h (Multiplicative.ofAdd m) := by
  change AddMonoidAlgebra.liftNC _ _ _ = _
  rw [AddMonoidAlgebra.liftNC_single]
  rfl

lemma evPt_one_sub (h : Multiplicative M →* R) (m : M) :
    evPt h (single m 1 - 1) = h (Multiplicative.ofAdd m) - 1 := by
  rw [map_sub, map_one, evPt_single, one_mul]

/-- The point `h` of `D(M)` lies on `F_n = V(J_n)`. -/
def IsFnPt (E : Set M) (n : ℕ) (h : Multiplicative M →* R) : Prop :=
  ∀ e ∈ E, (h (Multiplicative.ofAdd e) - 1) ^ n = 0

lemma evPt_Jn {E : Set M} {n : ℕ} {h : Multiplicative M →* R} (hh : IsFnPt E n h) :
    Jn R E n ≤ RingHom.ker (evPt h) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨e, he, rfl⟩
  change evPt h _ = 0
  rw [map_pow, evPt_one_sub]
  exact hh e he

/-- A point of `F_n` is infinitesimally close to the unit section. -/
lemma isNilpotent_of_isFnPt {E : Set M} {n k : ℕ} (hk : augI R M ^ k ≤ Jn R E n)
    {h : Multiplicative M →* R} (hh : IsFnPt E n h) (m : M) :
    (h (Multiplicative.ofAdd m) - 1) ^ k = 0 := by
  have : (single m 1 - 1 : AddMonoidAlgebra R M) ^ k ∈ Jn R E n :=
    hk (Ideal.pow_mem_pow (show single m 1 - 1 ∈ augI R M from Ideal.subset_span ⟨m, rfl⟩) k)
  have := evPt_Jn hh this
  rwa [RingHom.mem_ker, map_pow, evPt_one_sub] at this

lemma eq_one_of_pow_sub_one (hR : IsField R) {a : R} {k : ℕ} (h : (a - 1) ^ k = 0) : a = 1 := by
  let := hR.toField
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero] at h
    exact absurd h one_ne_zero
  · exact sub_eq_zero.1 ((pow_eq_zero_iff hk.ne').1 h)

/-- The ideal `J = im(I ⊗ A^∨ → O_X)` of the printed proof of **Lemma A.3**, for a set `W` of
functions on `D(N)` generating `I`. -/
def fixedJOf {A N : Type*} [CommRing A] [AddCommGroup N] (W : Set (AddMonoidAlgebra A N))
    (E : Set N) (n : ℕ) : Ideal A :=
  Ideal.span {c | ∃ (φ : (AddMonoidAlgebra A N ⧸ Jn A E n) →ₗ[A] A) (w : AddMonoidAlgebra A N),
    w ∈ W ∧ c = φ (Ideal.Quotient.mk _ w)}

/-- The computation in the printed proof of **Lemma A.3**: `I → A → O_X` vanishes after base change
along `u` iff `J ⊆ ker u`, the formation of the dual of `A` commuting with base change. -/
theorem baseR_mem_Jn_iff {A R' N : Type*} [CommRing A] [CommRing R'] [AddCommGroup N]
    (W : Set (AddMonoidAlgebra A N)) (E : Set N) (n : ℕ)
    (hF : Module.Free A (AddMonoidAlgebra A N ⧸ Jn A E n))
    (hf : Module.Finite A (AddMonoidAlgebra A N ⧸ Jn A E n)) (u : A →+* R') :
    (∀ w ∈ W, baseR u w ∈ Jn R' E n) ↔ fixedJOf W E n ≤ RingHom.ker u := by
  classical
  constructor
  · intro h
    refine Ideal.span_le.2 ?_
    rintro _ ⟨φ, w, hw, rfl⟩
    have h0 := formBase_eq_zero u φ (h w hw)
    have h1 := formBase_baseR u φ 0 1 w
    rw [AddMonoidAlgebra.one_def.symm, one_mul, one_mul, ← AddMonoidAlgebra.one_def, one_mul] at h1
    rw [h0] at h1
    exact h1.symm
  · intro h w hw
    let C := AddMonoidAlgebra A N ⧸ Jn A E n
    let b := Module.Free.chooseBasis A C
    have : Fintype (Module.Free.ChooseBasisIndex A C) := Module.Free.ChooseBasisIndex.fintype A C
    have hc : ∀ i, u (b.coord i (Ideal.Quotient.mk _ w)) = 0 := fun i =>
      h (Ideal.subset_span ⟨b.coord i, w, hw, rfl⟩)
    choose l hl using fun i => Ideal.Quotient.mk_surjective (b i)
    have hsum : w - ∑ i, b.coord i (Ideal.Quotient.mk _ w) • l i ∈ Jn A E n := by
      refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
      rw [map_sub, sub_eq_zero]
      conv_lhs => rw [← b.sum_repr (Ideal.Quotient.mk _ w)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      change _ • b i = Ideal.Quotient.mk _ (_ • l i)
      rw [← hl i]
      rfl
    have h2 := baseR_mem_Jn u E n hsum
    have e0 : baseR u (∑ i, b.coord i (Ideal.Quotient.mk _ w) • l i) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      have : baseR u (algebraMap A (AddMonoidAlgebra A N) (b.coord i (Ideal.Quotient.mk _ w))) = 0 := by
        change baseR u (single 0 _) = 0
        rw [baseR_single]
        have h3 : u (algebraMap A A (b.coord i (Ideal.Quotient.mk _ w))) = 0 := hc i
        rw [h3, AddMonoidAlgebra.single_zero]
      rw [this, zero_mul]
    rwa [map_sub, e0, sub_zero] at h2

end Ring

section Fixed

variable {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommGroup M]
variable {X : Cᵒᵖ ⥤ Type u}

/-- The functor of `F_n`-fixed points of **Lemma A.3**: the points `x ∈ X(T)` with
`h • x|_{T'} = x|_{T'}` for all `T' → T` and all `h ∈ F_n(T')`. -/
def fnFixed (act : AAction 𝒪 M X) (E : Set M) (n : ℕ) : Subfunctor X where
  obj T := {x | ∀ {T' : Cᵒᵖ} (s : T ⟶ T') (h : APt 𝒪 M T'), IsFnPt E n h →
    act.smul h (X.map s x) = X.map s x}
  map {T T'} i x hx {T''} s h hh := by
    have := hx (i ≫ s) h hh
    rwa [Functor.map_comp_apply] at this

lemma IsFnPt.res {E : Set M} {n : ℕ} {U V : Cᵒᵖ} (f : U ⟶ V) {h : APt 𝒪 M U} (hh : IsFnPt E n h) :
    IsFnPt E n (APt.res f h) := by
  intro e he
  have := congrArg (𝒪.map f).hom (hh e he)
  simpa [map_pow, map_sub, map_one, APt.res_apply] using this

/-- `X^{D(M)} ⊆ X^{F_n}`, the "obvious inclusions" of the proof of **Theorem A.1**. -/
lemma fixedPoints_le_fnFixed (act : AAction 𝒪 M X) (E : Set M) (n : ℕ) :
    fixedPoints act ≤ fnFixed act E n := fun _ _ hx _ s h _ => hx s h

end Fixed

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `TorsionResidue` passes to schemes over `S`. -/
lemma torsionResidue_of_hom {Y : Scheme.{u}} (t : Y ⟶ S) (h : TorsionResidue M S) :
    TorsionResidue M Y := by
  intro y q hq m hm
  obtain ⟨q', hq'⟩ := ExpChar.exists (S.residueField (t y))
  have h2 : ExpChar (Y.residueField y) q' :=
    expChar_of_injective_ringHom (f := (t.residueFieldMap y).hom) (t.residueFieldMap y).hom.injective q'
  have : q = q' := ExpChar.eq hq h2
  subst this
  exact h (t y) q hq' m hm


/-! ### Lifting étale sections along nil-thickenings -/

/-- Sections of an étale morphism lift along a surjection of rings with nilpotent kernel. The case of
a square-zero kernel is `Stacks.Smooth.formallySmoothScheme_of_etale`. -/
theorem exists_lift_nil {X₀ Y₀ : Scheme.{u}} (p : X₀ ⟶ Y₀) [Etale p] (k : ℕ) :
    ∀ {C D : CommRingCat.{u}} (φ : C ⟶ D), Function.Surjective φ.hom →
      RingHom.ker φ.hom ^ (k + 1) = ⊥ → ∀ (a : Spec D ⟶ X₀) (h : Spec C ⟶ Y₀),
      a ≫ p = Spec.map φ ≫ h → ∃ b : Spec C ⟶ X₀, b ≫ p = h ∧ Spec.map φ ≫ b = a := by
  induction k with
  | zero =>
    intro C D φ hs hk a h w
    have hb : Function.Bijective φ.hom :=
      ⟨(RingHom.injective_iff_ker_eq_bot _).2 (by simpa using hk), hs⟩
    have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).2 hb
    refine ⟨inv (Spec.map φ) ≫ a, ?_, by simp⟩
    rw [Category.assoc, w, IsIso.inv_hom_id_assoc]
  | succ k ih =>
    intro C D φ hs hk a h w
    let I := RingHom.ker φ.hom
    let Q : Ideal C := I ^ (k + 1)
    have hQI : Q ≤ I := Ideal.pow_le_self (by omega)
    let C₁ : CommRingCat.{u} := .of (C ⧸ Q)
    let π₁ : C ⟶ C₁ := CommRingCat.ofHom (Ideal.Quotient.mk Q)
    let φ₁ : C₁ ⟶ D := CommRingCat.ofHom (Ideal.Quotient.lift Q φ.hom fun x hx => hQI hx)
    have hc : π₁ ≫ φ₁ = φ := by
      ext x
      exact Ideal.Quotient.lift_mk Q φ.hom (fun x hx => hQI hx)
    have hs₁ : Function.Surjective φ₁.hom := Ideal.Quotient.lift_surjective_of_surjective _ _ hs
    have hk₁ : RingHom.ker φ₁.hom ^ (k + 1) = ⊥ := by
      have hle : RingHom.ker φ₁.hom ≤ I.map (Ideal.Quotient.mk Q) := by
        intro y hy
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact Ideal.mem_map_of_mem _ hy
      refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
      rw [← Ideal.map_pow]
      exact le_bot_iff.2 (Ideal.map_quotient_self Q)
    obtain ⟨b₁, hb₁, hb₂⟩ := ih φ₁ hs₁ hk₁ a (Spec.map π₁ ≫ h) (by
      rw [w, ← hc, Spec.map_comp, Category.assoc])
    have hsπ : Function.Surjective π₁.hom := Ideal.Quotient.mk_surjective
    have hk₂ : RingHom.ker π₁.hom ^ 2 = ⊥ := by
      have : RingHom.ker π₁.hom = Q := Ideal.mk_ker (I := Q)
      rw [this]
      refine le_bot_iff.1 ?_
      rw [← hk, ← pow_mul]
      exact Ideal.pow_le_pow_right (by nlinarith)
    obtain ⟨b, hb, hb'⟩ := Stacks.Smooth.formallySmoothScheme_of_etale p inferInstance inferInstance
      (Spec.map π₁) (Stacks.Smooth.isFirstOrderThickening_specMap π₁ hsπ hk₂) b₁ h hb₁
    refine ⟨b, hb, ?_⟩
    rw [← hc, Spec.map_comp, Category.assoc, hb', hb₂]

/-- The hypothesis of `lemmaA5` needed on `E`: the `F_n` are infinitesimal neighbourhoods. -/
def InfinitesimalE (E : Set M) (n : ℕ) : Prop :=
  ∀ (A : Type u) [CommRing A], TorsionResidue M (Spec (.of A)) → ∃ k, augI A M ^ k ≤ Jn A E n

lemma fieldPt_eq_one {E : Set M} {n : ℕ} (hE : InfinitesimalE E n) (hM : TorsionResidue M S)
    (Y : BigFppfOver B S hS) (g : (SCH).obj Y) (h : APt (fppfO B S hS) M (op (fieldObj Y g)))
    (hh : IsFnPt E n h) : h = 1 := by
  let K := (SCH).obj (fieldObj Y g)
  let A := Γ(K, ⊤)
  have hA : IsField A :=
    MulEquiv.isField (Field.toIsField (((SCH).obj Y).residueField g))
      (Scheme.ΓSpecIso (.of (((SCH).obj Y).residueField g))).commRingCatIsoToRingEquiv.toMulEquiv
  have : IsAffine K := inferInstanceAs (IsAffine (Spec _))
  have tA : Spec (.of A) ⟶ S := K.isoSpec.inv ≫ (fieldObj Y g).hom.hom
  obtain ⟨k, hk⟩ := hE A (torsionResidue_of_hom tA hM)
  refine MonoidHom.ext fun p => ?_
  have h0 := isNilpotent_of_isFnPt (R := A) hk (h := h) hh (Multiplicative.toAdd p)
  exact eq_one_of_pow_sub_one hA h0

/-- **Theorem A.1**, step `X^{F_n} = X ×_Y Y^{F_n}` of the printed proof: the action of `F_n` on
`X ×_Y Y^{F_n}` is trivial, because `F_n × X_0 → X ×_Y X` lands, topologically through the unit
section, in the open diagonal. -/
theorem mem_fnFixed_of_openEqualizers {E : Set M} {n : ℕ} (hE : InfinitesimalE E n)
    (hM : TorsionResidue M S) {U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {actU : AAction (fppfO B S hS) M U} {actX : AAction (fppfO B S hS) M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f) (hopen : HasOpenEqualizers f) {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : U.obj T) (hx : f.app T x ∈ (fnFixed actX E n).obj T) : x ∈ (fnFixed actU E n).obj T := by
  intro T' s h hh
  have hab : f.app _ (actU.smul h (U.map s x)) = f.app _ (U.map s x) := by
    rw [hf, NatTrans.naturality_apply f s x]
    exact hx s h hh
  obtain ⟨W, hW⟩ := hopen (unop T') _ _ hab
  have htop : ∀ g : (SCH).obj (unop T'), g ∈ W := by
    intro g
    let ρ := fieldHom (unop T') g
    have h1 : APt.res ρ.op h = 1 :=
      fieldPt_eq_one hE hM (unop T') g _ (IsFnPt.res ρ.op hh)
    have h2 : U.map ρ.op (actU.smul h (U.map s x)) = U.map ρ.op (U.map s x) := by
      rw [actU.map_smul, h1, actU.one_smul]
    have := (hW _ ρ).1 h2
    obtain ⟨z⟩ : Nonempty ((SCH).obj (fieldObj (unop T') g)) := inferInstance
    have e := this ⟨z, rfl⟩
    rwa [fieldHom_apply] at e
  have := (hW (unop T') (𝟙 _)).2 (fun y _ => htop y)
  simpa using this

/-- The same for étale equivariant morphisms. -/
theorem mem_fnFixed_of_etale {E : Set M} {n : ℕ} (hE : InfinitesimalE E n)
    (hM : TorsionResidue M S) {U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {actU : AAction (fppfO B S hS) M U} {actX : AAction (fppfO B S hS) M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f) {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : U.obj T) (hx : f.app T x ∈ (fnFixed actX E n).obj T) : x ∈ (fnFixed actU E n).obj T :=
  mem_fnFixed_of_openEqualizers hE hM hf (hasOpenEqualizers_of_etale het) x hx

/-! ### The scheme `F_n` over an affine `T` -/

section FnObj

variable (hM : B.Contains (Spec (ZMon M))) (E : Set M) (n : ℕ)
variable (T : BigFppfOver B S hS)

/-- The ring `Γ(T)[M]/J_n` of functions of `F_n` over `T`. -/
noncomputable abbrev fnRing : CommRingCat.{u} :=
  .of (AddMonoidAlgebra Γ((SCH).obj T, ⊤) M ⧸ Jn Γ((SCH).obj T, ⊤) E n)

/-- `Γ(T) → Γ(T)[M]/J_n`. -/
noncomputable def fnStr : CommRingCat.of Γ((SCH).obj T, ⊤) ⟶ fnRing E n T :=
  CommRingCat.ofHom ((Ideal.Quotient.mk _).comp AddMonoidAlgebra.singleZeroRingHom)

/-- The structure map of `F_n` as a morphism of schemes. -/
noncomputable def fnπ₀ [IsAffine ((SCH).obj T)] : Spec (fnRing E n T) ⟶ (SCH).obj T :=
  Spec.map (fnStr E n T) ≫ ((SCH).obj T).isoSpec.inv

include hM in
lemma contains_fn [IsAffine ((SCH).obj T)] : B.Contains (Spec (fnRing E n T)) := by
  let g : Spec (fnRing E n T) ⟶ MonAff M ((SCH).obj T) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ (MonAff.isoOfIsAffine M ((SCH).obj T)).inv
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Jn Γ((SCH).obj T, ⊤) E n)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion g := inferInstance
  exact Scheme.size_lt_of_isClosedImmersion g (contains_monAff M hM T)

/-- `F_n` over an affine `T`, as an object of the site. -/
noncomputable def fnObj [IsAffine ((SCH).obj T)] : BigFppfOver B S hS :=
  siteObject B S hS (contains_fn hM E n T) (fnπ₀ E n T ≫ structMap T)

/-- `F_n → T`. -/
noncomputable def fnπ [IsAffine ((SCH).obj T)] : fnObj hM E n T ⟶ T :=
  Over.homMk (ObjectProperty.homMk (fnπ₀ E n T)) rfl

/-- The class in `Γ(F_n)` of a function on `D(M)_T`. -/
noncomputable def fnCl [IsAffine ((SCH).obj T)] : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M →+* (fppfO B S hS).obj (op (fnObj hM E n T)) :=
  ((Scheme.ΓSpecIso (fnRing E n T)).inv.hom).comp (Ideal.Quotient.mk _)

/-- The universal point of `F_n` over `T`. -/
noncomputable def fnPt [IsAffine ((SCH).obj T)] : APt (fppfO B S hS) M (op (fnObj hM E n T)) :=
  (fnCl hM E n T).toMonoidHom.comp (AddMonoidAlgebra.of Γ((SCH).obj T, ⊤) M)

lemma isFnPt_fnPt [IsAffine ((SCH).obj T)] : IsFnPt E n (fnPt hM E n T) := by
  intro e he
  have h : (single e 1 - 1 : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M) ^ n ∈ Jn Γ((SCH).obj T, ⊤) E n :=
    Ideal.subset_span ⟨e, he, rfl⟩
  have h2 : fnCl hM E n T ((single e 1 - 1) ^ n) = 0 := by
    change (Scheme.ΓSpecIso (fnRing E n T)).inv.hom (Ideal.Quotient.mk _ _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]
  rw [map_pow, map_sub, map_one] at h2
  exact h2

variable {T} {E n}
variable {T' : BigFppfOver B S hS} (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T'))

/-- The ring map `Γ(T)[M] → Γ(T')` of a point `h` of `D(M)` over `T' → T`. -/
noncomputable def fnEv : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M →+* Γ((SCH).obj T', ⊤) :=
  (evPt (R := Γ((SCH).obj T', ⊤)) h).comp (baseR ((SCH).map t).appTop.hom)

lemma fnEv_single (m : M) (a : Γ((SCH).obj T, ⊤)) :
    fnEv t h (single m a) = ((SCH).map t).appTop.hom a * (show Γ((SCH).obj T', ⊤) from h (Multiplicative.ofAdd m)) :=
  (congrArg (evPt (R := Γ((SCH).obj T', ⊤)) h) (baseR_single _ m a)).trans
    (evPt_single (R := Γ((SCH).obj T', ⊤)) h m _)

/-- The morphism `T' → F_n` classifying a point `h` of `F_n` over `T' → T`. -/
noncomputable def fnLift₀ (hh : IsFnPt E n h) : (SCH).obj T' ⟶ Spec (fnRing E n T) :=
  ((SCH).obj T').toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (fnEv t h) (by
    intro a ha
    exact evPt_Jn (R := Γ((SCH).obj T', ⊤)) hh (baseR_mem_Jn _ E n ha))))

lemma fnLift₀_appTop (hh : IsFnPt E n h) (w : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M) :
    (fnLift₀ t h hh).appTop ((Scheme.ΓSpecIso (fnRing E n T)).inv.hom (Ideal.Quotient.mk _ w)) =
      fnEv t h w :=
  (MonAff.toSpecΓ_map_appTop _ _ _).trans (Ideal.Quotient.lift_mk _ _ _)

lemma fnStr_comp (hh : IsFnPt E n h) :
    fnStr E n T ≫ CommRingCat.ofHom (Ideal.Quotient.lift _ (fnEv t h) (by
      intro a ha
      exact evPt_Jn (R := Γ((SCH).obj T', ⊤)) hh (baseR_mem_Jn _ E n ha))) =
      ((SCH).map t).appTop := by
  ext a
  refine (fnEv_single t h 0 a).trans ?_
  have e : h (Multiplicative.ofAdd (0 : M)) = 1 := map_one h
  rw [e]
  exact mul_one _

lemma fnLift₀_comp [IsAffine ((SCH).obj T)] (hh : IsFnPt E n h) :
    fnLift₀ t h hh ≫ fnπ₀ E n T = (SCH).map t := by
  rw [fnπ₀, fnLift₀, Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp, fnStr_comp t h hh,
    ← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]

/-- The morphism of the site `T' → F_n` classifying a point of `F_n` over `T' → T`. -/
noncomputable def fnLift [IsAffine ((SCH).obj T)] (hh : IsFnPt E n h) : T' ⟶ fnObj hM E n T :=
  Over.homMk (ObjectProperty.homMk (fnLift₀ t h hh)) (by
    apply B.inclusion.map_injective
    have hw : (SCH).map t ≫ structMap T = structMap T' := congrArg B.inclusion.map (Over.w t)
    refine Eq.trans ?_ hw
    rw [← fnLift₀_comp t h hh]
    exact (Category.assoc _ _ _).symm)

lemma fnLift_π [IsAffine ((SCH).obj T)] (hh : IsFnPt E n h) :
    fnLift hM t h hh ≫ fnπ hM E n T = t := by
  apply (SCH).map_injective
  rw [Functor.map_comp]
  exact fnLift₀_comp t h hh

lemma fnLift_appTop [IsAffine ((SCH).obj T)] (hh : IsFnPt E n h)
    (w : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M) :
    ((SCH).map (fnLift hM t h hh)).appTop (fnCl hM E n T w) = fnEv t h w :=
  fnLift₀_appTop t h hh w

lemma res_fnLift [IsAffine ((SCH).obj T)] (hh : IsFnPt E n h) :
    APt.res (fnLift hM t h hh).op (fnPt hM E n T) = h := by
  refine MonoidHom.ext fun p => ?_
  refine (fnLift_appTop hM t h hh _).trans ?_
  refine (fnEv_single t h _ 1).trans ?_
  rw [map_one]
  exact one_mul _

/-! ### The unit section of `F_n` is a nil-thickening -/

variable (T) in
lemma isFnPt_one (hn : n ≠ 0) : IsFnPt E n (1 : APt (fppfO B S hS) M (op T)) := by
  intro e _
  have : (1 : APt (fppfO B S hS) M (op T)) (Multiplicative.ofAdd e) = 1 := rfl
  rw [this, sub_self, zero_pow hn]

variable (T) in
/-- The ring map of the unit section `T → F_n`. -/
noncomputable def fnψ (hn : n ≠ 0) : fnRing E n T ⟶ CommRingCat.of Γ((SCH).obj T, ⊤) :=
  CommRingCat.ofHom (Ideal.Quotient.lift _ (fnEv (𝟙 T) 1) (by
    intro a ha
    exact evPt_Jn (R := Γ((SCH).obj T, ⊤)) (isFnPt_one (E := E) T hn) (baseR_mem_Jn _ E n ha)))

variable (T) in
lemma fnEv_one (w : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M) :
    fnEv (𝟙 T) (1 : APt (fppfO B S hS) M (op T)) w = augHom _ _ w := by
  have hu : ∀ a : Γ((SCH).obj T, ⊤), ((SCH).map (𝟙 T)).appTop.hom a = a := by
    intro a
    simp
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single m a =>
    change evPt (R := Γ((SCH).obj T, ⊤)) 1 (baseR _ (single m a)) = evPt (R := Γ((SCH).obj T, ⊤)) 1 (single m a)
    rw [baseR_single, hu]

variable (T) in
lemma fnψ_surjective (hn : n ≠ 0) : Function.Surjective (fnψ (E := E) T hn).hom := by
  intro a
  refine ⟨Ideal.Quotient.mk _ (single 0 a), ?_⟩
  refine (fnEv_one T _).trans ?_
  change evPt (R := Γ((SCH).obj T, ⊤)) 1 (single 0 a) = a
  rw [evPt_single]
  simp

variable (T) in
lemma ker_fnψ_pow (hn : n ≠ 0) {k : ℕ} (hk : augI Γ((SCH).obj T, ⊤) M ^ k ≤ Jn Γ((SCH).obj T, ⊤) E n) :
    RingHom.ker (fnψ (E := E) T hn).hom ^ (k + 1) = ⊥ := by
  have hle : RingHom.ker (fnψ (E := E) T hn).hom ≤
      (augI Γ((SCH).obj T, ⊤) M).map (Ideal.Quotient.mk _) := by
    intro y hy
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Ideal.mem_map_of_mem _ ?_
    rw [← ker_augHom]
    exact (fnEv_one T w).symm.trans hy
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
  rw [← Ideal.map_pow]
  refine (Ideal.map_mono ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)).trans ?_
  exact le_bot_iff.2 (Ideal.map_quotient_self _)

variable (T) in
/-- The unit section `T → F_n`. -/
noncomputable def fnE [IsAffine ((SCH).obj T)] (hn : n ≠ 0) : T ⟶ fnObj hM E n T :=
  fnLift hM (𝟙 T) 1 (isFnPt_one T hn)

variable (T) in
lemma fnE_eq [IsAffine ((SCH).obj T)] (hn : n ≠ 0) :
    (SCH).map (fnE hM (E := E) T hn) =
      ((SCH).obj T).isoSpec.hom ≫ Spec.map (fnψ (E := E) T hn) := rfl

variable (T) in
/-- Every point of `F_n` lies on the unit section. -/
lemma fnE_surjective [IsAffine ((SCH).obj T)] (hn : n ≠ 0) {k : ℕ}
    (hk : augI Γ((SCH).obj T, ⊤) M ^ k ≤ Jn Γ((SCH).obj T, ⊤) E n) :
    Function.Surjective ((SCH).map (fnE hM (E := E) T hn)) := by
  have hc : IsClosedImmersion (Spec.map (fnψ (E := E) T hn)) :=
    IsClosedImmersion.spec_of_surjective _ (fnψ_surjective T hn)
  have ht := (Stacks.Thickenings.isThickening_of_ker_pow_eq_bot _ hc
    ((Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine _ _).2
      (Stacks.Smooth.ker_specMap_appTop_pow_eq_bot _ (ker_fnψ_pow T hn hk)))).2
  intro y
  obtain ⟨z, rfl⟩ := ht y
  obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso ((SCH).obj T).isoSpec).surjective z
  exact ⟨x, Scheme.Hom.comp_apply ((SCH).obj T).isoSpec.hom (Spec.map (fnψ (E := E) T hn)) x⟩

variable (E n) in
/-- An étale section over `T` extends to `F_n`: the lifting of étale sections along the
nil-thickening `T → F_n`, used for the closedness of the stabilizer in **Lemma A.3**. -/
theorem exists_section_fn [IsAffine ((SCH).obj T)] (hn : n ≠ 0) {k : ℕ}
    (hk : augI Γ((SCH).obj T, ⊤) M ^ k ≤ Jn Γ((SCH).obj T, ⊤) E n)
    {V₀ : Scheme.{u}} (p : V₀ ⟶ (SCH).obj (fnObj hM E n T)) [Etale p] (s : (SCH).obj T ⟶ V₀)
    (hs : s ≫ p = (SCH).map (fnE hM (E := E) T hn)) :
    ∃ b : (SCH).obj (fnObj hM E n T) ⟶ V₀, b ≫ p = 𝟙 _ ∧ (SCH).map (fnE hM (E := E) T hn) ≫ b = s := by
  obtain ⟨b, h1, h2⟩ := exists_lift_nil p k (fnψ (E := E) T hn) (fnψ_surjective T hn)
    (ker_fnψ_pow T hn hk) (((SCH).obj T).isoSpec.inv ≫ s) (𝟙 _)
    ((Category.assoc _ _ _).trans ((congrArg _ hs).trans
      ((Iso.inv_hom_id_assoc ((SCH).obj T).isoSpec (Spec.map (fnψ (E := E) T hn))).trans
        (Category.comp_id _).symm)))
  exact ⟨b, h1, (Category.assoc ((SCH).obj T).isoSpec.hom (Spec.map (fnψ (E := E) T hn)) b).trans
    ((congrArg _ h2).trans (Iso.hom_inv_id_assoc _ s))⟩

lemma fnEv_comp {T₁ : BigFppfOver B S hS} (q : T₁ ⟶ T') (w : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M) :
    ((SCH).map q).appTop.hom (fnEv t h w) = fnEv (q ≫ t) (APt.res q.op h) w := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single m a =>
    rw [fnEv_single, fnEv_single, map_mul, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl

lemma fnCl_single [IsAffine ((SCH).obj T)] (hM : B.Contains (Spec (ZMon M))) (m : M)
    (a : Γ((SCH).obj T, ⊤)) :
    fnCl hM E n T (single m a) =
      ((SCH).map (fnπ hM E n T)).appTop.hom a *
        (show Γ((SCH).obj (fnObj hM E n T), ⊤) from (fnPt hM E n T) (Multiplicative.ofAdd m)) := by
  have e0 : ((SCH).map (fnπ hM E n T)).appTop.hom a = fnCl hM E n T (single 0 a) := by
    have h1 : fnπ₀ E n T ≫ ((SCH).obj T).toSpecΓ = Spec.map (fnStr E n T) := by
      rw [fnπ₀, Category.assoc, Scheme.isoSpec_inv_toSpecΓ]
      exact Category.comp_id _
    have h2 : (fnπ₀ E n T).appTop.hom a =
        (Spec.map (fnStr E n T)).appTop.hom ((Scheme.ΓSpecIso (.of Γ((SCH).obj T, ⊤))).inv.hom a) := by
      rw [← h1, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
      change _ = (fnπ₀ E n T).appTop.hom ((Scheme.ΓSpecIso _).hom.hom ((Scheme.ΓSpecIso _).inv.hom a))
      congr 1
      exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of Γ((SCH).obj T, ⊤))).inv_hom_id a).symm
    have h3 := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (fnStr E n T)) a
    exact h2.trans h3.symm
  rw [e0]
  change _ = fnCl hM E n T _ * fnCl hM E n T _
  rw [← map_mul]
  congr 1
  change _ = single 0 a * single m 1
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

end FnObj

/-! ### Closedness of the stabilizer on a chart -/

section Chart

lemma exists_hom_of_section {Y Z : BigFppfOver B S hS} (q : Z ⟶ Y) (b₀ : (SCH).obj Y ⟶ (SCH).obj Z)
    (h : b₀ ≫ (SCH).map q = 𝟙 _) : ∃ b : Y ⟶ Z, (SCH).map b = b₀ := by
  refine ⟨Over.homMk (ObjectProperty.homMk b₀) ?_, rfl⟩
  apply B.inclusion.map_injective
  have hw : (SCH).map q ≫ structMap Y = structMap Z := congrArg B.inclusion.map (Over.w q)
  refine (congrArg (fun k => b₀ ≫ k) hw.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ structMap Y) h).trans ?_
  exact Category.id_comp _

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} {f₀ : yoneda.obj U ⟶ X}
variable (hM : B.Contains (Spec (ZMon M))) {E : Set M} {n : ℕ}

/-- A point of `X` over `F_n` extending, on the unit section, a point of the chart `U` lifts to `U`:
the lifting of étale sections along the nil-thickening `T → F_n`. -/
theorem exists_chart_lift
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f₀)
    {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (j : T ⟶ U) (hn : n ≠ 0) {k : ℕ}
    (hk : augI Γ((SCH).obj T, ⊤) M ^ k ≤ Jn Γ((SCH).obj T, ⊤) E n)
    (a₀ : X.obj (op (fnObj hM E n T)))
    (ha : X.map (fnE hM (E := E) T hn).op a₀ = f₀.app (op T) j) :
    ∃ b : fnObj hM E n T ⟶ U, f₀.app _ b = a₀ ∧ fnE hM (E := E) T hn ≫ b = j := by
  let F := fnObj hM E n T
  let e : T ⟶ F := fnE hM (E := E) T hn
  let g : yoneda.obj F ⟶ X := yonedaEquiv.symm a₀
  have hr := het.rep
  have w : yoneda.map j ≫ f₀ = yoneda.map e ≫ g := by
    apply yonedaEquiv.injective
    have e1 : yoneda.map e ≫ g = yonedaEquiv.symm (X.map e.op a₀) := yonedaEquiv_symm_map _ _ |>.symm
    rw [e1, Equiv.apply_symm_apply, ha, yonedaEquiv_comp]
    exact congrArg (f₀.app (op T)) (by simp [yonedaEquiv])
  let s := hr.lift (yoneda.map j) e w
  have hse : s ≫ hr.snd g = e := hr.lift_snd _ _ _
  have hsf : yoneda.map s ≫ hr.fst g = yoneda.map j := hr.lift_fst _ _ _
  have hp : Etale ((SCH).map (hr.snd g)) := het.property_snd g
  obtain ⟨b₀, hb₁, hb₂⟩ := exists_section_fn hM E n hn hk ((SCH).map (hr.snd g)) ((SCH).map s) (by
    rw [← Functor.map_comp, hse])
  obtain ⟨b, hb⟩ := exists_hom_of_section (hr.snd g) b₀ hb₁
  have hbs : b ≫ hr.snd g = 𝟙 F := by
    apply (SCH).map_injective
    rw [Functor.map_comp, hb, hb₁]
    exact ((SCH).map_id _).symm
  have hes : e ≫ b = s := by
    apply (SCH).map_injective
    rw [Functor.map_comp, hb]
    exact hb₂
  let c : F ⟶ U := (hr.fst g).app (op F) b
  refine ⟨c, ?_, ?_⟩
  · have hc := congrArg (fun q => q.app (op F) b) (hr.isPullback g).w
    refine (show f₀.app _ c = _ from hc).trans ?_
    change g.app (op F) (b ≫ hr.snd g) = a₀
    rw [hbs]
    simp [g, yonedaEquiv]
  · have h1 : e ≫ c = (hr.fst g).app (op T) (e ≫ b) :=
      (NatTrans.naturality_apply (hr.fst g) e.op b).symm
    rw [h1, hes]
    have h2 := congrArg (fun q => q.app (op T) (𝟙 T)) hsf
    simpa using h2

lemma fnEv_baseR {T T' T₁ : BigFppfOver B S hS} (t : T' ⟶ T) (q : T₁ ⟶ T')
    (h : APt (fppfO B S hS) M (op T₁)) (w : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M) :
    fnEv q h (baseR ((SCH).map t).appTop.hom w) = fnEv (q ≫ t) h w := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single m a =>
    rw [baseR_single, fnEv_single, fnEv_single, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl

lemma fnCl_eq_fnEv {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    (w : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M) :
    fnCl hM E n T w = fnEv (fnπ hM E n T) (fnPt hM E n T) w := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add a b ha hb => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ _ _).symm)
  | single m a => rw [fnCl_single, fnEv_single]

lemma fnCl_surjective {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] :
    Function.Surjective (fnCl hM E n T) := by
  intro z
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (fnRing E n T)).inv).2 z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨w, hy⟩

lemma mem_Jn_of_fnCl {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    {w : AddMonoidAlgebra Γ((SCH).obj T, ⊤) M} (h : fnCl hM E n T w = 0) :
    w ∈ Jn Γ((SCH).obj T, ⊤) E n := by
  refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
  refine (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (fnRing E n T)).inv).1 ?_
  exact h.trans (map_zero (Scheme.ΓSpecIso (fnRing E n T)).inv.hom).symm

include hM in
/-- **Lemma A.3 on a chart**: the fixed locus of `F_n` in a piece `T` of a chart of `X` is cut out by
an ideal of `Γ(T)`, for test objects `T''` affine. Closedness of the stabilizer: over `F_n`, the two
maps to `X` lift to the chart, hence to the affine `T`, and they agree in `X` exactly where they
agree in `T`, because the diagonal of the étale chart is open and contains the unit section. -/
theorem exists_ideal_chart
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f₀)
    (act : AAction (fppfO B S hS) M X)
    {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (j : T ⟶ U)
    [IsOpenImmersion ((SCH).map j)] (hn : n ≠ 0)
    (hk : ∀ (T₁ : BigFppfOver B S hS) [IsAffine ((SCH).obj T₁)], ∃ k, augI Γ((SCH).obj T₁, ⊤) M ^ k ≤ Jn Γ((SCH).obj T₁, ⊤) E n)
    (hF : Module.Free Γ((SCH).obj T, ⊤) (AddMonoidAlgebra Γ((SCH).obj T, ⊤) M ⧸ Jn Γ((SCH).obj T, ⊤) E n))
    (hf : Module.Finite Γ((SCH).obj T, ⊤) (AddMonoidAlgebra Γ((SCH).obj T, ⊤) M ⧸ Jn Γ((SCH).obj T, ⊤) E n)) :
    ∃ J : Ideal Γ((SCH).obj T, ⊤), (∀ {T'' : BigFppfOver B S hS} (t : T'' ⟶ T),
      J ≤ RingHom.ker ((SCH).map t).appTop.hom →
        X.map t.op (f₀.app (op T) j) ∈ (fnFixed act E n).obj (op T'')) ∧
      (∀ {T'' : BigFppfOver B S hS} [IsAffine ((SCH).obj T'')] (t : T'' ⟶ T),
        X.map t.op (f₀.app (op T) j) ∈ (fnFixed act E n).obj (op T'') →
          J ≤ RingHom.ker ((SCH).map t).appTop.hom) := by
  let x := f₀.app (op T) j
  let F := fnObj hM E n T
  let π := fnπ hM E n T
  let c := fnPt hM E n T
  let e : T ⟶ F := fnE hM (E := E) T hn
  let a₀ : X.obj (op F) := act.smul c (X.map π.op x)
  have hπe : e ≫ π = 𝟙 T := fnLift_π hM _ _ _
  have hce : APt.res e.op c = 1 := res_fnLift hM _ _ _
  have hpull : ∀ {Y : BigFppfOver B S hS} (r : Y ⟶ F),
      X.map r.op a₀ = act.smul (APt.res r.op c) (X.map (r ≫ π).op x) := by
    intro Y r
    refine (act.map_smul r.op c _).trans ?_
    rw [op_comp, Functor.map_comp_apply]
  have ha : X.map e.op a₀ = x := by
    rw [hpull, hce, act.one_smul, hπe]
    simp
  obtain ⟨k, hkk⟩ := hk T
  obtain ⟨b, hb, hbe⟩ := exists_chart_lift hM het j hn hkk a₀ ha
  have hnat : ∀ {Y : BigFppfOver B S hS} (q : Y ⟶ U) {Y' : BigFppfOver B S hS} (r : Y' ⟶ Y),
      f₀.app _ (r ≫ q) = X.map r.op (f₀.app _ q) := fun q _ r =>
    NatTrans.naturality_apply f₀ r.op q
  have hrange : Set.range ((SCH).map b) ⊆ Set.range ((SCH).map j) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨t, rfl⟩ := fnE_surjective hM T hn hkk y
    refine ⟨t, ?_⟩
    rw [← hbe, Functor.map_comp, Scheme.Hom.comp_apply]
  let bT := IsOpenImmersion.lift ((SCH).map j) ((SCH).map b) hrange
  have hbT : bT ≫ (SCH).map j = (SCH).map b := IsOpenImmersion.lift_fac _ _ _
  let W : Set (AddMonoidAlgebra Γ((SCH).obj T, ⊤) M) := {w | ∃ y : Γ((SCH).obj T, ⊤),
    fnCl hM E n T w = bT.appTop.hom y - ((SCH).map π).appTop.hom y}
  have hcrit : ∀ {Y : BigFppfOver B S hS} (r : Y ⟶ F),
      (r ≫ b = r ≫ π ≫ j ↔ ∀ w ∈ W, ((SCH).map r).appTop.hom (fnCl hM E n T w) = 0) := by
    intro Y r
    have key : r ≫ b = r ≫ π ≫ j ↔ (SCH).map r ≫ bT = (SCH).map r ≫ (SCH).map π := by
      constructor
      · intro h
        apply (cancel_mono ((SCH).map j)).1
        rw [Category.assoc, hbT, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
          ← Functor.map_comp, h]
      · intro h
        apply (SCH).map_injective
        rw [Functor.map_comp, ← hbT, ← Category.assoc, h, Functor.map_comp, Functor.map_comp,
          Category.assoc]
    rw [key]
    constructor
    · rintro h w ⟨y, hy⟩
      rw [hy, map_sub, sub_eq_zero]
      have k2 := congrArg (fun q => q.appTop.hom y) h
      exact k2
    · intro h
      apply ext_of_isAffine
      ext y
      obtain ⟨w, hw⟩ := fnCl_surjective hM (E := E) (n := n)
        (bT.appTop.hom y - ((SCH).map π).appTop.hom y)
      have := h w ⟨y, hw⟩
      rw [hw, map_sub, sub_eq_zero] at this
      exact this
  have hW0 : ∀ w ∈ W, fnEv (𝟙 T) (1 : APt (fppfO B S hS) M (op T)) w = 0 := by
    intro w hw
    have h1 := (hcrit e).1 (by rw [hbe, ← Category.assoc, hπe, Category.id_comp]) w hw
    exact (fnLift_appTop hM (𝟙 T) 1 (isFnPt_one T hn) w).symm.trans h1
  refine ⟨fixedJOf W E n, ?_, ?_⟩
  · intro T'' t hJ T' s h hh
    let τ : unop T' ⟶ T := s.unop ≫ t
    let r := fnLift hM τ h hh
    have hrπ : r ≫ π = τ := fnLift_π hM _ _ _
    have hrc : APt.res r.op c = h := res_fnLift hM _ _ _
    have hJ' : fixedJOf W E n ≤ RingHom.ker ((SCH).map τ).appTop.hom := by
      intro g hg
      have h0 := hJ hg
      change ((SCH).map (s.unop ≫ t)).appTop.hom g = 0
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]
      change ((SCH).map s.unop).appTop.hom (((SCH).map t).appTop.hom g) = 0
      rw [show ((SCH).map t).appTop.hom g = 0 from h0, map_zero]
    have heq : r ≫ b = r ≫ π ≫ j := by
      refine (hcrit r).2 fun w hw => ?_
      refine (fnLift_appTop hM τ h hh w).trans ?_
      exact evPt_Jn (R := Γ((SCH).obj (unop T'), ⊤)) hh
        ((baseR_mem_Jn_iff W E n hF hf _).2 hJ' w hw)
    have h1 : X.map r.op a₀ = X.map (r ≫ π).op x :=
      (congrArg (X.map r.op) hb).symm.trans ((hnat b r).symm.trans
        ((congrArg (f₀.app _) (heq.trans (Category.assoc r π j).symm)).trans (hnat j (r ≫ π))))
    rw [hpull, hrc, hrπ] at h1
    have e2 : X.map s (X.map t.op x) = X.map τ.op x := by
      rw [← Functor.map_comp_apply]
      rfl
    rw [e2]
    exact h1
  · intro T'' _ t hfix
    let F₂ := fnObj hM E n T''
    let π₂ := fnπ hM E n T''
    let c₂ := fnPt hM E n T''
    have hc₂ : IsFnPt E n c₂ := isFnPt_fnPt hM E n T''
    let τ := π₂ ≫ t
    let r := fnLift hM τ c₂ hc₂
    have hrπ : r ≫ π = τ := fnLift_π hM _ _ _
    have hrc : APt.res r.op c = c₂ := res_fnLift hM _ _ _
    have hfx := hfix π₂.op c₂ hc₂
    have hxx : X.map π₂.op (X.map t.op x) = X.map τ.op x := by
      rw [← Functor.map_comp_apply]
      rfl
    rw [hxx] at hfx
    have hab : f₀.app _ (r ≫ b) = f₀.app _ (r ≫ π ≫ j) := by
      have s1 : f₀.app _ (r ≫ b) = X.map r.op a₀ := (hnat b r).trans (congrArg _ hb)
      have s2 : f₀.app _ (r ≫ π ≫ j) = X.map (r ≫ π).op x :=
        (congrArg _ (Category.assoc r π j).symm).trans (hnat j (r ≫ π))
      have s3 : X.map (r ≫ π).op x = X.map τ.op x := by rw [hrπ]
      refine s1.trans ((hpull r).trans ?_)
      rw [hrc, s3, hfx, ← s3]
      exact s2.symm
    obtain ⟨O, hO⟩ := hasOpenEqualizers_of_etale het F₂ (r ≫ b) (r ≫ π ≫ j) hab
    let e₂ : T'' ⟶ F₂ := fnE hM (E := E) T'' hn
    have hce₂ : APt.res e₂.op c₂ = 1 := res_fnLift hM _ _ _
    have hzero : ∀ {T₁ : BigFppfOver B S hS} (τ₁ : T₁ ⟶ T), ∀ w ∈ W,
        fnEv τ₁ (1 : APt (fppfO B S hS) M (op T₁)) w = 0 := by
      intro T₁ τ₁ w hw
      have h1 := fnEv_comp (𝟙 T) (1 : APt (fppfO B S hS) M (op T)) τ₁ w
      have e1 : APt.res τ₁.op (1 : APt (fppfO B S hS) M (op T)) = 1 :=
        MonoidHom.ext fun p => map_one ((fppfO B S hS).map τ₁.op).hom
      rw [hW0 w hw, map_zero, Category.comp_id, e1] at h1
      exact h1.symm
    have hag : e₂ ≫ r ≫ b = e₂ ≫ r ≫ π ≫ j := by
      have := (hcrit (e₂ ≫ r)).2 fun w hw => by
        rw [Functor.map_comp, Scheme.Hom.comp_appTop]
        change ((SCH).map e₂).appTop.hom (((SCH).map r).appTop.hom (fnCl hM E n T w)) = 0
        rw [fnLift_appTop hM τ c₂ hc₂ w, fnEv_comp, hce₂]
        exact hzero _ w hw
      simpa using this
    have hall : ∀ y, y ∈ O := by
      intro y
      obtain ⟨k₂, hk₂⟩ := hk T''
      obtain ⟨z, rfl⟩ := fnE_surjective hM T'' hn hk₂ y
      exact (hO T'' e₂).1 hag ⟨z, rfl⟩
    have heq : r ≫ b = r ≫ π ≫ j := by
      simpa using (hO F₂ (𝟙 F₂)).2 (fun y _ => hall y)
    refine (baseR_mem_Jn_iff W E n hF hf _).1 fun w hw => ?_
    refine mem_Jn_of_fnCl hM ?_
    rw [fnCl_eq_fnEv, fnEv_baseR]
    exact (fnLift_appTop hM τ c₂ hc₂ w).symm.trans ((hcrit r).1 heq w hw)

end Chart

/-! ### Gluing closed subschemes of the pieces of a chart -/

section Glue

lemma hom_congr {A A' : Scheme.{u}} {k k' : A ⟶ A'} (h : k = k') (q : A) : k q = k' q := by
  subst h
  rfl

lemma sigmaDesc_range {I : Type u} {Zs W : I → Scheme.{u}} (i : ∀ a, Zs a ⟶ W a) (a : I) :
    Set.range (Sigma.ι Zs a) =
      SetLike.coe ((Sigma.desc fun a => i a ≫ Sigma.ι W a) ⁻¹ᵁ (Sigma.ι W a).opensRange) := by
  let g : ∐ Zs ⟶ ∐ W := Sigma.desc fun a => i a ≫ Sigma.ι W a
  have hg : ∀ a, Sigma.ι Zs a ≫ g = i a ≫ Sigma.ι W a := fun a => Sigma.ι_desc _ _
  have hmem : ∀ b (q : Zs b), g (Sigma.ι Zs b q) ∈ (Sigma.ι W b).opensRange := by
    intro b q
    refine ⟨i b q, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact hmem a q
  · intro hx
    obtain ⟨b, q, rfl⟩ := (sigmaOpenCover Zs).exists_eq x
    by_cases hab : a = b
    · subst hab
      exact ⟨q, rfl⟩
    · exact absurd (show g (Sigma.ι Zs b q) ∈
        ((Sigma.ι W a).opensRange ⊓ (Sigma.ι W b).opensRange : (∐ W).Opens) from ⟨hx, hmem b q⟩)
        (by rw [disjoint_iff.1 (disjoint_opensRange_sigmaι W a b hab)]; simp)

/-- A coproduct of closed immersions is a closed immersion. -/
theorem isClosedImmersion_sigmaDesc {I : Type u} {Zs W : I → Scheme.{u}} (i : ∀ a, Zs a ⟶ W a)
    [∀ a, IsClosedImmersion (i a)] :
    IsClosedImmersion (Sigma.desc fun a => i a ≫ Sigma.ι W a : ∐ Zs ⟶ ∐ W) := by
  let g : ∐ Zs ⟶ ∐ W := Sigma.desc fun a => i a ≫ Sigma.ι W a
  have hg : ∀ a, Sigma.ι Zs a ≫ g = i a ≫ Sigma.ι W a := fun a => Sigma.ι_desc _ _
  let V : I → (∐ W).Opens := fun a => (Sigma.ι W a).opensRange
  have hV : iSup V = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨b, q, rfl⟩ := (sigmaOpenCover W).exists_eq x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨b, q, rfl⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) (f := g) V hV).2
    fun a => ?_
  let e : Zs a ≅ (g ⁻¹ᵁ V a).toScheme := IsOpenImmersion.isoOfRangeEq (Sigma.ι Zs a) (g ⁻¹ᵁ V a).ι (by
    rw [Scheme.Opens.range_ι]
    exact sigmaDesc_range i a)
  have he : e.hom ≫ (g ⁻¹ᵁ V a).ι = Sigma.ι Zs a := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let eW : W a ≅ (V a).toScheme := IsOpenImmersion.isoOfRangeEq (Sigma.ι W a) (V a).ι (by
    rw [Scheme.Opens.range_ι]
    rfl)
  have heW : eW.hom ≫ (V a).ι = Sigma.ι W a := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hres : e.hom ≫ (g ∣_ V a) = i a ≫ eW.hom := by
    apply (cancel_mono (V a).ι).1
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, he, Category.assoc, heW]
    exact hg a
  have h2 : (g ∣_ V a) = e.inv ≫ i a ≫ eW.hom := (Iso.eq_inv_comp e).2 hres
  rw [h2]
  infer_instance

/-- `Spec (Γ(Y)/J) → Y` as a closed immersion. -/
noncomputable def quotI {Y : Scheme.{u}} [IsAffine Y] (J : Ideal Γ(Y, ⊤)) :
    Spec (.of (Γ(Y, ⊤) ⧸ J)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Y.isoSpec.inv

instance {Y : Scheme.{u}} [IsAffine Y] (J : Ideal Γ(Y, ⊤)) : IsClosedImmersion (quotI J) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold quotI
  infer_instance

/-- A morphism to an affine `Y` factors through `V(J)` iff `J` dies in global sections. -/
theorem exists_quotI_iff {Y Z : Scheme.{u}} [IsAffine Y] (J : Ideal Γ(Y, ⊤)) (t : Z ⟶ Y) :
    (∃ z : Z ⟶ Spec (.of (Γ(Y, ⊤) ⧸ J)), z ≫ quotI J = t) ↔ J ≤ RingHom.ker t.appTop.hom := by
  constructor
  · rintro ⟨z, rfl⟩ g hg
    have h1 : quotI J ≫ Y.toSpecΓ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
      rw [quotI, Category.assoc, Scheme.isoSpec_inv_toSpecΓ]
      exact Category.comp_id _
    have h2 : (quotI J).appTop.hom g = 0 := by
      have h3 := ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))) g
      have h4 : (quotI J).appTop.hom g = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
          ((Scheme.ΓSpecIso (.of Γ(Y, ⊤))).inv.hom g) := by
        rw [← h1, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
        change _ = (quotI J).appTop.hom ((Scheme.ΓSpecIso _).hom.hom ((Scheme.ΓSpecIso _).inv.hom g))
        congr 1
        exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of Γ(Y, ⊤))).inv_hom_id g).symm
      refine h4.trans (h3.symm.trans ?_)
      change (Scheme.ΓSpecIso (.of (Γ(Y, ⊤) ⧸ J))).inv.hom (Ideal.Quotient.mk J g) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hg, map_zero]
    change (z ≫ quotI J).appTop.hom g = 0
    rw [Scheme.Hom.comp_appTop]
    change z.appTop.hom ((quotI J).appTop.hom g) = 0
    rw [h2, map_zero]
  · intro h
    let ψ : CommRingCat.of (Γ(Y, ⊤) ⧸ J) ⟶ Γ(Z, ⊤) :=
      CommRingCat.ofHom (Ideal.Quotient.lift J t.appTop.hom fun a ha => h ha)
    refine ⟨Z.toSpecΓ ≫ Spec.map ψ, ?_⟩
    have hc : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ ψ = t.appTop := by
      ext a
      exact Ideal.Quotient.lift_mk J t.appTop.hom (fun a ha => h ha)
    rw [quotI, Category.assoc, ← Category.assoc (Spec.map ψ), ← Spec.map_comp, hc,
      ← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]

/-- A section vanishing on all affine opens vanishes. -/
theorem eq_zero_of_affine_opens {Z : Scheme.{u}} (g : Γ(Z, ⊤))
    (h : ∀ V : Z.Opens, IsAffineOpen V → V.ι.appTop.hom g = 0) : g = 0 := by
  refine TopCat.Presheaf.section_ext Z.sheaf ⊤ _ _ fun y hy => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  let V' : Z.Opens := V
  have h0 := h V' hV
  let y' : V'.toScheme := ⟨y, hyV⟩
  have hi : Function.Injective (V'.ι.stalkMap y').hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hz : Z.presheaf.germ ⊤ y hy g = 0 := by
    refine hi ?_
    refine (Scheme.Hom.germ_stalkMap_apply V'.ι ⊤ y' trivial g).trans ?_
    have h1 : V'.ι.app ⊤ g = 0 := h0
    refine (congrArg _ h1).trans ?_
    exact (map_zero _).trans (map_zero _).symm
  exact hz.trans (map_zero _).symm

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} {f₀ : yoneda.obj U ⟶ X}

/-- A representing closed subscheme of a chart gives that `Q → X` is a closed immersion after base
change to the chart. -/
theorem presheaf_snd_of_closed (Q : Subfunctor X) {Wz : BigFppfOver B S hS} (j' : Wz ⟶ U)
    (hj : IsClosedImmersion ((SCH).map j'))
    (hiff : ∀ {T : BigFppfOver B S hS} (y : T ⟶ U),
      (∃ c : T ⟶ Wz, c ≫ j' = y) ↔ f₀.app (op T) y ∈ Q.obj (op T)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (pullback.snd Q.ι f₀) := by
  have hm : Mono ((SCH).map j') := inferInstance
  have hinj : ∀ {T : BigFppfOver B S hS} (c c' : T ⟶ Wz), c ≫ j' = c' ≫ j' → c = c' := by
    intro T c c' h
    apply (SCH).map_injective
    apply (cancel_mono ((SCH).map j')).1
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  let κ : yoneda.obj Wz ⟶ Q.toFunctor :=
    { app := fun T => ↾ fun c => ⟨f₀.app T ((c : unop T ⟶ Wz) ≫ j'), (hiff _).1 ⟨c, rfl⟩⟩
      naturality := fun T T' s => by
        ext c
        refine Subtype.ext ?_
        have : (yoneda.obj Wz).map s c ≫ j' = (yoneda.obj U).map s (c ≫ j') :=
          Category.assoc _ _ _
        change f₀.app T' _ = X.map s (f₀.app T (c ≫ j'))
        exact (congrArg (f₀.app T') this).trans (NatTrans.naturality_apply f₀ s _) }
  have hpb : IsPullback κ (yoneda.map j') Q.ι f₀ := by
    refine IsPullback.of_forall_isPullback_app fun T => ?_
    refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
    · ext c
      rfl
    · rintro c c' ⟨-, h⟩
      exact hinj c c' h
    · intro q y h
      have hy : f₀.app T y ∈ Q.obj T := by
        have : f₀.app T y = q.1 := h.symm
        rw [this]
        exact q.2
      obtain ⟨c, hc⟩ := (hiff (T := unop T) y).2 hy
      exact ⟨c, Subtype.ext ((congrArg (f₀.app T) hc).trans h.symm), hc⟩
  have hP : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map j') :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ j').2 hj
  have hsq : IsPullback hpb.isoPullback.inv (pullback.snd Q.ι f₀) (yoneda.map j') (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hP

lemma exists_lift_of_open {W T : BigFppfOver B S hS} (j : W ⟶ U) [IsOpenImmersion ((SCH).map j)]
    (y : T ⟶ U) (hr : Set.range ((SCH).map y) ⊆ Set.range ((SCH).map j)) :
    ∃ t : T ⟶ W, t ≫ j = y := by
  have fac := IsOpenImmersion.lift_fac ((SCH).map j) ((SCH).map y) hr
  refine ⟨Over.homMk (ObjectProperty.homMk (IsOpenImmersion.lift ((SCH).map j) ((SCH).map y) hr)) ?_, ?_⟩
  · apply B.inclusion.map_injective
    have hw : (SCH).map y ≫ structMap U = structMap T := congrArg B.inclusion.map (Over.w y)
    have hj : (SCH).map j ≫ structMap U = structMap W := congrArg B.inclusion.map (Over.w j)
    refine Eq.trans ?_ hw
    refine Eq.trans (congrArg (fun q => IsOpenImmersion.lift ((SCH).map j) ((SCH).map y) hr ≫ q) hj.symm) ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ structMap U) fac)
  · apply (SCH).map_injective
    rw [Functor.map_comp]
    exact fac

/-- **Gluing.** Let `Q ⊆ X` be a local subfunctor and `U = ∐ W_i` a chart of `X`. If on each piece
`Q` is cut out by an ideal, then `Q` is cut out by a closed subscheme of `U`. -/
theorem exists_closed_of_chart_ideals (Q : Subfunctor X)
    (hQ : ∀ {T : BigFppfOver B S hS} (x : X.obj (op T)),
      Q.sieveOfSection x ∈ BigFppfOver.topology B S hS T → x ∈ Q.obj (op T))
    {I : Type u} (W : I → BigFppfOver B S hS) (j : ∀ i, W i ⟶ U)
    (e : (∐ fun i ↦ (SCH).obj (W i)) ≅ (SCH).obj U) [∀ i, IsAffine ((SCH).obj (W i))]
    (he : ∀ i, Sigma.ι (fun i ↦ (SCH).obj (W i)) i ≫ e.hom = (SCH).map (j i))
    [hoi : ∀ i, IsOpenImmersion ((SCH).map (j i))]
    (J : ∀ i, Ideal Γ((SCH).obj (W i), ⊤))
    (hJ : ∀ i {T'' : BigFppfOver B S hS} (t : T'' ⟶ W i),
      J i ≤ RingHom.ker ((SCH).map t).appTop.hom ↔ X.map t.op (f₀.app (op (W i)) (j i)) ∈ Q.obj (op T'')) :
    ∃ (Wz : BigFppfOver B S hS) (j' : Wz ⟶ U), IsClosedImmersion ((SCH).map j') ∧
      ∀ {T : BigFppfOver B S hS} (y : T ⟶ U),
        (∃ c : T ⟶ Wz, c ≫ j' = y) ↔ f₀.app (op T) y ∈ Q.obj (op T) := by
  let Ws := fun i ↦ (SCH).obj (W i)
  let Zs := fun i => Spec (.of (Γ(Ws i, ⊤) ⧸ J i))
  let iS : ∀ i, Zs i ⟶ Ws i := fun i => quotI (J i)
  have : ∀ i, IsClosedImmersion (iS i) := fun i => inferInstanceAs (IsClosedImmersion (quotI (J i)))
  let g : ∐ Zs ⟶ ∐ Ws := Sigma.desc fun a => iS a ≫ Sigma.ι Ws a
  have hgc : IsClosedImmersion g := isClosedImmersion_sigmaDesc iS
  let f : ∐ Zs ⟶ (SCH).obj U := g ≫ e.hom
  have hσf : ∀ a, Sigma.ι Zs a ≫ f = iS a ≫ (SCH).map (j a) := by
    intro a
    change Sigma.ι Zs a ≫ g ≫ e.hom = _
    rw [← Category.assoc, Sigma.ι_desc, Category.assoc, he]
  have hrange : ∀ a {q : ((∐ Zs : Scheme.{u}) : Scheme.{u})}, f q ∈ Set.range ((SCH).map (j a)) → q ∈ Set.range (Sigma.ι Zs a) := by
    intro a q hq
    rw [sigmaDesc_range iS a]
    obtain ⟨w, hw⟩ := hq
    refine ⟨w, ?_⟩
    apply (Scheme.homeoOfIso e).injective
    change e.hom _ = e.hom _
    rw [← Scheme.Hom.comp_apply, he, hw]
    rfl
  have hfc : IsClosedImmersion f := inferInstance
  have hWc : B.Contains (∐ Zs) := Scheme.size_lt_of_isClosedImmersion f U.left.2
  let Wz : BigFppfOver B S hS := siteObject B S hS hWc (f ≫ structMap U)
  let j' : Wz ⟶ U := Over.homMk (ObjectProperty.homMk f) rfl
  have hj' : (SCH).map j' = f := rfl
  have hcov : ∀ {T : BigFppfOver B S hS} (y : T ⟶ U), iSup (fun a => (SCH).map y ⁻¹ᵁ ((SCH).map (j a)).opensRange) = ⊤ := by
    intro T y
    rw [← Scheme.Hom.preimage_iSup]
    have : iSup (fun a => ((SCH).map (j a)).opensRange) = ⊤ := by
      refine top_le_iff.1 fun x _ => ?_
      obtain ⟨x', rfl⟩ := (Scheme.homeoOfIso e).surjective x
      obtain ⟨b, q, rfl⟩ := (sigmaOpenCover Ws).exists_eq x'
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨b, q,
        (hom_congr (he b) q).symm.trans (Scheme.Hom.comp_apply _ _ q)⟩
    rw [this]
    rfl
  have hlift : ∀ {T : BigFppfOver B S hS} (y : T ⟶ U) (a : I),
      ∃ t : openObj ((SCH).map y ⁻¹ᵁ ((SCH).map (j a)).opensRange) ⟶ W a,
        t ≫ j a = openJ _ ≫ y := by
    intro T y a
    have := hoi a
    refine exists_lift_of_open (j a) _ ?_
    rintro _ ⟨p, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact p.2
  have hpt : ∀ {T T₁ : BigFppfOver B S hS} (y : T ⟶ U) (a : I) (r : T₁ ⟶ T) (t : T₁ ⟶ W a),
      t ≫ j a = r ≫ y → X.map r.op (f₀.app (op T) y) = X.map t.op (f₀.app (op (W a)) (j a)) := by
    intro T T₁ y a r t ht
    exact (NatTrans.naturality_apply f₀ r.op y).symm.trans
      ((congrArg (f₀.app _) ht.symm).trans (NatTrans.naturality_apply f₀ t.op (j a)))
  refine ⟨Wz, j', hfc, fun {T} y => ⟨?_, fun hy => ?_⟩⟩
  · rintro ⟨c, rfl⟩
    refine hQ _ ?_
    let O := fun a => (SCH).map (c ≫ j') ⁻¹ᵁ ((SCH).map (j a)).opensRange
    have hc := BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS
      (fun a => openJ (O a)) (fun a => inferInstanceAs (IsOpenImmersion (iV (O a)))) (fun w => by
        have : w ∈ iSup O := by rw [hcov]; trivial
        obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 this
        exact ⟨a, ⟨w, ha⟩, rfl⟩)
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hc
    rintro T₁ q ⟨Z, h, r, ⟨a⟩, rfl⟩
    obtain ⟨t, ht⟩ := hlift (c ≫ j') a
    have hr : Set.range ((SCH).map (openJ (O a) ≫ c)) ⊆ Set.range (Sigma.ι Zs a) := by
      rintro _ ⟨p, rfl⟩
      refine hrange a ?_
      have e1 : f ((SCH).map (openJ (O a) ≫ c) p) = (SCH).map (c ≫ j') (iV (O a) p) := by
        have m : (SCH).map (openJ (O a) ≫ c) ≫ f = iV (O a) ≫ (SCH).map (c ≫ j') := by
          exact ((SCH).map_comp (openJ (O a) ≫ c) j').symm.trans ((congrArg (SCH).map
            (Category.assoc _ _ _)).trans ((SCH).map_comp (openJ (O a)) (c ≫ j')))
        exact (Scheme.Hom.comp_apply _ _ p).symm.trans ((hom_congr m p).trans
          (Scheme.Hom.comp_apply _ _ p))
      rw [e1]
      exact p.2
    let z := IsOpenImmersion.lift (Sigma.ι Zs a) ((SCH).map (openJ (O a) ≫ c)) hr
    have hz : z ≫ Sigma.ι Zs a = (SCH).map (openJ (O a) ≫ c) := IsOpenImmersion.lift_fac _ _ _
    have hzt : z ≫ iS a = (SCH).map t := by
      have := hoi a
      apply (cancel_mono ((SCH).map (j a))).1
      rw [Category.assoc, ← hσf, ← Category.assoc, hz, ← Functor.map_comp, ht]
      exact ((SCH).map_comp (openJ (O a) ≫ c) j').symm.trans
        (congrArg (SCH).map (Category.assoc _ _ _))
    have hJa := (exists_quotI_iff (J a) ((SCH).map t)).1 ⟨z, hzt⟩
    have hQa := (hJ a t).1 hJa
    have e2 := hpt (c ≫ j') a (openJ (O a)) t ht
    change X.map (h ≫ openJ (O a)).op _ ∈ Q.obj _
    rw [op_comp, Functor.map_comp_apply, e2]
    exact Q.map h.op hQa
  · let O := fun a => (SCH).map y ⁻¹ᵁ ((SCH).map (j a)).opensRange
    have hO : TopologicalSpace.IsOpenCover O := hcov y
    have hl : ∀ a, ∃ z : (O a).toScheme ⟶ ∐ Zs, z ≫ f = (O a).ι ≫ (SCH).map y := by
      intro a
      obtain ⟨t, ht⟩ := hlift y a
      have hfix : X.map t.op (f₀.app (op (W a)) (j a)) ∈ Q.obj _ := by
        rw [← hpt y a (openJ (O a)) t ht]
        exact Q.map (openJ (O a)).op hy
      obtain ⟨z, hz⟩ := (exists_quotI_iff (J a) ((SCH).map t)).2 ((hJ a t).2 hfix)
      have hmap := congrArg (SCH).map ht
      rw [Functor.map_comp, Functor.map_comp] at hmap
      refine ⟨z ≫ Sigma.ι Zs a, (Category.assoc _ _ _).trans ?_⟩
      refine (congrArg (fun q => z ≫ q) (hσf a)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun q => q ≫ (SCH).map (j a)) hz).trans ?_
      exact hmap
    choose z hz using hl
    let 𝒰 := ((SCH).obj T).openCoverOfIsOpenCover O hO
    have : Mono f := inferInstance
    let c₀ : (SCH).obj T ⟶ ∐ Zs := 𝒰.glueMorphisms z (fun a b => by
      apply (cancel_mono f).1
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun q => pullback.fst (𝒰.f a) (𝒰.f b) ≫ q) (hz a)).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (fun q => pullback.snd (𝒰.f a) (𝒰.f b) ≫ q) (hz b)).symm
      refine (Category.assoc _ _ _).symm.trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _)
      exact congrArg (fun q => q ≫ (SCH).map y) pullback.condition)
    have hc₀ : c₀ ≫ f = (SCH).map y := by
      refine Scheme.Cover.hom_ext 𝒰 _ _ fun a => ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (fun q => q ≫ f) (Scheme.Cover.ι_glueMorphisms 𝒰 z _ a)).trans (hz a)
    let c : T ⟶ Wz := Over.homMk (ObjectProperty.homMk c₀) (by
      apply B.inclusion.map_injective
      have hw : (SCH).map y ≫ structMap U = structMap T := congrArg B.inclusion.map (Over.w y)
      refine Eq.trans ?_ hw
      rw [← hc₀]
      exact (Category.assoc _ _ _).symm)
    refine ⟨c, ?_⟩
    apply (SCH).map_injective
    rw [Functor.map_comp]
    exact hc₀

/-- Extension to all test objects of the converse in `exists_ideal_chart`. -/
theorem le_ker_of_affine {T T'' : BigFppfOver B S hS} (J : Ideal Γ((SCH).obj T, ⊤)) (t : T'' ⟶ T)
    (h : ∀ V : ((SCH).obj T'').Opens, IsAffineOpen V →
      J ≤ RingHom.ker ((SCH).map (openJ V ≫ t)).appTop.hom) :
    J ≤ RingHom.ker ((SCH).map t).appTop.hom := by
  intro g hg
  refine eq_zero_of_affine_opens _ fun V hV => ?_
  have := h V hV hg
  rw [RingHom.mem_ker, Functor.map_comp, Scheme.Hom.comp_appTop] at this
  exact this

end Glue

lemma hk_of {E : Set M} {n : ℕ} (T₁ : BigFppfOver B S hS) [IsAffine ((SCH).obj T₁)]
    (hE : InfinitesimalE E n) (hT : TorsionResidue M S) :
    ∃ k, augI Γ((SCH).obj T₁, ⊤) M ^ k ≤ Jn Γ((SCH).obj T₁, ⊤) E n :=
  hE _ (torsionResidue_of_hom (((SCH).obj T₁).isoSpec.inv ≫ T₁.hom.hom) hT)

/-- `X^{F_n}` is an fppf sheaf if `X` is one. -/
theorem isSheaf_fnFixed {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (act : AAction (fppfO B S hS) M X)
    (E : Set M) (n : ℕ) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (fnFixed act E n).toFunctor := by
  have hX' := (isSheaf_iff_isSheaf_of_type _ _).mp hX
  refine (isSheaf_iff_isSheaf_of_type _ _).mpr ((Subfunctor.isSheaf_iff _ hX').mpr ?_)
  intro T x hx T₁ s h hh
  have hc := (BigFppfOver.topology B S hS).pullback_stable s.unop hx
  refine (hX' _ hc).isSeparatedFor.ext fun W q hq => ?_
  have hq2 := hq (T' := op W) (𝟙 _) (APt.res q.op h) (IsFnPt.res q.op hh)
  rw [act.map_smul]
  have ey : X.map q.op (X.map s x) = X.map (𝟙 (op W)) (X.map (q ≫ s.unop).op x) := by
    rw [CategoryTheory.Functor.map_id, op_comp, Functor.map_comp_apply]
    rfl
  rw [ey]
  exact hq2

/-- **Lemma A.5** in the form used here: a single `E` makes all `F_n` finite free and, under
`TorsionResidue`, infinitesimal. -/
theorem exists_E (M : Type u) [AddCommGroup M] [AddGroup.FG M] :
    ∃ E : Set M, ∀ n, InfinitesimalE E n ∧ ∀ (A : Type u) [CommRing A],
      Module.Free A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A M ⧸ Jn A E n) := by
  obtain ⟨E, hE⟩ := lemmaA5 M
  exact ⟨E, fun n => ⟨fun A _ h => (hE A n).2.2.2 h, fun A _ => ⟨(hE A n).1, (hE A n).2.1⟩⟩⟩

/-- A local subfunctor of an algebraic space cut out on the pieces of an atlas by ideals is a closed
subspace. -/
theorem presheaf_closed_of_ideals {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (Q : Subfunctor X)
    (hQs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q.toFunctor)
    (hJ : ∀ {U T : BigFppfOver B S hS} (f₀ : yoneda.obj U ⟶ X)
      (_ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f₀) [IsAffine ((SCH).obj T)] (j : T ⟶ U)
      [IsOpenImmersion ((SCH).map j)], ∃ J : Ideal Γ((SCH).obj T, ⊤),
      (∀ {T'' : BigFppfOver B S hS} (t : T'' ⟶ T), J ≤ RingHom.ker ((SCH).map t).appTop.hom →
        X.map t.op (f₀.app (op T) j) ∈ Q.obj (op T'')) ∧
      (∀ {T'' : BigFppfOver B S hS} [IsAffine ((SCH).obj T'')] (t : T'' ⟶ T),
        X.map t.op (f₀.app (op T) j) ∈ Q.obj (op T'') → J ≤ RingHom.ker ((SCH).map t).appTop.hom)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) Q.ι := by
  have hX' := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hQ := (Subfunctor.isSheaf_iff Q hX').mp ((isSheaf_iff_isSheaf_of_type _ _).mp hQs)
  obtain ⟨U, f₀, I, W, j, e, hs, het, haff, he, hoi, -, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS X hX
  have := haff
  have := hoi
  choose J hJ₁ hJ₂ using fun i => hJ (U := U) (T := W i) f₀ het (j i)
  have hiff : ∀ i {T'' : BigFppfOver B S hS} (t : T'' ⟶ W i),
      J i ≤ RingHom.ker ((SCH).map t).appTop.hom ↔
        X.map t.op (f₀.app (op (W i)) (j i)) ∈ Q.obj (op T'') := by
    intro i T'' t
    refine ⟨hJ₁ i t, fun h => le_ker_of_affine (J i) t fun V hV => ?_⟩
    have : IsAffine ((SCH).obj (openObj V)) := hV
    refine hJ₂ i (openJ V ≫ t) ?_
    have key := Q.map (openJ V).op h
    have e : X.map (openJ V ≫ t).op (f₀.app (op (W i)) (j i)) =
        X.map (openJ V).op (X.map t.op (f₀.app (op (W i)) (j i))) := by
      rw [op_comp, Functor.map_comp_apply]
    rw [e]
    exact key
  obtain ⟨Wz, j', hj', hc⟩ := exists_closed_of_chart_ideals (f₀ := f₀) Q
    (fun {T} x hx => hQ (op T) x hx) W j e he J hiff
  exact Space.presheaf_of_surjectiveEtaleChart
    (Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hQs hX.isSheaf hs het
    (presheaf_snd_of_closed Q j' hj' hc)

/-- **Lemma A.3** for `F = F_n ⊆ D(M)` acting on an algebraic space `X`: the functor of `F_n`-fixed
points is representable by a closed subspace of `X`. -/
theorem lemmaA3 [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (act : AAction (fppfO B S hS) M X) {E : Set M} {n : ℕ}
    (hn : n ≠ 0) (hE : InfinitesimalE E n) (hT : TorsionResidue M S)
    (hfr : ∀ (A : Type u) [CommRing A], Module.Free A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A M ⧸ Jn A E n)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (fnFixed act E n).ι := by
  have : Countable M := countable_of_fg M
  have hM := contains_zmon_of_countable hS M
  refine presheaf_closed_of_ideals hX _ (isSheaf_fnFixed hX.isSheaf act E n) ?_
  intro U T f₀ het _ j _
  exact exists_ideal_chart hM het act j hn (fun T₁ _ => hk_of T₁ hE hT)
    (hfr _).1 (hfr _).2

/-! ### From a neighbourhood of the unit section to all of `D(M)` -/

section Group

lemma hom_congr' {A A' : Scheme.{u}} {k k' : A ⟶ A'} (h : k = k') (q : A) : k q = k' q := by
  subst h
  rfl

/-- `D(M)_T → T` is flat and locally of finite presentation. -/
lemma monAff_π_flat_lfp [AddGroup.FG M] (T : Scheme.{u}) :
    Flat (MonAff.π M T) ∧ LocallyOfFinitePresentation (MonAff.π M T) := by
  let R := ULift.{u} ℤ
  let φ : CommRingCat.of R ⟶ ZMon M := CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R M))
  have hN : IsNoetherianRing R := isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv.symm)
  have hft : Algebra.FiniteType R (AddMonoidAlgebra R M) := AddMonoidAlgebra.finiteType_of_fg R M
  have hfp : Algebra.FinitePresentation R (AddMonoidAlgebra R M) :=
    Algebra.FinitePresentation.of_finiteType.1 hft
  have hFl : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    have hfl : Module.Flat R (AddMonoidAlgebra R M) := inferInstance
    exact RingHom.flat_algebraMap_iff.2 hfl
  have hLf : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact (RingHom.finitePresentation_algebraMap).2 hfp
  let t : Spec (CommRingCat.of R) ≅ ⊤_ Scheme.{u} := specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  have e : terminal.from (Spec (ZMon M)) = Spec.map φ ≫ t.hom := terminal.hom_ext _ _
  have h1 : Flat (terminal.from (Spec (ZMon M))) := by rw [e]; infer_instance
  have h2 : LocallyOfFinitePresentation (terminal.from (Spec (ZMon M))) := by rw [e]; infer_instance
  exact ⟨inferInstanceAs (Flat (pullback.fst _ _)), inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ _))⟩

lemma monAff_π_lft [AddGroup.FG M] (T : Scheme.{u}) : LocallyOfFiniteType (MonAff.π M T) := by
  let R := ULift.{u} ℤ
  let φ : CommRingCat.of R ⟶ ZMon M := CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R M))
  have hft : Algebra.FiniteType R (AddMonoidAlgebra R M) := AddMonoidAlgebra.finiteType_of_fg R M
  have hLf : LocallyOfFiniteType (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finiteType_algebraMap).2 hft
  let t : Spec (CommRingCat.of R) ≅ ⊤_ Scheme.{u} := specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  have e : terminal.from (Spec (ZMon M)) = Spec.map φ ≫ t.hom := terminal.hom_ext _ _
  have h2 : LocallyOfFiniteType (terminal.from (Spec (ZMon M))) := by rw [e]; infer_instance
  exact inferInstanceAs (LocallyOfFiniteType (pullback.fst _ _))

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Two points of `X` over `Y` coincide on a neighbourhood of a point of `Y`. -/
def EqNear {Y : BigFppfOver B S hS} (a b : X.obj (op Y)) (g : (SCH).obj Y) : Prop :=
  ∃ Ω : ((SCH).obj Y).Opens, g ∈ Ω ∧ X.map (openJ Ω).op a = X.map (openJ Ω).op b

/-- Equality over a flat morphism locally of finite presentation holds on a neighbourhood of the
image: fppf descent for the sheaf `X`. -/
theorem eqNear_of_flat (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {Y Z : BigFppfOver B S hS} (q : Z ⟶ Y) [Flat ((SCH).map q)]
    [LocallyOfFinitePresentation ((SCH).map q)] (O : ((SCH).obj Z).Opens) (a b : X.obj (op Y))
    (h : X.map (openJ O ≫ q).op a = X.map (openJ O ≫ q).op b) {z : (SCH).obj Z} (hz : z ∈ O) :
    EqNear a b ((SCH).map q z) := by
  have hX' := (isSheaf_iff_isSheaf_of_type _ _).mp hX
  let r : openObj O ⟶ Y := openJ O ≫ q
  have hre : (SCH).map r = iV O ≫ (SCH).map q := Functor.map_comp _ _ _
  have hrf : Flat ((SCH).map r) := by rw [hre]; infer_instance
  have hrl : LocallyOfFinitePresentation ((SCH).map r) := by rw [hre]; infer_instance
  have huo : UniversallyOpen ((SCH).map r) := UniversallyOpen.of_flat _
  have hopen : IsOpenMap ((SCH).map r) := ((SCH).map r).isOpenMap
  let Ω : ((SCH).obj Y).Opens := ⟨Set.range ((SCH).map r), hopen.isOpen_range⟩
  refine ⟨Ω, ⟨⟨z, hz⟩, hom_congr' hre _ |>.trans rfl⟩, ?_⟩
  have sq := (IsPullback.of_hasPullback (openJ Ω) r).map (SCH)
  have hsu : Surjective ((SCH).map (pullback.fst (openJ Ω) r)) := by
    refine ⟨fun w => ?_⟩
    obtain ⟨p, hp⟩ : (iV Ω) w ∈ Set.range ((SCH).map r) := w.2
    obtain ⟨c, hc1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := iV Ω) (g := (SCH).map r)
      w p hp.symm
    refine ⟨sq.isoPullback.inv c, ?_⟩
    exact ((Scheme.Hom.comp_apply _ _ c).symm.trans (hom_congr' sq.isoPullback_inv_fst c)).trans hc1
  have hc := Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS (pullback.fst (openJ Ω) r) hsu
    (MorphismProperty.of_isPullback sq.flip hrf) (MorphismProperty.of_isPullback sq.flip hrl)
  refine (hX' _ hc).isSeparatedFor.ext fun W f hf => ?_
  obtain ⟨Z', u, g, hg, rfl⟩ := hf
  cases hg
  have w : pullback.fst (openJ Ω) r ≫ openJ Ω = pullback.snd (openJ Ω) r ≫ r := pullback.condition
  have key : ∀ c : X.obj (op Y), X.map (u ≫ pullback.fst (openJ Ω) r).op (X.map (openJ Ω).op c) =
      X.map (u ≫ pullback.snd (openJ Ω) r).op (X.map r.op c) := by
    intro c
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    change X.map ((u ≫ pullback.fst (openJ Ω) r) ≫ openJ Ω).op c =
      X.map ((u ≫ pullback.snd (openJ Ω) r) ≫ r).op c
    rw [Category.assoc, Category.assoc, w]
  rw [key, key, h]

/-- If two points coincide near every point they coincide: `X` is a sheaf. -/
theorem eq_of_eqNear (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {Y : BigFppfOver B S hS} {a b : X.obj (op Y)} (h : ∀ g, EqNear a b g) : a = b := by
  have hX' := (isSheaf_iff_isSheaf_of_type _ _).mp hX
  choose Ω hΩ heq using h
  have hc := BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS
    (fun g => openJ (Ω g)) (fun g => inferInstanceAs (IsOpenImmersion (iV (Ω g)))) (fun w =>
      ⟨w, ⟨w, hΩ w⟩, rfl⟩)
  refine (hX' _ hc).isSeparatedFor.ext fun W f hf => ?_
  obtain ⟨Z', u, g, ⟨k⟩, rfl⟩ := hf
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, heq k]

/-- The last step of the printed proof of **Theorem A.1**: the locus near the unit section where a
point of `X` is fixed generates `D(M)`, because a neighbourhood of the unit is dense in fibres
(connectedness, here irreducibility of the fibres) and is stable by products. -/
theorem eq_of_eqNear_unit [AddGroup.FG M] (hM : B.Contains (Spec (ZMon M)))
    (hirr : IrreducibleFibres M S) (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (act : AAction (fppfO B S hS) M X) {Y : BigFppfOver B S hS} (x : X.obj (op Y))
    (hu : ∀ t : (SCH).obj Y, EqNear (act.smul (gc hM Y) (X.map (gπ hM Y).op x)) (X.map (gπ hM Y).op x)
      ((SCH).map (gLift hM (𝟙 Y) 1) t)) :
    act.smul (gc hM Y) (X.map (gπ hM Y).op x) = X.map (gπ hM Y).op x := by
  let G := monAffObj M hM Y
  let π := gπ hM Y
  let c := gc hM Y
  let a : X.obj (op G) := act.smul c (X.map π.op x)
  let b : X.obj (op G) := X.map π.op x
  have hpl : ∀ {P : BigFppfOver B S hS} (q : P ⟶ G), X.map q.op a =
      act.smul (APt.res q.op c) (X.map (q ≫ π).op x) ∧ X.map q.op b = X.map (q ≫ π).op x := by
    intro P q
    have e : X.map q.op b = X.map (q ≫ π).op x := by
      change X.map q.op (X.map π.op x) = _
      rw [op_comp, Functor.map_comp_apply]
    exact ⟨(act.map_smul q.op c _).trans (by rw [e]), e⟩
  refine eq_of_eqNear hX fun g => ?_
  let G₂ := monAffObj M hM G
  let π₂ := gπ hM G
  let c₂ := gc hM G
  let c' : APt (fppfO B S hS) M (op G₂) := APt.res π₂.op c
  let q₁ : G₂ ⟶ G := gLift hM (π₂ ≫ π) c₂
  let q₂ : G₂ ⟶ G := gLift hM (π₂ ≫ π) (c' * APt.inv c₂)
  have hq₁ : q₁ ≫ π = π₂ ≫ π := gLift_π hM _ _
  have hq₂ : q₂ ≫ π = π₂ ≫ π := gLift_π hM _ _
  have hc₁ : APt.res q₁.op c = c₂ := res_gLift hM _ _
  have hc₂ : APt.res q₂.op c = c' * APt.inv c₂ := res_gLift hM _ _
  -- the fibre over `g`
  let K := fieldObj G g
  let ρ : K ⟶ G := fieldHom G g
  let GK := monAffObj M hM K
  let πK := gπ hM K
  let cK := gc hM K
  let θ : GK ⟶ G₂ := gLift hM (πK ≫ ρ) cK
  have hθπ : θ ≫ π₂ = πK ≫ ρ := gLift_π hM _ _
  have hθc : APt.res θ.op c₂ = cK := res_gLift hM _ _
  let e₁ : K ⟶ GK := gLift hM (𝟙 K) 1
  let e₂ : K ⟶ GK := gLift hM (𝟙 K) (APt.res ρ.op c)
  have he₁ : e₁ ≫ πK = 𝟙 K := gLift_π hM _ _
  have he₂ : e₂ ≫ πK = 𝟙 K := gLift_π hM _ _
  have hc₁e : APt.res e₁.op cK = 1 := res_gLift hM _ _
  have hc₂e : APt.res e₂.op cK = APt.res ρ.op c := res_gLift hM _ _
  obtain ⟨z₀⟩ : Nonempty ((SCH).obj K) := inferInstance
  -- a morphism with trivial coordinate lands on the unit section
  have hunit : ∀ {P : BigFppfOver B S hS} (q : P ⟶ G), APt.res q.op c = 1 →
      q = (q ≫ π) ≫ gLift hM (𝟙 Y) 1 := by
    intro P q h
    apply (SCH).map_injective
    refine MonAff.hom_ext' ?_ fun p => ?_
    · have h2 : gLift hM (𝟙 Y) (1 : APt (fppfO B S hS) M (op Y)) ≫ π = 𝟙 Y := gLift_π hM _ _
      have : ((q ≫ π) ≫ gLift hM (𝟙 Y) 1) ≫ π = q ≫ π := by
        rw [Category.assoc, h2, Category.comp_id]
      exact (congrArg (SCH).map this).symm
    · have h1 := DFunLike.congr_fun h p
      have h3 : APt.res ((q ≫ π) ≫ gLift hM (𝟙 Y) (1 : APt (fppfO B S hS) M (op Y))).op c = 1 := by
        rw [op_comp, APt.res_comp]
        rw [show APt.res (gLift hM (𝟙 Y) (1 : APt (fppfO B S hS) M (op Y))).op c = 1 from res_gLift hM _ _]
        exact MonoidHom.ext fun p => map_one ((fppfO B S hS).map (q ≫ π).op).hom
      exact h1.trans (DFunLike.congr_fun h3 p).symm
  let w₁ : (SCH).obj K ⟶ (SCH).obj G := (SCH).map (e₁ ≫ θ ≫ q₁)
  let w₂ : (SCH).obj K ⟶ (SCH).obj G := (SCH).map (e₂ ≫ θ ≫ q₂)
  have hw₁c : APt.res (e₁ ≫ θ ≫ q₁).op c = 1 := by
    rw [op_comp, op_comp, APt.res_comp, APt.res_comp, hc₁, hθc, hc₁e]
  have hw₂c : APt.res (e₂ ≫ θ ≫ q₂).op c = 1 := by
    rw [op_comp, op_comp, APt.res_comp, APt.res_comp, hc₂, APt.res_mul, APt.inv_res, hθc,
      APt.res_mul, APt.inv_res, hc₂e]
    have : APt.res e₂.op (APt.res θ.op c') = APt.res ρ.op c := by
      change APt.res e₂.op (APt.res θ.op (APt.res π₂.op c)) = _
      rw [← APt.res_comp, ← op_comp, ← APt.res_comp, ← op_comp, Category.assoc, hθπ,
        ← Category.assoc, he₂, Category.id_comp]
    rw [this, mul_comm]
    exact APt.inv_mul _
  obtain ⟨Ω₁, hΩ₁, he₁Ω⟩ : EqNear a b (w₁ z₀) := by
    have := hu ((SCH).map ((e₁ ≫ θ ≫ q₁) ≫ π) z₀)
    have e := hom_congr' (congrArg (SCH).map (hunit _ hw₁c)) z₀
    rw [Functor.map_comp, Scheme.Hom.comp_apply] at e
    change EqNear a b _
    change _ = _ at e
    rw [show w₁ z₀ = _ from e]
    exact this
  obtain ⟨Ω₂, hΩ₂, he₂Ω⟩ : EqNear a b (w₂ z₀) := by
    have := hu ((SCH).map ((e₂ ≫ θ ≫ q₂) ≫ π) z₀)
    have e := hom_congr' (congrArg (SCH).map (hunit _ hw₂c)) z₀
    rw [Functor.map_comp, Scheme.Hom.comp_apply] at e
    change EqNear a b _
    rw [show w₂ z₀ = _ from e]
    exact this
  have hI := irreducible_monAff hM hirr G g
  obtain ⟨y, hy₁, hy₂⟩ := nonempty_preirreducible_inter (X := (SCH).obj GK)
    ((SCH).map (θ ≫ q₁) ⁻¹ᵁ Ω₁).2 ((SCH).map (θ ≫ q₂) ⁻¹ᵁ Ω₂).2
    ⟨(SCH).map e₁ z₀, by
      have : (SCH).map (θ ≫ q₁) ((SCH).map e₁ z₀) = w₁ z₀ :=
        ((Scheme.Hom.comp_apply _ _ z₀).symm.trans (hom_congr' ((SCH).map_comp e₁ (θ ≫ q₁)).symm z₀))
      change (SCH).map (θ ≫ q₁) ((SCH).map e₁ z₀) ∈ Ω₁
      rw [this]
      exact hΩ₁⟩
    ⟨(SCH).map e₂ z₀, by
      have : (SCH).map (θ ≫ q₂) ((SCH).map e₂ z₀) = w₂ z₀ :=
        ((Scheme.Hom.comp_apply _ _ z₀).symm.trans (hom_congr' ((SCH).map_comp e₂ (θ ≫ q₂)).symm z₀))
      change (SCH).map (θ ≫ q₂) ((SCH).map e₂ z₀) ∈ Ω₂
      rw [this]
      exact hΩ₂⟩
  let O : ((SCH).obj G₂).Opens := (SCH).map q₁ ⁻¹ᵁ Ω₁ ⊓ (SCH).map q₂ ⁻¹ᵁ Ω₂
  have hf := monAff_π_flat_lfp (M := M) ((SCH).obj G)
  have : Flat ((SCH).map π₂) := hf.1
  have : LocallyOfFinitePresentation ((SCH).map π₂) := hf.2
  let J := openJ O
  have hfac₁ : ∀ p, (SCH).map (J ≫ q₁) p ∈ Ω₁ := by
    intro p
    have e := hom_congr' ((SCH).map_comp J q₁) p
    rw [e, Scheme.Hom.comp_apply]
    exact p.2.1
  have hfac₂ : ∀ p, (SCH).map (J ≫ q₂) p ∈ Ω₂ := by
    intro p
    have e := hom_congr' ((SCH).map_comp J q₂) p
    rw [e, Scheme.Hom.comp_apply]
    exact p.2.2
  obtain ⟨t₁, ht₁⟩ := exists_lift_open (J ≫ q₁) hfac₁
  obtain ⟨t₂, ht₂⟩ := exists_lift_open (J ≫ q₂) hfac₂
  let x₂ : X.obj (op (openObj O)) := X.map (J ≫ π₂ ≫ π).op x
  have hfix₁ : act.smul (APt.res J.op c₂) x₂ = x₂ := by
    have h1 := congrArg (X.map t₁.op) he₁Ω
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at h1
    change X.map (t₁ ≫ openJ Ω₁).op a = X.map (t₁ ≫ openJ Ω₁).op b at h1
    rw [ht₁, (hpl _).1, (hpl _).2, op_comp, APt.res_comp, hc₁, Category.assoc, hq₁] at h1
    exact h1
  have hfix₂ : act.smul (APt.res J.op (c' * APt.inv c₂)) x₂ = x₂ := by
    have h1 := congrArg (X.map t₂.op) he₂Ω
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at h1
    change X.map (t₂ ≫ openJ Ω₂).op a = X.map (t₂ ≫ openJ Ω₂).op b at h1
    rw [ht₂, (hpl _).1, (hpl _).2, op_comp, APt.res_comp, hc₂, Category.assoc, hq₂] at h1
    exact h1
  have hfin : X.map (J ≫ π₂).op a = X.map (J ≫ π₂).op b := by
    rw [(hpl _).1, (hpl _).2, Category.assoc]
    have e : APt.res (J ≫ π₂).op c = APt.res J.op (c' * APt.inv c₂) * APt.res J.op c₂ := by
      rw [← APt.res_mul, mul_assoc, APt.inv_mul, mul_one, op_comp, APt.res_comp]
    rw [e, act.mul_smul, hfix₁, hfix₂]
  have hz : (SCH).map θ y ∈ O := by
    refine ⟨?_, ?_⟩
    · have e := hom_congr' ((SCH).map_comp θ q₁) y
      change (SCH).map q₁ ((SCH).map θ y) ∈ Ω₁
      rw [← Scheme.Hom.comp_apply, ← e]
      exact hy₁
    · have e := hom_congr' ((SCH).map_comp θ q₂) y
      change (SCH).map q₂ ((SCH).map θ y) ∈ Ω₂
      rw [← Scheme.Hom.comp_apply, ← e]
      exact hy₂
  have hne := eqNear_of_flat hX π₂ O a b hfin hz
  have hg : (SCH).map π₂ ((SCH).map θ y) = g := by
    rw [← Scheme.Hom.comp_apply, ← (SCH).map_comp, hθπ, (SCH).map_comp, Scheme.Hom.comp_apply]
    exact fieldHom_apply G g _
  rwa [hg] at hne

end Group

/-- The conclusion of the printed proof of **Theorem A.1** on FPR morphisms, under the equalities
`X^G = ⋂ X^{F_n}` and `Y^G = ⋂ Y^{F_n}` that the printed proof obtains first. -/
theorem isFPR_of_iInf_fnFixed {E : Set M} (hE : ∀ n, InfinitesimalE E n)
    (hM : TorsionResidue M S) {U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {actU : AAction (fppfO B S hS) M U} {actX : AAction (fppfO B S hS) M X} {f : U ⟶ X}
    (hf : IsEquivariant actU actX f)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    (hU : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (x : U.obj T),
      (∀ n, x ∈ (fnFixed actU E n).obj T) → x ∈ (fixedPoints actU).obj T) :
    IsFPR hf :=
  (isFPR_iff hf).2 fun T x hx => hU T x fun n =>
    mem_fnFixed_of_etale (hE n) hM hf het x (fixedPoints_le_fnFixed actX E n T hx)

/-! ### Near the unit section: formal étaleness along the unit section, in the noetherian case -/

section Unit

lemma ell_appTop (Z : Scheme.{u}) (v : Z) (I : Ideal (Z.presheaf.stalk v)) (d : Γ(Z, ⊤)) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Z.fromSpecStalk v).appTop.hom d =
      (Scheme.ΓSpecIso (.of (Z.presheaf.stalk v ⧸ I))).inv.hom
        (Ideal.Quotient.mk I (Z.presheaf.germ ⊤ v trivial d)) := by
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (Z.presheaf.germ ⊤ v trivial d)).symm

/-- A point of `Spec(O_{Z,v}/m^k)` maps to `v`. -/
lemma ell_apply (Z : Scheme.{u}) (v : Z) {k : ℕ} (hk : k ≠ 0)
    (o : Spec (.of (Z.presheaf.stalk v ⧸ IsLocalRing.maximalIdeal (Z.presheaf.stalk v) ^ k))) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Z.presheaf.stalk v) ^ k))) ≫ Z.fromSpecStalk v) o = v := by
  rw [Scheme.Hom.comp_apply]
  have hcl : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Z.presheaf.stalk v) ^ k))) o =
        IsLocalRing.closedPoint (Z.presheaf.stalk v) := by
    let q : PrimeSpectrum (Z.presheaf.stalk v ⧸ IsLocalRing.maximalIdeal (Z.presheaf.stalk v) ^ k) := o
    have e : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk v) ^ k))) o =
        PrimeSpectrum.comap (Ideal.Quotient.mk _) q := rfl
    rw [e]
    refine PrimeSpectrum.ext ?_
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    intro a ha
    change Ideal.Quotient.mk _ a ∈ q.asIdeal
    refine q.2.mem_of_pow_mem k ?_
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Z.presheaf.stalk v) ^ k) (a ^ k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (show a ∈ IsLocalRing.maximalIdeal _ from ha) k)
    have h1 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Z.presheaf.stalk v) ^ k) a) ^ k = 0 := by
      rw [← map_pow]
      exact h0
    rw [h1]
    exact Ideal.zero_mem _
  rw [hcl]
  exact Scheme.fromSpecStalk_closedPoint

lemma ell_pow {R : CommRingCat.{u}} {I : Ideal R} (a : R) {n : ℕ} (ha : a ^ n ∈ I) :
    ((Scheme.ΓSpecIso (.of (R ⧸ I))).inv.hom (Ideal.Quotient.mk I a)) ^ n = 0 := by
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

lemma germ_mem_max {Z Z' : Scheme.{u}} (s : Z' ⟶ Z) (t : Z') {w : Z} (hw : s t = w) (d : Γ(Z, ⊤))
    (h : s.appTop.hom d = 0) : Z.presheaf.germ ⊤ w trivial d ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk w) := by
  subst hw
  rw [IsLocalRing.mem_maximalIdeal]
  intro hu
  have h1 := Scheme.Hom.germ_stalkMap_apply s ⊤ t trivial d
  have h2 : s.app ⊤ d = 0 := h
  rw [h2, map_zero] at h1
  have h3 := hu.map (s.stalkMap t).hom
  have h4 : (s.stalkMap t).hom (Z.presheaf.germ ⊤ (s t) trivial d) = 0 := h1
  rw [h4] at h3
  exact not_isUnit_zero h3

lemma exists_open_of_germ (Z : Scheme.{u}) (v : Z) (S' : Finset Γ(Z, ⊤))
    (h : ∀ d ∈ S', Z.presheaf.germ ⊤ v trivial d = 0) :
    ∃ Ω : Z.Opens, v ∈ Ω ∧ ∀ d ∈ S', Ω.ι.appTop.hom d = 0 := by
  classical
  induction S' using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, by simp⟩
  | insert d S'' _ ih =>
    obtain ⟨Ω, hv, hΩ⟩ := ih fun c hc => h c (Finset.mem_insert_of_mem hc)
    have hd := h d (Finset.mem_insert_self _ _)
    obtain ⟨W, hW, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq Z.presheaf v (show v ∈ (⊤ : Z.Opens) from trivial) (show v ∈ (⊤ : Z.Opens) from trivial) d 0
      (hd.trans (map_zero _).symm)
    have hzero : ∀ (O : Z.Opens) (hle : O ≤ W),
        (Z.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom d = 0 := by
      intro O hle
      have e2 := congrArg (Z.presheaf.map (homOfLE hle).op).hom e
      have q1 := ConcreteCategory.congr_hom (Z.presheaf.map_comp i₁.op (homOfLE hle).op) d
      have q2 := ConcreteCategory.congr_hom (Z.presheaf.map_comp i₂.op (homOfLE hle).op) (0 : Γ(Z, ⊤))
      rw [map_zero] at q2
      exact q1.trans (e2.trans q2.symm)
    have hres : ∀ (Ω' : Z.Opens) (_ : Ω' ≤ W), Ω'.ι.appTop.hom d = 0 := by
      intro Ω' hle
      rw [Scheme.Opens.ι_appTop]
      refine hzero (Ω'.ι ''ᵁ ⊤) ?_
      rintro _ ⟨y, -, rfl⟩
      exact hle y.2
    refine ⟨Ω ⊓ W, ⟨hv, hW⟩, fun c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc'
    · exact hres _ inf_le_right
    · have e := Scheme.homOfLE_ι Z (inf_le_left : Ω ⊓ W ≤ Ω)
      have e2 := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop e) c
      simp only [Scheme.Hom.comp_appTop] at e2
      refine e2.symm.trans ?_
      change (Z.homOfLE (inf_le_left : Ω ⊓ W ≤ Ω)).appTop.hom (Ω.ι.appTop.hom c) = 0
      rw [hΩ c hc', map_zero]

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} {f₀ : yoneda.obj U ⟶ X}

set_option maxHeartbeats 3000000 in
/-- The technical core of the printed claim "`Stab₀ → G × X₀` is formally étale along the unit
section": near the unit section of `D(M)_Y`, for `Y` locally noetherian, a point of the chart fixed
by all the `F_n` is fixed. The artinian test objects of the printed proof are the
`Spec(O_{V,v}/m^k)`, which are points of `F_k`; Krull's intersection theorem concludes. -/
theorem eqNear_unit (hM : B.Contains (Spec (ZMon M))) [AddGroup.FG M] {E : Set M}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f₀)
    (act : AAction (fppfO B S hS) M X) {Y : BigFppfOver B S hS}
    [IsLocallyNoetherian ((SCH).obj Y)] (y : Y ⟶ U)
    (hfix : ∀ n, n ≠ 0 → f₀.app (op Y) y ∈ (fnFixed act E n).obj (op Y)) (t : (SCH).obj Y) :
    EqNear (act.smul (gc hM Y) (X.map (gπ hM Y).op (f₀.app (op Y) y)))
      (X.map (gπ hM Y).op (f₀.app (op Y) y)) ((SCH).map (gLift hM (𝟙 Y) 1) t) := by
  let x := f₀.app (op Y) y
  let G := monAffObj M hM Y
  let π := gπ hM Y
  let c := gc hM Y
  let e : Y ⟶ G := gLift hM (𝟙 Y) 1
  have heπ : e ≫ π = 𝟙 Y := gLift_π hM _ _
  have hec : APt.res e.op c = 1 := res_gLift hM _ _
  let a : X.obj (op G) := act.smul c (X.map π.op x)
  have hnat : ∀ {Z : BigFppfOver B S hS} (q : Z ⟶ U) {Z' : BigFppfOver B S hS} (r : Z' ⟶ Z),
      f₀.app _ (r ≫ q) = X.map r.op (f₀.app _ q) := fun q _ r =>
    NatTrans.naturality_apply f₀ r.op q
  have hpull : ∀ {P : BigFppfOver B S hS} (r : P ⟶ G),
      X.map r.op a = act.smul (APt.res r.op c) (X.map (r ≫ π).op x) := by
    intro P r
    refine (act.map_smul r.op c _).trans ?_
    rw [op_comp, Functor.map_comp_apply]
  have hae : X.map e.op a = x := by
    rw [hpull, hec, act.one_smul, heπ]
    simp
  let g : yoneda.obj G ⟶ X := yonedaEquiv.symm a
  have hr := het.rep
  have w : yoneda.map y ≫ f₀ = yoneda.map e ≫ g := by
    apply yonedaEquiv.injective
    have e1 : yoneda.map e ≫ g = yonedaEquiv.symm (X.map e.op a) := yonedaEquiv_symm_map _ _ |>.symm
    rw [e1, Equiv.apply_symm_apply, hae, yonedaEquiv_comp]
    exact congrArg (f₀.app (op Y)) (by simp [yonedaEquiv])
  let V := hr.pullback g
  let p : V ⟶ G := hr.snd g
  let s : Y ⟶ V := hr.lift (yoneda.map y) e w
  have hsp : s ≫ p = e := hr.lift_snd _ _ _
  have hsf : yoneda.map s ≫ hr.fst g = yoneda.map y := hr.lift_fst _ _ _
  let aT : V ⟶ U := (hr.fst g).app (op V) (𝟙 V)
  have hfa : f₀.app (op V) aT = X.map p.op a := by
    have hc := congrArg (fun q => q.app (op V) (𝟙 V)) (hr.isPullback g).w
    refine (show f₀.app (op V) aT = (yoneda.map (hr.snd g) ≫ g).app (op V) (𝟙 V) from hc).trans ?_
    change g.app (op V) (𝟙 V ≫ p) = _
    rw [Category.id_comp]
    simp [g, yonedaEquiv]
  have hsaT : s ≫ aT = y := by
    have h2 := congrArg (fun q => q.app (op Y) (𝟙 Y)) hsf
    have h1 : s ≫ aT = (hr.fst g).app (op Y) (s ≫ 𝟙 V) :=
      (NatTrans.naturality_apply (hr.fst g) s.op (𝟙 V)).symm
    rw [h1, Category.comp_id]
    simpa using h2
  let bT : V ⟶ U := p ≫ π ≫ y
  have hsb : s ≫ bT = y := by
    change s ≫ p ≫ π ≫ y = y
    rw [← Category.assoc, hsp, ← Category.assoc, heπ, Category.id_comp]
  have hfb : f₀.app (op V) bT = X.map p.op (X.map π.op x) := by
    have e1 : bT = p ≫ π ≫ y := rfl
    rw [e1, hnat, hnat]
  have hpe : Etale ((SCH).map p) := het.property_snd g
  have hfG := monAff_π_flat_lfp (M := M) ((SCH).obj Y)
  have hNG : IsLocallyNoetherian ((SCH).obj G) := by
    have := monAff_π_lft (M := M) ((SCH).obj Y)
    exact @LocallyOfFiniteType.isLocallyNoetherian _ _ (MonAff.π M ((SCH).obj Y)) (monAff_π_lft _) _
  have hNV : IsLocallyNoetherian ((SCH).obj V) :=
    LocallyOfFiniteType.isLocallyNoetherian ((SCH).map p)
  let v : (SCH).obj V := (SCH).map s t
  obtain ⟨_, ⟨W, hWa, rfl⟩, hyW, -⟩ := ((SCH).obj U).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((SCH).map y t)) isOpen_univ
  let W' : ((SCH).obj U).Opens := W
  have hvaT : (SCH).map aT v = (SCH).map y t := by
    change (SCH).map aT ((SCH).map s t) = _
    rw [← Scheme.Hom.comp_apply, ← (SCH).map_comp, hsaT]
  have hvb : (SCH).map bT v = (SCH).map y t := by
    change (SCH).map bT ((SCH).map s t) = _
    rw [← Scheme.Hom.comp_apply, ← (SCH).map_comp, hsb]
  let N₀ : ((SCH).obj V).Opens := (SCH).map aT ⁻¹ᵁ W' ⊓ (SCH).map bT ⁻¹ᵁ W'
  have hvN : v ∈ N₀ := ⟨by
      change (SCH).map aT v ∈ W'
      rw [hvaT]
      exact hyW, by
      change (SCH).map bT v ∈ W'
      rw [hvb]
      exact hyW⟩
  obtain ⟨_, ⟨A, hAa, rfl⟩, hvA, hAN⟩ := ((SCH).obj V).isBasis_affineOpens.exists_subset_of_mem_open
    hvN N₀.2
  let A' : ((SCH).obj V).Opens := A
  let V' := openObj A'
  have hV'a : IsAffine ((SCH).obj V') := hAa
  have hNV' : IsLocallyNoetherian ((SCH).obj V') := inferInstanceAs (IsLocallyNoetherian A'.toScheme)
  have hND : IsNoetherianRing Γ((SCH).obj V', ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let v' : (SCH).obj V' := ⟨v, hvA⟩
  let J₀ : V' ⟶ V := openJ A'
  let aP : V' ⟶ U := J₀ ≫ aT
  let bP : V' ⟶ U := J₀ ≫ bT
  let Wo := openObj W'
  have hraT : ∀ q, (SCH).map aP q ∈ W' := fun q => by
    have e := hom_congr' ((SCH).map_comp J₀ aT) q
    rw [e, Scheme.Hom.comp_apply]
    exact (hAN q.2).1
  have hrb : ∀ q, (SCH).map bP q ∈ W' := fun q => by
    have e := hom_congr' ((SCH).map_comp J₀ bT) q
    rw [e, Scheme.Hom.comp_apply]
    exact (hAN q.2).2
  obtain ⟨αm, hαm⟩ := exists_lift_open aP hraT
  obtain ⟨βm, hβm⟩ := exists_lift_open bP hrb
  have hWoa : IsAffine ((SCH).obj Wo) := hWa
  -- a map to `V'` with trivial test
  have hmono : ∀ {P : BigFppfOver B S hS} (r : P ⟶ V'), r ≫ aP = r ≫ bP →
      ∀ d : Γ((SCH).obj Wo, ⊤), ((SCH).map r).appTop.hom
        (((SCH).map αm).appTop.hom d - ((SCH).map βm).appTop.hom d) = 0 := by
    intro P r hrr d
    have e : r ≫ αm = r ≫ βm := by
      apply (SCH).map_injective
      apply (cancel_mono (iV W')).1
      rw [← Functor.map_comp, ← Functor.map_comp]
      change (SCH).map ((r ≫ αm) ≫ openJ W') = (SCH).map ((r ≫ βm) ≫ openJ W')
      rw [Category.assoc, Category.assoc, hαm, hβm, hrr]
    have e2 := congrArg (fun q : P ⟶ Wo => ((SCH).map q).appTop.hom d) e
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at e2
    rw [map_sub, sub_eq_zero]
    exact e2
  let q₀ : V' ⟶ G := J₀ ≫ p
  have hq₀π : ∀ {P : BigFppfOver B S hS} (r : P ⟶ V'),
      f₀.app _ (r ≫ aP) = X.map (r ≫ q₀).op a ∧
      f₀.app _ (r ≫ bP) = X.map ((r ≫ q₀) ≫ π).op x := by
    intro P r
    constructor
    · have e1 : r ≫ aP = (r ≫ J₀) ≫ aT := (Category.assoc _ _ _).symm
      rw [e1, hnat, hfa, ← Functor.map_comp_apply]
      rfl
    · have e1 : r ≫ bP = (r ≫ J₀) ≫ bT := (Category.assoc _ _ _).symm
      rw [e1, hnat, hfb, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
      rfl
  -- the section over the open of `Y`
  let Y₀O : ((SCH).obj Y).Opens := (SCH).map s ⁻¹ᵁ A'
  let Y₀ := openObj Y₀O
  obtain ⟨s₀, hs₀⟩ := exists_lift_open (V := A') (openJ Y₀O ≫ s) (fun q => by
    have e := hom_congr' ((SCH).map_comp (openJ Y₀O) s) q
    rw [e, Scheme.Hom.comp_apply]
    exact q.2)
  let t' : (SCH).obj Y₀ := ⟨t, hvA⟩
  have hs₀t : (SCH).map s₀ t' = v' := by
    apply Subtype.ext
    have e := hom_congr' (congrArg (SCH).map hs₀) t'
    have e1 := hom_congr' ((SCH).map_comp s₀ J₀) t'
    have e2 := hom_congr' ((SCH).map_comp (openJ Y₀O) s) t'
    exact e1.symm.trans (e.trans e2) |>.trans rfl
  have hs₀eq : s₀ ≫ aP = s₀ ≫ bP := by
    have h1 : s₀ ≫ aP = openJ Y₀O ≫ y := by
      change s₀ ≫ J₀ ≫ aT = _
      rw [← Category.assoc, hs₀, Category.assoc, hsaT]
    have h2 : s₀ ≫ bP = openJ Y₀O ≫ y := by
      change s₀ ≫ J₀ ≫ bT = _
      rw [← Category.assoc, hs₀, Category.assoc, hsb]
    rw [h1, h2]
  have hs₀c : ∀ m, ((SCH).map s₀).appTop.hom
      (((SCH).map q₀).appTop.hom (c m) - 1) = 0 := by
    intro m
    have h1 : APt.res (s₀ ≫ q₀).op c = 1 := by
      have e0 : s₀ ≫ q₀ = openJ Y₀O ≫ e := by
        change s₀ ≫ J₀ ≫ p = _
        rw [← Category.assoc, hs₀, Category.assoc, hsp]
      rw [e0, op_comp, APt.res_comp, hec]
      exact MonoidHom.ext fun _ => map_one ((fppfO B S hS).map (openJ Y₀O).op).hom
    have h2 := DFunLike.congr_fun h1 m
    rw [map_sub, map_one, sub_eq_zero]
    exact h2
  let R := ((SCH).obj V').presheaf.stalk v'
  have hgerm_nonunit : ∀ m, ((SCH).obj V').presheaf.germ ⊤ v' trivial
      (((SCH).map q₀).appTop.hom (c m) - 1) ∈ IsLocalRing.maximalIdeal R := by
    intro m
    exact germ_mem_max ((SCH).map s₀) t' hs₀t _ (hs₀c m)
  let bb : X.obj (op G) := X.map π.op x
  let diff : Γ((SCH).obj Wo, ⊤) → Γ((SCH).obj V', ⊤) := fun d =>
    ((SCH).map αm).appTop.hom d - ((SCH).map βm).appTop.hom d
  have hkey : ∀ d, ((SCH).obj V').presheaf.germ ⊤ v' trivial (diff d) = 0 := by
    intro d
    have hmem : ∀ i : ℕ, ((SCH).obj V').presheaf.germ ⊤ v' trivial (diff d) ∈
        IsLocalRing.maximalIdeal R ^ (i + 1) := by
      intro i
      let I₀ : Ideal R := IsLocalRing.maximalIdeal R ^ (i + 1)
      let mk₀ : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ I₀) := CommRingCat.ofHom (Ideal.Quotient.mk I₀)
      let ℓ₀ : Spec (.of (R ⧸ I₀)) ⟶ (SCH).obj V' := Spec.map mk₀ ≫ ((SCH).obj V').fromSpecStalk v'
      have hcm : IsClosedImmersion (Spec.map mk₀) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have hPc : B.Contains (Spec (.of (R ⧸ I₀))) :=
        lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact ℓ₀) V'.left.2
      let P : BigFppfOver B S hS := siteObject B S hS hPc (ℓ₀ ≫ structMap V')
      let ℓ : P ⟶ V' := Over.homMk (ObjectProperty.homMk ℓ₀) rfl
      have hℓa : ∀ c₀ : Γ((SCH).obj V', ⊤), ((SCH).map ℓ).appTop.hom c₀ =
          (Scheme.ΓSpecIso (.of (R ⧸ I₀))).inv.hom (Ideal.Quotient.mk I₀
            (((SCH).obj V').presheaf.germ ⊤ v' trivial c₀)) := fun c₀ =>
        ell_appTop ((SCH).obj V') v' I₀ c₀
      have hℓp : ∀ o : (SCH).obj P, (SCH).map ℓ o = v' := fun o =>
        ell_apply ((SCH).obj V') v' (Nat.succ_ne_zero i) o
      let h : APt (fppfO B S hS) M (op P) := APt.res (ℓ ≫ q₀).op c
      have hFn : IsFnPt E (i + 1) h := by
        intro e' _
        have h1 : (h (Multiplicative.ofAdd e') : Γ((SCH).obj P, ⊤)) - 1 =
            ((SCH).map ℓ).appTop.hom (((SCH).map q₀).appTop.hom (c (Multiplicative.ofAdd e')) - 1) := by
          rw [map_sub, map_one]
          rfl
        change ((h (Multiplicative.ofAdd e') : Γ((SCH).obj P, ⊤)) - 1) ^ (i + 1) = 0
        rw [h1, hℓa]
        exact ell_pow _ (Ideal.pow_mem_pow (hgerm_nonunit _) (i + 1))
      have hfx := hfix (i + 1) (Nat.succ_ne_zero i) ((ℓ ≫ q₀) ≫ π).op h hFn
      have hX₁ : f₀.app _ (ℓ ≫ aP) = f₀.app _ (ℓ ≫ bP) := by
        exact (hq₀π ℓ).1.trans ((hpull _).trans (hfx.trans (hq₀π ℓ).2.symm))
      obtain ⟨O, hO⟩ := hasOpenEqualizers_of_etale het P _ _ hX₁
      have hall : ∀ o, o ∈ O := by
        intro o
        let PB := pullback ℓ s₀
        have sq := (IsPullback.of_hasPullback ℓ s₀).map (SCH)
        obtain ⟨cz, hc1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (SCH).map ℓ)
          (g := (SCH).map s₀) o t' ((hℓp o).trans hs₀t.symm)
        have hpt : (SCH).map (pullback.fst ℓ s₀) (sq.isoPullback.inv cz) = o :=
          ((Scheme.Hom.comp_apply _ _ cz).symm.trans (hom_congr' sq.isoPullback_inv_fst cz)).trans hc1
        have hcomp : pullback.fst ℓ s₀ ≫ ℓ ≫ aP = pullback.fst ℓ s₀ ≫ ℓ ≫ bP := by
          rw [← Category.assoc, pullback.condition, Category.assoc, hs₀eq, ← Category.assoc,
            ← pullback.condition, Category.assoc]
        have := (hO PB (pullback.fst ℓ s₀)).1 hcomp ⟨sq.isoPullback.inv cz, rfl⟩
        rwa [hpt] at this
      have heq : ℓ ≫ aP = ℓ ≫ bP := by
        simpa using (hO P (𝟙 P)).2 (fun o _ => hall o)
      have h0 := hmono ℓ heq d
      rw [hℓa] at h0
      have h1 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (R ⧸ I₀))).inv).1
        (h0.trans (map_zero (Scheme.ΓSpecIso (.of (R ⧸ I₀))).inv.hom).symm)
      exact Ideal.Quotient.eq_zero_iff_mem.1 h1
    have hb : IsLocalRing.maximalIdeal R ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
    have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R) hb
    have : ((SCH).obj V').presheaf.germ ⊤ v' trivial (diff d) ∈
        (⨅ i : ℕ, IsLocalRing.maximalIdeal R ^ i) := by
      refine Ideal.mem_iInf.2 fun i => ?_
      exact Ideal.pow_le_pow_right (Nat.le_succ i) (hmem i)
    rw [hK] at this
    exact this
  let I : Ideal Γ((SCH).obj V', ⊤) := Ideal.span (Set.range diff)
  obtain ⟨S', hS'⟩ : I.FG := IsNoetherian.noetherian I
  have hger : I ≤ RingHom.ker (((SCH).obj V').presheaf.germ ⊤ v' trivial).hom :=
    Ideal.span_le.2 (by rintro _ ⟨d, rfl⟩; exact hkey d)
  obtain ⟨Ω, hvΩ, hΩ⟩ := exists_open_of_germ ((SCH).obj V') v' S' fun d hd =>
    hger (hS' ▸ Ideal.subset_span hd)
  have hΩI : I ≤ RingHom.ker Ω.ι.appTop.hom := by
    rw [← hS']
    exact Ideal.span_le.2 fun d hd => hΩ d hd
  have hΩeq : openJ Ω ≫ aP = openJ Ω ≫ bP := by
    have e : openJ Ω ≫ αm = openJ Ω ≫ βm := by
      apply (SCH).map_injective
      apply ext_of_isAffine
      ext d
      have h1 : Ω.ι.appTop.hom (diff d) = 0 := hΩI (Ideal.subset_span ⟨d, rfl⟩)
      rw [map_sub, sub_eq_zero] at h1
      rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
      exact h1
    rw [← hαm, ← hβm, ← Category.assoc, e, Category.assoc]
  have hq₀e : Etale ((SCH).map q₀) := by
    have : (SCH).map q₀ = iV A' ≫ (SCH).map p := Functor.map_comp _ _ _
    rw [this]
    infer_instance
  have hfin : X.map (openJ Ω ≫ q₀).op a = X.map (openJ Ω ≫ q₀).op bb := by
    refine (hq₀π (openJ Ω)).1.symm.trans (((congrArg (f₀.app _) hΩeq)).trans ((hq₀π (openJ Ω)).2.trans ?_))
    change _ = X.map (openJ Ω ≫ q₀).op (X.map π.op x)
    rw [op_comp, Functor.map_comp_apply]
  have hne := eqNear_of_flat hX q₀ Ω a bb hfin hvΩ
  have hpt : (SCH).map q₀ v' = (SCH).map e t := by
    have h1 := hom_congr' ((SCH).map_comp J₀ p) v'
    have h2 := hom_congr' ((SCH).map_comp s p) t
    have h3 : (SCH).map (s ≫ p) t = (SCH).map e t := by rw [hsp]
    exact h1.trans ((Scheme.Hom.comp_apply _ _ v').trans
      ((Scheme.Hom.comp_apply _ _ t).symm.trans (h2.symm.trans h3)))
  rw [hpt] at hne
  exact hne

end Unit

/-! ### `X_0 = ⋂ X^{F_n}` is closed, and equals `X^G` in the noetherian case -/

section Final

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The closed subspace `X_0 = ⋂_n X^{F_n}` of the printed proof of **Theorem A.1**. -/
def fnAll (act : AAction (fppfO B S hS) M X) (E : Set M) : Subfunctor X where
  obj T := {x | ∀ n, n ≠ 0 → x ∈ (fnFixed act E n).obj T}
  map {T T'} i x hx n hn := (fnFixed act E n).map i (hx n hn)

theorem isSheaf_fnAll (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (act : AAction (fppfO B S hS) M X) (E : Set M) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (fnAll act E).toFunctor := by
  have hX' := (isSheaf_iff_isSheaf_of_type _ _).mp hX
  refine (isSheaf_iff_isSheaf_of_type _ _).mpr ((Subfunctor.isSheaf_iff _ hX').mpr ?_)
  intro T x hx n hn T₁ s h hh
  have hc := (BigFppfOver.topology B S hS).pullback_stable s.unop hx
  refine (hX' _ hc).isSeparatedFor.ext fun W q hq => ?_
  have hq2 := hq n hn (T' := op W) (𝟙 _) (APt.res q.op h) (IsFnPt.res q.op hh)
  rw [act.map_smul]
  have ey : X.map q.op (X.map s x) = X.map (𝟙 (op W)) (X.map (q ≫ s.unop).op x) := by
    rw [CategoryTheory.Functor.map_id, op_comp, Functor.map_comp_apply]
    rfl
  rw [ey]
  exact hq2

/-- `X_0 = ⋂_n X^{F_n} → X` is a closed immersion. -/
theorem presheaf_fnAll_ι [AddGroup.FG M] (hX : IsAlgebraicSpace B S hS X)
    (act : AAction (fppfO B S hS) M X) {E : Set M} (hE : ∀ n, InfinitesimalE E n)
    (hT : TorsionResidue M S)
    (hfr : ∀ n, ∀ (A : Type u) [CommRing A], Module.Free A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A M ⧸ Jn A E n)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (fnAll act E).ι := by
  have : Countable M := countable_of_fg M
  have hM := contains_zmon_of_countable hS M
  refine presheaf_closed_of_ideals hX _ (isSheaf_fnAll hX.isSheaf act E) ?_
  intro U T f₀ het _ j _
  have h := fun (n : {n : ℕ // n ≠ 0}) => exists_ideal_chart (E := E) (n := n.1) hM het act j n.2
    (fun T₁ _ => hk_of T₁ (hE n.1) hT) (hfr _ _).1 (hfr _ _).2
  choose J hJ₁ hJ₂ using h
  refine ⟨⨆ n, J n, fun t hle n hn => hJ₁ ⟨n, hn⟩ t ((le_iSup J ⟨n, hn⟩).trans hle), fun t hmem => ?_⟩
  exact iSup_le fun n => hJ₂ n t (hmem n.1 n.2)

lemma mem_fixedPoints_of_cover (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (act : AAction (fppfO B S hS) M X) {T : BigFppfOver B S hS} (x : X.obj (op T)) {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T)
    (h : ∀ {W : BigFppfOver B S hS} (f : W ⟶ T), R f → X.map f.op x ∈ (fixedPoints act).obj (op W)) :
    x ∈ (fixedPoints act).obj (op T) := by
  have hX' := (isSheaf_iff_isSheaf_of_type _ _).mp hX
  intro T₁ s k
  have hc := (BigFppfOver.topology B S hS).pullback_stable s.unop hR
  refine (hX' _ hc).isSeparatedFor.ext fun W q hq => ?_
  have hq2 := h (q ≫ s.unop) hq (T' := op W) (𝟙 _) (APt.res q.op k)
  rw [act.map_smul]
  have ey : X.map q.op (X.map s x) = X.map (𝟙 (op W)) (X.map (q ≫ s.unop).op x) := by
    rw [CategoryTheory.Functor.map_id, op_comp, Functor.map_comp_apply]
    rfl
  rw [ey]
  exact hq2

/-- **Theorem A.1**, proof: `X_0 ⊆ X^G`, i.e. `X^G = ⋂ X^{F_n}`, in case (i): `S` locally noetherian
and `X` with charts locally of finite type over `S`. -/
theorem mem_fixedPoints_of_fnAll [AddGroup.FG M] [IsLocallyNoetherian S]
    (hX : IsAlgebraicSpace B S hS X) (hC : ChartsOfFiniteType X)
    (act : AAction (fppfO B S hS) M X) {E : Set M} (hE : ∀ n, InfinitesimalE E n)
    (hT : TorsionResidue M S)
    (hfr : ∀ n, ∀ (A : Type u) [CommRing A], Module.Free A (AddMonoidAlgebra A M ⧸ Jn A E n) ∧
      Module.Finite A (AddMonoidAlgebra A M ⧸ Jn A E n))
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : X.obj T) (hx : x ∈ (fnAll act E).obj T) :
    x ∈ (fixedPoints act).obj T := by
  have : Countable M := countable_of_fg M
  have hM := contains_zmon_of_countable hS M
  have hirr := irreducibleFibres_of_torsionResidue M S hT
  have hP := presheaf_fnAll_ι hX act hE hT hfr
  obtain ⟨U, f₀, hs, het⟩ := hX.exists_atlas
  have hLU : LocallyOfFiniteType U.hom.hom := hC U f₀ het
  have hNS : IsLocallyNoetherian (B.obj hS).obj := inferInstanceAs (IsLocallyNoetherian S)
  have hNU : IsLocallyNoetherian ((SCH).obj U) := LocallyOfFiniteType.isLocallyNoetherian U.hom.hom
  have repF := hP.rep
  let Wz := repF.pullback f₀
  let j' : Wz ⟶ U := repF.snd f₀
  have hcj : IsClosedImmersion ((SCH).map j') := hP.property_snd f₀
  have hNW : IsLocallyNoetherian ((SCH).obj Wz) := LocallyOfFiniteType.isLocallyNoetherian ((SCH).map j')
  have hpbF := repF.isPullback f₀
  have hj'mem : f₀.app (op Wz) j' ∈ (fnAll act E).obj (op Wz) := by
    have hw := congrArg (fun q => q.app (op Wz) (𝟙 Wz)) hpbF.w
    have e0 : f₀.app (op Wz) j' = ((repF.fst f₀).app (op Wz) (𝟙 Wz)).1 := by
      have e1 : (yoneda.map j' ≫ f₀).app (op Wz) (𝟙 Wz) = f₀.app (op Wz) (𝟙 Wz ≫ j') := rfl
      rw [Category.id_comp] at e1
      exact e1.symm.trans hw.symm
    rw [e0]
    exact ((repF.fst f₀).app (op Wz) (𝟙 Wz)).2
  -- the universal point of `X_0` on the chart is fixed
  have hfixW : f₀.app (op Wz) j' ∈ (fixedPoints act).obj (op Wz) := by
    have heq := eq_of_eqNear_unit hM hirr hX.isSheaf act (f₀.app (op Wz) j')
      (eqNear_unit hM hX.isSheaf het act j' hj'mem)
    intro T' s h
    let L := gLift hM s.unop h
    have h1 := congrArg (X.map L.op) heq
    rw [act.map_smul, res_gLift, ← Functor.map_comp_apply] at h1
    have e : (gπ hM Wz).op ≫ L.op = s := by
      rw [← op_comp, gLift_π]
      rfl
    rwa [e] at h1
  -- étale locally, a point of `X_0` lifts to the chart
  let g₀ : yoneda.obj (unop T) ⟶ X := yonedaEquiv.symm x
  let rep₀ := het.rep
  let T' := rep₀.pullback g₀
  let q : T' ⟶ unop T := rep₀.snd g₀
  let u : T' ⟶ U := rep₀.fst' g₀
  have hu : f₀.app (op T') u = X.map q.op x := by
    have h2 : yoneda.map u ≫ f₀ = yoneda.map q ≫ g₀ := by
      rw [Functor.relativelyRepresentable.map_fst']
      exact rep₀.w g₀
    have h3 := congrArg (fun k => k.app (op T') (𝟙 T')) h2
    have e1 : (yoneda.map u ≫ f₀).app (op T') (𝟙 T') = f₀.app (op T') (𝟙 T' ≫ u) := rfl
    rw [Category.id_comp] at e1
    refine e1.symm.trans (h3.trans ?_)
    change g₀.app (op T') (𝟙 T' ≫ q) = _
    rw [Category.id_comp]
    simp [g₀, yonedaEquiv]
  have hsq : Surjective ((SCH).map q) := hs.property_snd g₀
  have heq : Etale ((SCH).map q) := het.property_snd g₀
  have hcover := Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS q hsq inferInstance inferInstance
  have hxT : (unop T : BigFppfOver B S hS) = unop T := rfl
  suffices hs : ∀ {W : BigFppfOver B S hS} (f : W ⟶ unop T), (Sieve.generate (Presieve.singleton q)) f →
      X.map f.op x ∈ (fixedPoints act).obj (op W) by
    intro T₁ s k
    exact mem_fixedPoints_of_cover (T := unop T) hX.isSheaf act x hcover hs s k
  intro W f hf
  obtain ⟨Z', v, g, hg, rfl⟩ := hf
  cases hg
  -- `x|_{T'}` is in `X_0`, so `u` factors through `Wz`
  have hum : f₀.app (op T') u ∈ (fnAll act E).obj (op T') := by
    rw [hu]
    exact (fnAll act E).map q.op hx
  let i₀ : yoneda.obj T' ⟶ (fnAll act E).toFunctor :=
    yonedaEquiv.symm ⟨f₀.app (op T') u, hum⟩
  have wF : i₀ ≫ (fnAll act E).ι = yoneda.map u ≫ f₀ := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    have e : yonedaEquiv i₀ = ⟨f₀.app (op T') u, hum⟩ := Equiv.apply_symm_apply _ _
    rw [e]
    exact congrArg (f₀.app (op T')) (by simp [yonedaEquiv] : u = yonedaEquiv (yoneda.map u))
  let c : T' ⟶ Wz := repF.lift i₀ u wF
  have hc : c ≫ j' = u := repF.lift_snd _ _ _
  have hfixT' : X.map q.op x ∈ (fixedPoints act).obj (op T') := by
    rw [← hu, ← hc]
    have : f₀.app (op T') (c ≫ j') = X.map c.op (f₀.app (op Wz) j') :=
      NatTrans.naturality_apply f₀ c.op j'
    rw [this]
    intro T₁ s k
    exact (fixedPoints act).map c.op hfixW s k
  have e : X.map (v ≫ q).op x = X.map v.op (X.map q.op x) := by
    rw [op_comp, Functor.map_comp_apply]
  rw [e]
  intro T₁ s k
  exact (fixedPoints act).map v.op hfixT' s k

/-- **Theorem A.1**, closedness, case (i), for `D(M)` with connected fibres (`TorsionResidue`):
`X^G → X` is a closed immersion. -/
theorem thmA1_closed [AddGroup.FG M] [IsLocallyNoetherian S]
    (hX : IsAlgebraicSpace B S hS X) (hC : ChartsOfFiniteType X)
    (act : AAction (fppfO B S hS) M X) (hT : TorsionResidue M S) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (fixedPoints act).ι := by
  obtain ⟨E, hE⟩ := exists_E M
  have hA := fun n => (hE n).1
  have hF := fun n => (hE n).2
  have heq : fixedPoints act = fnAll act E := by
    refine le_antisymm ?_ ?_
    · intro T x hx n _
      exact fixedPoints_le_fnFixed act E n T hx
    intro T x hx
    exact mem_fixedPoints_of_fnAll hX hC act hA hT hF x hx
  rw [heq]
  exact presheaf_fnAll_ι hX act hA hT hF

/-- **Theorem A.1**, FPR assertion by the printed route, case (i), for `D(M)` with connected fibres:
every étale equivariant morphism `U → X` is fixed point reflecting. -/
theorem thmA1_isFPR [AddGroup.FG M] [IsLocallyNoetherian S]
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U) (hC : ChartsOfFiniteType U)
    {actU : AAction (fppfO B S hS) M U} {actX : AAction (fppfO B S hS) M X} {f : U ⟶ X}
    (hT : TorsionResidue M S) (hf : IsEquivariant actU actX f)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f) : IsFPR hf := by
  obtain ⟨E, hE⟩ := exists_E M
  have hA := fun n => (hE n).1
  have hF := fun n => (hE n).2
  refine (isFPR_iff hf).2 fun T x hx => mem_fixedPoints_of_fnAll hU hC actU hA hT hF x fun n _ => ?_
  exact mem_fnFixed_of_etale (hA n) hT hf het x (fixedPoints_le_fnFixed actX E n T hx)

end Final

end Site

end AlgMag.AppA3

#print axioms AlgMag.AppA3.exists_lift_nil
#print axioms AlgMag.AppA3.mem_fnFixed_of_etale
#print axioms AlgMag.AppA3.isFPR_of_iInf_fnFixed
#print axioms AlgMag.AppA3.exists_ideal_chart
#print axioms AlgMag.AppA3.exists_chart_lift
#print axioms AlgMag.AppA3.baseR_mem_Jn_iff
#print axioms AlgMag.AppA3.isSheaf_fnFixed
#print axioms AlgMag.AppA3.exists_E
#print axioms AlgMag.AppA3.lemmaA3
#print axioms AlgMag.AppA3.presheaf_fnAll_ι
#print axioms AlgMag.AppA3.mem_fixedPoints_of_fnAll
#print axioms AlgMag.AppA3.thmA1_closed
#print axioms AlgMag.AppA3.thmA1_isFPR
