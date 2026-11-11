/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartThickAffine
import AlgMag.AppendixA

/-!
# Points of the thickenings

Let `o : P → X` be a closed immersion and `𝒥(x)` the ideal of `T ×_X P` in `T`, for `x ∈ X(T)`.

* `AlgMag.ChartMain.mem_thickening_iff`: `x ∈ X_n(T)` iff `𝒥(x)^{n+1} = 0`.
* `AlgMag.ChartMain.exists_isPullback_thickening`: for every `ψ : T → X`, the subscheme
  `V(𝒥(ψ)^{n+1})` of `T` is `T ×_X X_n`.
* `AlgMag.ChartMain.idealOf_smul`: `𝒥(h • x) = 𝒥(x)` for an equivariant `o`.
* `AlgMag.ChartMain.thickeningAction`: the restricted action on `X_n`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartMain

section Ideals

variable {T W : Scheme.{u}}

lemma comap_eq_bot_iff (I : W.IdealSheafData) (f : T ⟶ W) : I.comap f = ⊥ ↔ I ≤ f.ker := by
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff]

lemma factors_mk_subschemeι_iff (I : W.IdealSheafData) (f : T ⟶ W) :
    (Subobject.mk I.subschemeι).Factors f ↔ I.comap f = ⊥ := by
  rw [comap_eq_bot_iff, Subobject.mk_factors_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact I.ker_subschemeι.symm.le.trans (Scheme.Hom.le_ker_comp g I.subschemeι)
  · intro h
    have h' : I.subschemeι.ker ≤ f.ker := I.ker_subschemeι.le.trans h
    have hc := IsClosedImmersion.lift_fac I.subschemeι f h'
    exact ⟨_, hc⟩

end Ideals

section Points

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {o : P ⟶ X} (ho : ClosedP o)

local notation "SCH" => BigFppfOver.toScheme B S hS

lemma yoneda_map_comp_pt {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : X.obj (op T)) :
    yoneda.map g ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.map g.op x) := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_apply]

/-- A surjective étale map detects the vanishing of an ideal. -/
lemma eq_bot_of_comap_eq_bot {T T' : BigFppfOver B S hS} (q : T' ⟶ T)
    (hqs : Surjective ((SCH).map q)) (hqe : Etale ((SCH).map q))
    (K : ((SCH).obj T).IdealSheafData) (hK : K.comap ((SCH).map q) = ⊥) : K = ⊥ := by
  have hci : IsClosedImmersion (Subobject.mk K.subschemeι).arrow := mk_arrow_closed _
  have him : AlgebraicGeometry.IsImmersion (Subobject.mk K.subschemeι).arrow := inferInstance
  have hmem : (𝟙 T : T ⟶ T) ∈ (Space.subschemePoints B S hS (Subobject.mk K.subschemeι)).obj (op T) := by
    refine Space.mem_subschemePoints_of_sieveOfSection B S hS
      (Space.subschemeι B S hS _ him) (Iso.refl _) (Category.id_comp _) (𝟙 T)
      ((BigFppfOver.topology B S hS).superset_covering ?_
        (Space.sieve_generate_singleton_mem_topology_over B S hS q hqs hqe))
    rintro Z r ⟨Y, a, b, hb, rfl⟩
    cases hb
    have e : (yoneda.obj T).map (a ≫ q).op (𝟙 T) = a ≫ q := by simp
    change (yoneda.obj T).map (a ≫ q).op (𝟙 T) ∈ _
    rw [e]
    refine (Space.mem_subschemePoints_iff B S hS _).2 ?_
    have : (Subobject.mk K.subschemeι).Factors ((SCH).map q) :=
      (factors_mk_subschemeι_iff K _).2 hK
    rw [Functor.map_comp]
    exact Subobject.factors_of_factors_right _ this
  have := (factors_mk_subschemeι_iff K _).1 ((Space.mem_subschemePoints_iff B S hS _).1 hmem)
  rwa [CategoryTheory.Functor.map_id, Scheme.IdealSheafData.comap_id] at this

variable {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}

/-- **§2**: `x ∈ X_n(T)` iff `𝒥(x)^{n+1} = 0`. -/
theorem mem_thickening_iff
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (n : ℕ) {T : BigFppfOver B S hS} (x : X.obj (op T)) :
    x ∈ (thickening ho φ n).obj (op T) ↔ idealOf ho (yonedaEquiv.symm x) ^ (n + 1) = ⊥ := by
  have key : ∀ {T' : BigFppfOver B S hS} (f : T' ⟶ U) (g : T' ⟶ T),
      φ.app (op T') f = X.map g.op x →
      (idealOf ho φ ^ (n + 1)).comap ((SCH).map f) =
        (idealOf ho (yonedaEquiv.symm x) ^ (n + 1)).comap ((SCH).map g) := by
    intro T' f g h
    have hw : yoneda.map f ≫ φ = yoneda.map g ≫ yonedaEquiv.symm x := by
      rw [yoneda_map_comp_pt, ← h]
      apply yonedaEquiv.injective
      simp [yonedaEquiv_apply]
    rw [IdealPow.comap_pow, IdealPow.comap_pow, ← idealOf_comp, ← idealOf_comp, hw]
  constructor
  · intro hx
    let t := yonedaEquiv.symm x
    let q := hs.rep.snd t
    have hqs : Surjective ((SCH).map q) := hs.property_snd t
    have hqe : Etale ((SCH).map q) := he.property_snd t
    let f : hs.rep.pullback t ⟶ U := yoneda.preimage (hs.rep.fst t)
    have hf : yoneda.map f ≫ φ = yoneda.map q ≫ t := by
      rw [Functor.map_preimage]; exact hs.rep.w t
    have hfx : φ.app (op _) f = X.map q.op x := by
      have e := congrArg yonedaEquiv hf
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at e
      refine e.trans ?_
      simp [t]
    refine eq_bot_of_comap_eq_bot q hqs hqe _ ?_
    rw [← key f q hfx]
    exact (factors_mk_subschemeι_iff _ _).1
      ((Space.mem_subschemePoints_iff B S hS _).1 (hx _ q f hfx))
  · intro hx T' g f hf
    refine (Space.mem_subschemePoints_iff B S hS _).2 ((factors_mk_subschemeι_iff _ _).2 ?_)
    rw [key f g hf, hx, Scheme.IdealSheafData.comap_bot]

variable (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- The thickenings increase. -/
theorem thickening_mono {m n : ℕ} (h : m ≤ n) : thickening ho φ m ≤ thickening ho φ n := by
  rintro ⟨T⟩ x hx
  rw [mem_thickening_iff ho hs he] at hx ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show m + k + 1 = (m + 1) + k by omega, pow_add, hx, Scheme.IdealSheafData.bot_mul]

include hs he in
/-- The base change of `X_n` along `ψ : T → X` is `V(𝒥(ψ)^{n+1})`. -/
theorem preimage_thickening {T : BigFppfOver B S hS} (ψ : yoneda.obj T ⟶ X) (n : ℕ) :
    (thickening ho φ n).preimage ψ = Space.subschemePoints B S hS (chartZ ho ψ n) := by
  refine le_antisymm (fun T' g hg => ?_) (fun T' g hg => ?_)
  all_goals
    obtain ⟨T'⟩ := T'
    have hc : yonedaEquiv.symm (ψ.app (op T') g) = yoneda.map g ≫ ψ := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      simp
    have hk : idealOf ho (yonedaEquiv.symm (ψ.app (op T') g)) ^ (n + 1) =
        (idealOf ho ψ ^ (n + 1)).comap ((SCH).map g) := by
      rw [hc, idealOf_comp, IdealPow.comap_pow]
  · have h1 := (mem_thickening_iff ho hs he n _).1 hg
    rw [hk] at h1
    exact (Space.mem_subschemePoints_iff B S hS _).2 ((factors_mk_subschemeι_iff _ _).2 h1)
  · refine (mem_thickening_iff ho hs he n _).2 ?_
    rw [hk]
    exact (factors_mk_subschemeι_iff _ _).1 ((Space.mem_subschemePoints_iff B S hS _).1 hg)

/-- `V(𝒥(ψ)^{n+1})`, as an object of the site. -/
noncomputable def thickChart {T : BigFppfOver B S hS} (ψ : yoneda.obj T ⟶ X) (n : ℕ) :
    BigFppfOver B S hS :=
  haveI := chartZ_arrow_closed ho ψ n
  Space.subschemeObject B S hS (chartZ ho ψ n) inferInstance

/-- The inclusion `V(𝒥(ψ)^{n+1}) → T`. -/
noncomputable def thickChartι {T : BigFppfOver B S hS} (ψ : yoneda.obj T ⟶ X) (n : ℕ) :
    thickChart ho ψ n ⟶ T :=
  haveI := chartZ_arrow_closed ho ψ n
  Space.subschemeι B S hS (chartZ ho ψ n) inferInstance

lemma thickChartι_closed {T : BigFppfOver B S hS} (ψ : yoneda.obj T ⟶ X) (n : ℕ) :
    IsClosedImmersion ((SCH).map (thickChartι ho ψ n)) :=
  chartZ_arrow_closed ho ψ n

lemma mk_arrow_ker {A W : Scheme.{u}} (i : A ⟶ W) [Mono i] : (Subobject.mk i).arrow.ker = i.ker := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk i, Scheme.Hom.ker_comp_of_isIso]

lemma ker_thickChartι {T : BigFppfOver B S hS} (ψ : yoneda.obj T ⟶ X) (n : ℕ) :
    ((SCH).map (thickChartι ho ψ n)).ker = idealOf ho ψ ^ (n + 1) := by
  change (Subobject.mk (idealOf ho ψ ^ (n + 1)).subschemeι).arrow.ker = _
  rw [mk_arrow_ker]
  exact Scheme.IdealSheafData.ker_subschemeι _

include hs he in
/-- `V(𝒥(ψ)^{n+1})` is the base change of `X_n` to `T`. -/
theorem exists_isPullback_thickening {T : BigFppfOver B S hS} (ψ : yoneda.obj T ⟶ X) (n : ℕ) :
    ∃ k : yoneda.obj (thickChart ho ψ n) ⟶ (thickening ho φ n).toFunctor,
      IsPullback k (yoneda.map (thickChartι ho ψ n)) (thickening ho φ n).ι ψ := by
  have hcl := thickChartι_closed ho ψ n
  have hmono : Mono (thickChartι ho ψ n) := (SCH).mono_of_mono_map inferInstance
  have key : (thickening ho φ n).preimage ψ = Subfunctor.range (yoneda.map (thickChartι ho ψ n)) :=
    (preimage_thickening ho hs he ψ n).trans
      (Space.subschemePoints_eq_range B S hS (thickChartι ho ψ n) (Iso.refl _) (Category.id_comp _))
  have hkι : Subfunctor.lift (yoneda.map (thickChartι ho ψ n)) key.ge ≫
      ((thickening ho φ n).preimage ψ).ι = yoneda.map (thickChartι ho ψ n) := Subfunctor.lift_ι _ _
  have hkiso := Subfunctor.isIso_lift key.ge key.le
  have h₁ := Subfunctor.isPullback_fromPreimage (thickening ho φ n) ψ
  refine ⟨Subfunctor.lift (yoneda.map (thickChartι ho ψ n)) key.ge ≫
    (thickening ho φ n).fromPreimage ψ, ?_⟩
  refine IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, (thickening ho φ n).fromPreimage_ι ψ, ← Category.assoc, hkι]⟩
    (asIso (Subfunctor.lift (yoneda.map (thickChartι ho ψ n)) key.ge) ≪≫ h₁.isoPullback) ?_ ?_
  · simp [h₁.isoPullback_hom_fst]
  · simp [h₁.isoPullback_hom_snd, hkι]

/-- A point of `X` through `P` has trivial ideal. -/
lemma idealOf_eq_bot_of_factors {T : BigFppfOver B S hS} (p : yoneda.obj T ⟶ P) :
    idealOf ho (p ≫ o) = ⊥ := by
  let l : T ⟶ ho.rep.pullback (p ≫ o) := ho.rep.lift p (𝟙 T) (by simp)
  have hl : l ≫ ho.rep.snd (p ≫ o) = 𝟙 T := ho.rep.lift_snd _ _ _
  have h := Scheme.Hom.le_ker_comp ((SCH).map l) ((SCH).map (ho.rep.snd (p ≫ o)))
  rw [← Functor.map_comp, hl, CategoryTheory.Functor.map_id] at h
  refine le_bot_iff.1 (h.trans ?_)
  simp

/-- `𝒥(x) = 0` iff `x` factors through `P`. -/
lemma exists_factors_of_idealOf_eq_bot {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ X)
    (h : idealOf ho t = ⊥) : ∃ p : yoneda.obj T ⟶ P, p ≫ o = t := by
  have hc := snd_closed ho t
  have hk : ((SCH).map (ho.rep.snd t)).ker = Scheme.Hom.ker (𝟙 ((SCH).obj T)) := by
    rw [show ((SCH).map (ho.rep.snd t)).ker = idealOf ho t from rfl, h]
    simp
  have hiso := IsClosedImmersion.isIso_lift ((SCH).map (ho.rep.snd t)) (𝟙 ((SCH).obj T)) hk
  have e := IsClosedImmersion.lift_fac ((SCH).map (ho.rep.snd t)) (𝟙 ((SCH).obj T)) hk.le
  have hi : IsIso ((SCH).map (ho.rep.snd t)) := by
    have : IsIso (IsClosedImmersion.lift ((SCH).map (ho.rep.snd t)) (𝟙 ((SCH).obj T)) hk.le ≫
      (SCH).map (ho.rep.snd t)) := by rw [e]; infer_instance
    exact IsIso.of_isIso_comp_left (IsClosedImmersion.lift _ _ hk.le) _
  have hi' : IsIso (ho.rep.snd t) := isIso_of_reflects_iso _ (SCH)
  refine ⟨yoneda.map (inv (ho.rep.snd t)) ≫ ho.rep.fst t, ?_⟩
  rw [Category.assoc, ho.rep.w t, ← Category.assoc, ← Functor.map_comp]
  simp

include ho in
/-- A closed immersion of presheaves is a monomorphism. -/
lemma mono_of_closedP : Mono o := by
  refine (NatTrans.mono_iff_mono_app _).2 fun ⟨T⟩ => (mono_iff_injective _).2 fun a b hab => ?_
  have hab' : yonedaEquiv.symm a ≫ o = yonedaEquiv.symm b ≫ o := by
    apply yonedaEquiv.injective
    simpa [yonedaEquiv_comp] using hab
  let t := yonedaEquiv.symm a ≫ o
  let la : T ⟶ ho.rep.pullback t := ho.rep.lift (yonedaEquiv.symm a) (𝟙 T) (by simp [t])
  let lb : T ⟶ ho.rep.pullback t := ho.rep.lift (yonedaEquiv.symm b) (𝟙 T) (by simp [t, hab'])
  have hc := snd_closed ho t
  have hm : Mono (ho.rep.snd t) := (SCH).mono_of_mono_map inferInstance
  have hsa : la ≫ ho.rep.snd t = 𝟙 T := ho.rep.lift_snd _ _ _
  have hsb : lb ≫ ho.rep.snd t = 𝟙 T := ho.rep.lift_snd _ _ _
  have hlab : la = lb := (cancel_mono (ho.rep.snd t)).1 (hsa.trans hsb.symm)
  have hfa : yoneda.map la ≫ ho.rep.fst t = yonedaEquiv.symm a := ho.rep.lift_fst _ _ _
  have hfb : yoneda.map lb ≫ ho.rep.fst t = yonedaEquiv.symm b := ho.rep.lift_fst _ _ _
  rw [hlab, hfb] at hfa
  exact (yonedaEquiv.symm.injective hfa).symm

variable {M : Type u} [AddCommGroup M] {actP : AAction (fppfO B S hS) M P}
  {actX : AAction (fppfO B S hS) M X}

lemma idealOf_le_smul (hequiv : IsEquivariant actP actX o) {T : BigFppfOver B S hS}
    (h : APt (fppfO B S hS) M (op T)) (x : X.obj (op T)) :
    idealOf ho (yonedaEquiv.symm x) ≤ idealOf ho (yonedaEquiv.symm (actX.smul h x)) := by
  let t := yonedaEquiv.symm x
  let t' := yonedaEquiv.symm (actX.smul h x)
  let P' := ho.rep.pullback t'
  let q' := ho.rep.snd t'
  have hc := snd_closed ho t
  let hq := APt.res q'.op h
  let y : P.obj (op P') := actP.smul (APt.inv hq) (yonedaEquiv (ho.rep.fst t'))
  have hy : yonedaEquiv.symm y ≫ o = yoneda.map q' ≫ t := by
    apply yonedaEquiv.injective
    have hw : o.app (op P') (yonedaEquiv (ho.rep.fst t')) = X.map q'.op (actX.smul h x) := by
      have e := congrArg yonedaEquiv (ho.rep.w t')
      rw [yonedaEquiv_comp, yoneda_map_comp_pt, Equiv.apply_symm_apply] at e
      exact e
    rw [yonedaEquiv_comp, yoneda_map_comp_pt, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change o.app _ y = _
    rw [hequiv, hw, actX.map_smul, ← actX.mul_smul, APt.inv_mul, actX.one_smul]
  let l : P' ⟶ ho.rep.pullback t := ho.rep.lift (yonedaEquiv.symm y) q' hy
  have hl : l ≫ ho.rep.snd t = q' := ho.rep.lift_snd _ _ _
  have := Scheme.Hom.le_ker_comp ((SCH).map l) ((SCH).map (ho.rep.snd t))
  rw [← Functor.map_comp, hl] at this
  exact this

/-- **§2**: `𝒥(h • x) = 𝒥(x)`, for an equivariant closed immersion. -/
theorem idealOf_smul (hequiv : IsEquivariant actP actX o) {T : BigFppfOver B S hS}
    (h : APt (fppfO B S hS) M (op T)) (x : X.obj (op T)) :
    idealOf ho (yonedaEquiv.symm (actX.smul h x)) = idealOf ho (yonedaEquiv.symm x) := by
  refine le_antisymm ?_ (idealOf_le_smul ho hequiv h x)
  have := idealOf_le_smul ho hequiv (APt.inv h) (actX.smul h x)
  rwa [← actX.mul_smul, APt.inv_mul, actX.one_smul] at this

include hs he in
/-- `X_n` is stable under the action. -/
lemma smul_mem_thickening (hequiv : IsEquivariant actP actX o) (n : ℕ)
    {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) {x : X.obj T}
    (hx : x ∈ (thickening ho φ n).obj T) : actX.smul h x ∈ (thickening ho φ n).obj T := by
  obtain ⟨T⟩ := T
  rw [mem_thickening_iff ho hs he] at hx ⊢
  rwa [idealOf_smul ho hequiv]

/-- **§2**: the action of `D(M)` restricted to `X_n`. -/
def thickeningAction (hequiv : IsEquivariant actP actX o) (n : ℕ) :
    AAction (fppfO B S hS) M (thickening ho φ n).toFunctor where
  smul h x := ⟨actX.smul h x.1, smul_mem_thickening ho hs he hequiv n h x.2⟩
  one_smul x := Subtype.ext (actX.one_smul x.1)
  mul_smul g h x := Subtype.ext (actX.mul_smul g h x.1)
  map_smul f h x := Subtype.ext (actX.map_smul f h x.1)

end Points

end AlgMag.ChartMain
