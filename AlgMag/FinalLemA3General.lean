/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.AppendixA3

/-!
# Lemma A.3 of *Algebraic Magnetism*, general `F` acting on an algebraic space

`lemmaA3` of `AppendixA3` is for `F = F_n ⊆ D(M)`. Here `F` is a pointed sheaf on the big fppf site over `S`, finite locally free over `S` and
infinitesimal, in the form `PointedFinFlat`: over each affine `T`, `F_T` is an affine scheme, its functions are a finite projective `Γ(T)`-algebra, and the unit
section is a nil-thickening. An action is a morphism `F × X → X` on which the unit acts trivially, as printed (no group law).
The printed proof is followed: the stabilizer is closed in `F × X` (étale sections lift along the nil-thickening, then the diagonal of a chart is open and contains the
unit section), and `J = im(I ⊗ A^∨ → O_X)` cuts out the fixed points. The conclusion that `X^F → X` is a closed immersion
contains the representability, so the Weil restriction of the printed first sentence is not used.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final.A3G

open AlgMag.AppR AlgMag.AppA3

/-- Dual basis form of "finite projective": an element all of whose contractions die, dies in any algebra over the base. -/
lemma map_eq_zero_of_contr {R E R' : Type*} [CommRing R] [CommRing E] [CommRing R'] (ρ : R →+* E)
    (τ : R →+* R') (φ : E →+* R') (hφ : φ.comp ρ = τ)
    (hfin : letI := ρ.toAlgebra; Module.Finite R E) (hpr : letI := ρ.toAlgebra; Module.Projective R E)
    (w : E) (hw : letI := ρ.toAlgebra; ∀ ℓ : E →ₗ[R] R, τ (ℓ w) = 0) : φ w = 0 := by
  letI := ρ.toAlgebra
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R E
  obtain ⟨i, hi⟩ := Module.projective_lifting_property p LinearMap.id hp
  have hw1 : w = ∑ j, ρ (i w j) * p (Pi.single j 1) := by
    have h0 : p (i w) = w := LinearMap.congr_fun hi w
    conv_lhs => rw [← h0, pi_eq_sum_univ' (i w), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  rw [hw1, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h0 : τ (i w j) = 0 := hw ((LinearMap.proj j).comp i)
  rw [map_mul, ← RingHom.comp_apply, hφ, h0, zero_mul]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A pointed `S`-space `(F, e)`, finite locally free and infinitesimal over `S`, read on affine `T`: `F_T` is the affine scheme `obj T`, with universal
point `c`, finite projective functions, unit section `sec` a nil-thickening, and the linear dual of its functions compatible with base change. -/
structure PointedFinFlat (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The section `e`. -/
  pt : ∀ U, F.obj U
  map_pt : ∀ {U V} (f : U ⟶ V), F.map f (pt U) = pt V
  /-- `F_T`. -/
  obj : ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)], BigFppfOver B S hS
  isAffine_obj : ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)], IsAffine ((SCH).obj (obj T))
  π : ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)], obj T ⟶ T
  c : ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)], F.obj (op (obj T))
  /-- The classifying map of a point of `F` over `Y → T`. -/
  lift : ∀ {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] {Y : BigFppfOver B S hS} (_ : Y ⟶ T),
    F.obj (op Y) → (Y ⟶ obj T)
  lift_π : ∀ {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] {Y : BigFppfOver B S hS} (τ : Y ⟶ T)
    (h : F.obj (op Y)), lift τ h ≫ π T = τ
  lift_c : ∀ {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] {Y : BigFppfOver B S hS} (τ : Y ⟶ T)
    (h : F.obj (op Y)), F.map (lift τ h).op (c T) = h
  lift_uniq : ∀ {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] {Y : BigFppfOver B S hS} (r : Y ⟶ obj T),
    r = lift (r ≫ π T) (F.map r.op (c T))
  finite : ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)],
    letI := ((SCH).map (π T)).appTop.hom.toAlgebra; Module.Finite Γ((SCH).obj T, ⊤) Γ((SCH).obj (obj T), ⊤)
  projective : ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)],
    letI := ((SCH).map (π T)).appTop.hom.toAlgebra; Module.Projective Γ((SCH).obj T, ⊤) Γ((SCH).obj (obj T), ⊤)
  /-- `F` is infinitesimal: the kernel of the unit section is nilpotent. -/
  nil : ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)], ∃ k : ℕ,
    RingHom.ker ((SCH).map (lift (𝟙 T) (pt (op T)))).appTop.hom ^ (k + 1) = ⊥
  /-- The formation of the linear dual commutes with base change. -/
  bc : ∀ {T T'' : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj T'')] (t : T'' ⟶ T)
    (w : Γ((SCH).obj (obj T), ⊤)),
    ((SCH).map (lift (π T'' ≫ t) (c T''))).appTop.hom w = 0 →
    letI := ((SCH).map (π T)).appTop.hom.toAlgebra
    ∀ ℓ : Γ((SCH).obj (obj T), ⊤) →ₗ[Γ((SCH).obj T, ⊤)] Γ((SCH).obj T, ⊤), ((SCH).map t).appTop.hom (ℓ w) = 0

/-- An action of the pointed `F` on `X`: a morphism `F × X → X`, through which the section acts trivially. -/
structure PointedAction (F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (P : PointedFinFlat F) where
  smul : ∀ {U}, F.obj U → X.obj U → X.obj U
  pt_smul : ∀ {U} (x : X.obj U), smul (P.pt U) x = x
  map_smul : ∀ {U V} (f : U ⟶ V) (h : F.obj U) (x : X.obj U), X.map f (smul h x) = smul (F.map f h) (X.map f x)

variable {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {P : PointedFinFlat F}

/-- The functor of `F`-fixed points: the maps `T → X` equivariant for the trivial action on `T`. -/
def fFixed (act : PointedAction F X P) : Subfunctor X where
  obj T := {x | ∀ {T' : (BigFppfOver B S hS)ᵒᵖ} (s : T ⟶ T') (h : F.obj T'), act.smul h (X.map s x) = X.map s x}
  map {T T'} i x hx {T''} s h := by
    have := hx (i ≫ s) h
    rwa [Functor.map_comp_apply] at this

/-- The functor of `F`-fixed points of a sheaf is a sheaf. -/
theorem isSheaf_fFixed (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (act : PointedAction F X P) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (fFixed act).toFunctor := by
  have hX' := (isSheaf_iff_isSheaf_of_type _ _).mp hX
  refine (isSheaf_iff_isSheaf_of_type _ _).mpr ((Subfunctor.isSheaf_iff _ hX').mpr ?_)
  intro T x hx T₁ s h
  have hc := (BigFppfOver.topology B S hS).pullback_stable s.unop hx
  refine (hX' _ hc).isSeparatedFor.ext fun W q hq => ?_
  have hq2 := hq (T' := op W) (𝟙 _) (F.map q.op h)
  rw [act.map_smul]
  have ey : X.map q.op (X.map s x) = X.map (𝟙 (op W)) (X.map (q ≫ s.unop).op x) := by
    rw [CategoryTheory.Functor.map_id, op_comp, Functor.map_comp_apply]
    rfl
  rw [ey]
  exact hq2

section Thick

/-- The unit section `T → F_T`. -/
noncomputable def sec (P : PointedFinFlat F) (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] : T ⟶ P.obj T := P.lift (𝟙 T) (P.pt (op T))

lemma sec_π (P : PointedFinFlat F) (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] : sec P T ≫ P.π T = 𝟙 T := P.lift_π _ _

lemma sec_c (P : PointedFinFlat F) (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] : F.map (sec P T).op (P.c T) = P.pt (op T) := P.lift_c _ _

lemma sec_surj_ring (P : PointedFinFlat F) (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] : Function.Surjective ((SCH).map (sec P T)).appTop.hom := by
  intro y
  refine ⟨((SCH).map (P.π T)).appTop.hom y, ?_⟩
  have h : (SCH).map (sec P T) ≫ (SCH).map (P.π T) = 𝟙 _ := by
    rw [← Functor.map_comp, sec_π]; exact (SCH).map_id _
  have h2 := congrArg (fun q => q.appTop.hom y) h
  exact h2

lemma sec_surjective (P : PointedFinFlat F) (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] : Function.Surjective ((SCH).map (sec P T)) := by
  haveI := P.isAffine_obj T
  obtain ⟨k, hk⟩ := P.nil T
  let φ : Γ((SCH).obj (P.obj T), ⊤) ⟶ Γ((SCH).obj T, ⊤) := ((SCH).map (sec P T)).appTop
  have hc : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective _ (sec_surj_ring P T)
  have ht := (Stacks.Thickenings.isThickening_of_ker_pow_eq_bot _ hc
    ((Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine _ _).2
      (Stacks.Smooth.ker_specMap_appTop_pow_eq_bot _ hk))).2
  have hnat : (SCH).map (sec P T) ≫ ((SCH).obj (P.obj T)).isoSpec.hom =
      ((SCH).obj T).isoSpec.hom ≫ Spec.map φ := (Scheme.isoSpec_hom_naturality _).symm
  intro y
  obtain ⟨z, hz⟩ := ht (((SCH).obj (P.obj T)).isoSpec.hom y)
  obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso ((SCH).obj T).isoSpec).surjective z
  refine ⟨x, (Scheme.homeoOfIso ((SCH).obj (P.obj T)).isoSpec).injective ?_⟩
  have h1 := congrArg (fun q => q x) hnat
  exact (h1.trans hz)

/-- An étale section over `T` extends to `F_T`. -/
theorem exists_section (P : PointedFinFlat F) (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] {V₀ : Scheme.{u}} (p : V₀ ⟶ (SCH).obj (P.obj T)) [Etale p] (s : (SCH).obj T ⟶ V₀)
    (hs : s ≫ p = (SCH).map (sec P T)) :
    ∃ b : (SCH).obj (P.obj T) ⟶ V₀, b ≫ p = 𝟙 _ ∧ (SCH).map (sec P T) ≫ b = s := by
  haveI := P.isAffine_obj T
  obtain ⟨k, hk⟩ := P.nil T
  let φ : Γ((SCH).obj (P.obj T), ⊤) ⟶ Γ((SCH).obj T, ⊤) := ((SCH).map (sec P T)).appTop
  have hnat : (SCH).map (sec P T) ≫ ((SCH).obj (P.obj T)).isoSpec.hom =
      ((SCH).obj T).isoSpec.hom ≫ Spec.map φ := (Scheme.isoSpec_hom_naturality _).symm
  have hnat' : ((SCH).obj T).isoSpec.inv ≫ (SCH).map (sec P T) =
      Spec.map φ ≫ ((SCH).obj (P.obj T)).isoSpec.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨b, h1, h2⟩ := exists_lift_nil p k φ (sec_surj_ring P T) hk
    (((SCH).obj T).isoSpec.inv ≫ s) ((SCH).obj (P.obj T)).isoSpec.inv
    (by rw [Category.assoc, hs, hnat'])
  refine ⟨((SCH).obj (P.obj T)).isoSpec.hom ≫ b, ?_, ?_⟩
  · rw [Category.assoc, h1, Iso.hom_inv_id]
  · rw [← Category.assoc, hnat, Category.assoc, h2, Iso.hom_inv_id_assoc]

end Thick

section Chart

variable {U : BigFppfOver B S hS} {f₀ : yoneda.obj U ⟶ X}

/-- **Lemma A.3 on a chart.** The fixed locus in a piece `T` of an étale chart is cut out by the ideal `J` of the printed proof. -/
theorem exists_ideal_chart
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f₀)
    (act : PointedAction F X P) {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (j : T ⟶ U)
    [IsOpenImmersion ((SCH).map j)] :
    ∃ J : Ideal Γ((SCH).obj T, ⊤), (∀ {T'' : BigFppfOver B S hS} (t : T'' ⟶ T),
      J ≤ RingHom.ker ((SCH).map t).appTop.hom → X.map t.op (f₀.app (op T) j) ∈ (fFixed act).obj (op T'')) ∧
      (∀ {T'' : BigFppfOver B S hS} [IsAffine ((SCH).obj T'')] (t : T'' ⟶ T),
        X.map t.op (f₀.app (op T) j) ∈ (fFixed act).obj (op T'') → J ≤ RingHom.ker ((SCH).map t).appTop.hom) := by
  haveI := P.isAffine_obj T
  let x := f₀.app (op T) j
  let Fo := P.obj T
  let π := P.π T
  let c := P.c T
  let e : T ⟶ Fo := sec P T
  let a₀ : X.obj (op Fo) := act.smul c (X.map π.op x)
  have hπe : e ≫ π = 𝟙 T := sec_π P T
  have hpull : ∀ {Y : BigFppfOver B S hS} (r : Y ⟶ Fo),
      X.map r.op a₀ = act.smul (F.map r.op c) (X.map (r ≫ π).op x) := by
    intro Y r
    refine (act.map_smul r.op c _).trans ?_
    rw [op_comp, Functor.map_comp_apply]
  have ha : X.map e.op a₀ = x := by
    rw [hpull, sec_c, act.pt_smul, hπe]
    simp
  -- the lift of `a₀` to the chart
  obtain ⟨b, hb, hbe⟩ : ∃ b : Fo ⟶ U, f₀.app _ b = a₀ ∧ e ≫ b = j := by
    let g : yoneda.obj Fo ⟶ X := yonedaEquiv.symm a₀
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
    obtain ⟨b₀, hb₁, hb₂⟩ := exists_section P T ((SCH).map (hr.snd g)) ((SCH).map s) (by
      rw [← Functor.map_comp, hse])
    obtain ⟨b, hb⟩ := exists_hom_of_section (hr.snd g) b₀ hb₁
    have hbs : b ≫ hr.snd g = 𝟙 Fo := by
      apply (SCH).map_injective
      rw [Functor.map_comp, hb, hb₁]
      exact ((SCH).map_id _).symm
    have hes : e ≫ b = s := by
      apply (SCH).map_injective
      rw [Functor.map_comp, hb]
      exact hb₂
    let c' : Fo ⟶ U := (hr.fst g).app (op Fo) b
    refine ⟨c', ?_, ?_⟩
    · have hc := congrArg (fun q => q.app (op Fo) b) (hr.isPullback g).w
      refine (show f₀.app _ c' = _ from hc).trans ?_
      change g.app (op Fo) (b ≫ hr.snd g) = a₀
      rw [hbs]
      simp [g, yonedaEquiv]
    · have h1 : e ≫ c' = (hr.fst g).app (op T) (e ≫ b) :=
        (NatTrans.naturality_apply (hr.fst g) e.op b).symm
      rw [h1, hes]
      have h2 := congrArg (fun q => q.app (op T) (𝟙 T)) hsf
      simpa using h2
  have hnat : ∀ {Y : BigFppfOver B S hS} (q : Y ⟶ U) {Y' : BigFppfOver B S hS} (r : Y' ⟶ Y),
      f₀.app _ (r ≫ q) = X.map r.op (f₀.app _ q) := fun q _ r =>
    NatTrans.naturality_apply f₀ r.op q
  have hrange : Set.range ((SCH).map b) ⊆ Set.range ((SCH).map j) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨t, rfl⟩ := sec_surjective P T y
    refine ⟨t, ?_⟩
    rw [← hbe, Functor.map_comp, Scheme.Hom.comp_apply]
  let bT := IsOpenImmersion.lift ((SCH).map j) ((SCH).map b) hrange
  have hbT : bT ≫ (SCH).map j = (SCH).map b := IsOpenImmersion.lift_fac _ _ _
  let W : Set Γ((SCH).obj Fo, ⊤) := {w | ∃ y : Γ((SCH).obj T, ⊤),
    w = bT.appTop.hom y - ((SCH).map π).appTop.hom y}
  have hcrit : ∀ {Y : BigFppfOver B S hS} (r : Y ⟶ Fo),
      (r ≫ b = r ≫ π ≫ j ↔ ∀ w ∈ W, ((SCH).map r).appTop.hom w = 0) := by
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
    · rintro h w ⟨y, rfl⟩
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun q => q.appTop.hom y) h
    · intro h
      apply ext_of_isAffine
      ext y
      have := h _ ⟨y, rfl⟩
      rw [map_sub, sub_eq_zero] at this
      exact this
  letI := ((SCH).map π).appTop.hom.toAlgebra
  refine ⟨Ideal.span {g | ∃ w ∈ W, ∃ ℓ : Γ((SCH).obj Fo, ⊤) →ₗ[Γ((SCH).obj T, ⊤)] Γ((SCH).obj T, ⊤), g = ℓ w},
    ?_, ?_⟩
  · intro T'' t hJ T' s h
    let τ : unop T' ⟶ T := s.unop ≫ t
    let r := P.lift τ h
    have hrπ : r ≫ π = τ := P.lift_π _ _
    have hrc : F.map r.op c = h := P.lift_c _ _
    have heq : r ≫ b = r ≫ π ≫ j := by
      refine (hcrit r).2 fun w hw => ?_
      refine map_eq_zero_of_contr ((SCH).map π).appTop.hom ((SCH).map τ).appTop.hom
        ((SCH).map r).appTop.hom ?_ (P.finite T) (P.projective T) w fun ℓ => ?_
      · rw [← hrπ, Functor.map_comp, Scheme.Hom.comp_appTop]
        rfl
      · have h0 : ((SCH).map t).appTop.hom (ℓ w) = 0 := hJ (Ideal.subset_span ⟨w, hw, ℓ, rfl⟩)
        change ((SCH).map (s.unop ≫ t)).appTop.hom (ℓ w) = 0
        rw [Functor.map_comp, Scheme.Hom.comp_appTop]
        change ((SCH).map s.unop).appTop.hom (((SCH).map t).appTop.hom (ℓ w)) = 0
        rw [h0, map_zero]
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
    haveI := P.isAffine_obj T''
    let F₂ := P.obj T''
    let π₂ := P.π T''
    let c₂ := P.c T''
    let τ := π₂ ≫ t
    let r := P.lift τ c₂
    have hrπ : r ≫ π = τ := P.lift_π _ _
    have hrc : F.map r.op c = c₂ := P.lift_c _ _
    have hfx := hfix π₂.op c₂
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
    let e₂ : T'' ⟶ F₂ := sec P T''
    have hsec : e₂ ≫ r = t ≫ e := by
      rw [P.lift_uniq (e₂ ≫ r), P.lift_uniq (t ≫ e)]
      have h1 : (e₂ ≫ r) ≫ π = (t ≫ e) ≫ π := by
        rw [Category.assoc, hrπ, Category.assoc, hπe, Category.comp_id, ← Category.assoc]
        change (sec P T'' ≫ P.π T'') ≫ t = t
        rw [sec_π, Category.id_comp]
      have h2 : F.map (e₂ ≫ r).op c = F.map (t ≫ e).op c := by
        rw [op_comp, Functor.map_comp_apply, hrc, op_comp, Functor.map_comp_apply]
        change F.map (sec P T'').op (P.c T'') = F.map t.op (F.map (sec P T).op (P.c T))
        rw [sec_c, sec_c, P.map_pt]
      rw [h1, h2]
    have hag : e₂ ≫ r ≫ b = e₂ ≫ r ≫ π ≫ j := by
      rw [← Category.assoc, hsec, Category.assoc, hbe, ← Category.assoc e₂, hsec]
      simp only [Category.assoc]
      rw [← Category.assoc e π, hπe, Category.id_comp]
    have hall : ∀ y, y ∈ O := by
      intro y
      obtain ⟨z, rfl⟩ := sec_surjective P T'' y
      exact (hO T'' e₂).1 hag ⟨z, rfl⟩
    have heq : r ≫ b = r ≫ π ≫ j := by
      simpa using (hO F₂ (𝟙 F₂)).2 (fun y _ => hall y)
    refine Ideal.span_le.2 ?_
    rintro _ ⟨w, hw, ℓ, rfl⟩
    exact P.bc t w ((hcrit r).1 heq w hw) ℓ

end Chart

/-- **Lemma A.3**: `F` finite locally free, infinitesimal, pointed, acting on the algebraic space `X`: the functor of `F`-fixed points is represented by a closed
subspace of `X`. -/
theorem lemA3_general (hX : IsAlgebraicSpace B S hS X) (act : PointedAction F X P) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (fFixed act).ι := by
  refine presheaf_closed_of_ideals hX _ (isSheaf_fFixed hX.isSheaf act) ?_
  intro U T f₀ het _ j _
  exact exists_ideal_chart het act j

end AlgMag.Final.A3G

#print axioms AlgMag.Final.A3G.lemA3_general
