/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartDeligneLim
import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# Lemma 4.3 of the chart-lemma proof: the map on the open stratum `T_U = T \ V(a)`

`Lam f ∈ Γ(T_U)` is the section characterized by `r Lam f = t` for `(r, t) ∈ LL f`. It is a ring map,
whence `T_U → U₀`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space
open TopologicalSpace

universe u

namespace AlgMag.ChartMain.DeligneInst

/-! ### Sections through stalks -/

section Stalk

variable {Y : Scheme.{u}}

/-- The germ on global sections. -/
noncomputable abbrev gm (y : Y) : Γ(Y, ⊤) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ ⊤ y trivial).hom

lemma sec_ext {ξ η : Γ(Y, ⊤)} (h : ∀ y : Y, gm y ξ = gm y η) : ξ = η :=
  TopCat.Presheaf.section_ext Y.sheaf ⊤ _ _ fun y _ => h y

lemma isUnit_gm {w : Γ(Y, ⊤)} {y : Y} (h : y ∈ Y.basicOpen w) : IsUnit (gm y w) :=
  (Scheme.mem_basicOpen_top Y w y).1 h

/-- Gluing `t i / (w i)^(N i)`. -/
lemma exists_glue {I : Type u} (w : I → Γ(Y, ⊤)) (hcov : ∀ y : Y, ∃ i, y ∈ Y.basicOpen (w i))
    (N : I → ℕ) (t : I → Γ(Y, ⊤))
    (hc : ∀ i k (y : Y), y ∈ Y.basicOpen (w i) → y ∈ Y.basicOpen (w k) →
      gm y (w k) ^ N k * gm y (t i) = gm y (w i) ^ N i * gm y (t k)) :
    ∃ F : Γ(Y, ⊤), ∀ i (y : Y), y ∈ Y.basicOpen (w i) → gm y (w i) ^ N i * gm y F = gm y (t i) := by
  classical
  let D : I → Y.Opens := fun i => Y.basicOpen (w i)
  let res : ∀ i, Γ(Y, ⊤) →+* Γ(Y, D i) := fun i => (Y.presheaf.map (homOfLE (le_top : D i ≤ ⊤)).op).hom
  have hu : ∀ i, IsUnit (res i (w i)) := fun i => RingedSpace.isUnit_res_basicOpen _ (w i)
  let s : ∀ i, Γ(Y, D i) := fun i => ((hu i).unit ^ N i)⁻¹.1 * res i (t i)
  have hgerm : ∀ i (y : Y) (hy : y ∈ D i) (z : Γ(Y, ⊤)),
      Y.presheaf.germ (D i) y hy (res i z) = gm y z := fun i y hy z =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hs : ∀ i (y : Y) (hy : y ∈ D i), gm y (w i) ^ N i * Y.presheaf.germ (D i) y hy (s i) = gm y (t i) := by
    intro i y hy
    have h1 : res i (w i) ^ N i * s i = res i (t i) := by
      simp only [s]
      rw [← mul_assoc]
      have : res i (w i) ^ N i = ((hu i).unit ^ N i).1 := by simp
      rw [this, Units.mul_inv, one_mul]
    have h2 := congrArg (Y.presheaf.germ (D i) y hy) h1
    rw [map_mul, map_pow, hgerm, hgerm] at h2
    exact h2
  have hcomp : TopCat.Presheaf.IsCompatible Y.sheaf.1 D s := by
    intro i k
    refine TopCat.Presheaf.section_ext Y.sheaf (D i ⊓ D k) _ _ fun y hy => ?_
    change Y.presheaf.germ _ y hy (Y.presheaf.map _ _) = Y.presheaf.germ _ y hy (Y.presheaf.map _ _)
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    have ha := isUnit_gm (show y ∈ Y.basicOpen (w i) from hy.1)
    have hb := isUnit_gm (show y ∈ Y.basicOpen (w k) from hy.2)
    have e1 := hs i y hy.1
    have e2 := hs k y hy.2
    have e3 := hc i k y hy.1 hy.2
    apply ((ha.pow (N i)).mul (hb.pow (N k))).mul_left_cancel
    calc _ = gm y (w k) ^ N k * (gm y (w i) ^ N i * Y.presheaf.germ (D i) y hy.1 (s i)) := by ring
      _ = gm y (w i) ^ N i * (gm y (w k) ^ N k * Y.presheaf.germ (D k) y hy.2 (s k)) := by
        rw [e1, e2, e3]
      _ = _ := by ring
  obtain ⟨F, hF, -⟩ := Y.sheaf.existsUnique_gluing' D ⊤ (fun i => homOfLE le_top)
    (fun y _ => by
      obtain ⟨i, hi⟩ := hcov y
      exact Opens.mem_iSup.2 ⟨i, hi⟩) s hcomp
  refine ⟨F, fun i y hy => ?_⟩
  have e := hs i y hy
  rw [← hF i] at e
  have e2 : Y.presheaf.germ (D i) y hy (Y.sheaf.1.map (homOfLE (le_top : D i ≤ ⊤)).op F) = gm y F :=
    hgerm i y hy F
  rw [← e, ← e2]

end Stalk

/-! ### The open stratum -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {actX : AAction (fppfO B S hS) M X} {U₀ : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] {actU : AAction (fppfO B S hS) M (yoneda.obj U₀)}
  {fU : yoneda.obj U₀ ⟶ X} {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {φ : yoneda.obj V ⟶ X} (C : Ctx actX actU fU φ)
  [DecidableEq M] {T : BigFppfOver B S hS} [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {actT : AAction (fppfO B S hS) M (yoneda.obj T)}
  {m : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)}
  (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m)
  {x : ∀ n, X.obj (op (Vc T (m ^ n)))} (hx : IsEquivSystem actT actX m x)
  {a : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)}
  (hax : ∀ n, C.idl (x n) = a.map (sec (ιc T (m ^ n))))

/-- `D(g)` for `g` in a set, as an open. -/
noncomputable def openOf (gens : Set Γ((SCH).obj T, ⊤)) : ((SCH).obj T).Opens :=
  ⨆ g : gens, ((SCH).obj T).basicOpen (g : Γ((SCH).obj T, ⊤))

/-- `T_U`. -/
noncomputable abbrev UTo (gens : Set Γ((SCH).obj T, ⊤)) : BigFppfOver B S hS :=
  Chart.immObj T (openOf gens).ι

/-- `T_U → T`. -/
noncomputable abbrev jo (gens : Set Γ((SCH).obj T, ⊤)) : UTo gens ⟶ T :=
  Chart.immι T (openOf gens).ι

omit [AddMonoid.FG M] [DecidableEq M] [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
lemma isOpenImmersion_jo (gens : Set Γ((SCH).obj T, ⊤)) : IsOpenImmersion ((SCH).map (jo gens)) :=
  inferInstanceAs (IsOpenImmersion (openOf gens).ι)

/-- `D(g)` cover `T_U`. -/
lemma jo_cover (gens : Set Γ((SCH).obj T, ⊤)) (y : (SCH).obj (UTo gens)) :
    ∃ g : gens, y ∈ ((SCH).obj (UTo gens)).basicOpen ((sec (jo gens)) (g : Γ((SCH).obj T, ⊤))) := by
  obtain ⟨g, hg⟩ := Opens.mem_iSup.1 y.2
  refine ⟨g, ?_⟩
  have e := Scheme.preimage_basicOpen ((SCH).map (jo gens)) (g : Γ((SCH).obj T, ⊤))
  have : y ∈ ((SCH).map (jo gens)) ⁻¹ᵁ ((SCH).obj T).basicOpen (g : Γ((SCH).obj T, ⊤)) := hg
  rw [e] at this
  exact this

lemma jo_range (gens : Set Γ((SCH).obj T, ⊤)) (y : (SCH).obj T) :
    y ∈ Set.range ((SCH).map (jo gens)) ↔ ∃ g ∈ Ideal.span gens, y ∈ ((SCH).obj T).basicOpen g := by
  have hr : Set.range ((SCH).map (jo gens)) = (openOf gens : Set _) := Scheme.Opens.range_ι _
  rw [hr]
  constructor
  · intro hy
    obtain ⟨g, hg⟩ := Opens.mem_iSup.1 hy
    exact ⟨g, Ideal.subset_span g.2, hg⟩
  · rintro ⟨g, hg, hy⟩
    by_contra hn
    have hv : ∀ c ∈ gens, y ∉ ((SCH).obj T).basicOpen c := fun c hc hyc =>
      hn (Opens.mem_iSup.2 ⟨⟨c, hc⟩, hyc⟩)
    let 𝔭 : Ideal Γ((SCH).obj T, ⊤) := (((SCH).obj T).isoSpec.hom y).asIdeal
    have hle : Ideal.span gens ≤ 𝔭 := Ideal.span_le.2 fun c hc => by
      by_contra hc'
      exact hv c hc ((mem_basicOpen_iff y c).2 hc')
    exact (mem_basicOpen_iff y g).1 hy (hle hg)

variable {gens : Set Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} (hgens : a = Ideal.span gens)
  (hhom : ∀ g ∈ gens, ∃ d, g ∈ homog actT d)

include hP hx hax hgens hhom in
/-- A value of `f` near each `g ∈ gens`. -/
lemma exists_val (g : gens) (f) : ∃ (N : ℕ) (t : Γ((SCH).obj T, ⊤)),
    LL C x f ((g : Γ((SCH).obj T, ⊤)) ^ N) t := by
  obtain ⟨δ, hδ⟩ := hhom g g.2
  exact exists_LL C hP hx hax hδ (hgens ▸ Ideal.subset_span g.2) f

include hP hax hgens in
/-- The cross relation at a point of `D(g)`. -/
lemma gm_cross {f r r' t t'} (h : LL C x f r t) (h' : LL C x f r' t') (g : gens)
    (y : (SCH).obj (UTo gens))
    (hy : y ∈ ((SCH).obj (UTo gens)).basicOpen ((sec (jo gens)) (g : Γ((SCH).obj T, ⊤)))) :
    gm y ((sec (jo gens)) r') * gm y ((sec (jo gens)) t) =
      gm y ((sec (jo gens)) r) * gm y ((sec (jo gens)) t') := by
  have hg : (g : Γ((SCH).obj T, ⊤)) ^ E₀ C f ∈ a ^ E₀ C f :=
    Ideal.pow_mem_pow (hgens ▸ Ideal.subset_span g.2) _
  have key := LL.cross C hP hax h h' hg
  have k2 := congrArg (fun z => gm y ((sec (jo gens)) z)) key
  simp only [map_mul, map_sub, map_pow, map_zero] at k2
  have hu := (isUnit_gm hy).pow (E₀ C f)
  have := hu.mul_left_cancel (a := _) (b := gm y ((sec (jo gens)) r') * gm y ((sec (jo gens)) t))
    (c := gm y ((sec (jo gens)) r) * gm y ((sec (jo gens)) t')) (by linear_combination k2)
  exact this

include hP hx hax hgens hhom in
/-- **`Lam f`.** -/
theorem exists_lam (f) : ∃ F : Γ((SCH).obj (UTo gens), ⊤), ∀ r t, LL C x f r t →
    (sec (jo gens)) r * F = (sec (jo gens)) t := by
  choose N t ht using fun g : gens => exists_val C hP hx hax hgens hhom g f
  obtain ⟨F, hF⟩ := exists_glue (Y := (SCH).obj (UTo gens))
    (fun g : gens => (sec (jo gens)) (g : Γ((SCH).obj T, ⊤))) (jo_cover gens) N
    (fun g => (sec (jo gens)) (t g)) (fun i k y hi hk => by
      have := gm_cross C hP hax hgens (ht i) (ht k) i y hi
      simpa only [map_pow] using this)
  refine ⟨F, fun r s hrs => sec_ext fun y => ?_⟩
  obtain ⟨g, hg⟩ := jo_cover gens y
  have h1 := hF g y hg
  have h2 := gm_cross C hP hax hgens hrs (ht g) g y hg
  simp only [map_pow] at h2
  have hu := (isUnit_gm hg).pow (N g)
  apply hu.mul_left_cancel
  simp only [map_mul]
  rw [h2, ← h1]
  ring

/-- `Lam f`. -/
noncomputable def lamFun (hh : ∀ f, ∃ F : Γ((SCH).obj (UTo gens), ⊤), ∀ r t, LL C x f r t →
    (sec (jo gens)) r * F = (sec (jo gens)) t) (f : Γ((SCH).obj U₀, ⊤)) : Γ((SCH).obj (UTo gens), ⊤) :=
  (hh f).choose

lemma lamFun_spec (hh : ∀ f, ∃ F : Γ((SCH).obj (UTo gens), ⊤), ∀ r t, LL C x f r t →
    (sec (jo gens)) r * F = (sec (jo gens)) t) (f) {r t} (h : LL C x f r t) : (sec (jo gens)) r * lamFun C hh f = (sec (jo gens)) t :=
  (hh f).choose_spec r t h

/-- Equality of sections, from values at powers of each `g`. -/
lemma ext_vals {ξ η : Γ((SCH).obj (UTo gens), ⊤)}
    (h : ∀ g : gens, ∃ N : ℕ, ((sec (jo gens)) (g : Γ((SCH).obj T, ⊤))) ^ N * ξ =
      ((sec (jo gens)) (g : Γ((SCH).obj T, ⊤))) ^ N * η) : ξ = η := by
  refine sec_ext fun y => ?_
  obtain ⟨g, hg⟩ := jo_cover gens y
  obtain ⟨N, hN⟩ := h g
  have := congrArg (gm y) hN
  simp only [map_mul, map_pow] at this
  exact ((isUnit_gm hg).pow N).mul_left_cancel this

/-- **The ring map `Γ(U₀) → Γ(T_U)`.** -/
noncomputable def lamRing (hh : ∀ g : gens, ∀ f, ∃ (N : ℕ) (t : Γ((SCH).obj T, ⊤)),
    LL C x f ((g : Γ((SCH).obj T, ⊤)) ^ N) t)
    (hl : ∀ f, ∃ F : Γ((SCH).obj (UTo gens), ⊤), ∀ r t, LL C x f r t →
      (sec (jo gens)) r * F = (sec (jo gens)) t) :
    Γ((SCH).obj U₀, ⊤) →+* Γ((SCH).obj (UTo gens), ⊤) where
  toFun := lamFun C hl
  map_one' := by
    have : LL C x 1 1 1 := fun n => by
      rw [map_one]
      exact lift_one_of C (x n) 1 1 (fun W c y₀ _ => by simp) 1 (by simp)
    have h := lamFun_spec C hl 1 this
    simpa using h
  map_zero' := by
    have : LL C x 0 1 0 := fun n => by
      rw [map_one, map_zero]
      exact lift_one_of C (x n) 0 0 (fun W c y₀ _ => by simp) 0 (by simp)
    have h := lamFun_spec C hl 0 this
    simpa using h
  map_mul' f f' := by
    refine ext_vals (gens := gens) fun g => ?_
    obtain ⟨N, t, ht⟩ := hh g f
    obtain ⟨N', t', ht'⟩ := hh g f'
    refine ⟨N + N', ?_⟩
    have h1 := lamFun_spec C hl _ (ht.mul C ht')
    have h2 := lamFun_spec C hl _ ht
    have h3 := lamFun_spec C hl _ ht'
    simp only [map_mul, map_pow] at h1 h2 h3
    rw [pow_add]
    rw [h1, ← h2, ← h3]
    ring
  map_add' f f' := by
    refine ext_vals (gens := gens) fun g => ?_
    obtain ⟨N, t, ht⟩ := hh g f
    obtain ⟨N', t', ht'⟩ := hh g f'
    refine ⟨N + N', ?_⟩
    have h1 := lamFun_spec C hl _ (ht.add C ht')
    have h2 := lamFun_spec C hl _ ht
    have h3 := lamFun_spec C hl _ ht'
    simp only [map_mul, map_pow, map_add] at h1 h2 h3
    rw [pow_add, h1, ← h2, ← h3]
    ring

/-! ### Local checks on `W` -/

section Local

omit [AddMonoid.FG M] [DecidableEq M] [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- A section with `D(z) = ⊤` of an affine scheme is a unit. -/
lemma isUnit_of_basicOpen_top {Y : Scheme.{u}} [IsAffine Y] {z : Γ(Y, ⊤)} (h : ∀ y : Y, y ∈ Y.basicOpen z) :
    IsUnit z := by
  by_contra hn
  obtain ⟨𝔪, h𝔪, hz⟩ := exists_max_ideal_of_mem_nonunits hn
  let pt : Spec Γ(Y, ⊤) := (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum Γ(Y, ⊤))
  let y : Y := Y.isoSpec.inv pt
  have hy : Y.isoSpec.hom y = pt := by
    have h' : (Y.isoSpec.inv ≫ Y.isoSpec.hom) pt = pt := by rw [Iso.inv_hom_id]; rfl
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans h'
  have := (mem_basicOpen_iff y z).1 (h y)
  rw [hy] at this
  exact this hz

/-- **Locality of points**: `p = q` on `W` if they agree on each affine open inside some `D(e i)`. -/
theorem eq_of_affine_local (hX : IsAlgebraicSpace B S hS X) {W : BigFppfOver B S hS} {p q : X.obj (op W)}
    {I : Type u} (e : I → Γ((SCH).obj W, ⊤)) (hcov : ∀ w : (SCH).obj W, ∃ i, w ∈ ((SCH).obj W).basicOpen (e i))
    (h : ∀ (A : ((SCH).obj W).Opens) (_ : IsAffineOpen A) (i : I), A ≤ ((SCH).obj W).basicOpen (e i) →
      X.map (Chart.immι W A.ι).op p = X.map (Chart.immι W A.ι).op q) : p = q := by
  let Y := (SCH).obj W
  let J := ULift.{u + 1, u} {A : Y.Opens // IsAffineOpen A ∧ ∃ i, A ≤ Y.basicOpen (e i)}
  let W' : J → BigFppfOver B S hS := fun j => Chart.immObj W j.down.1.ι
  let q' : ∀ j, W' j ⟶ W := fun j => Chart.immι W j.down.1.ι
  have hP : Presieve.ofArrows (fun i ↦ B.inclusion.obj (W' i).left)
      (fun i ↦ B.inclusion.map (q' i).left) ∈ Scheme.fppfPrecoverage (B.inclusion.obj W.left) := by
    have hz : Presieve.ofArrows (fun i ↦ (SCH).obj (W' i)) (fun i ↦ (SCH).map (q' i)) ∈
        Scheme.zariskiPrecoverage ((SCH).obj W) := by
      rw [Scheme.ofArrows_mem_precoverage_iff (P := @AlgebraicGeometry.IsOpenImmersion)]
      refine ⟨fun w => ?_, fun j => inferInstanceAs (IsOpenImmersion j.down.1.ι)⟩
      obtain ⟨i, hi⟩ := hcov w
      obtain ⟨_, ⟨A, hA, rfl⟩, hwA, hAle⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open hi (Y.basicOpen (e i)).2
      exact ⟨ULift.up ⟨A, hA, i, hAle⟩, ⟨w, hwA⟩, rfl⟩
    exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hz
  have hcovS := generated_over_fppf_family_mem_topology B S hS W' q' hP
  have hXs : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  refine (hXs _ hcovS).isSeparatedFor.ext ?_
  rintro Z r ⟨Y', a, b, hb, rfl⟩
  cases hb with
  | mk j =>
    obtain ⟨hA, i, hle⟩ := j.down.2
    have := h j.down.1 hA i hle
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg _ this

end Local

/-! ### The map `T_U → U₀` -/

section Tau

omit [AddMonoid.FG M] [DecidableEq M] [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] hT in
lemma sec_str {A A' : BigFppfOver B S hS} (c : A ⟶ A') (b : Γ(S, ⊤)) :
    (sec c) (A'.hom.hom.appTop.hom b) = A.hom.hom.appTop.hom b := by
  have e := site_w c
  conv_rhs => rw [← e]
  rw [Scheme.Hom.comp_appTop]
  rfl

set_option maxHeartbeats 4000000 in
include hP hx hax hgens hhom in
/-- **The map `T_U → U₀`**, for `S` affine. -/
theorem exists_y₀ [IsAffine S] : ∃ y₀ : UTo gens ⟶ U₀, ∀ f r t, LL C x f r t →
    (sec (jo gens)) r * (sec y₀) f = (sec (jo gens)) t := by
  have hh := fun (g : gens) f => exists_val C hP hx hax hgens hhom g f
  have hl := fun f => exists_lam (gens := gens) C hP hx hax hgens hhom f
  let Λ := lamRing C hh hl
  haveI : IsAffine (B.obj hS).obj := ‹IsAffine S›
  have hw : toAffine Λ ≫ U₀.hom.hom = (UTo gens).hom.hom := by
    refine toAffine_ext (RingHom.ext fun b => ?_)
    rw [Scheme.Hom.comp_appTop]
    change (toAffine Λ).appTop.hom (U₀.hom.hom.appTop.hom b) = _
    rw [toAffine_appTop]
    have hL : LL C x (U₀.hom.hom.appTop.hom b) 1 (T.hom.hom.appTop.hom b) := fun n => by
      rw [map_one]
      refine lift_one_of C (x n) _ (V.hom.hom.appTop.hom b) (fun W c y₀ _ => ?_) _ ?_
      · simp only [map_one, one_mul]
        rw [sec_str, sec_str]
      · rw [sec_str, sec_str, sec_str]
    have := lamFun_spec C hl _ hL
    rw [map_one, one_mul, sec_str] at this
    exact this
  refine ⟨siteHom (toAffine Λ) hw, fun f r t h => ?_⟩
  have e : (sec (siteHom (toAffine Λ) hw)) f = Λ f := by
    change (toAffine Λ).appTop.hom f = _
    rw [toAffine_appTop]
  rw [e]
  exact lamFun_spec C hl f h

variable (y₀ : UTo gens ⟶ U₀)
  (hy₀ : ∀ f r t, LL C x f r t → (sec (jo gens)) r * (sec y₀) f = (sec (jo gens)) t)

omit [AddMonoid.FG M] [DecidableEq M] [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] hT in
/-- Two maps to `U₀` with the same ring map are equal. -/
lemma eq_of_sec {W : BigFppfOver B S hS} {y y' : W ⟶ U₀} (h : ∀ f, (sec y) f = (sec y') f) : y = y' :=
  siteExt (toAffine_ext (RingHom.ext h))

omit [DecidableEq M] in
/-- A local check on `W → T_U`. -/
theorem eq_of_unit (hX : IsAlgebraicSpace B S hS X) {W : BigFppfOver B S hS} (s : W ⟶ UTo gens)
    {p q : X.obj (op W)}
    (h : ∀ {A : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj A)] (i : A ⟶ W) (g : gens),
      IsUnit ((sec (i ≫ s ≫ jo gens)) (g : Γ((SCH).obj T, ⊤))) → X.map i.op p = X.map i.op q) : p = q := by
  refine eq_of_affine_local hX (fun g : gens => (sec (s ≫ jo gens)) (g : Γ((SCH).obj T, ⊤))) (fun w => ?_)
    (fun A hA g hAle => ?_)
  · obtain ⟨g, hg⟩ := jo_cover gens ((SCH).map s w)
    refine ⟨g, ?_⟩
    have e := Scheme.preimage_basicOpen ((SCH).map s) ((sec (jo gens)) (g : Γ((SCH).obj T, ⊤)))
    have h1 : w ∈ ((SCH).map s) ⁻¹ᵁ ((SCH).obj (UTo gens)).basicOpen ((sec (jo gens)) (g : Γ((SCH).obj T, ⊤))) := hg
    rw [e] at h1
    rw [sec_comp]
    exact h1
  · haveI hA' : IsAffine ((BigFppfOver.toScheme B S hS).obj (Chart.immObj W A.ι)) := hA
    refine h (Chart.immι W A.ι) g (isUnit_of_basicOpen_top fun y => ?_)
    rw [sec_comp]
    have e := Scheme.preimage_basicOpen ((SCH).map (Chart.immι W A.ι)) ((sec (s ≫ jo gens)) (g : Γ((SCH).obj T, ⊤)))
    have h1 : y ∈ ((SCH).map (Chart.immι W A.ι)) ⁻¹ᵁ ((SCH).obj W).basicOpen ((sec (s ≫ jo gens)) (g : Γ((SCH).obj T, ⊤))) :=
      hAle y.2
    rw [e] at h1
    exact h1

set_option maxHeartbeats 4000000 in
include hP hx hax hgens hhom hy₀ in
/-- `τ` restricts to `x` on an affine `W` where some `g` is a unit. -/
theorem tau_x_aff (n : ℕ) {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (g₁ : W ⟶ UTo gens) (g₂ : W ⟶ Vc T (m ^ n)) (hc : g₁ ≫ jo gens = g₂ ≫ ιc T (m ^ n)) (g : gens)
    (hu : IsUnit ((sec (g₁ ≫ jo gens)) (g : Γ((SCH).obj T, ⊤)))) :
    X.map g₁.op (fU.app (op _) y₀) = X.map g₂.op (x n) := by
  have hga : (g : Γ((SCH).obj T, ⊤)) ∈ a := hgens ▸ Ideal.subset_span g.2
  have hmem : (sec (g₂ ≫ ιc T (m ^ n))) (g : Γ((SCH).obj T, ⊤)) ∈ C.idl (X.map g₂.op (x n)) := by
    rw [C.idl_map, hax, sec_comp]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hga)
  rw [← hc] at hmem
  obtain ⟨y₁, hy₁⟩ := C.lift_U (X.map g₂.op (x n)) (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  have hsec : ∀ f, (sec y₁) f = (sec (g₁ ≫ y₀)) f := by
    intro f
    obtain ⟨N, t, ht⟩ := exists_val C hP hx hax hgens hhom g f
    have l := lift_map C g₂ (ht n)
    rw [← hy₁] at l
    have e₁ := lift_formula C y₁ l
    have e₂ := congrArg (sec g₁) (hy₀ f _ _ ht)
    have hcs : ∀ z, (sec g₁) ((sec (jo gens)) z) = (sec g₂) ((sec (ιc T (m ^ n))) z) := fun z => by
      rw [← sec_comp, ← sec_comp, hc]
    rw [map_mul, hcs, hcs, map_pow, map_pow] at e₂
    rw [map_pow, map_pow] at e₁
    apply (hu.pow N).mul_left_cancel
    rw [sec_comp g₁ (jo gens), sec_comp g₁ y₀, hcs]
    exact e₁.symm.trans e₂.symm
  have : y₁ = g₁ ≫ y₀ := eq_of_sec hsec
  rw [← hy₁, this, map_yoneda_app (φ := fU) g₁ y₀]

include hP hx hax hgens hhom hy₀ in
/-- **`τ` restricts to `x`.** -/
theorem tau_x (hX : IsAlgebraicSpace B S hS X) (n : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ UTo gens)
    (g₂ : W ⟶ Vc T (m ^ n)) (hc : g₁ ≫ jo gens = g₂ ≫ ιc T (m ^ n)) :
    X.map g₁.op (fU.app (op _) y₀) = X.map g₂.op (x n) := by
  refine eq_of_unit hX g₁ fun {A} _ i g hu => ?_
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  refine tau_x_aff C hP hx hax hgens hhom y₀ hy₀ n (i ≫ g₁) (i ≫ g₂) ?_ g ?_
  · rw [Category.assoc, Category.assoc, hc]
  · rwa [Category.assoc]

set_option maxHeartbeats 4000000 in
include hP hx hax hgens hhom hy₀ in
/-- The action on an affine `W` where some `g` is a unit. -/
theorem tau_equiv_aff {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (t t' : W ⟶ UTo gens) (h : Multiplicative M →* Γ((SCH).obj W, ⊤))
    (hr : t' ≫ jo gens = smulAt actT h (t ≫ jo gens)) (g : gens)
    (hu : IsUnit ((sec (t ≫ jo gens)) (g : Γ((SCH).obj T, ⊤)))) :
    t' ≫ y₀ = smulAt actU h (t ≫ y₀) := by
  classical
  letI := gradedRingOfAction actU
  obtain ⟨δ, hδ⟩ := hhom g g.2
  have hga : (g : Γ((SCH).obj T, ⊤)) ∈ a := hgens ▸ Ideal.subset_span g.2
  refine siteExt (toAffine_ext (ringHom_ext_homogeneous (homog actU) fun d f hf => ?_))
  obtain ⟨c, hcd, hc⟩ := exists_LL_homog C hP hx hax hf hδ hga
  set N := expo C f + expo C f
  have q := hy₀ f _ _ hc
  have q₁ := congrArg (sec t) q
  have q₂ := congrArg (sec t') q
  have hχu : ∀ z : Multiplicative M, IsUnit (h z) := fun z => (Group.isUnit z).map h
  have hs : ∀ {D : M} {z : Γ((SCH).obj T, ⊤)}, z ∈ homog actT D →
      (sec t') ((sec (jo gens)) z) = (sec t) ((sec (jo gens)) z) * h (Multiplicative.ofAdd D) := by
    intro D z hz
    rw [← sec_comp, hr, ← sec_comp]
    exact appTop_smul_of_mem actT (t ≫ jo gens) h hz
  rw [map_mul, map_pow] at q₁ q₂
  rw [map_pow] at q₁ q₂
  rw [hs hδ, hs hcd] at q₂
  have hhd : h (Multiplicative.ofAdd (d + N • δ)) =
      h (Multiplicative.ofAdd d) * h (Multiplicative.ofAdd δ) ^ N := by
    rw [ofAdd_add, map_mul, ofAdd_nsmul, map_pow]
  rw [hhd] at q₂
  rw [sec_comp t] at hu
  rw [appTop_smul_of_mem actU (t ≫ y₀) h hf]
  change (sec (t' ≫ y₀)) f = (sec (t ≫ y₀)) f * _
  rw [sec_comp t', sec_comp t]
  have hU := ((hu.mul (hχu (Multiplicative.ofAdd δ))).pow N)
  apply hU.mul_left_cancel
  rw [q₂, mul_pow, ← q₁]
  ring

include hP hx hax hgens hhom hy₀ in
/-- **`τ` is equivariant.** -/
theorem tau_equiv (hX : IsAlgebraicSpace B S hS X) (hequ : IsEquivariant actU actX fU) :
    EquivAlong actT actX (jo gens) (fU.app (op _) y₀) := by
  intro W t t' h hr
  refine eq_of_unit hX t fun {A} _ i g hu => ?_
  have hr' : (i ≫ t') ≫ jo gens = smulAt actT (secPt (sec i) h) ((i ≫ t) ≫ jo gens) := by
    rw [Category.assoc, hr, Category.assoc]
    exact comp_smulAt actT i h _
  have key := tau_equiv_aff C hP hx hax hgens hhom y₀ hy₀ (i ≫ t) (i ≫ t') _ hr' g
    (by rwa [Category.assoc])
  have e1 : X.map i.op (X.map t'.op (fU.app (op _) y₀)) = fU.app (op A) ((i ≫ t') ≫ y₀) := by
    rw [map_yoneda_app (φ := fU) (i ≫ t') y₀, op_comp, Functor.map_comp_apply]
  have e2 : X.map i.op (actX.smul (F := X) (U := op W) h (X.map t.op (fU.app (op _) y₀))) =
      fU.app (op A) (smulAt actU (secPt (sec i) h) ((i ≫ t) ≫ y₀)) := by
    have e := hequ (T := op A) (secPt (sec i) h) ((i ≫ t) ≫ y₀)
    rw [map_yoneda_app (φ := fU) (i ≫ t) y₀, op_comp, Functor.map_comp_apply] at e
    change X.map i.op (smX actX h _) = _
    rw [smX_map]
    exact e.symm
  rw [e1, e2, key]

end Tau

end AlgMag.ChartMain.DeligneInst
