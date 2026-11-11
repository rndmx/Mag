/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSIndCompat
import AlgMag.ChartQSEffective

/-!
# The context `DeligneQS.Ctx` of the tower of paragraph 4

The fields of `DeligneQS.Ctx` on the tower `complTower`, independent of the comparison with `theta`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS.ChartQSLocal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

open AlgebraicGeometry.Space (pointsMap range_pointsMap_yoneda_map
  preimage_range_pointsMap_eq_range_pointsMap_snd)

section Concrete

variable (actX : AAction (fppfO B S hS) M X) {P₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {o₀ : P₀ ⟶ X}
  (ho : ClosedP o₀) {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {φ : yoneda.obj V ⟶ X}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  (hX : IsAlgebraicSpace B S hS X)

/-- `J·Γ(W)`, the ideal of `W ×_X P`. -/
noncomputable def idlP {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (y : X.obj (op W)) : Ideal Γ((SCH).obj W, ⊤) :=
  topI (idealOf (stableP_closedP actX ho hs he hX) (yonedaEquiv.symm y))

lemma idlP_map {W W' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W')] (q : W' ⟶ W) (y : X.obj (op W)) :
    idlP actX ho hs he hX (X.map q.op y) = (idlP actX ho hs he hX y).map (sec q) :=
  topI_idealOf_map _ q y

/-- `y ∈ X_k` iff `J^{k+1} = 0`, on an affine. -/
lemma mem_thick_of_pow {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (y : X.obj (op W)) (k : ℕ) (h : idlP actX ho hs he hX y ^ (k + 1) = ⊥) :
    y ∈ (strataZ actX ho hs he hX k).obj (op W) := by
  refine (mem_thickening_iff (stableP_closedP actX ho hs he hX) hs he k y).2 ?_
  refine le_bot_iff.1 (Scheme.IdealSheafData.le_of_isAffine ?_)
  change (idlP actX ho hs he hX y) ^ (k + 1) ≤ _
  rw [h]
  exact bot_le

/-- `J = 0` on a point of `X_0`. -/
lemma idlP_eq_bot_of_mem {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (y : X.obj (op W)) (h : y ∈ (strataZ actX ho hs he hX 0).obj (op W)) : idlP actX ho hs he hX y = ⊥ := by
  have := (mem_thickening_iff (stableP_closedP actX ho hs he hX) hs he 0 y).1 h
  rw [zero_add, pow_one] at this
  unfold idlP
  rw [this]
  simp [topI]

set_option maxHeartbeats 4000000 in
/-- `J` of `y` is inside `J` of `h • y`. -/
lemma idlP_le_smul {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (h : Multiplicative M →* Γ((SCH).obj W, ⊤)) (y : X.obj (op W)) :
    idlP actX ho hs he hX y ≤ idlP actX ho hs he hX (smX actX h y) := by
  let I := idlP actX ho hs he hX (smX actX h y)
  let i := ιc W I
  have hb : idlP actX ho hs he hX (X.map i.op (smX actX h y)) = ⊥ := by
    rw [idlP_map, Ideal.map_eq_bot_iff_le_ker]
    exact fun c hc => (ιc_ker _ c).2 hc
  have hm := mem_thick_of_pow actX ho hs he hX (X.map i.op (smX actX h y)) 0
    (by rw [zero_add, pow_one]; exact hb)
  let h' : Multiplicative M →* Γ((SCH).obj W, ⊤) := APt.inv (U := op W) h
  have hinv : h' * h = 1 := APt.inv_mul (U := op W) h
  have e : actX.smul (F := X) (U := op _) (secPt (sec i) h') (X.map i.op (smX actX h y)) = X.map i.op y := by
    have t1 := smX_map actX i h' (smX actX h y)
    rw [← smX_mul, hinv, smX_one] at t1
    exact t1.symm
  have hm2 : X.map i.op y ∈ (strataZ actX ho hs he hX 0).obj (op (Vc W I)) := by
    rw [← e]
    exact smul_mem_thickening (stableP_closedP actX ho hs he hX) hs he
      (stableAct_equiv ho actX hs he) 0 (secPt (sec i) h') hm
  have hb2 := idlP_eq_bot_of_mem actX ho hs he hX _ hm2
  rw [idlP_map, Ideal.map_eq_bot_iff_le_ker] at hb2
  exact fun c hc => (ιc_ker _ c).1 (hb2 hc)

/-- `idl_smul`. -/
lemma idlP_smul {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (h : Multiplicative M →* Γ((SCH).obj W, ⊤)) (y : X.obj (op W)) :
    idlP actX ho hs he hX (smX actX h y) = idlP actX ho hs he hX y := by
  refine le_antisymm ?_ (idlP_le_smul actX ho hs he hX h y)
  let h' : Multiplicative M →* Γ((SCH).obj W, ⊤) := APt.inv (U := op W) h
  have := idlP_le_smul actX ho hs he hX h' (smX actX h y)
  have e : h' * h = 1 := APt.inv_mul (U := op W) h
  rwa [← smX_mul, e, smX_one] at this

variable {U₀ : BigFppfOver B S hS} {fU : yoneda.obj U₀ ⟶ X}

/-- A point with `J = 1` lies in the open `U₀`, whose complement is `|P₀|`. -/
lemma lift_U_of_top (hfo : Space.IsOpenImmersion B S hS fU)
    (hT : Set.range (pointsMap B S hS P₀ o₀) = (Set.range (pointsMap B S hS (yoneda.obj U₀) fU))ᶜ)
    {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (y : X.obj (op W))
    (h : idlP actX ho hs he hX y = ⊤) : ∃ y₀ : W ⟶ U₀, fU.app (op W) y₀ = y := by
  let hP := stableP_closedP actX ho hs he hX
  let t := yonedaEquiv.symm y
  let R := hfo.rep.pullback t
  let sn : R ⟶ W := hfo.rep.snd t
  have hop : IsOpenImmersion ((SCH).map sn) := hfo.property_snd t
  have hsurj : Set.range ((SCH).map (𝟙 W)) ⊆ Set.range ((SCH).map sn) := by
    rintro _ ⟨w, rfl⟩
    have hw : (SCH).map (𝟙 W) w = w := by simp
    rw [hw]
    have h1 := Set.ext_iff.1 (preimage_range_pointsMap_eq_range_pointsMap_snd B S hS hfo.rep t)
      ((Space.pointsEquivScheme B S hS W).symm w)
    rw [Set.mem_preimage] at h1
    by_cases hin : pointsMap B S hS (yoneda.obj W) t ((Space.pointsEquivScheme B S hS W).symm w) ∈
        Set.range (pointsMap B S hS (yoneda.obj U₀) fU)
    · have h3 := h1.1 hin
      rw [range_pointsMap_yoneda_map] at h3
      obtain ⟨v, hv, e⟩ := h3
      rw [← (Space.pointsEquivScheme B S hS W).symm.injective e]
      exact hv
    · exfalso
      have h2 : pointsMap B S hS (yoneda.obj W) t ((Space.pointsEquivScheme B S hS W).symm w) ∈
          Set.range (pointsMap B S hS P₀ o₀) := by rw [hT]; exact hin
      obtain ⟨a₀, ha₀⟩ := h2
      let l : P₀ ⟶ (stableP ho actX φ).toFunctor :=
        { app := fun T => TypeCat.ofHom fun a => ⟨o₀.app T a, o₀_mem_stableP ho actX a⟩
          naturality := by
            intro T T' f
            ext a
            exact Subtype.ext (show o₀.app T' (P₀.map f a) = X.map f (o₀.app T a) from
              NatTrans.naturality_apply o₀ f a) }
      have h3 : pointsMap B S hS (yoneda.obj W) t ((Space.pointsEquivScheme B S hS W).symm w) ∈
          Set.range (pointsMap B S hS _ (stableP ho actX φ).ι) := by
        refine ⟨pointsMap B S hS _ l a₀, ?_⟩
        rw [← ha₀, ← Space.pointsMap_comp_apply]
        rfl
      have h4 := (mem_range_iff_support hP t w).1 h3
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top _⟩) trivial,
        Scheme.mem_zeroLocus_iff] at h4
      have h5 : (1 : Γ((SCH).obj W, ⊤)) ∈ topI (idealOf hP t) := by
        change (1 : Γ((SCH).obj W, ⊤)) ∈ idlP actX ho hs he hX y
        rw [h]; trivial
      refine h4 1 h5 ?_
      rw [Scheme.basicOpen_of_isUnit _ isUnit_one]
      trivial
  haveI := hop
  obtain ⟨c, hc⟩ := exists_factor_open sn (𝟙 W) hsurj
  let q1 : R ⟶ U₀ := yoneda.preimage (hfo.rep.fst t)
  have hq1y : yoneda.map q1 ≫ fU = yoneda.map sn ≫ t := by
    rw [Functor.map_preimage]; exact hfo.rep.w t
  have hq1 : fU.app (op R) q1 = X.map sn.op y := by
    have e := congrArg yonedaEquiv hq1y
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at e
    refine e.trans ?_
    simp [t]
  refine ⟨c ≫ q1, ?_⟩
  rw [map_yoneda_app (φ := fU) c q1, hq1, ← Functor.map_comp_apply, ← op_comp, hc]
  simp

/-- An open immersion is injective on points. -/
lemma mono_of_open (hfo : Space.IsOpenImmersion B S hS fU) (W : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective (fU.app W) := by
  obtain ⟨W⟩ := W
  intro p q hpq
  change fU.app (op W) p = fU.app (op W) q at hpq
  let t := yonedaEquiv.symm (fU.app (op W) p)
  have hop : IsOpenImmersion ((SCH).map (hfo.rep.snd t)) := hfo.property_snd t
  have hmono : Mono (hfo.rep.snd t) := (SCH).mono_of_mono_map inferInstance
  have hv : ∀ (r : W ⟶ U₀), fU.app (op W) r = fU.app (op W) p →
      yoneda.map r ≫ fU = yoneda.map (𝟙 W) ≫ t := fun r hr => by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map, hr]
    simp [t]
  let l₁ := hfo.rep.lift (yoneda.map p) (𝟙 W) (hv p rfl)
  let l₂ := hfo.rep.lift (yoneda.map q) (𝟙 W) (hv q hpq.symm)
  have e : l₁ = l₂ := (cancel_mono (hfo.rep.snd t)).1
    ((hfo.rep.lift_snd _ _ _).trans (hfo.rep.lift_snd _ _ _).symm)
  have h1 := hfo.rep.lift_fst (yoneda.map p) (𝟙 W) (hv p rfl)
  have h2 := hfo.rep.lift_fst (yoneda.map q) (𝟙 W) (hv q hpq.symm)
  have h3 : yoneda.map p = yoneda.map q := by
    rw [← h1, ← h2]
    exact congrArg (fun z => yoneda.map z ≫ hfo.rep.fst t) e
  exact yoneda.map_injective h3

set_option maxHeartbeats 4000000 in
/-- The truncations of `V(a^k)` land in `Z^(k)`. -/
lemma hfac_aux [DecidableEq M] {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    {m a : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} {x : ∀ n, X.obj (op (Vc T (m ^ n)))}
    (hax : ∀ n, idlP actX ho hs he hX (x n) = a.map (sec (ιc T (m ^ n)))) (k n : ℕ)
    {W : BigFppfOver B S hS} (g₁ : W ⟶ Vc T (a ^ k)) (g₂ : W ⟶ Vc T (m ^ n))
    (h : g₁ ≫ ιc T (a ^ k) = g₂ ≫ ιc T (m ^ n)) :
    ∃ z : (strataZ actX ho hs he hX k).toFunctor.obj (op W), z.1 = X.map g₂.op (x n) := by
  let R := a ^ k ⊔ m ^ n
  have hker : ∀ c ∈ R, (sec (g₂ ≫ ιc T (m ^ n))) c = 0 := by
    intro c hc
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hc
    have e1 : (sec (g₂ ≫ ιc T (m ^ n))) u = 0 := by
      rw [← h, sec_comp, (ιc_ker _ u).2 hu, map_zero]
    have e2 : (sec (g₂ ≫ ιc T (m ^ n))) v = 0 := by
      rw [sec_comp, (ιc_ker _ v).2 hv, map_zero]
    rw [map_add, e1, e2, add_zero]
  obtain ⟨g₃, hg₃⟩ := exists_factor_closed (g₂ ≫ ιc T (m ^ n)) R hker
  obtain ⟨ρ, hρ⟩ := exists_factor_closed (ιc T R) (m ^ n) (fun c hc =>
    closedι_appTop_of_mem _ (Ideal.mem_sup_right hc))
  have hm : Mono (ιc T (m ^ n)) := (SCH).mono_of_mono_map
    (inferInstanceAs (Mono (Chart.closedι ((SCH).obj T) (m ^ n))))
  have hcomp : g₃ ≫ ρ = g₂ := (cancel_mono (ιc T (m ^ n))).1 (by
    rw [Category.assoc, hρ, hg₃])
  have hmem : X.map ρ.op (x n) ∈ (strataZ actX ho hs he hX k).obj (op (Vc T R)) := by
    refine mem_thick_of_pow actX ho hs he hX _ k ?_
    rw [idlP_map, hax, Ideal.map_map, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro c hc
    rw [RingHom.mem_ker, RingHom.comp_apply, ← sec_comp, hρ]
    refine (ιc_ker _ c).2 (Ideal.mem_sup_left ?_)
    exact Ideal.pow_le_pow_right (Nat.le_succ k) hc
  refine ⟨⟨X.map g₂.op (x n), ?_⟩, rfl⟩
  rw [← hcomp, op_comp, Functor.map_comp_apply]
  exact (strataZ actX ho hs he hX k).map g₃.op hmem

end Concrete

end AlgMag.ChartMain.DeligneQS.ChartQSLocal
