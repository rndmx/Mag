/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSL11Stable

/-!
# Lemma 1.1 for quasi-separated `X`, step C: translating flatness along the orbit

`GoodAtQS` tests on a possibly non-affine `W = O ×_X T`. The shear uses the scheme `W ×_T T[M]`, which
exists without `W` affine; `Gk M W'` is used only for an affine open `W'` of `W`, to find the point.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQSL11

open ChartMain AlgMag.ChartPoint

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]

/-- `o : O → Y` is flat at `x`, tested on affine `T` and the fibre product `W`. -/
def GoodAtQS (o : yoneda.obj (Ob P N) ⟶ X) (x : (SCH).obj (Ob P N)) : Prop :=
  ∀ {T W : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    (g : yoneda.obj T ⟶ X), g.app (op T) (𝟙 T) ∈ (imS o).obj (op T) →
    ∀ (p : W ⟶ Ob P N) (w : W ⟶ T), IsPullback (yoneda.map p) (yoneda.map w) o g →
    ∀ v : (SCH).obj W, (SCH).map p v = x → ((SCH).map w |>.stalkMap v).hom.Flat

variable [IsAffine S] {o : yoneda.obj (Ob P N) ⟶ X}

/-- **The shear**, `W` not affine: `W ×_T T[M] = T[M] ×_{g·, X} O`. -/
theorem isPullback_shear_qs (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    {T W Wm : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    {g : yoneda.obj T ⟶ X} {p : W ⟶ Ob P N} {w : W ⟶ T}
    (sq : IsPullback (yoneda.map p) (yoneda.map w) o g) {A : Wm ⟶ W} {wM : Wm ⟶ Gk M T}
    (hA : IsPullback A wM w (Gπ M T)) :
    IsPullback (yoneda.map (oSmul N (secPt ((SCH).map wM).appTop.hom (univPt1 (U := T))) (A ≫ p)))
      (yoneda.map wM) o (orbMap actX g) := by
  have hsm : ∀ {V : BigFppfOver B S hS} (c : Multiplicative M →* Γ((SCH).obj V, ⊤)) (a : V ⟶ Ob P N),
      o.app (op V) (oSmul N c a) = actX.smul (U := op V) c (o.app (op V) a) :=
    fun c a => hoe (T := op _) c a
  have hspec : ∀ {V : BigFppfOver B S hS} (l : V ⟶ Wm),
      secPt ((SCH).map (l ≫ wM)).appTop.hom (univPt1 (U := T)) =
        secPt ((SCH).map l).appTop.hom (secPt ((SCH).map wM).appTop.hom (univPt1 (U := T))) := by
    intro V l
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  have hoc : ∀ {V : BigFppfOver B S hS} (l : V ⟶ W), o.app (op V) (l ≫ p) = g.app (op V) (l ≫ w) := by
    intro V l
    rw [hom_nat, hom_nat, pb_comm sq]
  let hm := secPt ((SCH).map wM).appTop.hom (univPt1 (U := T))
  refine pb_mk ?_ ?_ ?_
  · rw [hsm, orbMap_app, hoc, hA.w]
  · intro V a b hab
    rw [orbMap_app] at hab
    let hb := secPt ((SCH).map b).appTop.hom (univPt1 (U := T))
    let a' := oSmul N (invPt hb) a
    have ha' : o.app (op V) a' = g.app (op V) (b ≫ Gπ M T) := by
      rw [hsm, hab]
      refine (actX.mul_smul (U := op V) (invPt hb) hb _).symm.trans ?_
      have : (invPt hb * hb : Multiplicative M →* Γ((SCH).obj V, ⊤)) = 1 := invPt_mul hb
      refine (congrArg (fun c => actX.smul (U := op V) c (g.app (op V) (b ≫ Gπ M T))) this).trans ?_
      exact actX.one_smul (U := op V) _
    obtain ⟨l0, hl1, hl2⟩ := pb_lift sq a' (b ≫ Gπ M T) ha'
    refine ⟨hA.lift l0 b hl2, ?_, hA.lift_snd _ _ _⟩
    rw [comp_oSmul, ← Category.assoc, hA.lift_fst, hl1]
    change oSmul N (secPt ((SCH).map (hA.lift l0 b hl2)).appTop.hom
      (secPt ((SCH).map wM).appTop.hom (univPt1 (U := T)))) a' = a
    rw [← hspec, hA.lift_snd]
    change oSmul N hb a' = a
    rw [← oSmul_mul]
    have : (hb * invPt hb : Multiplicative M →* Γ((SCH).obj V, ⊤)) = 1 := by
      rw [mul_comm]; exact invPt_mul hb
    rw [this, oSmul_one]
  · intro V l l' e1 e2
    have e2' : l ≫ wM = l' ≫ wM := e2
    have hc : secPt ((SCH).map l).appTop.hom hm = secPt ((SCH).map l').appTop.hom hm := by
      rw [← hspec, ← hspec, e2']
    refine hA.hom_ext (pb_ext sq ?_ ?_) e2'
    · have e1' : oSmul N (secPt ((SCH).map l).appTop.hom hm) (l ≫ A ≫ p) =
          oSmul N (secPt ((SCH).map l').appTop.hom hm) (l' ≫ A ≫ p) := by
        have := e1
        rw [comp_oSmul, comp_oSmul] at this
        exact this
      rw [hc] at e1'
      have e3 := congrArg (oSmul N (invPt (secPt ((SCH).map l').appTop.hom hm))) e1'
      rw [← oSmul_mul, ← oSmul_mul, invPt_mul, oSmul_one, oSmul_one] at e3
      simpa using e3
    · simp only [Category.assoc, hA.w]
      simp only [← Category.assoc, e2']

/-- `orbMap_mem`, `X` not separated. -/
lemma orbMap_mem_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o)
    {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (g : yoneda.obj T ⟶ X)
    (hg : g.app (op T) (𝟙 T) ∈ (imS o).obj (op T)) :
    (orbMap actX g).app (op (Gk M T)) (𝟙 _) ∈ (imS o).obj (op (Gk M T)) := by
  rw [orbMap_app]
  refine image_stable_qs hX hqc actX hoe hlfp _ _ ?_
  have : g.app (op (Gk M T)) (𝟙 _ ≫ Gπ M T) = X.map (Gπ M T).op (g.app (op T) (𝟙 T)) := by
    rw [← hom_nat]; simp
  rw [this]
  exact (imS o).map _ hg

/-- **Lemma 1.1, step C**, `X` not separated. -/
theorem goodAt_of_basicOpen_qs (hX : IsAlgebraicSpace B S hS X) (hqc : Space.IsQuasiCompact B S hS o)
    (hK : IsField (RT P))
    (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o)
    (h : RN P N) (hn : ¬ IsNilpotent h)
    (hgood : ∀ x : (SCH).obj (Ob P N),
      x ∈ ((SCH).obj (Ob P N)).basicOpen (spSec P _ (containsN N) h) → GoodAtQS o x)
    (x : (SCH).obj (Ob P N)) : GoodAtQS o x := by
  classical
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  intro T W _ g hg p w sq v hv
  obtain ⟨W0, hW0, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (x := v) (U := ⊤) trivial
  let Ws := Space.openSiteObject B S hS W W0
  let j : Ws ⟶ W := Space.openSiteObjectHom B S hS W W0
  haveI hWs : IsAffine ((SCH).obj Ws) := hW0
  let ps : Ws ⟶ Ob P N := j ≫ p
  let vs : (SCH).obj Ws := (⟨v, hmem⟩ : W0)
  have hvs : (SCH).map j vs = v := rfl
  let R := RT Ws
  let φ : RN P N →+* R := ((SCH).map ps).appTop.hom.comp (spSec P _ (containsN N))
  let v' : PrimeSpectrum R := ((SCH).obj Ws).isoSpec.hom vs
  obtain ⟨Q, hQ, hQc, hQh⟩ := exists_prime_evAt (M := M) hK φ h hn v'.asIdeal
  let z : (SCH).obj (Gk M Ws) := (⟨Q, hQ⟩ : PrimeSpectrum (R1 Ws M))
  have hz : (SCH).map (Gπ M Ws) z = vs := by
    change ((SCH).obj Ws).isoSpec.inv (Spec.map (CommRingCat.ofHom (ι1 Ws (M := M))) z) = vs
    have : Spec.map (CommRingCat.ofHom (ι1 Ws (M := M))) z = v' :=
      PrimeSpectrum.ext hQc
    rw [this]
    simp [v']
  -- `Ws[M] → T[M]`
  obtain ⟨wMs, h1, h2⟩ := exists_gk_lift (T := T) (M := M) (Gπ M Ws ≫ j ≫ w) (univPt1 (U := Ws))
  let xts := oSmul N (univPt1 (U := Ws)) (Gπ M Ws ≫ ps)
  have hval : ((SCH).map xts).appTop.hom (spSec P _ (containsN N) h) =
      spSec Ws (ι1 Ws (M := M)) contains1 (evAt φ h) := by
    let s := spSec Ws (ι1 Ws (M := M)) contains1
    let ρ : RT P →+* R1 Ws M := (AddMonoidAlgebra.singleZeroRingHom : R →+* R1 Ws M).comp
      (φ.comp AddMonoidAlgebra.singleZeroRingHom)
    have eb : ((SCH).map (xts ≫ Oπ P N)).appTop.hom = s.comp ρ := by
      have e0 : xts ≫ Oπ P N = Gπ M Ws ≫ ps ≫ Oπ P N := by
        rw [oSmul_π, Category.assoc]
      rw [e0]
      refine RingHom.ext fun a => ?_
      rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
      change ((SCH).map (Gπ M Ws)).appTop.hom (((SCH).map ps).appTop.hom
        (((SCH).map (Oπ P N)).appTop.hom a)) = _
      rw [spToT_appTop, spToT_appTop]
      rfl
    have ec : oChar xts = s.toMonoidHom.comp (chiAt φ) := by
      refine MonoidHom.ext fun z => ?_
      rw [oChar_oSmul, oChar_comp]
      change ((SCH).map (Gπ M Ws)).appTop.hom (oChar ps z) * s (AddMonoidAlgebra.single
        ((Multiplicative.toAdd z : N) : M) 1) = s (AddMonoidAlgebra.single
        ((Multiplicative.toAdd z : N) : M) _)
      rw [spToT_appTop]
      change s (AddMonoidAlgebra.single 0 _) * _ = _
      rw [← map_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
      rfl
    rw [appTop_eq_eval, eb, ec, eval_secPt]
    rfl
  have hxts : (SCH).map xts z ∈ ((SCH).obj (Ob P N)).basicOpen (spSec P _ (containsN N) h) := by
    have hz' : z ∈ ((SCH).map xts) ⁻¹ᵁ ((SCH).obj (Ob P N)).basicOpen (spSec P _ (containsN N) h) := by
      rw [Scheme.preimage_basicOpen]
      change z ∈ ((SCH).obj (Gk M Ws)).basicOpen
        (((SCH).map xts).appTop.hom (spSec P _ (containsN N) h))
      rw [hval]
      have e5 := basicOpen_eq_of_affine (R := CommRingCat.of (R1 Ws M)) (evAt φ h)
      change z ∈ (Spec (CommRingCat.of (R1 Ws M))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of (R1 Ws M))).inv.hom (evAt φ h))
      rw [e5]
      exact hQh
    exact hz'
  -- `W ×_T T[M]`
  let Wm := pullback w (Gπ M T)
  let A : Wm ⟶ W := pullback.fst w (Gπ M T)
  let wM : Wm ⟶ Gk M T := pullback.snd w (Gπ M T)
  have hA : IsPullback A wM w (Gπ M T) := IsPullback.of_hasPullback _ _
  have sq' := isPullback_shear_qs actX hoe sq hA
  let hm := secPt ((SCH).map wM).appTop.hom (univPt1 (U := T))
  let xt := oSmul N hm (A ≫ p)
  let k : Gk M Ws ⟶ Wm := hA.lift (Gπ M Ws ≫ j) wMs (by rw [h1, Category.assoc])
  have hk1 : k ≫ A = Gπ M Ws ≫ j := hA.lift_fst _ _ _
  have hk2 : k ≫ wM = wMs := hA.lift_snd _ _ _
  have hkxt : k ≫ xt = xts := by
    change k ≫ oSmul N hm (A ≫ p) = _
    rw [comp_oSmul, ← Category.assoc, hk1]
    have e : secPt ((SCH).map k).appTop.hom hm = univPt1 (U := Ws) := by
      rw [← h2, ← hk2, Functor.map_comp, Scheme.Hom.comp_appTop]
      rfl
    change oSmul N (secPt ((SCH).map k).appTop.hom hm) _ = _
    rw [e, Category.assoc]
  let zt : (SCH).obj Wm := (SCH).map k z
  have hztx : (SCH).map xt zt ∈ ((SCH).obj (Ob P N)).basicOpen (spSec P _ (containsN N) h) := by
    have e : (SCH).map xt zt = (SCH).map xts z := by
      rw [← hkxt, Functor.map_comp, Scheme.Hom.comp_apply]
    rw [e]
    exact hxts
  have hfl := hgood _ hztx (orbMap actX g) (orbMap_mem_qs hX hqc actX hoe hlfp g hg) xt wM sq' zt rfl
  have hπT : Flat ((SCH).map (Gπ M T)) := flat_gπ T
  have hAF : Flat ((SCH).map A) := MorphismProperty.of_isPullback (P := @Flat) (hA.map (SCH)).flip hπT
  have hcomp : (((SCH).map A ≫ (SCH).map w).stalkMap zt).hom.Flat := by
    rw [← Functor.map_comp, hA.w, Functor.map_comp, Scheme.Hom.stalkMap_comp]
    exact RingHom.Flat.comp (Flat.stalkMap _ _) hfl
  have := flat_stalk_descend ((SCH).map A) ((SCH).map w) zt (Flat.stalkMap _ _) hcomp
  have hAz : (SCH).map A zt = v := by
    change (SCH).map A ((SCH).map k z) = v
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hk1, Functor.map_comp, Scheme.Hom.comp_apply, hz, hvs]
  rwa [hAz] at this

end AlgMag.ChartQSL11
