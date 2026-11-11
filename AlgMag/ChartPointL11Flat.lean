/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointL11Trans

/-!
# Translating flatness along the orbit (Lemma 1.1 of the chart-lemma proof, step C)

`GoodAt o x`: `o : O → Y` is flat at `x`, tested on affine points of the image `Y`. If this holds on
a nonempty basic open of `O`, it holds everywhere, by the shear `(g, x) ↦ (g, g x)` and transitivity.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]

/-- `o : O → Y` is flat at `x`. -/
def GoodAt (o : yoneda.obj (Ob P N) ⟶ X) (x : (SCH).obj (Ob P N)) : Prop :=
  ∀ {T W : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj W)]
    (g : yoneda.obj T ⟶ X), g.app (op T) (𝟙 T) ∈ (imS o).obj (op T) →
    ∀ (p : W ⟶ Ob P N) (w : W ⟶ T), IsPullback (yoneda.map p) (yoneda.map w) o g →
    ∀ v : (SCH).obj W, (SCH).map p v = x → ((SCH).map w |>.stalkMap v).hom.Flat

/-- A point of `T[M]` is a point of `T` and a point of `D(M)`. -/
lemma gk_eval {T V : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (a : V ⟶ Gk M T) (x : R1 T M) :
    ((SCH).map a).appTop.hom (spSec T (ι1 T (M := M)) contains1 x) =
      evalAt ((SCH).map (a ≫ Gπ M T)).appTop.hom
        (secPt ((SCH).map a).appTop.hom (univPt1 (U := T))) x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single m c =>
    rw [evalAt_single]
    have e : AddMonoidAlgebra.single m c = (ι1 T (M := M) c) *
        AddMonoidAlgebra.single m (1 : RT T) := by
      rw [show (ι1 T (M := M) c) = AddMonoidAlgebra.single 0 c from rfl,
        AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rw [e, map_mul, map_mul, Functor.map_comp, Scheme.Hom.comp_appTop]
    congr 1
    change _ = ((SCH).map a).appTop.hom (((SCH).map (Gπ M T)).appTop.hom c)
    rw [spToT_appTop]

lemma gk_ext {T V : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] {a b : V ⟶ Gk M T}
    (h1 : a ≫ Gπ M T = b ≫ Gπ M T)
    (h2 : secPt ((SCH).map a).appTop.hom (univPt1 (U := T)) =
      secPt ((SCH).map b).appTop.hom (univPt1 (U := T))) : a = b := by
  refine sp_hom_ext T fun x => ?_
  rw [gk_eval, gk_eval, h1, h2]

/-- The point of `T[M]` with given components. -/
lemma exists_gk_lift {T V : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (t : V ⟶ T)
    (h : Multiplicative M →* Γ((SCH).obj V, ⊤)) :
    ∃ τ : V ⟶ Gk M T, τ ≫ Gπ M T = t ∧ secPt ((SCH).map τ).appTop.hom (univPt1 (U := T)) = h := by
  have hψ : (evalAt ((SCH).map t).appTop.hom h).comp (ι1 T (M := M)) =
      ((SCH).map t).appTop.hom := RingHom.ext fun b => evalAt_ι _ _ b
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_spLift (R' := R1 T M) (ι1 T) contains1 t _ hψ
  refine ⟨τ, hτ₁, MonoidHom.ext fun m => ?_⟩
  refine (hτ₂ _).trans ?_
  refine (evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
  rw [map_one, one_mul]
  rfl

/-- The inverse of a point of `D(M)`. -/
noncomputable def invPt {R : Type*} [CommMonoid R] (h : Multiplicative M →* R) :
    Multiplicative M →* R := h.comp invMonoidHom

lemma invPt_mul {R : Type*} [CommMonoid R] (h : Multiplicative M →* R) : invPt h * h = 1 :=
  MonoidHom.ext fun m => by
    change h m⁻¹ * h m = 1
    rw [← map_mul, inv_mul_cancel, map_one]

lemma flat_gπ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] :
    Flat ((SCH).map (Gπ M T)) := by
  have hf : Flat (Spec.map (CommRingCat.ofHom (ι1 T (M := M)))) := by
    refine Flat.SpecMap_iff.2 ?_
    change (algebraMap (RT T) (R1 T M)).Flat
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  change Flat (Spec.map _ ≫ ((SCH).obj T).isoSpec.inv)
  infer_instance

variable [IsAffine S] {o : yoneda.obj (Ob P N) ⟶ X}

/-- **The shear**: for `W = T ×_X O`, `W[M] = T[M] ×_{g·, X} O` with `O`-component `g · p`. -/
theorem isPullback_shear (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    {T W : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj W)]
    {g : yoneda.obj T ⟶ X} {p : W ⟶ Ob P N} {w : W ⟶ T}
    (sq : IsPullback (yoneda.map p) (yoneda.map w) o g) (wM : Gk M W ⟶ Gk M T)
    (h1 : wM ≫ Gπ M T = Gπ M W ≫ w)
    (h2 : secPt ((SCH).map wM).appTop.hom (univPt1 (U := T)) = univPt1 (U := W)) :
    IsPullback (yoneda.map (oSmul N (univPt1 (U := W)) (Gπ M W ≫ p))) (yoneda.map wM) o
      (orbMap actX g) := by
  have hsm : ∀ {V : BigFppfOver B S hS} (c : Multiplicative M →* Γ((SCH).obj V, ⊤)) (a : V ⟶ Ob P N),
      o.app (op V) (oSmul N c a) = actX.smul (U := op V) c (o.app (op V) a) :=
    fun c a => hoe (T := op _) c a
  have hspec : ∀ {V : BigFppfOver B S hS} (l : V ⟶ Gk M W),
      secPt ((SCH).map (l ≫ wM)).appTop.hom (univPt1 (U := T)) =
        secPt ((SCH).map l).appTop.hom (univPt1 (U := W)) := by
    intro V l
    rw [← h2, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  have hoc : ∀ {V : BigFppfOver B S hS} (l : V ⟶ W), o.app (op V) (l ≫ p) = g.app (op V) (l ≫ w) := by
    intro V l
    rw [hom_nat, hom_nat, pb_comm sq]
  refine pb_mk ?_ ?_ ?_
  · rw [hsm, orbMap_app, h2, h1, hoc]
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
    obtain ⟨l, hl3, hl4⟩ := exists_gk_lift (M := M) l0 hb
    refine ⟨l, ?_, gk_ext ?_ ?_⟩
    · rw [comp_oSmul, ← Category.assoc, hl3, hl1]
      change oSmul N (secPt ((SCH).map l).appTop.hom (univPt1 (U := W))) a' = a
      rw [hl4, ← oSmul_mul]
      have : (hb * invPt hb : Multiplicative M →* Γ((SCH).obj V, ⊤)) = 1 := by
        rw [mul_comm]; exact invPt_mul hb
      rw [this, oSmul_one]
    · rw [Category.assoc, h1, ← Category.assoc, hl3, hl2]
    · rw [hspec, hl4]
  · intro V l l' e1 e2
    have hc : secPt ((SCH).map l).appTop.hom (univPt1 (U := W)) =
        secPt ((SCH).map l').appTop.hom (univPt1 (U := W)) := by
      rw [← hspec, ← hspec, e2]
    refine gk_ext (pb_ext sq ?_ ?_) hc
    · have e1' : oSmul N (secPt ((SCH).map l).appTop.hom (univPt1 (U := W))) (l ≫ Gπ M W ≫ p) =
          oSmul N (secPt ((SCH).map l').appTop.hom (univPt1 (U := W))) (l' ≫ Gπ M W ≫ p) := by
        have := e1
        rw [comp_oSmul, comp_oSmul] at this
        exact this
      rw [hc] at e1'
      have e3 := congrArg (oSmul N (invPt (secPt ((SCH).map l').appTop.hom (univPt1 (U := W))))) e1'
      rw [← oSmul_mul, ← oSmul_mul, invPt_mul, oSmul_one, oSmul_one] at e3
      simpa using e3
    · have := congrArg (· ≫ Gπ M T) e2
      simp only [Category.assoc, h1] at this
      simpa using this

/-- `T[M] → ` the action: the point `g · t` lies in the image if `t` does. -/
lemma orbMap_mem (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o)
    {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (g : yoneda.obj T ⟶ X)
    (hg : g.app (op T) (𝟙 T) ∈ (imS o).obj (op T)) :
    (orbMap actX g).app (op (Gk M T)) (𝟙 _) ∈ (imS o).obj (op (Gk M T)) := by
  rw [orbMap_app]
  refine image_stable hX hsep actX hoe hlfp _ _ ?_
  have : g.app (op (Gk M T)) (𝟙 _ ≫ Gπ M T) = X.map (Gπ M T).op (g.app (op T) (𝟙 T)) := by
    rw [← hom_nat]; simp
  rw [this]
  exact (imS o).map _ hg

/-- **Lemma 1.1, step C.** Flatness of `o` on a nonempty basic open of `O` spreads to all of `O`. -/
theorem goodAt_of_basicOpen (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    (hK : IsField (RT P))
    (actX : AAction (fppfO B S hS) M X) (hoe : IsEquivariant (oAct N) actX o)
    (hlfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) o)
    (h : RN P N) (hn : ¬ IsNilpotent h)
    (hgood : ∀ x : (SCH).obj (Ob P N),
      x ∈ ((SCH).obj (Ob P N)).basicOpen (spSec P _ (containsN N) h) → GoodAt o x)
    (x : (SCH).obj (Ob P N)) : GoodAt o x := by
  classical
  intro T W _ _ g hg p w sq v hv
  let R := RT W
  let φ : RN P N →+* R := ((SCH).map p).appTop.hom.comp (spSec P _ (containsN N))
  let v' : PrimeSpectrum R := ((SCH).obj W).isoSpec.hom v
  obtain ⟨Q, hQ, hQc, hQh⟩ := exists_prime_evAt (M := M) hK φ h hn v'.asIdeal
  let z : (SCH).obj (Gk M W) := (⟨Q, hQ⟩ : PrimeSpectrum (R1 W M))
  have hz : (SCH).map (Gπ M W) z = v := by
    change ((SCH).obj W).isoSpec.inv (Spec.map (CommRingCat.ofHom (ι1 W (M := M))) z) = v
    have : Spec.map (CommRingCat.ofHom (ι1 W (M := M))) z = v' :=
      PrimeSpectrum.ext hQc
    rw [this]
    simp [v']
  -- `W[M] → T[M]`
  obtain ⟨wM, h1, h2⟩ := exists_gk_lift (T := T) (M := M) (Gπ M W ≫ w) (univPt1 (U := W))
  have sq' := isPullback_shear actX hoe sq wM h1 h2
  let xt := oSmul N (univPt1 (U := W)) (Gπ M W ≫ p)
  have hval : ((SCH).map xt).appTop.hom (spSec P _ (containsN N) h) =
      spSec W (ι1 W (M := M)) contains1 (evAt φ h) := by
    let s := spSec W (ι1 W (M := M)) contains1
    let ρ : RT P →+* R1 W M := (AddMonoidAlgebra.singleZeroRingHom : R →+* R1 W M).comp
      (φ.comp AddMonoidAlgebra.singleZeroRingHom)
    have eb : ((SCH).map (xt ≫ Oπ P N)).appTop.hom = s.comp ρ := by
      have e0 : xt ≫ Oπ P N = Gπ M W ≫ p ≫ Oπ P N := by
        rw [oSmul_π, Category.assoc]
      rw [e0]
      refine RingHom.ext fun a => ?_
      rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
      change ((SCH).map (Gπ M W)).appTop.hom (((SCH).map p).appTop.hom
        (((SCH).map (Oπ P N)).appTop.hom a)) = _
      rw [spToT_appTop, spToT_appTop]
      rfl
    have ec : oChar xt = s.toMonoidHom.comp (chiAt φ) := by
      refine MonoidHom.ext fun z => ?_
      rw [oChar_oSmul, oChar_comp]
      change ((SCH).map (Gπ M W)).appTop.hom (oChar p z) * s (AddMonoidAlgebra.single
        ((Multiplicative.toAdd z : N) : M) 1) = s (AddMonoidAlgebra.single
        ((Multiplicative.toAdd z : N) : M) _)
      rw [spToT_appTop]
      change s (AddMonoidAlgebra.single 0 _) * _ = _
      rw [← map_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
      rfl
    rw [appTop_eq_eval, eb, ec, eval_secPt]
    rfl
  have hxt : (SCH).map xt z ∈ ((SCH).obj (Ob P N)).basicOpen (spSec P _ (containsN N) h) := by
    have hz' : z ∈ ((SCH).map xt) ⁻¹ᵁ ((SCH).obj (Ob P N)).basicOpen (spSec P _ (containsN N) h) := by
      rw [Scheme.preimage_basicOpen]
      change z ∈ ((SCH).obj (Gk M W)).basicOpen
        (((SCH).map xt).appTop.hom (spSec P _ (containsN N) h))
      rw [hval]
      have e5 := basicOpen_eq_of_affine (R := CommRingCat.of (R1 W M)) (evAt φ h)
      change z ∈ (Spec (CommRingCat.of (R1 W M))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of (R1 W M))).inv.hom (evAt φ h))
      rw [e5]
      exact hQh
    exact hz'
  have hfl := hgood _ hxt (orbMap actX g) (orbMap_mem hX hsep actX hoe hlfp g hg) xt wM sq' z rfl
  have hπT : Flat ((SCH).map (Gπ M T)) := flat_gπ T
  have hπW : Flat ((SCH).map (Gπ M W)) := flat_gπ W
  have hcomp : (((SCH).map (Gπ M W) ≫ (SCH).map w).stalkMap z).hom.Flat := by
    rw [← Functor.map_comp, ← h1, Functor.map_comp, Scheme.Hom.stalkMap_comp]
    exact RingHom.Flat.comp (Flat.stalkMap _ _) hfl
  have := flat_stalk_descend ((SCH).map (Gπ M W)) ((SCH).map w) z (Flat.stalkMap _ _) hcomp
  rwa [hz] at this

end AlgMag.ChartPoint
