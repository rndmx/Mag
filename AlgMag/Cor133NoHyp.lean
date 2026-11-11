/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SecFinal1316
import AlgMag.Sec12Topology

/-!
# Corollary 13.3 without assuming the existence of `Bl_{Y^N}^{D^N} X^N`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126-201.

* `AlgMag.Dil.isPullback_jN`: **Proposition 9.1 (ii)** for schemes over an arbitrary `S`: for an
  equivariant closed immersion `j : Y ⟶ X`, the square `Y^N ⟶ X^N`, `Y ⟶ X` (evaluation at the unit)
  is cartesian.
* `AlgMag.Dil.isClosedImmersion_jN`: hence `j^N : Y^N ⟶ X^N` is a closed immersion.
* `AlgMag.Dil.cor13_3'`: **Corollary 13.3**, the dilatation `Bl_{Y^N}^{D^N} X^N` being produced by
  `AlgMag.Dil.exists_dilatation` instead of being assumed.

The key point is the schematic density of the orbit `𝔸(M)_T ⟶ 𝔸(N)_T` of the unit section, which is
`Γ(T)[N] ⟶ Γ(T)[M]` on an affine `T` (`AlgMag.Dil.oMagnet_injective`); for this we use the model
`Spec Γ(T)[N]` of `𝔸(N)_T` over an affine `T` (`AlgMag.Dil.oUniversal`), as in
`AlgMag.specUniversal` for the fppf site.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Dil

open GB

/-! ### `𝔸(P)_V = Spec Γ(V)[P]` for an affine `V` over `S` -/

section SpecModel

variable {S : Scheme.{u}} (P : Type u) [AddCommMonoid P]

/-- `Γ(V, 𝒪)[P]`. -/
abbrev oRing (V : Over S) : Type u := AddMonoidAlgebra Γ(V.left, ⊤) P

/-- The morphism `Spec Γ(V)[P] ⟶ V` of schemes. -/
def oPrS (V : Over S) [IsAffine V.left] : Spec (.of (oRing P V)) ⟶ V.left :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ V.left.isoSpec.inv

/-- `𝔸(P)_V` as a scheme over `S`. -/
def oObj (V : Over S) [IsAffine V.left] : Over S := Over.mk (oPrS P V ≫ V.hom)

instance (V : Over S) [IsAffine V.left] : IsAffine (oObj P V).left :=
  inferInstanceAs (IsAffine (Spec _))

/-- The structure morphism `𝔸(P)_V ⟶ V`. -/
def oPr (V : Over S) [IsAffine V.left] : oObj P V ⟶ V := Over.homMk (oPrS P V) rfl

/-- The universal point of `𝔸(P)` on `𝔸(P)_V`. -/
def oPt (V : Over S) [IsAffine V.left] : APt (GB.overO S) P (op (oObj P V)) where
  toFun n := (Scheme.ΓSpecIso (.of (oRing P V))).inv
    (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  map_one' := by
    exact (map_one (Scheme.ΓSpecIso (.of (oRing P V))).inv.hom)
  map_mul' x y := by
    refine Eq.trans ?_ (map_mul (Scheme.ΓSpecIso (.of (oRing P V))).inv.hom _ _)
    rw [AddMonoidAlgebra.single_mul_single, mul_one]
    rfl

variable {P}

/-- The ring morphism `Γ(V)[P] → Γ(T')` classifying a point of `𝔸(P)` over `t : T' ⟶ V`. -/
def oRingHom {V T' : Over S} (t : T' ⟶ V) (a : APt (GB.overO S) P (op T')) :
    oRing P V →+* Γ(T'.left, ⊤) :=
  AddMonoidAlgebra.liftNCRingHom t.left.appTop.hom a (fun _ _ => mul_comm _ _)

lemma oRingHom_single {V T' : Over S} (t : T' ⟶ V) (a : APt (GB.overO S) P (op T')) (n : P)
    (r : Γ(V.left, ⊤)) :
    oRingHom t a (AddMonoidAlgebra.single n r) =
      t.left.appTop.hom r * (show Γ(T'.left, ⊤) from a (Multiplicative.ofAdd n)) := by
  simp [oRingHom, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]
  rfl

lemma oPrS_appTop (V : Over S) [IsAffine V.left] (r : Γ(V.left, ⊤)) :
    (oPrS P V).appTop.hom r = (Scheme.ΓSpecIso (.of (oRing P V))).inv.hom
      (AddMonoidAlgebra.single 0 r) := by
  have hk : V.left.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(V.left, ⊤)).inv := by
    have h := congrArg (fun k => k.appTop) (Scheme.toSpecΓ_isoSpec_inv V.left)
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] at h
    exact (Iso.comp_hom_eq_id _).mp h
  have h3 := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap Γ(V.left, ⊤) (oRing P V)))
  have h5 := congrArg (fun k => k.hom r) h3
  have h6 : (oPrS P V).appTop = (Scheme.ΓSpecIso Γ(V.left, ⊤)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(V.left, ⊤) (oRing P V)))).appTop := by
    rw [oPrS, Scheme.Hom.comp_appTop, hk]
  rw [h6]
  exact h5.symm

/-- The classifying morphism of a point of `𝔸(P)`, on schemes. -/
def oLiftS {V T' : Over S} (t : T' ⟶ V) (a : APt (GB.overO S) P (op T')) :
    T'.left ⟶ Spec (.of (oRing P V)) :=
  T'.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (oRingHom t a))

lemma oLiftS_pr {V T' : Over S} [IsAffine V.left] (t : T' ⟶ V) (a : APt (GB.overO S) P (op T')) :
    oLiftS t a ≫ oPrS P V = t.left := by
  have h : CommRingCat.ofHom (algebraMap Γ(V.left, ⊤) (oRing P V)) ≫
      CommRingCat.ofHom (oRingHom t a) = t.left.appTop := by
    ext r
    change oRingHom t a (AddMonoidAlgebra.single 0 r) = _
    rw [oRingHom_single]
    have : (show Γ(T'.left, ⊤) from a (Multiplicative.ofAdd (0 : P))) = 1 := map_one a
    rw [this, mul_one]
  simp only [oLiftS, oPrS, Category.assoc]
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, h]
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
  simp

/-- The classifying morphism of a point of `𝔸(P)`, over `S`. -/
def oLift {V T' : Over S} [IsAffine V.left] (t : T' ⟶ V) (a : APt (GB.overO S) P (op T')) :
    T' ⟶ oObj P V :=
  Over.homMk (oLiftS t a) (by
    change oLiftS t a ≫ oPrS P V ≫ V.hom = _
    rw [← Category.assoc, oLiftS_pr]
    exact Over.w t)

lemma oLift_pr {V T' : Over S} [IsAffine V.left] (t : T' ⟶ V) (a : APt (GB.overO S) P (op T')) :
    oLift t a ≫ oPr P V = t :=
  Over.OverMorphism.ext (oLiftS_pr t a)

lemma res_oLift {V T' : Over S} [IsAffine V.left] (t : T' ⟶ V) (a : APt (GB.overO S) P (op T')) :
    APt.res (oLift t a).op (oPt P V) = a := by
  refine MonoidHom.ext fun n => ?_
  refine (appTop_toSpec_comp (oRingHom t a)
    (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)).trans ?_
  rw [oRingHom_single, map_one, one_mul]
  rfl

lemma oLift_uniq {V T' : Over S} [IsAffine V.left] (t : T' ⟶ V) (a : APt (GB.overO S) P (op T'))
    (s : T' ⟶ oObj P V) (h₁ : s ≫ oPr P V = t) (h₂ : APt.res s.op (oPt P V) = a) :
    s = oLift t a := by
  have key : s.left.appTop.hom.comp (Scheme.ΓSpecIso (.of (oRing P V))).inv.hom =
      oRingHom t a := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun n => ?_)
    · rw [oRingHom_single]
      change s.left.appTop.hom ((Scheme.ΓSpecIso (.of (oRing P V))).inv.hom
        (AddMonoidAlgebra.single 0 r)) = _
      rw [← oPrS_appTop]
      have : (show Γ(T'.left, ⊤) from a (Multiplicative.ofAdd (0 : P))) = 1 := map_one a
      rw [this, mul_one, ← h₁, Over.comp_left, Scheme.Hom.comp_appTop]
      rfl
    · rw [oRingHom_single, map_one, one_mul, ← h₂]
      rfl
  refine Over.OverMorphism.ext (ext_of_isAffine ?_)
  have hiso : Function.Surjective (Scheme.ΓSpecIso (.of (oRing P V))).inv.hom := fun y =>
    ⟨(Scheme.ΓSpecIso (.of (oRing P V))).hom.hom y, by
      simpa using congrArg (fun k => k.hom y) (Scheme.ΓSpecIso (.of (oRing P V))).hom_inv_id⟩
  refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := hiso y
  refine (congrArg (fun k => k x) key).trans ?_
  exact (appTop_toSpec_comp (oRingHom t a) x).symm

/-- `𝔸(N)_V = Spec Γ(V)[N]` with its universal point, for an affine `V` over `S`. -/
def oUniversal {M : Type u} [AddCommMonoid M] (N : AddSubmonoid M) (V : Over S) [IsAffine V.left] :
    UniversalPoint (GB.overO S) N V where
  P := oObj N V
  π := oPr N V
  u := oPt N V
  lift t a := oLift t a
  lift_π := oLift_pr
  res_lift := res_oLift
  uniq t a s h₁ h₂ := oLift_uniq t a s h₁ h₂

/-- `Γ(V)[N] → Γ(V)[M]` is injective: the orbit `𝔸(M)_V ⟶ 𝔸(N)_V` of the unit section is
schematically dominant. -/
lemma oMagnet_injective {M : Type u} [AddCommMonoid M] (N : AddSubmonoid M) (V : Over S)
    [IsAffine V.left] :
    Function.Injective (oLift (oPr M V) (APt.toMagnet N (oPt M V))).left.appTop.hom := by
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (.of (oRing N V))).inv.hom := fun y =>
    ⟨(Scheme.ΓSpecIso (.of (oRing N V))).hom.hom y, by
      simpa using congrArg (fun k => k.hom y) (Scheme.ΓSpecIso (.of (oRing N V))).hom_inv_id⟩
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of (oRing M V))).inv.hom :=
    fun y y' h => by
      have e := congrArg (Scheme.ΓSpecIso (.of (oRing M V))).hom.hom h
      simpa using e
  let j : oRing N V →+* oRing M V := AddMonoidAlgebra.mapDomainRingHom _ N.subtype
  have hj : Function.Injective j := AddMonoidAlgebra.mapDomain_injective Subtype.val_injective
  have hjs : ∀ (n : N) (r : Γ(V.left, ⊤)), j (AddMonoidAlgebra.single n r) =
      AddMonoidAlgebra.single (n : M) r := fun n r => AddMonoidAlgebra.mapDomain_single
  have key : oRingHom (oPr M V) (APt.toMagnet N (oPt M V)) =
      (Scheme.ΓSpecIso (.of (oRing M V))).inv.hom.comp j := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun n => ?_)
    · rw [oRingHom_single]
      change _ = (Scheme.ΓSpecIso (.of (oRing M V))).inv.hom (j (AddMonoidAlgebra.single 0 r))
      rw [hjs]
      have : (show Γ((oObj M V).left, ⊤) from
          APt.toMagnet N (oPt M V) (Multiplicative.ofAdd (0 : N))) = 1 :=
        map_one (APt.toMagnet N (oPt M V))
      rw [this, mul_one]
      exact oPrS_appTop V r
    · rw [oRingHom_single, map_one, one_mul]
      change _ = (Scheme.ΓSpecIso (.of (oRing M V))).inv.hom (j (AddMonoidAlgebra.single n 1))
      rw [hjs]
      rfl
  intro x y h
  obtain ⟨x, rfl⟩ := hsurj x
  obtain ⟨y, rfl⟩ := hsurj y
  have e := (appTop_toSpec_comp (oRingHom (oPr M V) (APt.toMagnet N (oPt M V))) x).symm.trans
    (h.trans (appTop_toSpec_comp (oRingHom (oPr M V) (APt.toMagnet N (oPt M V))) y))
  rw [key] at e
  rw [hj (hinj e)]

end SpecModel

/-! ### Proposition 9.1 (ii) for schemes over `S` -/

section ClosedImm

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M] {X Y : Over S} {j : Y ⟶ X}
  {act : AAction (GB.overO S) M (yoneda.obj X)} {actY : AAction (GB.overO S) M (yoneda.obj Y)}
  (hs : Stable j act actY)

/-- A morphism over `S` which is a closed immersion is a monomorphism. -/
lemma mono_of_isClosedImmersion_left [IsClosedImmersion j.left] : Mono j :=
  ⟨fun _ _ e => Over.OverMorphism.ext ((cancel_mono j.left).1 (congrArg (fun q => q.left) e))⟩

attribute [local instance] mono_of_isClosedImmersion_left

include hs in
/-- On an affine `T`, the value at the universal point of a point of `X^N` whose value at the unit
lies in `Y` factors through `Y`: the orbit of the unit is schematically dense. -/
lemma exists_factor_univ_affine [IsClosedImmersion j.left] {N : AddSubmonoid M} {T : Over S}
    [IsAffine T.left] (φ : AttractorPt act N T) {x : T ⟶ Y} (hx : φ.toPoint = x ≫ j) :
    ∃ y : oObj N T ⟶ Y, y ≫ j = (show oObj N T ⟶ X from φ.app (oPr N T) (oPt N T)) := by
  set ψ : oObj N T ⟶ X := φ.app (oPr N T) (oPt N T) with hψ
  let ϖ : oObj M T ⟶ oObj N T := oLift (oPr M T) (APt.toMagnet N (oPt M T))
  have hϖ : ϖ ≫ oPr N T = oPr M T := oLift_pr _ _
  let q : oObj M T ⟶ T := oPr M T
  have h1 : ϖ ≫ ψ = φ.app q (APt.toMagnet N (oPt M T)) := by
    have := φ.naturality ϖ (oPr N T) (oPt N T)
    rw [res_oLift, hϖ] at this
    exact this.symm
  have h2 : φ.app q (APt.toMagnet N (oPt M T) * 1) = act.smul (oPt M T) (φ.app q 1) :=
    φ.equivariant q _ _
  rw [mul_one] at h2
  have h3 : (show oObj M T ⟶ X from φ.app q 1) = q ≫ φ.toPoint := by
    have := φ.naturality q (𝟙 T) 1
    have hone : APt.res (𝒪 := GB.overO S) (P := N) q.op 1 = 1 := by
      ext p; simp
    rw [Category.comp_id, hone] at this
    exact this
  let yM : oObj M T ⟶ Y := sm actY (oPt M T) (q ≫ x)
  have hyM : yM ≫ j = ϖ ≫ ψ := by
    rw [h1, h2]
    change _ = sm act (oPt M T) (show oObj M T ⟶ X from φ.app q 1)
    rw [h3, hx, ← Category.assoc, hs]
  -- the closed subscheme `ψ⁻¹(Y)` of `𝔸(N)_T`
  let i := pullback.fst ψ.left j.left
  have hi : IsClosedImmersion i := inferInstance
  have hc : ϖ.left ≫ ψ.left = yM.left ≫ j.left := by
    have := congrArg (fun k => k.left) hyM
    simp only [Over.comp_left] at this
    exact this.symm
  let e := pullback.lift ϖ.left yM.left hc
  have hiso : IsIso i := by
    refine isIso_of_isClosedImmersion_of_dominant i e ?_
    rw [pullback.lift_fst]
    exact oMagnet_injective N T
  let y0 : (oObj N T).left ⟶ Y.left := inv i ≫ pullback.snd ψ.left j.left
  have hy0 : y0 ≫ j.left = ψ.left := by
    simp only [y0, Category.assoc, ← pullback.condition]
    simp [i]
  refine ⟨Over.homMk y0 ?_, Over.OverMorphism.ext hy0⟩
  rw [← Over.w j, ← Category.assoc, hy0]
  exact Over.w ψ

include hs in
/-- **Proposition 9.1 (ii)**, key step: if the value at the unit of a point of `X^N` lies in the
closed `Y`, then all its values lie in `Y`. -/
lemma exists_factor_app [IsClosedImmersion j.left] {N : AddSubmonoid M} {T : Over S}
    (φ : AttractorPt act N T) {x : T ⟶ Y} (hx : φ.toPoint = x ≫ j) {T' : Over S} (t : T' ⟶ T)
    (a : APt (GB.overO S) N (op T')) : ∃ y : T' ⟶ Y, y ≫ j = (show T' ⟶ X from φ.app t a) := by
  refine exists_lift_of_cover j _ T'.left.affineCover ?_ fun i => ?_
  · intro P p _ f g e
    exact (cancel_mono j).1 e
  · let Ti : Over S := Over.mk (T'.left.affineCover.f i ≫ T'.hom)
    let m : Ti ⟶ T' := Over.homMk (T'.left.affineCover.f i) rfl
    have : IsAffine Ti.left := inferInstanceAs (IsAffine (Spec _))
    let φ' := φ.baseChange (m ≫ t)
    have hx' : φ'.toPoint = (m ≫ t ≫ x) ≫ j := by
      rw [AttractorPt.toPoint_baseChange]
      change (m ≫ t) ≫ φ.toPoint = _
      rw [hx]
      simp only [Category.assoc]
    obtain ⟨y', hy'⟩ := exists_factor_univ_affine hs φ' hx'
    let a' := APt.res m.op a
    refine ⟨oLift (𝟙 Ti) a' ≫ y', ?_⟩
    rw [Category.assoc, hy']
    have h1 := φ'.app_eq_of_universal (oUniversal N Ti) (𝟙 Ti) a'
    have h2 := φ.naturality m t a
    refine h1.symm.trans ?_
    refine Eq.trans (congrArg (fun k => φ.app k a') (Category.id_comp (m ≫ t))) ?_
    exact h2

end ClosedImm

section Pullback

attribute [local instance] mono_of_isClosedImmersion_left

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]

/-- The evaluation at the unit `Z ⟶ A` of a scheme `Z` representing `A^N`. -/
def attEv {Z A : Over S} {act : AAction (GB.overO S) M (yoneda.obj A)} {N : AddSubmonoid M}
    (r : RepresentsAttractor act N (yoneda.obj Z)) : Z ⟶ A :=
  (rp r (𝟙 Z)).toPoint

lemma rp_toPoint {Z A : Over S} {act : AAction (GB.overO S) M (yoneda.obj A)} {N : AddSubmonoid M}
    (r : RepresentsAttractor act N (yoneda.obj Z)) {T : Over S} (z : T ⟶ Z) :
    (rp r z).toPoint = z ≫ attEv r := by
  have h := rp_comp r z (𝟙 Z)
  rw [Category.comp_id] at h
  rw [h, AttractorPt.toPoint_baseChange]
  rfl

variable {X Y ZX ZY : Over S} {j : Y ⟶ X}
  {act : AAction (GB.overO S) M (yoneda.obj X)} {actY : AAction (GB.overO S) M (yoneda.obj Y)}
  (hs : Stable j act actY) {N : AddSubmonoid M}
  (rX : RepresentsAttractor act N (yoneda.obj ZX))
  (rY : RepresentsAttractor actY N (yoneda.obj ZY))

lemma rp_jN {T : Over S} (z : T ⟶ ZY) :
    rp rX (z ≫ jN hs rX rY) = pushPt (equivar_j hs) (rp rY z) :=
  rp_comp_repMap rY rX (equivar_j hs) z

lemma jN_attEv : jN hs rX rY ≫ attEv rX = attEv rY ≫ j := by
  rw [← rp_toPoint, ← Category.id_comp (jN hs rX rY), rp_jN]
  rfl

lemma pushPt_injective [Mono j] {T : Over S} {γ γ' : AttractorPt actY N T}
    (h : pushPt (equivar_j hs) γ = pushPt (equivar_j hs) γ') : γ = γ' := by
  refine AttractorPt.ext ?_
  funext T' t a
  exact (cancel_mono j).1 (congrArg (fun p : AttractorPt act N T => p.app t a) h)

/-- **Proposition 9.1 (ii)** for schemes over an arbitrary `S`. Let `j : Y ⟶ X` be an equivariant
closed immersion (`Y` stable), and `X^N`, `Y^N` be represented by schemes. Then
`Y^N = X^N ×_X Y`: the square formed by `j^N` and the evaluations at the unit is cartesian. -/
theorem isPullback_jN [IsClosedImmersion j.left] :
    IsPullback (jN hs rX rY) (attEv rY) (attEv rX) j := by
  have w := jN_attEv hs rX rY
  have key : ∀ s : PullbackCone (attEv rX) j, ∃ γ : AttractorPt actY N s.pt,
      pushPt (equivar_j hs) γ = rp rX s.fst := fun s =>
    exists_Y_pt hs (rp rX s.fst) fun T' t a =>
      exists_factor_app hs (rp rX s.fst) (x := s.snd)
        (by rw [rp_toPoint]; exact s.condition) t a
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (rY.equiv s.pt).symm (key s).choose)
    ?_ ?_ ?_⟩⟩
  · intro s
    refine (rX.equiv s.pt).injective ?_
    change rp rX (_ ≫ jN hs rX rY) = rp rX s.fst
    rw [rp_jN]
    change pushPt _ ((rY.equiv s.pt) ((rY.equiv s.pt).symm _)) = _
    rw [Equiv.apply_symm_apply]
    exact (key s).choose_spec
  · intro s
    refine (cancel_mono j).1 ?_
    rw [Category.assoc, ← w, ← Category.assoc, ← s.condition]
    congr 1
    refine (rX.equiv s.pt).injective ?_
    change rp rX (_ ≫ jN hs rX rY) = rp rX s.fst
    rw [rp_jN]
    change pushPt _ ((rY.equiv s.pt) ((rY.equiv s.pt).symm _)) = _
    rw [Equiv.apply_symm_apply]
    exact (key s).choose_spec
  · intro s m h1 _
    refine (rY.equiv s.pt).injective ?_
    rw [Equiv.apply_symm_apply]
    refine pushPt_injective hs ?_
    change pushPt _ (rp rY m) = _
    rw [← rp_jN hs rX rY, (key s).choose_spec]
    exact congrArg (rp rX) h1

/-- **Proposition 9.1 (ii)**, last assertion: `j^N : Y^N ⟶ X^N` is a closed immersion. -/
theorem isClosedImmersion_jN [IsClosedImmersion j.left] : IsClosedImmersion (jN hs rX rY).left := by
  have h := (isPullback_jN hs rX rY).map (Over.forget S)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip ‹_›

end Pullback

/-! ### Corollary 13.3 -/

section Cor

variable {S : Scheme.{u}} {I : S.IdealSheafData} {X Y : Over S} {j : Y ⟶ X}

/-- The dilatation `Bl_{Y^N}^{D^N} X^N` exists (and is affine over `X^N`), for `Y` a closed subscheme
of `X|_{S'}` stable under the action and `S'` locally principal. -/
theorem exists_dilatation_jN {M : Type u} [AddCommMonoid M] {ZX ZY : Over S}
    {act : AAction (GB.overO S) M (yoneda.obj X)} {actY : AAction (GB.overO S) M (yoneda.obj Y)}
    [IsClosedImmersion j.left] (hYI : LiesOver I Y) (hP : LocPrincipal I)
    (hs : Stable j act actY) {N : AddSubmonoid M} (rX : RepresentsAttractor act N (yoneda.obj ZX))
    (rY : RepresentsAttractor actY N (yoneda.obj ZY)) :
    ∃ (B' : Over S) (b' : B' ⟶ ZX), IsDilatation I (jN hs rX rY) b' ∧ IsAffineHom b'.left := by
  have := isClosedImmersion_jN hs rX rY
  exact exists_dilatation (jN hs rX rY) (hYI.of_hom (attEv rY)) hP

/-- **Corollary 13.3**, with the dilatation `Bl_{Y^N}^{D^N} X^N` constructed rather than assumed.
`S'` an effective Cartier divisor of `S`, `X` a smooth `S`-scheme with an action of `D(M)_S`, `Y` a
closed subscheme of `X|_{S'}`, smooth over `S'` and stable under the action, `N` a submonoid of `M`,
the attractors represented by schemes. Then `(Bl_Y^D X)^N → S` is smooth, `b^N` is the dilatation of
`X^N` with center `Y^N`, and the dilatation `Bl_{Y^N}^{D^N} X^N` exists and is canonically
`(Bl_Y^D X)^N` over `X^N`. -/
theorem cor13_3' {M : Type u} [AddCommGroup M] {B ZX ZY ZB : Over S} {b : B ⟶ X}
    {act : AAction (GB.overO S) M (yoneda.obj X)} {actY : AAction (GB.overO S) M (yoneda.obj Y)}
    (hC : IsEffCartier I) [IsClosedImmersion j.left] [Mono j]
    {l : Y.left ⟶ I.subscheme} (hl : l ≫ I.subschemeι = Y.hom) [Smooth l] [Smooth X.hom]
    (hs : Stable j act actY) (hD : IsDilatation I j b)
    {N : AddSubmonoid M} (rX : RepresentsAttractor act N (yoneda.obj ZX))
    (rY : RepresentsAttractor actY N (yoneda.obj ZY))
    (rB : RepresentsAttractor (blAction hs hD) N (yoneda.obj ZB)) :
    Smooth ZB.hom ∧ IsDilatation I (jN hs rX rY) (bN hs hD rX rB) ∧
      ∃ (B' : Over S) (b' : B' ⟶ ZX), IsDilatation I (jN hs rX rY) b' ∧
        ∃ e : ZB ≅ B', e.hom ≫ b' = bN hs hD rX rB := by
  obtain ⟨B', b', hB', -⟩ := exists_dilatation_jN ⟨l, hl⟩ hC.1 hs rX rY
  obtain ⟨h1, h2, h3⟩ := cor13_3 hC hl hs hD rX rY rB hB'
  exact ⟨h1, h2, B', b', hB', h3⟩

/-- **Corollary 13.3**, short form: `(Bl_Y^D X)^N → S` is smooth and `b^N` is the dilatation of `X^N`
with center `Y^N`. -/
theorem cor13_3'' {M : Type u} [AddCommGroup M] {B ZX ZY ZB : Over S} {b : B ⟶ X}
    {act : AAction (GB.overO S) M (yoneda.obj X)} {actY : AAction (GB.overO S) M (yoneda.obj Y)}
    (hC : IsEffCartier I) [IsClosedImmersion j.left] [Mono j]
    {l : Y.left ⟶ I.subscheme} (hl : l ≫ I.subschemeι = Y.hom) [Smooth l] [Smooth X.hom]
    (hs : Stable j act actY) (hD : IsDilatation I j b)
    {N : AddSubmonoid M} (rX : RepresentsAttractor act N (yoneda.obj ZX))
    (rY : RepresentsAttractor actY N (yoneda.obj ZY))
    (rB : RepresentsAttractor (blAction hs hD) N (yoneda.obj ZB)) :
    Smooth ZB.hom ∧ IsDilatation I (jN hs rX rY) (bN hs hD rX rB) :=
  ⟨(cor13_3' hC hl hs hD rX rY rB).1, (cor13_3' hC hl hs hD rX rY rB).2.1⟩

end Cor

end AlgMag.Dil

#print axioms AlgMag.Dil.isPullback_jN
#print axioms AlgMag.Dil.isClosedImmersion_jN
#print axioms AlgMag.Dil.cor13_3''
#print axioms AlgMag.Dil.cor13_3'
