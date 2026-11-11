/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBase
import AlgMag.GeneralBaseChart
import AlgMag.GeneralBaseMilnor

/-!
# Proposition 2.19 over an arbitrary base

For submonoids `N ⊆ L ⊆ L'` of `M` with `L` a face of `L'` and `N' = L' \ (L \ N)`, the scheme
`𝔸(N')_S` is the push-out of `𝔸(N)_S ← 𝔸(L)_S → 𝔸(L')_S` in the category of schemes.

The printed proof cites [Stacks, 0ET0] for the affine case. The map `𝔸(L) → 𝔸(N)` is not integral in
general, so we prove what is needed directly in `AlgMag.GeneralBaseMilnor`.

## Main results

* `AlgMag.GB.faceA`: the morphism `𝔸(F)_S → 𝔸(N)_S` of a face.
* `AlgMag.GB.isPushout_glued`: Proposition 2.19.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open scoped Classical

universe u

namespace AlgMag.GB

variable {M : Type u} [AddCommMonoid M]

section Ext

/-- Extension by zero of a point of `𝔸(F)` to `𝔸(N)`, for a face `F` of `N`. -/
def extZero {F N : AddSubmonoid M} (hc : FaceCond F N) {B : Type u} [CommRing B]
    (a : Multiplicative F →* B) : Multiplicative N →* B where
  toFun n := if h : (Multiplicative.toAdd n : N).1 ∈ F then a (Multiplicative.ofAdd ⟨_, h⟩) else 0
  map_one' := by
    have h0 : ((Multiplicative.toAdd (1 : Multiplicative N) : N) : M) ∈ F := F.zero_mem
    rw [dif_pos h0]
    exact map_one a
  map_mul' x y := by
    by_cases hx : (Multiplicative.toAdd x : N).1 ∈ F
    · by_cases hy : (Multiplicative.toAdd y : N).1 ∈ F
      · have hxy : (Multiplicative.toAdd (x * y) : N).1 ∈ F := F.add_mem hx hy
        rw [dif_pos hx, dif_pos hy, dif_pos hxy, ← map_mul]
        rfl
      · have hxy : (Multiplicative.toAdd (x * y) : N).1 ∉ F := fun h =>
          hy (hc _ (Multiplicative.toAdd x).2 _ (Multiplicative.toAdd y).2 h).2
        rw [dif_neg hy, dif_neg hxy, mul_zero]
    · have hxy : (Multiplicative.toAdd (x * y) : N).1 ∉ F := fun h =>
        hx (hc _ (Multiplicative.toAdd x).2 _ (Multiplicative.toAdd y).2 h).1
      rw [dif_neg hx, dif_neg hxy, zero_mul]

lemma extZero_of_mem {F N : AddSubmonoid M} (hc : FaceCond F N) {B : Type u} [CommRing B]
    (a : Multiplicative F →* B) (n : N) (h : (n : M) ∈ F) :
    extZero hc a (Multiplicative.ofAdd n) = a (Multiplicative.ofAdd ⟨n, h⟩) := dif_pos h

lemma extZero_of_notMem {F N : AddSubmonoid M} (hc : FaceCond F N) {B : Type u} [CommRing B]
    (a : Multiplicative F →* B) (n : N) (h : (n : M) ∉ F) :
    extZero hc a (Multiplicative.ofAdd n) = 0 := dif_neg h

lemma extZero_map {F N : AddSubmonoid M} (hc : FaceCond F N) {B B' : Type u} [CommRing B]
    [CommRing B'] (ρ : B →+* B') (a : Multiplicative F →* B) :
    (ρ : B →* B').comp (extZero hc a) = extZero hc ((ρ : B →* B').comp a) := by
  refine MonoidHom.ext fun n => ?_
  by_cases h : (Multiplicative.toAdd n : N).1 ∈ F
  · exact (congrArg ρ (extZero_of_mem hc a _ h)).trans
      (extZero_of_mem hc ((ρ : B →* B').comp a) _ h).symm
  · exact (congrArg ρ (extZero_of_notMem hc a _ h)).trans
      ((map_zero ρ).trans (extZero_of_notMem hc ((ρ : B →* B').comp a) _ h).symm)

variable (S : Scheme.{u})

/-- **Fact 2.15**: the morphism `𝔸(F)_S → 𝔸(N)_S` of a face `F` of `N`, dual to the projection
`ℤ[N] → ℤ[F]`. -/
def faceA {F N : AddSubmonoid M} (hc : FaceCond F N) : A F S ⟶ A N S :=
  (pts _).symm (extZero hc (pts (A F S) (𝟙 _)))

variable {S}

lemma pts_comp_faceA {F N : AddSubmonoid M} (hc : FaceCond F N) {T : Over S} (g : T ⟶ A F S) :
    pts T (g ≫ faceA S hc) = extZero hc (pts T g) := by
  rw [pts_comp, faceA, Equiv.apply_symm_apply]
  have : pts T g = APt.res g.op (pts (A F S) (𝟙 _)) := by
    rw [← pts_comp, Category.comp_id]
  rw [this]
  exact extZero_map hc (g.left.appTop).hom _

end Ext

section Ring

variable (R : Type u) [CommRing R]

lemma faceProj_one {F N : AddSubmonoid M} (h : F ≤ N) (hc : FaceCond F N) :
    faceProj R h 1 = 1 := by
  by_cases hn : Nontrivial R
  · exact ((isFace_iff h).2 hc).1
  · have := not_nontrivial_iff_subsingleton.1 hn
    exact Subsingleton.elim (α := AddMonoidAlgebra R F) _ _

lemma faceProj_mul {F N : AddSubmonoid M} (h : F ≤ N) (hc : FaceCond F N)
    (a b : AddMonoidAlgebra R N) : faceProj R h (a * b) = faceProj R h a * faceProj R h b := by
  by_cases hn : Nontrivial R
  · exact ((isFace_iff h).2 hc).2 a b
  · have := not_nontrivial_iff_subsingleton.1 hn
    exact Subsingleton.elim (α := AddMonoidAlgebra R F) _ _

/-- The projection `R[N] → R[F]` of a face, as a morphism of `R`-algebras, over any ring `R`. -/
def faceAlg {F N : AddSubmonoid M} (h : F ≤ N) (hc : FaceCond F N) :
    AddMonoidAlgebra R N →ₐ[R] AddMonoidAlgebra R F :=
  AlgHom.ofLinearMap (faceProj R h) (faceProj_one R h hc) (faceProj_mul R h hc)

lemma faceProj_incl {F N : AddSubmonoid M} (h : F ≤ N) (x : AddMonoidAlgebra R F) :
    faceProj R h (incl R h x) = x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n c =>
    rw [incl_single]
    exact faceProj_single_mem h n c

variable {N L L' : AddSubmonoid M} (hNL : N ≤ L) (hLL' : L ≤ L') (hc : FaceCond L L')

/-- **Proposition 2.19**, the rings: `R[N'] = R[L'] ×_{R[L]} R[N]`. -/
theorem milnor_glued : MilnorData (incl R (gluedMagnet_le hNL hc)).toRingHom
    (faceAlg R (le_gluedMagnet hNL hLL' hc) (faceCond_gluedMagnet hNL hc)).toRingHom
    (faceAlg R hLL' hc).toRingHom (incl R hNL).toRingHom where
  comm z := glued_comm R hNL hLL' hc z
  surj x := ⟨incl R hLL' x, faceProj_incl R hLL' x⟩
  inj z h1 h2 := by
    obtain ⟨w, -, hw⟩ := existsUnique_glued R hNL hLL' hc 0 0 (by simp)
    have e1 := hw z ⟨h1, h2⟩
    have e2 := hw 0 ⟨map_zero _, map_zero _⟩
    exact e1.trans e2.symm
  ex x y hxy := by
    obtain ⟨z, ⟨h1, h2⟩, -⟩ := existsUnique_glued R hNL hLL' hc x y hxy
    exact ⟨z, h1, h2⟩

end Ring

section Chart

variable {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)

/-- The algebra `R[N]` over `R = Γ(S, U)`. -/
abbrev Dalg (U : S.Opens) (N : Type u) [AddCommMonoid N] : CommAlgCat.{u} Γ(S, U) :=
  CommAlgCat.of Γ(S, U) (AddMonoidAlgebra Γ(S, U) N)

variable {N : Type u} [AddCommMonoid N]

/-- The point `n ↦ X^n` of `𝔸(N)` over `Spec R[N]`. -/
def univN : APt (overO S) N (op (Phi hU (Dalg U N))) :=
  ((eta hU (Dalg U N) : Dalg U N →* Ga hU _ (liesOver_Phi hU _))).comp
    (AddMonoidAlgebra.of Γ(S, U) N)

/-- The chart `Spec R[N] → 𝔸(N)_S`. -/
def chi : Phi hU (Dalg U N) ⟶ A N S := (pts _).symm (univN hU)

lemma pts_comp_chi {T : Over S} (hT : LiesOver T U) (c : T ⟶ Phi hU (Dalg U N)) :
    pts T (c ≫ chi hU) =
      ((homPhi hU T hT _ c : Dalg U N →* Ga hU T hT)).comp (AddMonoidAlgebra.of Γ(S, U) N) := by
  rw [pts_comp, chi, Equiv.apply_symm_apply]
  have h := homPhi_comp hU (liesOver_Phi hU (Dalg U N)) hT c (𝟙 _)
  rw [Category.comp_id] at h
  rw [h]
  rfl

/-- A morphism to `𝔸(N)_S` from a scheme over `U` factors uniquely through the chart. -/
lemma existsUnique_chi {T : Over S} (hT : LiesOver T U) (x : T ⟶ A N S) :
    ∃ c : T ⟶ Phi hU (Dalg U N), c ≫ chi hU = x := by
  let e : AddMonoidAlgebra Γ(S, U) N →ₐ[Γ(S, U)] Ga hU T hT :=
    AddMonoidAlgebra.lift Γ(S, U) (Ga hU T hT) N (pts T x)
  refine ⟨(homPhi hU T hT (Dalg U N)).symm e, (pts T).injective ?_⟩
  rw [pts_comp_chi hU hT, Equiv.apply_symm_apply]
  refine MonoidHom.ext fun n => ?_
  change e (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) = _
  change AddMonoidAlgebra.lift Γ(S, U) (Ga hU T hT) N (pts T x) _ = _
  exact (AddMonoidAlgebra.lift_single _ _ _).trans (one_smul _ _)

lemma chi_cancel {T : Over S} (hT : LiesOver T U) {c c' : T ⟶ Phi hU (Dalg U N)}
    (h : c ≫ chi hU = c' ≫ chi hU) : c = c' := by
  apply (homPhi hU T hT _).injective
  have h1 := pts_comp_chi hU hT c
  have h2 := pts_comp_chi hU hT c'
  rw [h, h2] at h1
  refine AlgHom.ext fun x => ?_
  induction (x : AddMonoidAlgebra Γ(S, U) N) using AddMonoidAlgebra.induction_linear with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add a b ha hb => exact (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ a b).symm)
  | single n r =>
    have hs : (AddMonoidAlgebra.single n r : AddMonoidAlgebra Γ(S, U) N) =
        r • AddMonoidAlgebra.single n 1 := by simp [AddMonoidAlgebra.smul_single]
    rw [hs]
    refine (map_smul _ r _).trans ((congrArg (r • ·) ?_).trans (map_smul _ r _).symm)
    exact (DFunLike.congr_fun h1 (Multiplicative.ofAdd n)).symm

/-- `Spec R[N] = 𝔸(N)_S ×_S U`. -/
lemma isPullback_chi : IsPullback (chi hU (N := N)).left
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) (Dalg U N)))) (A N S).hom hU.fromSpec := by
  have w : (chi hU (N := N)).left ≫ (A N S).hom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) (Dalg U N))) ≫ hU.fromSpec :=
    Over.w (chi hU (N := N))
  have key : ∀ {W : Scheme.{u}} (a : W ⟶ (A N S).left) (b : W ⟶ Spec Γ(S, U))
      (_ : a ≫ (A N S).hom = b ≫ hU.fromSpec),
      ∃ m : W ⟶ (Phi hU (Dalg U N)).left, m ≫ (chi hU).left = a ∧
        m ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) (Dalg U N))) = b ∧
        ∀ m' : W ⟶ (Phi hU (Dalg U N)).left, m' ≫ (chi hU).left = a → m' = m := by
    intro W a b hab
    let T : Over S := Over.mk (b ≫ hU.fromSpec)
    have hT : LiesOver T U := liesOver_of_forall fun x => by
      have e : (b ≫ hU.fromSpec) x = hU.fromSpec (b x) := Scheme.Hom.comp_apply _ _ _
      change (b ≫ hU.fromSpec) x ∈ U
      rw [e, ← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨_, rfl⟩
    let a' : T ⟶ A N S := Over.homMk a hab
    obtain ⟨c, hc⟩ := existsUnique_chi hU hT a'
    refine ⟨c.left, congrArg (fun k => k.left) hc, ?_, ?_⟩
    · refine (cancel_mono hU.fromSpec).1 ?_
      exact (Category.assoc _ _ _).trans (Over.w c)
    · intro m' hm'
      have hm : m' ≫ (Phi hU (Dalg U N)).hom = T.hom := by
        rw [← Over.w (chi hU (N := N)), ← Category.assoc, hm']
        exact hab
      have := chi_cancel hU hT (c := Over.homMk m' hm) (c' := c)
        (Over.OverMorphism.ext (hm'.trans (congrArg (fun k => k.left) hc).symm))
      exact congrArg (fun k => k.left) this
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => (key s.fst s.snd s.condition).choose) ?_ ?_ ?_⟩⟩
  · exact fun s => (key s.fst s.snd s.condition).choose_spec.1
  · exact fun s => (key s.fst s.snd s.condition).choose_spec.2.1
  · exact fun s m h1 _ => (key s.fst s.snd s.condition).choose_spec.2.2 m h1

instance : IsOpenImmersion (chi hU (N := N)).left :=
  MorphismProperty.of_isPullback (isPullback_chi hU).flip
    (inferInstanceAs (IsOpenImmersion hU.fromSpec))

lemma isOpen_chi : IsOpenImmersion (chi hU (N := N)).left := inferInstance

/-- Every point of `𝔸(N)_S` over `U` is in the chart. -/
lemma mem_range_chi (x : (A N S).left) (hx : (A N S).hom x ∈ U) :
    x ∈ Set.range (chi hU (N := N)).left := by
  have hr : (A N S).hom x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hx
  obtain ⟨y, hy⟩ := hr
  obtain ⟨t, h1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (A N S).hom)
    (g := hU.fromSpec) x y hy.symm
  have hp := isPullback_chi hU (N := N)
  have hopen : IsOpenImmersion (chi hU (N := N)).left := inferInstance
  rw [← h1]
  let e := hp.isoPullback
  refine ⟨e.inv t, ?_⟩
  have h2 : e.inv ≫ (chi hU (N := N)).left = pullback.fst _ _ := hp.isoPullback_inv_fst
  rw [← h2]
  exact (Scheme.Hom.comp_apply _ _ _).symm

/-- A square of `S`-schemes compatible with charts is cartesian. -/
lemma isPullback_chart_map {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (m : A P S ⟶ A Q S)
    (t : Dalg U Q →ₐ[Γ(S, U)] Dalg U P) (hm : chi hU ≫ m = PhiMap hU t ≫ chi hU) :
    IsPullback (chi hU (N := P)).left (PhiMap hU t).left m.left (chi hU (N := Q)).left := by
  have w : (chi hU (N := P)).left ≫ m.left = (PhiMap hU t).left ≫ (chi hU (N := Q)).left :=
    congrArg (fun k => k.left) hm
  have key : ∀ {W : Scheme.{u}} (a : W ⟶ (A P S).left) (b : W ⟶ (Phi hU (Dalg U Q)).left)
      (_ : a ≫ m.left = b ≫ (chi hU (N := Q)).left),
      ∃ c : W ⟶ (Phi hU (Dalg U P)).left, c ≫ (chi hU).left = a ∧ c ≫ (PhiMap hU t).left = b := by
    intro W a b hab
    let T : Over S := Over.mk (b ≫ (Phi hU (Dalg U Q)).hom)
    have hT : LiesOver T U := LiesOver.of_hom (Over.homMk b rfl) (liesOver_Phi hU _)
    have hw : a ≫ (A P S).hom = T.hom := by
      change a ≫ (A P S).hom = b ≫ (Phi hU (Dalg U Q)).hom
      rw [← Over.w m, ← Over.w (chi hU (N := Q)), ← Category.assoc, hab, Category.assoc]
    let a' : T ⟶ A P S := Over.homMk a hw
    let b' : T ⟶ Phi hU (Dalg U Q) := Over.homMk b rfl
    obtain ⟨c, hc⟩ := existsUnique_chi hU hT a'
    refine ⟨c.left, congrArg (fun k => k.left) hc, ?_⟩
    have : c ≫ PhiMap hU t = b' := by
      refine chi_cancel hU hT ?_
      rw [Category.assoc, ← hm, ← Category.assoc, hc]
      exact Over.OverMorphism.ext hab
    exact congrArg (fun k => k.left) this
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => (key s.fst s.snd s.condition).choose) ?_ ?_ ?_⟩⟩
  · exact fun s => (key s.fst s.snd s.condition).choose_spec.1
  · exact fun s => (key s.fst s.snd s.condition).choose_spec.2
  · intro s c h1 _
    rw [← cancel_mono (chi hU (N := P)).left, h1]
    exact (key s.fst s.snd s.condition).choose_spec.1.symm

end Chart

section Main

variable {S : Scheme.{u}} {N L L' : AddSubmonoid M} (hNL : N ≤ L) (hLL' : L ≤ L')
  (hc : FaceCond L L')

/-- The morphism `𝔸(L')_S → 𝔸(N')_S`. -/
abbrev aMor : A L' S ⟶ A (gluedMagnet hNL hc) S :=
  Amap (AddSubmonoid.inclusion (gluedMagnet_le hNL hc)) S

/-- The morphism `𝔸(N)_S → 𝔸(N')_S`. -/
abbrev cMor : A N S ⟶ A (gluedMagnet hNL hc) S := faceA S (faceCond_gluedMagnet hNL hc)

/-- The morphism `𝔸(L)_S → 𝔸(L')_S`. -/
abbrev bAMor : A L S ⟶ A L' S := faceA S hc

/-- The morphism `𝔸(L)_S → 𝔸(N)_S`. -/
abbrev bCMor : A L S ⟶ A N S := Amap (AddSubmonoid.inclusion hNL) S

/-- The square of Proposition 2.19 commutes. -/
lemma square_w : bAMor (S := S) hc ≫ aMor hNL hc = bCMor hNL ≫ cMor hNL hc := by
  refine (pts _).injective ?_
  rw [pts_comp_Amap, pts_comp_faceA]
  have h1 : pts (A L S) (bAMor (S := S) hc) = extZero hc (pts (A L S) (𝟙 _)) :=
    Equiv.apply_symm_apply _ _
  have h2 : pts (A L S) (bCMor (S := S) hNL) =
      (pts (A L S) (𝟙 _)).comp (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hNL)) :=
    Equiv.apply_symm_apply _ _
  rw [h1, h2]
  refine MonoidHom.ext fun x => ?_
  let n : gluedMagnet hNL hc := Multiplicative.toAdd x
  let a0 : APt (overO S) N (op (A L S)) :=
    (pts (A L S) (𝟙 _)).comp (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hNL))
  by_cases h : (n : M) ∈ N
  · exact (extZero_of_mem hc _ (AddSubmonoid.inclusion (gluedMagnet_le hNL hc) n) (hNL h)).trans
      (extZero_of_mem (faceCond_gluedMagnet hNL hc) a0 n h).symm
  · have hL : (n : M) ∉ L := fun hL => n.2.2 ⟨hL, h⟩
    exact (extZero_of_notMem hc _ (AddSubmonoid.inclusion (gluedMagnet_le hNL hc) n) hL).trans
      (extZero_of_notMem (faceCond_gluedMagnet hNL hc) a0 n h).symm

include hLL' in
/-- The square of Proposition 2.19 is cartesian. -/
lemma square_isPullback : IsPullback (bAMor (S := S) hc).left (bCMor hNL).left
    (aMor hNL hc).left (cMor hNL hc).left := by
  have w : (bAMor (S := S) hc).left ≫ (aMor hNL hc).left =
      (bCMor hNL).left ≫ (cMor hNL hc).left :=
    congrArg (fun k : A L S ⟶ A (gluedMagnet hNL hc) S => k.left) (square_w (S := S) hNL hc)
  have key : ∀ {W : Scheme.{u}} (u : W ⟶ (A L' S).left) (v : W ⟶ (A N S).left)
      (_ : u ≫ (aMor hNL hc).left = v ≫ (cMor hNL hc).left),
      ∃ m : W ⟶ (A L S).left, m ≫ (bAMor (S := S) hc).left = u ∧ m ≫ (bCMor hNL).left = v ∧
        ∀ m' : W ⟶ (A L S).left, m' ≫ (bAMor (S := S) hc).left = u → m' = m := by
    intro W u v huv
    let T : Over S := Over.mk (u ≫ (A L' S).hom)
    let u' : T ⟶ A L' S := Over.homMk u rfl
    have hv : v ≫ (A N S).hom = T.hom := by
      change v ≫ _ = u ≫ _
      rw [← Over.w (cMor (S := S) hNL hc), ← Over.w (aMor (S := S) hNL hc), ← Category.assoc,
        ← Category.assoc, huv]
    let v' : T ⟶ A N S := Over.homMk v hv
    have huv' : u' ≫ aMor hNL hc = v' ≫ cMor hNL hc := Over.OverMorphism.ext huv
    have hE := congrArg (pts T) huv'
    rw [pts_comp_Amap, pts_comp_faceA] at hE
    let x := pts T u'
    let wpt : APt (overO S) L (op T) :=
      x.comp (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hLL'))
    let t : T ⟶ A L S := (pts T).symm wpt
    have ht : pts T t = wpt := Equiv.apply_symm_apply _ _
    have h1 : t ≫ bAMor hc = u' := by
      refine (pts T).injective ?_
      rw [pts_comp_faceA, ht]
      refine MonoidHom.ext fun y => ?_
      let n : L' := Multiplicative.toAdd y
      by_cases hn : (n : M) ∈ L
      · exact extZero_of_mem hc wpt n hn
      · refine (extZero_of_notMem hc wpt n hn).trans ?_
        have hmem : (n : M) ∈ gluedMagnet hNL hc := ⟨n.2, fun h => hn h.1⟩
        have hnN : (n : M) ∉ N := fun h => hn (hNL h)
        have := DFunLike.congr_fun hE (Multiplicative.ofAdd (⟨n, hmem⟩ : gluedMagnet hNL hc))
        exact ((extZero_of_notMem (faceCond_gluedMagnet hNL hc) (pts T v') ⟨n, hmem⟩ hnN).symm.trans
          this.symm)
    have h2 : t ≫ bCMor hNL = v' := by
      refine (pts T).injective ?_
      rw [pts_comp_Amap, ht]
      refine MonoidHom.ext fun y => ?_
      let n : N := Multiplicative.toAdd y
      have hmem : (n : M) ∈ gluedMagnet hNL hc := le_gluedMagnet hNL hLL' hc n.2
      have := DFunLike.congr_fun hE (Multiplicative.ofAdd (⟨n, hmem⟩ : gluedMagnet hNL hc))
      exact this.trans (extZero_of_mem (faceCond_gluedMagnet hNL hc) (pts T v') ⟨n, hmem⟩ n.2)
    refine ⟨t.left, congrArg (fun k => k.left) h1, congrArg (fun k => k.left) h2, ?_⟩
    intro m' hm'
    have hm0 : m' ≫ (A L S).hom = T.hom := by
      change m' ≫ _ = u ≫ _
      rw [← hm', Category.assoc, Over.w]
    let m'' : T ⟶ A L S := Over.homMk m' hm0
    have h3 : m'' ≫ bAMor hc = u' := Over.OverMorphism.ext hm'
    have : m'' = t := by
      refine (pts T).injective ?_
      rw [ht]
      refine MonoidHom.ext fun y => ?_
      let n : L := Multiplicative.toAdd y
      have h4 := congrArg (pts T) h3
      rw [pts_comp_faceA] at h4
      have h5 := DFunLike.congr_fun h4 (Multiplicative.ofAdd (AddSubmonoid.inclusion hLL' n))
      exact (extZero_of_mem hc (pts T m'') (AddSubmonoid.inclusion hLL' n) n.2).symm.trans h5
    exact congrArg (fun k => k.left) this
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => (key s.fst s.snd s.condition).choose) ?_ ?_ ?_⟩⟩
  · exact fun s => (key s.fst s.snd s.condition).choose_spec.1
  · exact fun s => (key s.fst s.snd s.condition).choose_spec.2.1
  · exact fun s m h1 _ => (key s.fst s.snd s.condition).choose_spec.2.2 m h1

/-- The chart square for `𝔸(L') → 𝔸(N')`. -/
lemma chi_aMor {U : S.Opens} (hU : IsAffineOpen U) :
    chi hU ≫ aMor hNL hc = PhiMap hU (incl Γ(S, U) (gluedMagnet_le hNL hc)) ≫ chi hU := by
  refine (pts _).injective ?_
  rw [pts_comp_Amap, pts_comp_chi hU (liesOver_Phi hU _), homPhi_PhiMap]
  have h1 : pts (Phi hU (Dalg U L')) (chi hU) = univN hU := Equiv.apply_symm_apply _ _
  rw [h1]
  refine MonoidHom.ext fun x => ?_
  change eta hU _ _ = eta hU _ _
  congr 1
  exact (incl_single _ _ _ _).symm

/-- The chart square for `𝔸(N) → 𝔸(N')`. -/
lemma chi_cMor {U : S.Opens} (hU : IsAffineOpen U) :
    chi hU ≫ cMor hNL hc = PhiMap hU (faceAlg Γ(S, U) (le_gluedMagnet hNL hLL' hc)
      (faceCond_gluedMagnet hNL hc)) ≫ chi hU := by
  refine (pts _).injective ?_
  rw [pts_comp_faceA, pts_comp_chi hU (liesOver_Phi hU _), homPhi_PhiMap]
  have h1 : pts (Phi hU (Dalg U N)) (chi hU) = univN hU := Equiv.apply_symm_apply _ _
  rw [h1]
  refine MonoidHom.ext fun x => ?_
  let n : gluedMagnet hNL hc := Multiplicative.toAdd x
  by_cases h : (n : M) ∈ N
  · refine (extZero_of_mem (faceCond_gluedMagnet hNL hc) _ n h).trans ?_
    change eta hU _ _ = eta hU _ _
    congr 1
    exact (faceProj_single_mem (R := Γ(S, U)) (le_gluedMagnet hNL hLL' hc) ⟨n, h⟩ 1).symm
  · refine (extZero_of_notMem (faceCond_gluedMagnet hNL hc) _ n h).trans ?_
    refine Eq.trans (map_zero (eta hU (Dalg U N))).symm ?_
    change eta hU _ _ = eta hU _ _
    congr 1
    exact (faceProj_single_notMem (R := Γ(S, U)) (le_gluedMagnet hNL hLL' hc) n h 1).symm

include hLL' in
/-- The local form of the push-out property for `𝔸(L')_S → 𝔸(N')_S ← 𝔸(N)_S`. -/
theorem isLocalPO_glued :
    IsLocalPO (aMor (S := S) hNL hc).left (cMor (S := S) hNL hc).left := by
  refine IsLocalPO.of_cover (I := S.affineOpens)
    (Ai := fun U => (Phi U.2 (Dalg U.1 L')).left) (Ci := fun U => (Phi U.2 (Dalg U.1 N)).left)
    (Pi := fun U => (Phi U.2 (Dalg U.1 (gluedMagnet hNL hc))).left)
    (fun U => (chi U.2).left) (fun U => (chi U.2).left) (fun U => (chi U.2).left)
    (fun U => (PhiMap U.2 (incl Γ(S, U.1) (gluedMagnet_le hNL hc))).left)
    (fun U => (PhiMap U.2 (faceAlg Γ(S, U.1) (le_gluedMagnet hNL hLL' hc)
      (faceCond_gluedMagnet hNL hc))).left) (fun U => isOpen_chi U.2) ?_ ?_ ?_ ?_
  · intro x
    obtain ⟨U, z, hz⟩ := S.directedAffineCover.exists_eq ((A _ S).hom x)
    let U' : S.affineOpens := U
    refine ⟨U', mem_range_chi U'.2 x ?_⟩
    rw [← hz]
    exact z.2
  · exact fun U => isPullback_chart_map U.2 _ _ (chi_aMor hNL hc U.2)
  · exact fun U => isPullback_chart_map U.2 _ _ (chi_cMor hNL hLL' hc U.2)
  · exact fun U => (milnor_glued Γ(S, U.1) hNL hLL' hc).isLocalPO

include hLL' in
/-- **Proposition 2.19.** Let `N ⊆ L ⊆ L'` be submonoids of `M`, with `L` a face of `L'`, and
`N' = L' \ (L \ N)` (`AlgMag.gluedMagnet`; it is a submonoid, with `N` as a face:
`AlgMag.faceCond_gluedMagnet`). Then, for any scheme `S`, `𝔸(N')_S` is the push-out of
`𝔸(N)_S ← 𝔸(L)_S → 𝔸(L')_S` in the category of schemes. -/
theorem isPushout_glued : IsPushout (bAMor (S := S) hc).left (bCMor hNL).left
    (aMor hNL hc).left (cMor hNL hc).left :=
  (isLocalPO_glued hNL hLL' hc).isPushout (square_isPullback hNL hLL' hc)

end Main

end AlgMag.GB
