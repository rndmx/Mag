/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover2D

/-!
# Algebraic Magnetism, Example 3.33, with the printed identifications

`X = 𝔸(ℕ²)_S = 𝔸²_S` with the action of `D(ℤ²)_S`. As printed:
`X^{ℕ×0} = 𝔸¹_S ×_S 0_{𝔸¹_S} ⊆ 𝔸²_S` and `X^{(ℕ×0)∩(0×ℕ)} = 0_{𝔸²_S}`.

* `AlgMag.GB.ex333_A2`: `𝔸²_S = 𝔸¹_S ×_S 𝔸¹_S` through the coordinates `p₁`, `p₂`.
* `AlgMag.GB.ex333_printed_axis`: `X^{ℕ×0}`, represented by `repFace`, with its closed immersion
  `faceIota` to `𝔸²_S`, is the fibre product `𝔸²_S ×_{p₂, 𝔸¹_S} 0`, and `p₁` identifies it with `𝔸¹_S`.
* `AlgMag.GB.ex333_printed_zero`: `X^{(ℕ×0)∩(0×ℕ)}` is the zero section of `𝔸²_S`, a closed immersion
  `S → 𝔸²_S` with coordinates `(0, 0)`.

The iterated form `(X^{ℕ×0})^{0×ℕ}` is `AlgMag.GB.ex333_iter`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace AlgMag.GB

variable (S : Scheme.{u})

/-- `ℕ`, in the universe of `S`. -/
abbrev NatU : Type u := ULift.{u} ℕ

/-- The first axis `ℕ → ℕ²`. -/
def axis₁ : NatU.{u} →+ Q2.{u} where
  toFun k := ⟨⟨((k.down : ℤ), 0)⟩, ⟨Int.natCast_nonneg _, le_refl (0 : ℤ)⟩⟩
  map_zero' := rfl
  map_add' a b := Subtype.ext (ULift.ext _ _ (Prod.ext (by simp) (by simp)))

/-- The second axis `ℕ → ℕ²`. -/
def axis₂ : NatU.{u} →+ Q2.{u} where
  toFun k := ⟨⟨(0, (k.down : ℤ))⟩, ⟨le_refl (0 : ℤ), Int.natCast_nonneg _⟩⟩
  map_zero' := rfl
  map_add' a b := Subtype.ext (ULift.ext _ _ (Prod.ext (by simp) (by simp)))

/-- `ℕ² = ℕ × ℕ`. -/
def q2Equiv : NatU.{u} × NatU.{u} ≃+ Q2.{u} where
  toFun k := axis₁ k.1 + axis₂ k.2
  invFun n := (⟨(n.1.down.1).toNat⟩, ⟨(n.1.down.2).toNat⟩)
  left_inv k := by
    refine Prod.ext (ULift.ext _ _ ?_) (ULift.ext _ _ ?_)
    · change ((k.1.down : ℤ) + 0).toNat = k.1.down
      simp
    · change (0 + (k.2.down : ℤ)).toNat = k.2.down
      simp
  right_inv n := by
    have h1 : (0 : ℤ) ≤ n.1.down.1 := n.2.1
    have h2 : (0 : ℤ) ≤ n.1.down.2 := n.2.2
    refine Subtype.ext (ULift.ext _ _ (Prod.ext ?_ ?_))
    · change (((n.1.down.1).toNat : ℕ) : ℤ) + 0 = n.1.down.1
      omega
    · change 0 + (((n.1.down.2).toNat : ℕ) : ℤ) = n.1.down.2
      omega
  map_add' a b := by
    change axis₁ (a.1 + b.1) + axis₂ (a.2 + b.2) = axis₁ a.1 + axis₂ a.2 + (axis₁ b.1 + axis₂ b.2)
    rw [map_add, map_add]
    abel

/-- `𝔸¹_S`. -/
abbrev Line : Over S := A NatU.{u} S

/-- The first coordinate `𝔸²_S → 𝔸¹_S`. -/
def p₁ : A Q2.{u} S ⟶ Line S := Amap axis₁ S
/-- The second coordinate `𝔸²_S → 𝔸¹_S`. -/
def p₂ : A Q2.{u} S ⟶ Line S := Amap axis₂ S

/-- `S` over `S`. -/
abbrev OS : Over S := Over.mk (𝟙 S)

variable {S} in
/-- The structure map to `S`, in `Over S`. -/
def toOS (T : Over S) : T ⟶ OS S := Over.homMk T.hom (Category.comp_id _)

lemma toOS_uniq {T : Over S} (g : T ⟶ OS S) : g = toOS T :=
  Over.OverMorphism.ext ((Category.comp_id _).symm.trans (Over.w g))

open Classical in
/-- The coordinates of the origin of `𝔸¹`. -/
def lineZeroPt (T : Over S) : APt (overO S) NatU.{u} (op T) where
  toFun n := if Multiplicative.toAdd n = 0 then 1 else 0
  map_one' := if_pos rfl
  map_mul' a b := by
    by_cases ha : Multiplicative.toAdd a = 0
    · by_cases hb : Multiplicative.toAdd b = 0
      · have : Multiplicative.toAdd (a * b) = 0 := by rw [toAdd_mul, ha, hb, add_zero]
        simp only [ha, hb, this, if_true, mul_one]
      · have : Multiplicative.toAdd (a * b) ≠ 0 := by
          rw [toAdd_mul, ha, zero_add]; exact hb
        simp only [hb, this, if_false, mul_zero]
    · have : Multiplicative.toAdd (a * b) ≠ 0 := by
        intro h
        apply ha
        rw [toAdd_mul] at h
        have h1 : (Multiplicative.toAdd a).down + (Multiplicative.toAdd b).down = 0 :=
          congrArg ULift.down h
        exact ULift.ext _ _ (by change (Multiplicative.toAdd a).down = 0; omega)
      simp only [ha, this, if_false, zero_mul]

/-- The zero section `0_{𝔸¹_S}` of `𝔸¹_S`. -/
def lineZero : OS S ⟶ Line S := (pts (OS S)).symm (lineZeroPt S (OS S))

/-- The zero section `0_{𝔸²_S}` of `𝔸²_S`. -/
def planeZero : OS S ⟶ A Q2.{u} S := (pts (OS S)).symm (ex333ZeroPt (OS S))

variable {S}

lemma lineZeroPt_ne {T : Over S} {n : Multiplicative NatU.{u}} (h : Multiplicative.toAdd n ≠ 0) :
    lineZeroPt S T n = 0 := if_neg h

lemma pts_comp_p₁ {T : Over S} (t : T ⟶ A Q2.{u} S) (k : NatU.{u}) :
    pts T (t ≫ p₁ S) (Multiplicative.ofAdd k) = pts T t (Multiplicative.ofAdd (axis₁ k)) := by
  rw [p₁, pts_comp_Amap]
  rfl

lemma pts_comp_p₂ {T : Over S} (t : T ⟶ A Q2.{u} S) (k : NatU.{u}) :
    pts T (t ≫ p₂ S) (Multiplicative.ofAdd k) = pts T t (Multiplicative.ofAdd (axis₂ k)) := by
  rw [p₂, pts_comp_Amap]
  rfl

lemma pts_toOS_lineZero (T : Over S) : pts T (toOS T ≫ lineZero S) = lineZeroPt S T := by
  rw [pts_comp, lineZero, Equiv.apply_symm_apply]
  refine MonoidHom.ext fun n => ?_
  by_cases hn : Multiplicative.toAdd n = 0
  · have e : lineZeroPt S (OS S) n = 1 := if_pos hn
    exact (congrArg (fun v => ((overO S).map (toOS T).op).hom v) e).trans
      ((map_one ((overO S).map (toOS T).op).hom).trans (if_pos hn).symm)
  · have e : lineZeroPt S (OS S) n = 0 := if_neg hn
    exact (congrArg (fun v => ((overO S).map (toOS T).op).hom v) e).trans
      ((map_zero ((overO S).map (toOS T).op).hom).trans (if_neg hn).symm)

lemma pts_toOS_planeZero (T : Over S) : pts T (toOS T ≫ planeZero S) = ex333ZeroPt T := by
  rw [pts_comp, planeZero, Equiv.apply_symm_apply]
  refine MonoidHom.ext fun n => ?_
  by_cases hn : Multiplicative.toAdd n = 0
  · have e : ex333ZeroPt (OS S) n = 1 := if_pos hn
    exact (congrArg (fun v => ((overO S).map (toOS T).op).hom v) e).trans
      ((map_one ((overO S).map (toOS T).op).hom).trans (if_pos hn).symm)
  · have e : ex333ZeroPt (OS S) n = 0 := if_neg hn
    exact (congrArg (fun v => ((overO S).map (toOS T).op).hom v) e).trans
      ((map_zero ((overO S).map (toOS T).op).hom).trans (if_neg hn).symm)

lemma pts_Amap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q) :
    pts _ (Amap φ S) = (pts (A Q S) (𝟙 _)).comp (AddMonoidHom.toMultiplicative φ) :=
  (pts _).apply_symm_apply _

/-- `Amap` of an isomorphism of monoids is an isomorphism. -/
lemma isIso_Amap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P ≃+ Q) :
    IsIso (Amap (φ : P →+ Q) S) := by
  refine ⟨Amap (φ.symm : Q →+ P) S, (pts _).injective ?_, (pts _).injective ?_⟩
  · rw [pts_comp_Amap, pts_Amap]
    refine MonoidHom.ext fun n => ?_
    change pts _ (𝟙 _) (Multiplicative.ofAdd (φ (φ.symm (Multiplicative.toAdd n)))) = _
    rw [φ.apply_symm_apply]
    rfl
  · rw [pts_comp_Amap, pts_Amap]
    refine MonoidHom.ext fun n => ?_
    change pts _ (𝟙 _) (Multiplicative.ofAdd (φ.symm (φ (Multiplicative.toAdd n)))) = _
    rw [φ.symm_apply_apply]
    rfl

variable (S)

lemma Amap_comp {P Q R : Type u} [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid R] (φ : P →+ Q)
    (ψ : Q →+ R) : Amap ψ S ≫ Amap φ S = Amap (ψ.comp φ) S := by
  refine (pts _).injective ?_
  rw [pts_comp_Amap, pts_Amap, pts_Amap]
  rfl

lemma q2_inl : (q2Equiv.{u} : NatU.{u} × NatU.{u} →+ Q2.{u}).comp (AddMonoidHom.inl _ _) = axis₁ :=
  AddMonoidHom.ext fun k => by
    change axis₁ k + axis₂ 0 = axis₁ k
    rw [map_zero, add_zero]

lemma q2_inr : (q2Equiv.{u} : NatU.{u} × NatU.{u} →+ Q2.{u}).comp (AddMonoidHom.inr _ _) = axis₂ :=
  AddMonoidHom.ext fun k => by
    change axis₁ 0 + axis₂ k = axis₂ k
    rw [map_zero, zero_add]

/-- **Example 3.33**: `𝔸²_S = 𝔸¹_S ×_S 𝔸¹_S` through the two coordinates (Fact 2.7). -/
theorem ex333_A2 : IsPullback (p₁ S).left (p₂ S).left (Line S).hom (Line S).hom := by
  have hI := isIso_Amap (S := S) (q2Equiv.{u})
  let J : (A Q2.{u} S).left ≅ (A (NatU.{u} × NatU.{u}) S).left :=
    (Over.forget S).mapIso (asIso (Amap (q2Equiv.{u} : NatU.{u} × NatU.{u} →+ Q2.{u}) S))
  have h₁ : J.hom ≫ (Amap (AddMonoidHom.inl NatU.{u} NatU.{u}) S).left = (p₁ S).left := by
    have := congrArg (fun k => k.left) (Amap_comp S (AddMonoidHom.inl NatU.{u} NatU.{u})
      (q2Equiv.{u} : NatU.{u} × NatU.{u} →+ Q2.{u}))
    rw [q2_inl] at this
    exact this
  have h₂ : J.hom ≫ (Amap (AddMonoidHom.inr NatU.{u} NatU.{u}) S).left = (p₂ S).left := by
    have := congrArg (fun k => k.left) (Amap_comp S (AddMonoidHom.inr NatU.{u} NatU.{u})
      (q2Equiv.{u} : NatU.{u} × NatU.{u} →+ Q2.{u}))
    rw [q2_inr] at this
    exact this
  refine IsPullback.of_iso (isPullback_A_prod NatU.{u} NatU.{u} S) J.symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  · refine (Category.comp_id _).trans ?_
    rw [← h₁]
    exact (J.inv_hom_id_assoc _).symm
  · refine (Category.comp_id _).trans ?_
    rw [← h₂]
    exact (J.inv_hom_id_assoc _).symm

/-- `X^{ℕ×0} → 𝔸²_S`, the closed immersion. -/
abbrev faceX : A (Q2.{u} ⊓ X2.{u} : AddSubmonoid Z2.{u}) S ⟶ A Q2.{u} S :=
  faceIota Q2.{u} X2.{u} X2_face

variable {S} in
lemma axis₂_not_mem {k : NatU.{u}} (hk : k ≠ 0) : ((axis₂ k : Q2.{u}) : Z2.{u}) ∉ X2.{u} := by
  intro h
  have h0 : ((k.down : ℕ) : ℤ) = 0 := h.2
  exact hk (ULift.ext _ _ (by exact_mod_cast h0))

lemma pts_faceX : pts _ (faceX S) = extOff Q2.{u} X2.{u} X2_face (pts _ (𝟙 _)) := by
  have := pts_comp_faceIota (S := S) Q2.{u} X2.{u} X2_face (𝟙 _)
  rwa [Category.id_comp] at this

lemma faceX_comp_p₂ : faceX S ≫ p₂ S = toOS _ ≫ lineZero S := by
  refine (pts _).injective ?_
  rw [pts_toOS_lineZero, p₂, pts_comp_Amap, pts_faceX]
  refine MonoidHom.ext fun n => ?_
  by_cases hn : Multiplicative.toAdd n = 0
  · have e0 : n = 1 := hn
    subst e0
    exact (map_one _).trans (map_one _).symm
  · exact (dif_neg (axis₂_not_mem hn)).trans (if_neg hn).symm

/-- **Example 3.33**, first equality, with the printed identification. `X^{ℕ×0}` is represented by
`Y = 𝔸(ℕ² ∩ (ℕ×0))_S` (`repFace`), with `Y → X` the closed immersion `faceX`; and `Y` is the fibre product
`𝔸²_S ×_{p₂, 𝔸¹_S} 0_{𝔸¹_S}`, that is `𝔸¹_S ×_S 0_{𝔸¹_S}` inside `𝔸²_S = 𝔸¹_S ×_S 𝔸¹_S`
(`AlgMag.GB.ex333_A2`), the coordinate `p₁` being an isomorphism `Y = 𝔸¹_S`. -/
theorem ex333_printed_axis :
    (∀ (T : Over S) (z : T ⟶ A (Q2.{u} ⊓ X2.{u} : AddSubmonoid Z2.{u}) S),
      (repFace Q2.{u} X2.{u} X2_face T z).toPoint = z ≫ faceX S) ∧
    IsClosedImmersion (faceX S).left ∧
    IsPullback (faceX S).left (A (Q2.{u} ⊓ X2.{u} : AddSubmonoid Z2.{u}) S).hom
      (p₂ S).left (lineZero S).left ∧
    IsIso (faceX S ≫ p₁ S) := by
  refine ⟨fun T z => repFace_toPoint _ _ _ z, ex333_closed S, ?_, ?_⟩
  · have hc : IsClosedImmersion (faceX S).left := ex333_closed S
    refine IsPullback.of_isLimit' ⟨congrArg (fun k => k.left) (faceX_comp_p₂ S)⟩ ?_
    have hdata : ∀ c : PullbackCone (p₂ S).left (lineZero S).left,
        ∃ l : c.pt ⟶ (A (Q2.{u} ⊓ X2.{u} : AddSubmonoid Z2.{u}) S).left,
          l ≫ (faceX S).left = c.fst ∧ l ≫ (A (Q2.{u} ⊓ X2.{u} : AddSubmonoid Z2.{u}) S).hom = c.snd := by
      intro c
      have hs : c.fst ≫ (A Q2.{u} S).hom = c.snd := by
        have h1 : (p₂ S).left ≫ (Line S).hom = (A Q2.{u} S).hom := Over.w (p₂ S)
        have h2 : (lineZero S).left ≫ (Line S).hom = 𝟙 S := Over.w (lineZero S)
        have h3 := congrArg (· ≫ (Line S).hom) c.condition
        simp only [Category.assoc] at h3
        rw [h1, h2] at h3
        exact h3.trans (Category.comp_id c.snd)
      let T : Over S := Over.mk c.snd
      let x : T ⟶ A Q2.{u} S := Over.homMk c.fst hs
      have hu : x ≫ p₂ S = toOS T ≫ lineZero S := Over.OverMorphism.ext c.condition
      have h2 : pts T x (Multiplicative.ofAdd e2) = 0 := by
        have h := pts_comp_p₂ x (⟨1⟩ : NatU.{u})
        rw [hu, pts_toOS_lineZero] at h
        refine (h.symm.trans ?_)
        exact lineZeroPt_ne fun h0 => one_ne_zero (congrArg ULift.down h0)
      have hx : ∀ n : Q2.{u}, (n : Z2.{u}) ∉ X2.{u} → pts T x (Multiplicative.ofAdd n) = 0 := fun n hn =>
        pts_eq_zero_of_snd _ h2 n fun h0 => hn ⟨n.2.1, h0⟩
      let l := (pts T).symm (resInf Q2.{u} X2.{u} (pts T x))
      have hl : l ≫ faceX S = x := by
        refine (pts T).injective ?_
        rw [pts_comp_faceIota, Equiv.apply_symm_apply, extOff_resInf _ _ _ _ hx]
      exact ⟨l.left, congrArg (fun k => k.left) hl, Over.w l⟩
    refine PullbackCone.IsLimit.mk _ (fun c => (hdata c).choose) (fun c => (hdata c).choose_spec.1)
      (fun c => (hdata c).choose_spec.2) fun c m h1 _ => ?_
    exact (cancel_mono (faceX S).left).1 (h1.trans (hdata c).choose_spec.1.symm)
  · let ψ : NatU.{u} ≃+ (Q2.{u} ⊓ X2.{u} : AddSubmonoid Z2.{u}) :=
      { toFun := fun k => ⟨⟨((k.down : ℤ), 0)⟩, AddSubmonoid.mem_inf.mpr
          ⟨⟨Int.natCast_nonneg _, le_refl (0 : ℤ)⟩, ⟨Int.natCast_nonneg _, rfl⟩⟩⟩
        invFun := fun n => ⟨(n.1.down.1).toNat⟩
        left_inv := fun k => ULift.ext _ _ (by simp)
        right_inv := fun n => by
          have h := AddSubmonoid.mem_inf.mp n.2
          have h1 : (0 : ℤ) ≤ n.1.down.1 := h.1.1
          have h2 : n.1.down.2 = (0 : ℤ) := h.2.2
          refine Subtype.ext (ULift.ext _ _ (Prod.ext ?_ h2.symm))
          change (((n.1.down.1).toNat : ℕ) : ℤ) = n.1.down.1
          omega
        map_add' := fun a b => Subtype.ext (ULift.ext _ _ (Prod.ext (by simp) (by simp))) }
    have hψ : faceX S ≫ p₁ S = Amap (ψ : NatU.{u} →+ (Q2.{u} ⊓ X2.{u} : AddSubmonoid Z2.{u})) S := by
      refine (pts _).injective ?_
      rw [p₁, pts_comp_Amap, pts_faceX, pts_Amap]
      refine MonoidHom.ext fun n => ?_
      exact dif_pos (show ((axis₁ (Multiplicative.toAdd n) : Q2.{u}) : Z2.{u}) ∈ X2.{u} from
        ⟨Int.natCast_nonneg _, rfl⟩)
    rw [hψ]
    exact isIso_Amap ψ

/-- `𝔸(ℕ² ∩ 0)_S` has one point over each `T`. -/
lemma botA_hom_ext {T : Over S} (x y : T ⟶ A (Q2.{u} ⊓ ⊥ : AddSubmonoid Z2.{u}) S) : x = y := by
  refine (pts T).injective (MonoidHom.ext fun n => ?_)
  have hn : n = 1 := by
    refine Multiplicative.toAdd.injective (Subtype.ext ?_)
    exact AddSubmonoid.mem_bot.mp (AddSubmonoid.mem_inf.mp (Multiplicative.toAdd n).2).2
  rw [hn, map_one, map_one]

/-- The zero section is `S = 𝔸(ℕ² ∩ 0)_S → 𝔸²_S`. -/
lemma planeZero_factor :
    planeZero S = (pts (OS S)).symm 1 ≫ faceIota Q2.{u} ⊥ bot_face := by
  refine (pts _).injective ?_
  rw [pts_comp_faceIota, planeZero, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine MonoidHom.ext fun n => ?_
  by_cases hn : Multiplicative.toAdd n = 0
  · have e0 : n = 1 := hn
    subst e0
    exact (map_one _).trans (map_one _).symm
  · have hm : ((Multiplicative.toAdd n : Q2.{u}) : Z2.{u}) ∉ (⊥ : AddSubmonoid Z2.{u}) :=
      fun h => hn (Subtype.ext (AddSubmonoid.mem_bot.mp h))
    have e : extOff Q2.{u} ⊥ bot_face (1 : APt (overO S) _ (op (OS S))) n = 0 := dif_neg hm
    have e1 : ex333ZeroPt (OS S) n = 0 := if_neg hn
    exact e1.trans e.symm

/-- **Example 3.33**, second equality, with the printed identification:
`X^{(ℕ×0)∩(0×ℕ)} = 0_{𝔸²_S}`. A point of `𝔸²_S` lies in this attractor iff it factors through the zero
section, a closed immersion `S → 𝔸²_S` with coordinates `(0_{𝔸¹_S}, 0_{𝔸¹_S})`. -/
theorem ex333_printed_zero :
    (∀ (T : Over S) (t : T ⟶ A Q2.{u} S),
      (∃ φ : AttractorPt (aAction Q2.{u} S) (X2.{u} ⊓ Y2.{u}) T, φ.toPoint = t) ↔
        t = toOS T ≫ planeZero S) ∧
    IsClosedImmersion (planeZero S).left ∧
    planeZero S ≫ p₁ S = lineZero S ∧ planeZero S ≫ p₂ S = lineZero S := by
  refine ⟨fun T t => ?_, ?_, ?_, ?_⟩
  · have hz : ∃ φ : AttractorPt (aAction Q2.{u} S) (X2.{u} ⊓ Y2.{u}) T,
        φ.toPoint = toOS T ≫ planeZero S := by
      rw [exists_att_A_iff, pts_toOS_planeZero]
      intro n hn
      refine if_neg fun h0 => hn ?_
      have e : (Multiplicative.toAdd (Multiplicative.ofAdd n)) = n := rfl
      rw [e] at h0
      rw [h0]
      exact AddSubmonoid.zero_mem _
    refine ⟨fun h => ?_, fun h => h ▸ hz⟩
    exact (ex333_zero_unique T).unique h hz
  · let e : OS S ⟶ A (Q2.{u} ⊓ ⊥ : AddSubmonoid Z2.{u}) S := (pts (OS S)).symm 1
    have hi : IsIso e :=
      ⟨toOS _, (toOS_uniq S _).trans (toOS_uniq S _).symm, botA_hom_ext S _ _⟩
    have hl : IsIso e.left := inferInstanceAs (IsIso ((Over.forget S).map e))
    have hc : IsClosedImmersion (faceIota (S := S) Q2.{u} ⊥ bot_face).left := ex333_zero_closed S
    rw [planeZero_factor]
    change IsClosedImmersion (e.left ≫ (faceIota (S := S) Q2.{u} ⊥ bot_face).left)
    infer_instance
  · refine (pts _).injective (MonoidHom.ext fun n => ?_)
    have hL : pts (OS S) (lineZero S) = lineZeroPt S (OS S) := (pts _).apply_symm_apply _
    rw [p₁, pts_comp_Amap, planeZero, Equiv.apply_symm_apply, hL]
    by_cases hn : Multiplicative.toAdd n = 0
    · have e0 : n = 1 := hn
      subst e0
      exact (map_one _).trans (map_one _).symm
    · refine Eq.trans ?_ (lineZeroPt_ne hn).symm
      refine (if_neg fun h => hn (ULift.ext _ _ ?_))
      have : (((Multiplicative.toAdd n).down : ℕ) : ℤ) = 0 := congrArg (fun z : Q2.{u} => z.1.down.1) h
      exact_mod_cast this
  · refine (pts _).injective (MonoidHom.ext fun n => ?_)
    have hL : pts (OS S) (lineZero S) = lineZeroPt S (OS S) := (pts _).apply_symm_apply _
    rw [p₂, pts_comp_Amap, planeZero, Equiv.apply_symm_apply, hL]
    by_cases hn : Multiplicative.toAdd n = 0
    · have e0 : n = 1 := hn
      subst e0
      exact (map_one _).trans (map_one _).symm
    · refine Eq.trans ?_ (lineZeroPt_ne hn).symm
      refine (if_neg fun h => hn (ULift.ext _ _ ?_))
      have : (((Multiplicative.toAdd n).down : ℕ) : ℤ) = 0 := congrArg (fun z : Q2.{u} => z.1.down.2) h
      exact_mod_cast this

end AlgMag.GB

#print axioms AlgMag.GB.ex333_A2
#print axioms AlgMag.GB.ex333_printed_axis
#print axioms AlgMag.GB.ex333_printed_zero
