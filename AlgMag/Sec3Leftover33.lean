/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBaseCor
import AlgMag.Sec3Remaining
import AlgMag.Sec3Final

/-!
# Algebraic Magnetism, Example 3.21 on points and Example 3.33 in printed form, over any scheme

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026).

* `AlgMag.GB.exists_att_A_iff`: for `X = 𝔸(L)_S`, a point `x` of `X` lies in `X^N` iff `x(n) = 0` for
  all `n ∈ L`, `n ∉ N`.
* `AlgMag.GB.ex333_axis_points`, `ex333_zero_points`, `ex333_iter`: Example 3.33 as printed: for
  `X = 𝔸(ℕ²)_S`, `X^{ℕ×0} = 𝔸¹_S ×_S 0 ⊆ 𝔸²_S` and `(X^{ℕ×0})^{0×ℕ} = 0_{𝔸²_S} = X^{(ℕ×0)∩(0×ℕ)}`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

noncomputable section

namespace AlgMag.GB

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M] (L N : AddSubmonoid M)

/-- A global section vanishes if it vanishes on every open lying over an affine open of `S`. -/
lemma section_eq_zero_of_liesOver {T : Over S} (r : Γ(T.left, ⊤))
    (H : ∀ (U : S.affineOpens) (W : Over S) (_ : LiesOver W U.1) (s : W ⟶ T),
      s.left.appTop.hom r = 0) : r = 0 := by
  refine TopCat.Presheaf.section_ext T.left.sheaf ⊤ r 0 fun y hy => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (T.hom y)) isOpen_univ
  let A : T.left.Opens := T.hom ⁻¹ᵁ V
  let WO : Over S := Over.mk ((Scheme.Opens.ι A) ≫ T.hom)
  let j : WO ⟶ T := Over.homMk (Scheme.Opens.ι A) rfl
  have hWO : LiesOver WO V := liesOver_of_forall fun z => by
    let z' : (Scheme.Opens.toScheme A) := z
    have h : T.hom ((Scheme.Opens.ι A) z') ∈ V := z'.2
    have e : ((Scheme.Opens.ι A) ≫ T.hom) z' = T.hom ((Scheme.Opens.ι A) z') :=
      Scheme.Hom.comp_apply _ _ _
    rw [← e] at h
    exact h
  have q : (Scheme.Opens.ι A).appTop.hom r = 0 := H ⟨V, hV⟩ WO hWO j
  let y₀ : Scheme.Opens.toScheme A := ⟨y, hyV⟩
  have hinj : Function.Injective ((Scheme.Opens.ι A).stalkMap y₀) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
  refine hinj ?_
  have g1 := Scheme.Hom.germ_stalkMap_apply (Scheme.Opens.ι A) ⊤ y₀ hy r
  have g2 := Scheme.Hom.germ_stalkMap_apply (Scheme.Opens.ι A) ⊤ y₀ hy 0
  refine g1.trans (Eq.trans ?_ g2.symm)
  exact congrArg _ (q.trans (map_zero _).symm)

section Coordinates

variable {U : S.Opens} (hU : IsAffineOpen U)

/-- The coordinate function `X^n` on `𝔸(L)_S`, over the affine open `U`. -/
def coord (n : L) : Aalg (A L S) U :=
  (etaEquiv hU (Aalg (A L S) U)).symm (pts _ (iotaX (A L S) hU) (Multiplicative.ofAdd n))

lemma ptX_iota : ptX (A L S) hU _ (liesOver_Phi hU _) (iotaX (A L S) hU) =
    eta hU (Aalg (A L S) U) := by
  have h : toChart (A L S) hU _ (liesOver_Phi hU _) (iotaX (A L S) hU) = 𝟙 _ :=
    (toChart (A L S) hU _ (liesOver_Phi hU _)).symm.injective
      (((toChart (A L S) hU _ (liesOver_Phi hU _)).symm_apply_apply _).trans
        (Category.id_comp _).symm)
  change homPhi hU _ _ _ (toChart (A L S) hU _ (liesOver_Phi hU _) (iotaX (A L S) hU)) = _
  rw [h]
  rfl

lemma ptX_coord {T : Over S} (hT : LiesOver T U) (t : T ⟶ A L S) (n : L) :
    ptX (A L S) hU T hT t (coord L hU n) = pts T t (Multiplicative.ofAdd n) := by
  let s := toChart (A L S) hU T hT t
  have e : s ≫ iotaX (A L S) hU = t := (toChart (A L S) hU T hT).symm_apply_apply t
  have h1 : ptX (A L S) hU _ (liesOver_Phi hU _) (iotaX (A L S) hU) (coord L hU n) =
      pts _ (iotaX (A L S) hU) (Multiplicative.ofAdd n) := by
    rw [ptX_iota]
    exact (etaEquiv hU (Aalg (A L S) U)).apply_symm_apply _
  have q := ptX_comp (A L S) hU (liesOver_Phi hU _) hT s (iotaX (A L S) hU)
  rw [e] at q
  have e' : pts T t = APt.res s.op (pts _ (iotaX (A L S) hU)) := by
    rw [← pts_comp, e]
  rw [q, e']
  exact congrArg (gpull hU (liesOver_Phi hU _) hT s) h1

lemma coord_mem (n : L) : coord L hU n ∈ gradingOf hU (aAction L S) (n : M) := by
  refine mem_gradingOf_of_forall hU _ fun {T} hT h x => ?_
  rw [ptX_coord, ptX_coord]
  have : pts T ((aAction L S).smul (U := op T) h x) = APt.toMagnet L h * pts T x :=
    Equiv.apply_symm_apply _ _
  rw [this]
  rfl

end Coordinates

/-- The function `n ↦ a(n) y(n)` on `N`, `0` off `N`. -/
def attAux {R : Type u} [CommRing R] (y : Multiplicative L →* R) (a : Multiplicative N →* R)
    (n : L) : R :=
  if hn : (n : M) ∈ N then a (Multiplicative.ofAdd ⟨n, hn⟩) * y (Multiplicative.ofAdd n) else 0

lemma attAux_add {R : Type u} [CommRing R] (y : Multiplicative L →* R) (a : Multiplicative N →* R)
    (hy : ∀ n : L, (n : M) ∉ N → y (Multiplicative.ofAdd n) = 0) (p q : L) :
    attAux L N y a (p + q) = attAux L N y a p * attAux L N y a q := by
  have ey : y (Multiplicative.ofAdd (p + q)) =
      y (Multiplicative.ofAdd p) * y (Multiplicative.ofAdd q) := map_mul y _ _
  unfold attAux
  by_cases hp : (p : M) ∈ N
  · by_cases hq : (q : M) ∈ N
    · have hpq : ((p + q : L) : M) ∈ N := N.add_mem hp hq
      have hh : (Multiplicative.ofAdd ⟨((p + q : L) : M), hpq⟩ : Multiplicative N) =
          Multiplicative.ofAdd ⟨p, hp⟩ * Multiplicative.ofAdd ⟨q, hq⟩ := rfl
      have ea : a (Multiplicative.ofAdd ⟨((p + q : L) : M), hpq⟩) =
          a (Multiplicative.ofAdd ⟨p, hp⟩) * a (Multiplicative.ofAdd ⟨q, hq⟩) := by
        rw [hh, map_mul]
      rw [dif_pos hpq, dif_pos hp, dif_pos hq, ey, ea]
      ring
    · rw [dif_neg hq, mul_zero]
      split_ifs
      · rw [ey, hy q hq]; ring
      · rfl
  · rw [dif_neg hp, zero_mul]
    split_ifs
    · rw [ey, hy p hp]; ring
    · rfl

/-- The monoid map `n ↦ a(n) y(n)` on `N`, `0` off `N`. -/
def attVal {R : Type u} [CommRing R] (y : Multiplicative L →* R) (a : Multiplicative N →* R)
    (hy : ∀ n : L, (n : M) ∉ N → y (Multiplicative.ofAdd n) = 0) : Multiplicative L →* R where
  toFun n := attAux L N y a (Multiplicative.toAdd n)
  map_one' := by
    have h0 : ((0 : L) : M) ∈ N := N.zero_mem
    change attAux L N y a (0 : L) = 1
    unfold attAux
    rw [dif_pos h0]
    have e1 : a (Multiplicative.ofAdd ⟨((0 : L) : M), h0⟩) = 1 := map_one a
    have e2 : y (Multiplicative.ofAdd (0 : L)) = 1 := map_one y
    exact (congrArg₂ (· * ·) e1 e2).trans (one_mul _)
  map_mul' p q := attAux_add L N y a hy _ _

/-- The point of `𝔸(L)^N` attached to `x` vanishing off `N`. -/
def attPt {T : Over S} (x : APt (overO S) L (op T))
    (hx : ∀ n : L, (n : M) ∉ N → x (Multiplicative.ofAdd n) = 0) :
    AttractorPt (aAction L S) N T where
  app {T'} t a := (pts T').symm (attVal L N (APt.res (𝒪 := overO S) t.op x) a fun n hn => by
    change ((overO S).map t.op).hom (x (Multiplicative.ofAdd n)) = 0
    rw [hx n hn, map_zero])
  naturality {T' T''} s t a := by
    apply (pts T'').injective
    refine ((pts T'').apply_symm_apply _).trans ?_
    refine Eq.trans ?_ (pts_comp s _).symm
    rw [Equiv.apply_symm_apply]
    refine MonoidHom.ext fun n => ?_
    change attAux L N (R := (overO S).obj (op T'')) _ _ (Multiplicative.toAdd n) =
      ((overO S).map s.op).hom (attAux L N (R := (overO S).obj (op T')) _ _ _)
    unfold attAux
    split_ifs
    · refine Eq.trans ?_ (map_mul ((overO S).map s.op).hom _ _).symm
      refine congrArg (_ * ·) ?_
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        ((overO S).map_comp t.op s.op)) _
    · exact (map_zero _).symm
  equivariant {T'} t h a := by
    apply (pts T').injective
    refine ((pts T').apply_symm_apply _).trans ?_
    refine Eq.trans ?_ (Equiv.apply_symm_apply (pts T') _).symm
    rw [Equiv.apply_symm_apply]
    refine MonoidHom.ext fun n => ?_
    change attAux L N (R := (overO S).obj (op T')) _ _ (Multiplicative.toAdd n) =
      _ * attAux L N (R := (overO S).obj (op T')) _ _ (Multiplicative.toAdd n)
    unfold attAux
    split_ifs
    · exact mul_assoc (G := Γ(T'.left, ⊤)) _ _ _
    · exact (mul_zero (M₀ := Γ(T'.left, ⊤)) _).symm

lemma pts_attPt_toPoint {T : Over S} (x : APt (overO S) L (op T))
    (hx : ∀ n : L, (n : M) ∉ N → x (Multiplicative.ofAdd n) = 0) :
    pts T (attPt L N x hx).toPoint = x := by
  refine (Equiv.apply_symm_apply (pts T) _).trans (MonoidHom.ext fun n => ?_)
  have hres : APt.res (𝒪 := overO S) (𝟙 T).op x = x := by
    rw [op_id]
    exact APt.res_id x
  change attAux L N (R := (overO S).obj (op T)) (APt.res (𝒪 := overO S) (𝟙 T).op x) 1
    (Multiplicative.toAdd n) = x n
  rw [hres]
  unfold attAux
  split_ifs with hn
  · exact one_mul _
  · exact (hx _ hn).symm

/-- **Example 3.21**, on points, over any scheme `S`: a point `x` of `X = 𝔸(L)_S` lies in `X^N` iff
`x(n) = 0` for all `n ∈ L` with `n ∉ N`. -/
theorem exists_att_A_iff {T : Over S} (t : T ⟶ A L S) :
    (∃ φ : AttractorPt (aAction L S) N T, φ.toPoint = t) ↔
      ∀ n : L, (n : M) ∉ N → pts T t (Multiplicative.ofAdd n) = 0 := by
  constructor
  · rintro ⟨φ, rfl⟩ n hn
    refine section_eq_zero_of_liesOver _ fun U W hW s => ?_
    have hk := (exists_att_iff_kills (aAction L S) U.2 hW (s ≫ φ.toPoint)).mp
      ⟨φ.baseChange s, toPoint_baseChange _ _ _ φ⟩ (coord L U.2 n)
      (mem_magnetIdeal_of_notMem hn (coord_mem L U.2 n))
    have e := ptX_coord L U.2 hW (s ≫ φ.toPoint) n
    have e2 := pts_comp s φ.toPoint
    exact (congrArg (fun z => z (Multiplicative.ofAdd n)) e2).symm.trans (e.symm.trans hk)
  · intro h
    exact ⟨attPt L N (pts T t) h, (pts T).injective (pts_attPt_toPoint L N _ h)⟩

/-! ### Example 3.33 -/

section Ex333

/-- `ℤ²`, in the universe of `S`. -/
abbrev Z2 : Type u := ULift.{u} (ℤ × ℤ)

/-- The down map. -/
abbrev dn : Z2.{u} →+ ℤ × ℤ := (AddEquiv.ulift (α := ℤ × ℤ)).toAddMonoidHom

/-- `ℕ² ⊆ ℤ²`. -/
def Q2 : AddSubmonoid Z2.{u} := quadrant.comap dn
/-- `ℕ × 0`. -/
def X2 : AddSubmonoid Z2.{u} := axisX.comap dn
/-- `0 × ℕ`. -/
def Y2 : AddSubmonoid Z2.{u} := axisY.comap dn

/-- The coordinates. -/
def e1 : Q2.{u} := ⟨⟨(1, 0)⟩, ⟨show (0 : ℤ) ≤ 1 by norm_num, le_refl (0 : ℤ)⟩⟩
/-- The coordinates. -/
def e2 : Q2.{u} := ⟨⟨(0, 1)⟩, ⟨le_refl (0 : ℤ), show (0 : ℤ) ≤ 1 by norm_num⟩⟩

theorem X2_inf_Y2 : X2.{u} ⊓ Y2.{u} = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have h1 : 0 ≤ (x.down).1 ∧ (x.down).2 = 0 := hx.1
  have h2 : (x.down).1 = 0 ∧ 0 ≤ (x.down).2 := hx.2
  exact ULift.ext _ _ (Prod.ext h2.1 h1.2)

variable {S : Scheme.{u}} {T : Over S} (t : T ⟶ A Q2.{u} S)

lemma pts_eq_zero_of_snd (x : APt (overO S) Q2.{u} (op T))
    (h : x (Multiplicative.ofAdd e2) = 0) (n : Q2.{u}) (hn : (n.1.down).2 ≠ 0) :
    x (Multiplicative.ofAdd n) = 0 := by
  have hn2 : 0 ≤ (n.1.down).2 := n.2.2
  have hn1 : 0 ≤ (n.1.down).1 := n.2.1
  let n' : Q2.{u} := ⟨⟨((n.1.down).1, (n.1.down).2 - 1)⟩, ⟨hn1, by
    change 0 ≤ (n.1.down).2 - 1
    omega⟩⟩
  have e : n = n' + e2 := by
    refine Subtype.ext (ULift.ext _ _ (Prod.ext ?_ ?_))
    · change (n.1.down).1 = (n.1.down).1 + 0
      omega
    · change (n.1.down).2 = (n.1.down).2 - 1 + 1
      omega
  rw [e]
  refine (map_mul x (Multiplicative.ofAdd n') (Multiplicative.ofAdd e2)).trans ?_
  rw [h, mul_zero]

lemma pts_eq_zero_of_fst (x : APt (overO S) Q2.{u} (op T))
    (h : x (Multiplicative.ofAdd e1) = 0) (n : Q2.{u}) (hn : (n.1.down).1 ≠ 0) :
    x (Multiplicative.ofAdd n) = 0 := by
  have hn2 : 0 ≤ (n.1.down).2 := n.2.2
  have hn1 : 0 ≤ (n.1.down).1 := n.2.1
  let n' : Q2.{u} := ⟨⟨((n.1.down).1 - 1, (n.1.down).2)⟩, ⟨by
    change 0 ≤ (n.1.down).1 - 1
    omega, hn2⟩⟩
  have e : n = n' + e1 := by
    refine Subtype.ext (ULift.ext _ _ (Prod.ext ?_ ?_))
    · change (n.1.down).1 = (n.1.down).1 - 1 + 1
      omega
    · change (n.1.down).2 = (n.1.down).2 + 0
      omega
  rw [e]
  refine (map_mul x (Multiplicative.ofAdd n') (Multiplicative.ofAdd e1)).trans ?_
  rw [h, mul_zero]

/-- **Example 3.33**, first equality, as printed: for `X = 𝔸(ℕ²)_S` with the action of `D(ℤ²)_S`,
`X^{ℕ×0} = 𝔸¹_S ×_S 0 ⊆ 𝔸²_S`: a point `(x, y)` of `𝔸²` lies in it iff `y = 0`. -/
theorem ex333_axis_points :
    (∃ φ : AttractorPt (aAction Q2.{u} S) X2.{u} T, φ.toPoint = t) ↔
      pts T t (Multiplicative.ofAdd e2) = 0 := by
  rw [exists_att_A_iff]
  constructor
  · intro h
    refine h e2 fun hm => ?_
    have : (1 : ℤ) = 0 := hm.2
    omega
  · intro h n hn
    refine pts_eq_zero_of_snd _ h n fun h0 => hn ?_
    exact ⟨n.2.1, h0⟩

/-- **Example 3.33**, second equality, as printed: `X^{(ℕ×0)∩(0×ℕ)} = 0_{𝔸²_S}`: a point `(x, y)` lies
in it iff `x = y = 0`. -/
theorem ex333_zero_points :
    (∃ φ : AttractorPt (aAction Q2.{u} S) (X2.{u} ⊓ Y2.{u}) T, φ.toPoint = t) ↔
      pts T t (Multiplicative.ofAdd e1) = 0 ∧ pts T t (Multiplicative.ofAdd e2) = 0 := by
  rw [exists_att_A_iff, X2_inf_Y2]
  constructor
  · intro h
    refine ⟨h e1 fun hm => ?_, h e2 fun hm => ?_⟩
    · have : (ULift.up ((1 : ℤ), (0 : ℤ)) : Z2.{u}) = 0 := hm
      have := congrArg (fun z : Z2.{u} => (z.down).1) this
      simp at this
    · have : (ULift.up ((0 : ℤ), (1 : ℤ)) : Z2.{u}) = 0 := hm
      have := congrArg (fun z : Z2.{u} => (z.down).2) this
      simp at this
  · rintro ⟨h1, h2⟩ n hn
    by_cases h0 : (n.1.down).2 = 0
    · refine pts_eq_zero_of_fst _ h1 n fun h3 => hn ?_
      exact ULift.ext _ _ (Prod.ext h3 h0)
    · exact pts_eq_zero_of_snd _ h2 n h0

/-- **Example 3.33**, the iterated attractor: `(X^{ℕ×0})^{0×ℕ} = X^{(ℕ×0)∩(0×ℕ)}`. -/
def ex333_iter (T : Over S) :=
  prop332_i (aAction Q2.{u} S) X2.{u} Y2.{u} T

end Ex333

end AlgMag.GB
