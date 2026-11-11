/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalMisc331Ring
import AlgMag.DoubleScalarSpaces
import AlgMag.Sec3Rest

/-!
# Proposition 3.31 (ii) for a separated algebraic space, `Z = ℤ`, `Y = ℕ`

`f : M → ℤ` arbitrary, `f = d g` with `g` zero or with `1` in its image. `AlgMag.DoubleScalar` has the case of `g`.
Here `f = d`. The printed map is `(u, x) ↦ u x^d`, `D(ℤ) × 𝔸(ℕ) → 𝔸(N)`. It is an fppf cover here (`FinalMisc331Ring`);
the printed fpqc quotient by `D(K)` is replaced by this cover. Compatibility on the fibre product is the printed
"closed equalizer": the universal fibre product is `Spec R[Q]`, with `Q ⊆ ℤ × ℤ × ℕ`, and `R[Q] → R[ℤ × ℤ × ℕ]` is injective,
`(c, u, x)` being sent to the pair `(u, x)`, `(u c^{-d}, c x)`. `X` is separated (not in the printed statement): this
is where the printed proof uses that the equalizer is closed, and it is what `HasDensePullback`-type arguments need.
-/

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

namespace AlgMag.FinalMisc

open AlgMag AlgMag.DoubleScalar AlgMag.SQ

variable {B : BigFppfSite.{0}} {S : Scheme.{0}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type} {a : AAction (fppfO B S hS) ℤ F}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `ℤ × ℕ`. -/
abbrev PP : Type := ℤ × posN

variable (d : ℕ)

/-- The action of `G_m` through `d`. -/
abbrev actD (a : AAction (fppfO B S hS) ℤ F) : AAction (fppfO B S hS) ℤ F := actAlong (mulD d) a

/-- `(u, x) ↦ u • ψ(x)`. -/
def gValD {T : BigFppfOver B S hS} (ψ : AttractorPt (actD d a) posN T) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (c : APt (fppfO B S hS) PP (op T')) : F.obj (op T') :=
  a.smul (APt.along (AddMonoidHom.inl ℤ posN) c) (ψ.app t (APt.along (AddMonoidHom.inr ℤ posN) c))

lemma gValD_res {T : BigFppfOver B S hS} (ψ : AttractorPt (actD d a) posN T) {T' T'' : BigFppfOver B S hS}
    (s : T'' ⟶ T') (t : T' ⟶ T) (c : APt (fppfO B S hS) PP (op T')) :
    gValD d ψ (s ≫ t) (APt.res s.op c) = F.map s.op (gValD d ψ t c) := by
  refine Eq.trans ?_ (a.map_smul s.op _ _).symm
  exact congrArg (a.smul _) (ψ.naturality s t (APt.along (AddMonoidHom.inr ℤ posN) c))

/-! ### The universal fibre product -/

variable {d} (hd : 0 < d)

include hd in
lemma emod_add_split (c c' : ℤ) :
    ((c + c') % (d : ℤ) = c % d + c' % d ∧ (c + c') / (d : ℤ) = c / d + c' / d) ∨
      ((c + c') % (d : ℤ) = c % d + c' % d - d ∧ (c + c') / (d : ℤ) = c / d + c' / d + 1) := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have r0 := Int.emod_nonneg c hd'.ne'
  have r1 := Int.emod_lt_of_pos c hd'
  have s0 := Int.emod_nonneg c' hd'.ne'
  have s1 := Int.emod_lt_of_pos c' hd'
  have e1 := Int.mul_ediv_add_emod c d
  have e2 := Int.mul_ediv_add_emod c' d
  by_cases h : c % (d : ℤ) + c' % d < d
  · left
    have := (Int.ediv_emod_unique (a := c + c') (q := c / d + c' / d) (r := c % d + c' % d) hd').2
      ⟨by rw [mul_add]; omega, by omega, h⟩
    exact ⟨this.2, this.1⟩
  · right
    have := (Int.ediv_emod_unique (a := c + c') (q := c / d + c' / d + 1) (r := c % d + c' % d - d) hd').2
      ⟨by rw [mul_add, mul_add, mul_one]; omega, by omega, by omega⟩
    exact ⟨this.2, this.1⟩

/-- The monoid of the fibre product: `(c, e, n)` with `c mod d ≤ n`. -/
def Qd : AddSubmonoid (ℤ × PP) where
  carrier := {p | p.1 % (d : ℤ) ≤ (p.2.2 : ℤ)}
  zero_mem' := by
    change (0 : ℤ) % (d : ℤ) ≤ 0
    simp
  add_mem' := by
    intro p p' hp hp'
    change (p.1 + p'.1) % (d : ℤ) ≤ (p.2.2 : ℤ) + (p'.2.2 : ℤ)
    have hd' : (0 : ℤ) < d := by exact_mod_cast hd
    have h2 : p.1 % (d : ℤ) ≤ (p.2.2 : ℤ) := hp
    have h3 : p'.1 % (d : ℤ) ≤ (p'.2.2 : ℤ) := hp'
    rcases emod_add_split hd p.1 p'.1 with h | h <;> omega

/-- `(i, y) ↦ (0, i, y)`: the first point. -/
def j₁ : PP →+ Qd hd where
  toFun p := ⟨(0, p), by
    change (0 : ℤ) % (d : ℤ) ≤ (p.2 : ℤ)
    rw [Int.zero_emod]
    exact p.2.2⟩
  map_zero' := rfl
  map_add' p q := Subtype.ext (Prod.ext (by simp) rfl)

/-- `(k, y) ↦ (y - k d, k, y)`: the second point. -/
def j₂ : PP →+ Qd hd where
  toFun p := ⟨((p.2 : ℤ) - p.1 * d, p), by
    change ((p.2 : ℤ) - p.1 * d) % (d : ℤ) ≤ (p.2 : ℤ)
    have hd' : (0 : ℤ) < d := by exact_mod_cast hd
    rw [show (p.2 : ℤ) - p.1 * d = (p.2 : ℤ) + (-p.1) * d by ring, Int.add_mul_emod_self_right]
    have y0 : (0 : ℤ) ≤ p.2 := p.2.2
    have e1 := Int.mul_ediv_add_emod (p.2 : ℤ) d
    have : 0 ≤ (p.2 : ℤ) / d := Int.ediv_nonneg y0 hd'.le
    nlinarith⟩
  map_zero' := Subtype.ext (Prod.ext (by simp) rfl)
  map_add' p q := Subtype.ext (Prod.ext (by
    change (((p + q).2 : ℤ)) - (p + q).1 * d = _ + _
    change ((p.2 : ℤ) + (q.2 : ℤ)) - (p.1 + q.1) * d = ((p.2 : ℤ) - p.1 * d) + ((q.2 : ℤ) - q.1 * d)
    ring) rfl)

/-- The normal form on `Q`: the point `(i, y)` of the first factor in `(c, e, n)`. -/
def nfA (p : Qd hd) : PP :=
  (p.1.2.1 + p.1.1 / (d : ℤ), ⟨(p.1.2.2 : ℤ) - p.1.1 % (d : ℤ), show (0 : ℤ) ≤ _ from sub_nonneg.2 p.2⟩)

/-- The normal form on `Q`: the point of the second factor in `(c, e, n)`. -/
def nfC (p : Qd hd) : PP :=
  (-(p.1.1 / (d : ℤ)), ⟨p.1.1 % (d : ℤ), show (0 : ℤ) ≤ _ from Int.emod_nonneg _ (by exact_mod_cast hd.ne')⟩)

/-- `(1, d)`, the generator of the relation. -/
def rel1 : PP := (1, ⟨(d : ℤ), Int.natCast_nonneg d⟩)

/-- The point of `𝔸(Q)` given by two points `c₁`, `c₂` of `𝔸(ℤ × ℕ)` with the same image under `(u, x) ↦ u x^d`. -/
def hQ {W : Type} [CommMonoid W] (c₁ c₂ : Multiplicative PP →* W)
    (hr : c₁ (Multiplicative.ofAdd (rel1 (d := d))) = c₂ (Multiplicative.ofAdd (rel1 (d := d)))) :
    Multiplicative (Qd hd) →* W where
  toFun p := c₁ (Multiplicative.ofAdd (nfA hd (Multiplicative.toAdd p))) *
    c₂ (Multiplicative.ofAdd (nfC hd (Multiplicative.toAdd p)))
  map_one' := by
    have hA : nfA hd (0 : Qd hd) = 0 := by
      refine Prod.ext ?_ (Subtype.ext ?_)
      · change (0 : ℤ) + (0 : ℤ) / (d : ℤ) = 0
        simp
      · change (0 : ℤ) - (0 : ℤ) % (d : ℤ) = 0
        simp
    have hC : nfC hd (0 : Qd hd) = 0 := by
      refine Prod.ext ?_ (Subtype.ext ?_)
      · change -((0 : ℤ) / (d : ℤ)) = 0
        simp
      · change (0 : ℤ) % (d : ℤ) = 0
        simp
    change c₁ (Multiplicative.ofAdd (nfA hd 0)) * c₂ (Multiplicative.ofAdd (nfC hd 0)) = 1
    rw [hA, hC]
    simp
  map_mul' p q := by
    change c₁ (Multiplicative.ofAdd (nfA hd (Multiplicative.toAdd p + Multiplicative.toAdd q))) *
      c₂ (Multiplicative.ofAdd (nfC hd (Multiplicative.toAdd p + Multiplicative.toAdd q))) = _
    set P := Multiplicative.toAdd p
    set Q := Multiplicative.toAdd q
    have hsum : ∀ {x y : PP}, c₁ (Multiplicative.ofAdd (x + y)) =
        c₁ (Multiplicative.ofAdd x) * c₁ (Multiplicative.ofAdd y) := fun {x y} => map_mul c₁ _ _
    have hsum2 : ∀ {x y : PP}, c₂ (Multiplicative.ofAdd (x + y)) =
        c₂ (Multiplicative.ofAdd x) * c₂ (Multiplicative.ofAdd y) := fun {x y} => map_mul c₂ _ _
    rcases emod_add_split hd P.1.1 Q.1.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have eA : nfA hd (P + Q) = nfA hd P + nfA hd Q := by
        refine Prod.ext ?_ (Subtype.ext ?_)
        · change (P.1.2.1 + Q.1.2.1) + (P.1.1 + Q.1.1) / (d : ℤ) = _ + _
          change _ = (P.1.2.1 + P.1.1 / (d : ℤ)) + (Q.1.2.1 + Q.1.1 / (d : ℤ))
          rw [h2]; ring
        · change ((P.1.2.2 : ℤ) + (Q.1.2.2 : ℤ)) - (P.1.1 + Q.1.1) % (d : ℤ) =
            ((P.1.2.2 : ℤ) - P.1.1 % (d : ℤ)) + ((Q.1.2.2 : ℤ) - Q.1.1 % (d : ℤ))
          rw [h1]; ring
      have eC : nfC hd (P + Q) = nfC hd P + nfC hd Q := by
        refine Prod.ext ?_ (Subtype.ext ?_)
        · change -((P.1.1 + Q.1.1) / (d : ℤ)) = -(P.1.1 / (d : ℤ)) + -(Q.1.1 / (d : ℤ))
          rw [h2]; ring
        · exact h1
      rw [eA, eC, hsum, hsum2]
      exact mul_mul_mul_comm _ _ _ _
    · have eA : nfA hd (P + Q) = nfA hd P + nfA hd Q + rel1 (d := d) := by
        refine Prod.ext ?_ (Subtype.ext ?_)
        · change (P.1.2.1 + Q.1.2.1) + (P.1.1 + Q.1.1) / (d : ℤ) =
            (P.1.2.1 + P.1.1 / (d : ℤ)) + (Q.1.2.1 + Q.1.1 / (d : ℤ)) + 1
          rw [h2]; ring
        · change ((P.1.2.2 : ℤ) + (Q.1.2.2 : ℤ)) - (P.1.1 + Q.1.1) % (d : ℤ) =
            ((P.1.2.2 : ℤ) - P.1.1 % (d : ℤ)) + ((Q.1.2.2 : ℤ) - Q.1.1 % (d : ℤ)) + (d : ℤ)
          rw [h1]; ring
      have eC : nfC hd P + nfC hd Q = nfC hd (P + Q) + rel1 (d := d) := by
        refine Prod.ext ?_ (Subtype.ext ?_)
        · change -(P.1.1 / (d : ℤ)) + -(Q.1.1 / (d : ℤ)) = -((P.1.1 + Q.1.1) / (d : ℤ)) + 1
          rw [h2]; ring
        · change P.1.1 % (d : ℤ) + Q.1.1 % (d : ℤ) = (P.1.1 + Q.1.1) % (d : ℤ) + (d : ℤ)
          rw [h1]; ring
      change _ = (c₁ (Multiplicative.ofAdd (nfA hd P)) * c₂ (Multiplicative.ofAdd (nfC hd P))) *
        (c₁ (Multiplicative.ofAdd (nfA hd Q)) * c₂ (Multiplicative.ofAdd (nfC hd Q)))
      have eC' : c₂ (Multiplicative.ofAdd (nfC hd P)) * c₂ (Multiplicative.ofAdd (nfC hd Q)) =
          c₂ (Multiplicative.ofAdd (nfC hd (P + Q))) * c₂ (Multiplicative.ofAdd (rel1 (d := d))) := by
        rw [← hsum2, ← hsum2, eC]
      rw [eA, hsum, hsum, hr, mul_mul_mul_comm (c₁ (Multiplicative.ofAdd (nfA hd P))) (c₂ _) (c₁ _) (c₂ _), eC']
      exact (mul_assoc _ _ _).trans (congrArg _ (mul_comm _ _))

lemma hQ_j₁ {W : Type} [CommMonoid W] (c₁ c₂ : Multiplicative PP →* W)
    (hr : c₁ (Multiplicative.ofAdd (rel1 (d := d))) = c₂ (Multiplicative.ofAdd (rel1 (d := d)))) :
    (hQ hd c₁ c₂ hr).comp (AddMonoidHom.toMultiplicative (j₁ hd)) = c₁ := by
  refine MonoidHom.ext fun p => ?_
  have hA : nfA hd (j₁ hd (Multiplicative.toAdd p)) = Multiplicative.toAdd p := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change (Multiplicative.toAdd p).1 + (0 : ℤ) / (d : ℤ) = _
      simp
    · change ((Multiplicative.toAdd p).2 : ℤ) - (0 : ℤ) % (d : ℤ) = _
      simp
  have hC : nfC hd (j₁ hd (Multiplicative.toAdd p)) = 0 := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change -((0 : ℤ) / (d : ℤ)) = 0
      simp
    · change (0 : ℤ) % (d : ℤ) = 0
      simp
  change c₁ (Multiplicative.ofAdd (nfA hd (j₁ hd (Multiplicative.toAdd p)))) *
    c₂ (Multiplicative.ofAdd (nfC hd (j₁ hd (Multiplicative.toAdd p)))) = _
  rw [hA, hC]
  change _ * c₂ 1 = _
  rw [map_one, mul_one]
  rfl

include hd in
lemma hQ_j₂_aux (p : PP) : ∃ q : N₀ d, nfA hd (j₂ hd p) = jnD d q ∧ jnD d q + nfC hd (j₂ hd p) = p := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have y0 : (0 : ℤ) ≤ p.2 := p.2.2
  have hq : (0 : ℤ) ≤ (p.2 : ℤ) / d := Int.ediv_nonneg y0 hd'.le
  have ediv : ((p.2 : ℤ) - p.1 * d) / (d : ℤ) = (p.2 : ℤ) / d - p.1 := by
    rw [show (p.2 : ℤ) - p.1 * d = (p.2 : ℤ) + (-p.1) * d by ring, Int.add_mul_ediv_right _ _ hd'.ne']
    ring
  have emod : ((p.2 : ℤ) - p.1 * d) % (d : ℤ) = (p.2 : ℤ) % d := by
    rw [show (p.2 : ℤ) - p.1 * d = (p.2 : ℤ) + (-p.1) * d by ring, Int.add_mul_emod_self_right]
  have e1 := Int.mul_ediv_add_emod (p.2 : ℤ) d
  refine ⟨⟨(p.2 : ℤ) / d, (mem_N₀ d hd _).2 hq⟩, ?_, ?_⟩
  · refine Prod.ext ?_ (Subtype.ext ?_)
    · change p.1 + ((p.2 : ℤ) - p.1 * d) / (d : ℤ) = (p.2 : ℤ) / d
      rw [ediv]; ring
    · change (p.2 : ℤ) - ((p.2 : ℤ) - p.1 * d) % (d : ℤ) = mulD d ((p.2 : ℤ) / d)
      rw [emod, mulD_apply]
      linarith
  · refine Prod.ext ?_ (Subtype.ext ?_)
    · change (p.2 : ℤ) / d + -(((p.2 : ℤ) - p.1 * d) / (d : ℤ)) = p.1
      rw [ediv]; ring
    · change mulD d ((p.2 : ℤ) / d) + ((p.2 : ℤ) - p.1 * d) % (d : ℤ) = p.2
      rw [emod, mulD_apply]
      linarith

lemma hQ_j₂ {W : Type} [CommMonoid W] (c₁ c₂ : Multiplicative PP →* W)
    (hr : c₁ (Multiplicative.ofAdd (rel1 (d := d))) = c₂ (Multiplicative.ofAdd (rel1 (d := d))))
    (hrel : c₁.comp (AddMonoidHom.toMultiplicative (jnD d)) = c₂.comp (AddMonoidHom.toMultiplicative (jnD d))) :
    (hQ hd c₁ c₂ hr).comp (AddMonoidHom.toMultiplicative (j₂ hd)) = c₂ := by
  refine MonoidHom.ext fun p => ?_
  obtain ⟨q, h1, h2⟩ := hQ_j₂_aux hd (Multiplicative.toAdd p)
  change c₁ (Multiplicative.ofAdd (nfA hd (j₂ hd (Multiplicative.toAdd p)))) *
    c₂ (Multiplicative.ofAdd (nfC hd (j₂ hd (Multiplicative.toAdd p)))) = _
  rw [h1]
  have e := DFunLike.congr_fun hrel (Multiplicative.ofAdd q)
  change c₁ (Multiplicative.ofAdd (jnD d q)) = c₂ (Multiplicative.ofAdd (jnD d q)) at e
  rw [e]
  refine (map_mul c₂ _ _).symm.trans (congrArg c₂ ?_)
  exact congrArg Multiplicative.ofAdd h2

/-! ### The compatibility -/

/-- `(i, y) ↦ (0, i, y)` in `ℤ × ℤ × ℕ`. -/
def j₁' : PP →+ ℤ × PP := (Qd hd).subtype.comp (j₁ hd)
/-- `(k, y) ↦ (y - k d, k, y)` in `ℤ × ℤ × ℕ`. -/
def j₂' : PP →+ ℤ × PP := (Qd hd).subtype.comp (j₂ hd)

/-- **The computation on `D(ℤ) × D(ℤ) × 𝔸(ℕ)`.** `(u, x)` and `(u c^{-d}, c x)` have the same value. -/
lemma gVal_twist {T : BigFppfOver B S hS} (ψ : AttractorPt (actD d a) posN T) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (e : APt (fppfO B S hS) (ℤ × PP) (op T')) :
    gValD d ψ t (APt.along (j₁' hd) e) = gValD d ψ t (APt.along (j₂' hd) e) := by
  let g : APt (fppfO B S hS) ℤ (op T') := APt.along (AddMonoidHom.inl ℤ PP) e
  have e1 : APt.along (AddMonoidHom.inr ℤ posN) (APt.along (j₂' hd) e) =
      APt.toMagnet posN g * APt.along (AddMonoidHom.inr ℤ posN) (APt.along (j₁' hd) e) := by
    refine MonoidHom.ext fun y => ?_
    refine Eq.trans (congrArg e ?_) (map_mul e _ _)
    refine congrArg Multiplicative.ofAdd (Prod.ext ?_ (Prod.ext ?_ ?_))
    · change ((Multiplicative.toAdd y : posN) : ℤ) - 0 * d = ((Multiplicative.toAdd y : posN) : ℤ) + 0
      simp
    · change (0 : ℤ) = 0 + 0
      rfl
    · exact (zero_add _).symm
  have e2 : APt.along (AddMonoidHom.inl ℤ posN) (APt.along (j₁' hd) e) =
      APt.along (AddMonoidHom.inl ℤ posN) (APt.along (j₂' hd) e) * g.comp (AddMonoidHom.toMultiplicative (mulD d)) := by
    refine MonoidHom.ext fun k => ?_
    refine Eq.trans (congrArg e ?_) (map_mul e _ _)
    refine congrArg Multiplicative.ofAdd (Prod.ext ?_ (Prod.ext ?_ ?_))
    · change (0 : ℤ) = ((0 : ℤ) - (Multiplicative.toAdd k) * d) + mulD d (Multiplicative.toAdd k)
      rw [mulD_apply]; ring
    · exact (add_zero _).symm
    · exact (add_zero _).symm
  change a.smul _ _ = a.smul _ (ψ.app t _)
  rw [e1, ψ.equivariant, e2, a.mul_smul]
  rfl

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- `Spec` of an injective map of monoid algebras is dense for maps to a separated space. -/
lemma dense_specAlong {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type} (hsep : IsSeparatedOver X) {P' P : Type} [AddCommMonoid P]
    [AddCommMonoid P'] [Countable P] [Countable P'] (g : P' →+ P) (hg : Function.Injective g)
    {x y : X.obj (op (specObj P' T))}
    (h : X.map (specAlong T g).op x = X.map (specAlong T g).op y) : x = y := by
  refine eq_of_forall_restrict_eq hsep (ι := Unit) (fun _ => specAlong T g) ?_ fun _ => h
  intro z hz
  have hsu : Function.Surjective (Scheme.ΓSpecIso (.of (gRing P' T))).inv.hom := fun w =>
    ⟨(Scheme.ΓSpecIso (.of (gRing P' T))).hom.hom w, by
      simpa using congrArg (fun k => k.hom w) (Scheme.ΓSpecIso (.of (gRing P' T))).hom_inv_id⟩
  obtain ⟨z, rfl⟩ := hsu z
  have h1 := hz ()
  rw [map_specAlong] at h1
  have h2 := (appTop_sp_inv (monι g _) z).symm.trans h1
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of (gRing P T))).inv.hom := fun w w' hw => by
    simpa using congrArg (Scheme.ΓSpecIso (.of (gRing P T))).hom.hom hw
  have h3 : monι g _ z = 0 := hinj (h2.trans (map_zero _).symm)
  have h4 : z = 0 := AddMonoidAlgebra.mapDomain_injective hg (h3.trans (by simp))
  rw [h4, map_zero]
  rfl

include hd in
/-- **The compatibility on the fibre product of `(u, x) ↦ u x^d`**: the printed closed equalizer. -/
theorem gVal_eq (hsep : IsSeparatedOver F) (ψ : AttractorPt (actD d a) posN T) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (c₁ c₂ : APt (fppfO B S hS) PP (op T'))
    (hc : APt.along (jnD d) c₁ = APt.along (jnD d) c₂) : gValD d ψ t c₁ = gValD d ψ t c₂ := by
  have hrq : c₁ (Multiplicative.ofAdd (rel1 (d := d))) = c₂ (Multiplicative.ofAdd (rel1 (d := d))) := by
    have e := DFunLike.congr_fun hc (Multiplicative.ofAdd ⟨1, (mem_N₀ d hd _).2 zero_le_one⟩)
    refine Eq.trans (congrArg c₁ ?_) (e.trans (congrArg c₂ ?_))
    · exact congrArg Multiplicative.ofAdd (Prod.ext rfl (Subtype.ext (by simp [rel1, jnD])))
    · exact congrArg Multiplicative.ofAdd (Prod.ext rfl (Subtype.ext (by simp [rel1, jnD])))
  let Q := Qd hd
  let A := gValD d ψ (specPr Q T) (APt.along (j₁ hd) (specPt Q T))
  let C := gValD d ψ (specPr Q T) (APt.along (j₂ hd) (specPt Q T))
  have hAC : A = C := by
    refine dense_specAlong hsep (Qd hd).subtype Subtype.val_injective ?_
    have hL : ∀ j : PP →+ Q, F.map (specAlong T (Qd hd).subtype).op
        (gValD d ψ (specPr Q T) (APt.along j (specPt Q T))) =
        gValD d ψ (specPr (ℤ × PP) T) (APt.along ((Qd hd).subtype.comp j) (specPt (ℤ × PP) T)) := by
      intro j
      rw [← gValD_res, specAlong_pr]
      congr 1
      have e := res_specAlong T (Qd hd).subtype
      exact congrArg (fun z => z.comp (AddMonoidHom.toMultiplicative j)) e
    rw [show A = _ from rfl, show C = _ from rfl, hL, hL]
    exact gVal_twist hd ψ _ _
  let κ : T' ⟶ specObj Q T := specLift t (hQ hd c₁ c₂ hrq)
  have hκ : ∀ j : PP →+ Q, F.map κ.op (gValD d ψ (specPr Q T) (APt.along j (specPt Q T))) =
      gValD d ψ t ((hQ hd c₁ c₂ hrq).comp (AddMonoidHom.toMultiplicative j)) := by
    intro j
    rw [← gValD_res]
    have e1 : κ ≫ specPr Q T = t := specLift_pr t _
    rw [e1]
    congr 1
    exact congrArg (fun z => z.comp (AddMonoidHom.toMultiplicative j)) (res_specLift t (hQ hd c₁ c₂ hrq))
  have h1 := hκ (j₁ hd)
  have h2 := hκ (j₂ hd)
  rw [hQ_j₁] at h1
  rw [hQ_j₂ hd c₁ c₂ hrq hc] at h2
  rw [← h1, ← h2]
  exact congrArg _ hAC

/-! ### The descent -/

include hd in
/-- `(u, x) ↦ u x^d` is an fppf cover. -/
theorem cover_jnD : Sieve.generate (Presieve.singleton (specAlong T (jnD d))) ∈ BigFppfOver.topology B S hS (specObj (N₀ d) T) := by
  have hfl : Flat (specAlong T (jnD d) |> (BigFppfOver.toScheme B S hS).map) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (flat_of_isFreeAlong _ (isFreeAlong_jnD d hd))
  have hlf : LocallyOfFinitePresentation (specAlong T (jnD d) |> (BigFppfOver.toScheme B S hS).map) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr (fp_jnD d hd _)
  have hsu : Surjective (specAlong T (jnD d) |> (BigFppfOver.toScheme B S hS).map) :=
    ⟨comap_jnD_surjective d hd _⟩
  exact Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS _ hsu hfl hlf

include hd in
theorem exists_chi (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F) (hsep : IsSeparatedOver F)
    (ψ : AttractorPt (actD d a) posN T) :
    ∃ χ : F.obj (op (specObj (N₀ d) T)),
      F.map (specAlong T (jnD d)).op χ = gValD d ψ (specPr PP T) (specPt PP T) := by
  have hsf := (Presieve.isSheafFor_iff_generate _).2 (hF _ (cover_jnD hd (T := T)))
  let x : Presieve.FamilyOfElements F (Presieve.singleton (specAlong T (jnD d))) := fun _ f hf =>
    (Presieve.singleton.rec (motive := fun Y f _ => F.obj (op Y))
      (gValD d ψ (specPr PP T) (specPt PP T)) hf)
  have hx : x.Compatible := by
    rintro Y₁ Y₂ W g₁ g₂ f₁ f₂ ⟨⟩ ⟨⟩ comm
    change F.map g₁.op (gValD d ψ (specPr PP T) (specPt PP T)) = F.map g₂.op (gValD d ψ (specPr PP T) (specPt PP T))
    rw [← gValD_res, ← gValD_res]
    have hh : g₁ ≫ specPr PP T = g₂ ≫ specPr PP T := by
      rw [← specAlong_pr T (jnD d), ← Category.assoc, ← Category.assoc, comm]
    rw [hh]
    refine gVal_eq hd hsep ψ _ _ _ ?_
    have e := res_specAlong T (jnD d)
    have e1 : ∀ g : W ⟶ specObj PP T, APt.along (jnD d) (APt.res g.op (specPt PP T)) =
        APt.res (g ≫ specAlong T (jnD d)).op (specPt (N₀ d) T) := by
      intro g
      rw [op_comp, APt.res_comp, e]
      rfl
    rw [e1, e1, comm]
  obtain ⟨χ, hχ, -⟩ := hsf x hx
  exact ⟨χ, hχ _ (Presieve.singleton.mk)⟩

lemma chi_on {ψ : AttractorPt (actD d a) posN T} {χ : F.obj (op (specObj (N₀ d) T))}
    (hχ : F.map (specAlong T (jnD d)).op χ = gValD d ψ (specPr PP T) (specPt PP T))
    {T' : BigFppfOver B S hS} (t : T' ⟶ T) (c : APt (fppfO B S hS) PP (op T')) :
    F.map (specLift t (APt.along (jnD d) c)).op χ = gValD d ψ t c := by
  rw [specLift_along, op_comp, Functor.map_comp_apply, hχ, ← gValD_res, specLift_pr, res_specLift]

/-- The sieve on which a point of `𝔸(N)` comes from `D(ℤ) × 𝔸(ℕ)`. -/
def liftSieve {T' : BigFppfOver B S hS} (b : APt (fppfO B S hS) (N₀ d) (op T')) : Sieve T' where
  arrows {W} s := ∃ c : APt (fppfO B S hS) PP (op W), APt.along (jnD d) c = APt.res s.op b
  downward_closed := by
    rintro W W' s ⟨c, hc⟩ g
    refine ⟨APt.res g.op c, ?_⟩
    rw [op_comp, APt.res_comp, ← hc]
    rfl

include hd in
theorem liftSieve_mem {T' : BigFppfOver B S hS} (t : T' ⟶ T) (b : APt (fppfO B S hS) (N₀ d) (op T')) :
    liftSieve b ∈ BigFppfOver.topology B S hS T' := by
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable (specLift t b) (cover_jnD hd (T := T)))
  rintro W s ⟨Z, w, g, ⟨⟩, hf⟩
  refine ⟨APt.res w.op (specPt PP T), ?_⟩
  have e := res_specAlong T (jnD d)
  have e0 : APt.along (jnD d) (APt.res w.op (specPt PP T)) =
      APt.res (w ≫ specAlong T (jnD d)).op (specPt (N₀ d) T) := by
    rw [op_comp, APt.res_comp, e]
    rfl
  rw [e0, hf, op_comp, APt.res_comp, res_specLift]

/-- `(u, x) ↦ u x^d` on points. -/
lemma along_jnD {W : BigFppfOver B S hS} (c : APt (fppfO B S hS) PP (op W)) :
    APt.along (jnD d) c = APt.toMagnet (N₀ d) (APt.along (AddMonoidHom.inl ℤ posN) c) *
      (APt.along (AddMonoidHom.inr ℤ posN) c).comp (AddMonoidHom.toMultiplicative (linMagnetHom (mulD d) posN)) := by
  refine MonoidHom.ext fun n => ?_
  refine Eq.trans (congrArg c ?_) (map_mul c _ _)
  exact congrArg Multiplicative.ofAdd (Prod.ext (add_zero _).symm (zero_add _).symm)

/-- The point of `X^N` over `ψ`. -/
def chiPt (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F) {ψ : AttractorPt (actD d a) posN T}
    {χ : F.obj (op (specObj (N₀ d) T))}
    (hχ : F.map (specAlong T (jnD d)).op χ = gValD d ψ (specPr PP T) (specPt PP T)) :
    AttractorPt a (N₀ d) T where
  app t b := F.map (specLift t b).op χ
  naturality s t b := by
    rw [specLift_comp, op_comp, Functor.map_comp_apply]
  equivariant {T'} t h b := by
    refine (hF _ (liftSieve_mem hd t b)).isSeparatedFor.ext ?_
    rintro W s ⟨c, hc⟩
    have nat : ∀ b' : APt (fppfO B S hS) (N₀ d) (op T'),
        F.map s.op (F.map (specLift t b').op χ) = F.map (specLift (s ≫ t) (APt.res s.op b')).op χ := by
      intro b'
      rw [specLift_comp, op_comp, Functor.map_comp_apply]
    let c' : APt (fppfO B S hS) PP (op W) :=
      (APt.res s.op h).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst ℤ posN)) * c
    have e1 : APt.res s.op (APt.toMagnet (N₀ d) h * b) = APt.along (jnD d) c' := by
      rw [APt.res_mul, ← hc]
      rfl
    have e2 : APt.along (AddMonoidHom.inl ℤ posN) c' = APt.res s.op h * APt.along (AddMonoidHom.inl ℤ posN) c := by
      refine MonoidHom.ext fun k => rfl
    have e3 : APt.along (AddMonoidHom.inr ℤ posN) c' = APt.along (AddMonoidHom.inr ℤ posN) c := by
      refine MonoidHom.ext fun y => ?_
      change (APt.res s.op h) (Multiplicative.ofAdd (0 : ℤ)) * _ = _
      rw [show (APt.res s.op h) (Multiplicative.ofAdd (0 : ℤ)) = 1 from map_one _, one_mul]
      rfl
    rw [nat, e1, chi_on hχ, a.map_smul, nat, ← hc, chi_on hχ]
    change a.smul _ (ψ.app _ _) = a.smul _ (a.smul _ (ψ.app _ _))
    rw [e2, e3, a.mul_smul]

include hd in
/-- **Proposition 3.31 (ii)** for `f = d`, `T` affine. -/
theorem existsUnique_ptAlong_d (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F) (hsep : IsSeparatedOver F)
    (ψ : AttractorPt (actD d a) posN T) : ∃! φ : AttractorPt a (N₀ d) T, ptAlong a φ = ψ := by
  obtain ⟨χ, hχ⟩ := exists_chi hd hF hsep ψ
  refine ⟨chiPt hd hF hχ, ?_, fun φ hφ => ?_⟩
  · refine AttractorPt.ext ?_
    funext T' t y
    let c : APt (fppfO B S hS) PP (op T') := y.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd ℤ posN))
    have e1 : APt.along (jnD d) c = y.comp (AddMonoidHom.toMultiplicative (linMagnetHom (mulD d) posN)) := rfl
    have e2 : APt.along (AddMonoidHom.inl ℤ posN) c = 1 := MonoidHom.ext fun k => map_one y
    have e3 : APt.along (AddMonoidHom.inr ℤ posN) c = y := MonoidHom.ext fun _ => rfl
    change F.map (specLift t (y.comp (AddMonoidHom.toMultiplicative (linMagnetHom (mulD d) posN)))).op χ = ψ.app t y
    rw [← e1, chi_on hχ]
    change a.smul _ (ψ.app t _) = _
    rw [e2, e3, a.one_smul]
  · refine AttractorPt.ext ?_
    funext T' t b
    refine (hF _ (liftSieve_mem hd t b)).isSeparatedFor.ext ?_
    rintro W s ⟨c, hc⟩
    have e1 := φ.naturality s t b
    change F.map s.op (φ.app t b) = F.map s.op (F.map (specLift t b).op χ)
    rw [← e1, ← hc, ← Functor.map_comp_apply, ← op_comp, ← specLift_comp, ← hc]
    rw [chi_on hχ, along_jnD, φ.equivariant]
    change _ = a.smul _ (ψ.app _ _)
    rw [← hφ]
    rfl

/-! ### Gluing and the general `f` -/

include hd in
/-- **Proposition 3.31 (ii)** for `f = d`, any `T`. -/
theorem ptAlong_d_bijective (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F) (hsep : IsSeparatedOver F)
    (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong a : AttractorPt a (N₀ d) T → AttractorPt (actD d a) posN T) := by
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  have hsh := isSheaf_attractor a (N₀ d) _ hF
  have hshB := isSheaf_attractor (actD d a) posN _ hF
  have hbc : ∀ {W W' : BigFppfOver B S hS} (s : W' ⟶ W) (φ : AttractorPt a (N₀ d) W),
      ptAlong a (AttractorPt.baseChange s φ) = AttractorPt.baseChange s (ptAlong a φ) := fun _ _ => rfl
  have hbcc : ∀ {W W' W'' : BigFppfOver B S hS} (s : W' ⟶ W) (s' : W'' ⟶ W') (φ : AttractorPt a (N₀ d) W),
      AttractorPt.baseChange (s' ≫ s) φ = AttractorPt.baseChange s' (AttractorPt.baseChange s φ) := by
    intro W W' W'' s s' φ
    refine AttractorPt.ext ?_
    funext T' t b
    change φ.app (t ≫ s' ≫ s) b = φ.app ((t ≫ s') ≫ s) b
    rw [Category.assoc]
  have hbcB : ∀ {W W' W'' : BigFppfOver B S hS} (s : W' ⟶ W) (s' : W'' ⟶ W') (φ : AttractorPt (actD d a) posN W),
      AttractorPt.baseChange (s' ≫ s) φ = AttractorPt.baseChange s' (AttractorPt.baseChange s φ) := by
    intro W W' W'' s s' φ
    refine AttractorPt.ext ?_
    funext T' t b
    change φ.app (t ≫ s' ≫ s) b = φ.app ((t ≫ s') ≫ s) b
    rw [Category.assoc]
  have hinj : Function.Injective (ptAlong a : AttractorPt a (N₀ d) T → AttractorPt (actD d a) posN T) := by
    intro χ χ' h
    refine (hsh _ hcov).isSeparatedFor.ext ?_
    rintro W g ⟨W', u, b, ⟨i⟩, rfl⟩
    have := hV i
    have e : AttractorPt.baseChange (π i) χ = AttractorPt.baseChange (π i) χ' :=
      (existsUnique_ptAlong_d hd hF hsep (AttractorPt.baseChange (π i) (ptAlong a χ))).unique
        (hbc _ _) ((hbc _ _).trans (congrArg _ h.symm))
    change AttractorPt.baseChange (u ≫ π i) χ = AttractorPt.baseChange (u ≫ π i) χ'
    rw [hbcc, hbcc, e]
  refine ⟨hinj, fun φ => ?_⟩
  have key : ∀ {W : BigFppfOver B S hS} (g : W ⟶ T), (Sieve.ofArrows V π) g →
      ∃ χ : AttractorPt a (N₀ d) W, ptAlong a χ = AttractorPt.baseChange g φ := by
    rintro W g ⟨W', u, b, ⟨i⟩, rfl⟩
    have := hV i
    obtain ⟨χ, hχ, -⟩ := existsUnique_ptAlong_d hd hF hsep (AttractorPt.baseChange (π i) φ)
    refine ⟨AttractorPt.baseChange u χ, ?_⟩
    rw [hbc, hχ, hbcB]
  choose x hx using @key
  have hcomp : Presieve.FamilyOfElements.Compatible (P := attractor a (N₀ d))
      (R := (Sieve.ofArrows V π).arrows) (fun _ g hg => x g hg) := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ comm
    have huniq : ∀ {W₀ : BigFppfOver B S hS} (χ χ' : AttractorPt a (N₀ d) W₀), ptAlong a χ = ptAlong a χ' → χ = χ' := by
      intro W₀ χ χ' he
      obtain ⟨I', V', π', hV', hcov'⟩ := exists_affine_cover W₀
      refine (hsh _ hcov').isSeparatedFor.ext ?_
      rintro W₁ g ⟨W₂, u, b, ⟨i⟩, rfl⟩
      have := hV' i
      have e : AttractorPt.baseChange (π' i) χ = AttractorPt.baseChange (π' i) χ' :=
        (existsUnique_ptAlong_d hd hF hsep (AttractorPt.baseChange (π' i) (ptAlong a χ))).unique
          (hbc _ _) ((hbc _ _).trans (congrArg _ he.symm))
      change AttractorPt.baseChange (u ≫ π' i) χ = AttractorPt.baseChange (u ≫ π' i) χ'
      rw [hbcc, hbcc, e]
    apply huniq
    change ptAlong a (AttractorPt.baseChange g₁ (x f₁ h₁)) = ptAlong a (AttractorPt.baseChange g₂ (x f₂ h₂))
    rw [hbc, hbc, hx, hx, ← hbcB, ← hbcB, comm]
  have hamal := (hsh _ hcov).isAmalgamation hcomp
  let t : AttractorPt a (N₀ d) T := (hsh _ hcov).amalgamate _ hcomp
  refine ⟨t, (hshB _ hcov).isSeparatedFor.ext ?_⟩
  intro W g hg
  have e : AttractorPt.baseChange g t = x g hg := hamal g hg
  exact (hbc g t).symm.trans ((congrArg (ptAlong a) e).trans (hx g hg))

/-- `f = d g` with `d > 0` and `1` in the image of `g`, or `f = 0`. -/
theorem exists_d_primitive {M : Type} [AddCommGroup M] (f : M →+ ℤ) :
    f = 0 ∨ ∃ (d : ℕ) (g : M →+ ℤ) (m₀ : M), 0 < d ∧ f = (mulD d).comp g ∧ g m₀ = 1 := by
  by_cases hf : f = 0
  · exact Or.inl hf
  refine Or.inr ?_
  obtain ⟨g, hc, hg⟩ := exists_primitive f
  rcases hg with rfl | ⟨m₀, hm⟩
  · exfalso
    apply hf
    refine AddMonoidHom.ext fun m => ?_
    have h1 : m ∈ posN.comap f := by
      rw [← hc]
      exact le_refl (0 : ℤ)
    have h2 : -m ∈ posN.comap f := by
      rw [← hc]
      exact le_refl (0 : ℤ)
    have h1' : 0 ≤ f m := h1
    have h2' : 0 ≤ f (-m) := h2
    rw [map_neg] at h2'
    change f m = 0
    omega
  · have hpos : 0 ≤ f m₀ := by
      have : m₀ ∈ posN.comap g := show (0 : ℤ) ≤ g m₀ by rw [hm]; exact zero_le_one
      rw [hc] at this
      exact this
    have hne : f m₀ ≠ 0 := by
      intro h0
      apply hf
      refine AddMonoidHom.ext fun m => ?_
      have key : ∀ m, 0 ≤ g m → 0 ≤ f m := fun m hm' => by
        have : m ∈ posN.comap g := hm'
        rw [hc] at this
        exact this
      have key2 : ∀ m, 0 ≤ f m → 0 ≤ g m := fun m hm' => by
        have : m ∈ posN.comap f := hm'
        rw [← hc] at this
        exact this
      let r := m - g m • m₀
      have gr : g r = 0 := by simp [r, hm]
      have fr : f r = 0 := by
        have h1 := key r gr.ge
        have h2 := key (-r) (by rw [map_neg, gr]; simp)
        rw [map_neg] at h2
        omega
      have : f m = f r + g m * f m₀ := by simp [r]
      rw [this, fr, h0]
      simp
    have hfac : ∀ m, f m = g m * f m₀ := by
      intro m
      have key : ∀ m, 0 ≤ g m → 0 ≤ f m := fun m hm' => by
        have : m ∈ posN.comap g := hm'
        rw [hc] at this
        exact this
      let r := m - g m • m₀
      have gr : g r = 0 := by simp [r, hm]
      have fr : f r = 0 := by
        have h1 := key r gr.ge
        have h2 := key (-r) (by rw [map_neg, gr]; simp)
        rw [map_neg] at h2
        omega
      have : f m = f r + g m * f m₀ := by simp [r]
      rw [this, fr, zero_add]
    refine ⟨(f m₀).toNat, g, m₀, by omega, AddMonoidHom.ext fun m => ?_, hm⟩
    change f m = mulD _ (g m)
    rw [mulD_apply, hfac m, Int.toNat_of_nonneg hpos]

/-- **Proposition 3.31 (ii)**, `Z = ℤ`, `Y = ℕ`: `X` a separated algebraic space over any `S`, `M` a finitely generated
abelian group, `f : M → ℤ` any morphism. `X^{f⁻¹(ℕ)}_M = X^ℕ_ℤ`, the action of `G_m` being through `f`. `S` is in the
universe `0` because `ℤ` is. -/
theorem prop331_ii_spaces {M : Type} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type}
    {aX : AAction (fppfO B S hS) M X} (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (f : M →+ ℤ)
    (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong aX : AttractorPt aX (posN.comap f) T → AttractorPt (actAlong f aX) posN T) := by
  have hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  rcases exists_d_primitive f with rfl | ⟨d, g, m₀, hd, rfl, hm⟩
  · exact ptAlong_bijective_space hX hsep (Or.inl rfl) T
  have stepA : ∀ Y' : AddSubmonoid ℤ, Y' = posN →
      Function.Bijective (ptAlong aX : AttractorPt aX (Y'.comap g) T → AttractorPt (actAlong g aX) Y' T) := by
    rintro Y' rfl
    exact ptAlong_bijective_of_primitive g hm T
  have hY : N₀ d = posN := by
    ext m
    exact mem_N₀ d hd m
  exact (ptAlong_d_bijective hd hF hsep T).comp (stepA (N₀ d) hY)

end AlgMag.FinalMisc

#print axioms AlgMag.FinalMisc.prop331_ii_spaces
