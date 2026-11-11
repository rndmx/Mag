/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.DoubleScalarSpaces
import AlgMag.Sec3Intersections
import AlgMag.Sec3SchemeQuotient

/-!
# §16.4 (ii): two stages of `G_m`-attractors, the printed route

Mayeux, *Algebraic Magnetism*, §16.4 (ii): "Using Propositions 3.32 and 3.31, we have
`X^{ℕ×ℕ} = (X^{ℕ×ℤ})^{ℤ×ℕ} = (X^{ℕ×0}_{ℤ×0})^{0×ℕ}_{0×ℤ}`".

Here `f₁, f₂ : M → ℤ` have `1` in their image, `N_i = f_i⁻¹(ℕ)`; `M = ℤ²`, `f_i` the projections is the printed case
(`S` in the universe `0`, because `M : Type u`). `X` is a scheme, the case in which Proposition 3.32 (ii) is
formalized (`prop332_scheme`). Proposition 3.31 in this primitive case holds for any functor with an action,
`DoubleScalar.ptAlong_bijective_of_primitive`; it is reproved for the iterated attractor `IterPt`, because `X^{N₁}` as a
functor takes values in a larger universe, where `AttractorPt` is not defined. The direct proof `AlgMag.S16.stagesEquiv` stays, for any functor.

Section 16.4 (i) is not treated here.
-/

suppress_compilation

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgMag.Sec164

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M]

section Along

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) M F)

open AlgMag.DoubleScalar

/-- `m ↦ m - f(m) m₀`, into `f⁻¹(ℕ)`. -/
def retrZ (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) : M →+ posN.comap f where
  toFun m := ⟨m - f m • m₀, by
    change (0 : ℤ) ≤ f (m - f m • m₀)
    simp [h]⟩
  map_zero' := by ext; simp
  map_add' x y := by
    ext
    simp only [map_add, add_zsmul, AddSubmonoid.coe_add]
    abel

/-- `b ↦ b m₀`, into `f⁻¹(ℕ)`. -/
def secZ (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) : posN →+ posN.comap f where
  toFun b := ⟨(b : ℤ) • m₀, by
    change (0 : ℤ) ≤ f ((b : ℤ) • m₀)
    have hb : (0 : ℤ) ≤ (b : ℤ) := b.2
    simpa [h] using hb⟩
  map_zero' := by ext; simp
  map_add' x y := by
    ext
    simp [add_zsmul]

/-- `z ↦ z m₀`. -/
def mulZ (m₀ : M) : ℤ →+ M := (zmultiplesHom M) m₀


/-- The action of `𝔸(ℤ)` through `f : M → ℤ`. -/
noncomputable def actZ (f : M →+ ℤ) : AAction (fppfO B S hS) ℤ F where
  smul h x := act.smul (h.comp (AddMonoidHom.toMultiplicative f)) x
  one_smul x := act.one_smul x
  mul_smul g h x := act.mul_smul (g.comp (AddMonoidHom.toMultiplicative f))
    (h.comp (AddMonoidHom.toMultiplicative f)) x
  map_smul r h x := act.map_smul r _ x

/-- `f` on `f⁻¹(ℕ) → ℕ`. -/
def hN (f : M →+ ℤ) : posN.comap f →+ posN where
  toFun n := ⟨f n, n.2⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : M) (b : M))

/-- The map of Proposition 3.31: a point of `X^{f⁻¹(ℕ)}` is a point of `X^ℕ` for `𝔸(ℤ)`. -/
noncomputable def ptZ (f : M →+ ℤ) {T : BigFppfOver B S hS} (φ : AttractorPt act (posN.comap f) T) :
    AttractorPt (actZ act f) posN T where
  app t a := φ.app t (a.comp (AddMonoidHom.toMultiplicative (hN f)))
  naturality s t a := φ.naturality s t (a.comp (AddMonoidHom.toMultiplicative (hN f)))
  equivariant t h a := by
    refine Eq.trans (congrArg (φ.app t) (MonoidHom.ext fun _ => rfl))
      (φ.equivariant t (h.comp (AddMonoidHom.toMultiplicative f))
        (a.comp (AddMonoidHom.toMultiplicative (hN f))))

variable {act}

/-- The inverse map, when `f(m₀) = 1`. -/
noncomputable def liftZ (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) {T : BigFppfOver B S hS}
    (ψ : AttractorPt (actZ act f) posN T) : AttractorPt act (posN.comap f) T where
  app t a := act.smul (a.comp (AddMonoidHom.toMultiplicative (retrZ f h)))
    (ψ.app t (a.comp (AddMonoidHom.toMultiplicative (secZ f h))))
  naturality s t a := by
    refine Eq.trans ?_ (act.map_smul s.op _ _).symm
    exact congrArg (act.smul _) (ψ.naturality s t (a.comp (AddMonoidHom.toMultiplicative (secZ f h))))
  equivariant {T'} t g a := by
    let e : APt (fppfO B S hS) ℤ (op T') := g.comp (AddMonoidHom.toMultiplicative (mulZ m₀))
    let c : APt (fppfO B S hS) M (op T') :=
      g.comp (AddMonoidHom.toMultiplicative ((posN.comap f).subtype.comp (retrZ f h)))
    have e1 : (APt.toMagnet (posN.comap f) g * a).comp (AddMonoidHom.toMultiplicative (secZ f h)) =
        APt.toMagnet posN e * a.comp (AddMonoidHom.toMultiplicative (secZ f h)) :=
      MonoidHom.ext fun _ => rfl
    have e2 : (APt.toMagnet (posN.comap f) g * a).comp (AddMonoidHom.toMultiplicative (retrZ f h)) =
        c * a.comp (AddMonoidHom.toMultiplicative (retrZ f h)) :=
      MonoidHom.ext fun _ => rfl
    have e3 : g = c * e.comp (AddMonoidHom.toMultiplicative f) := by
      refine MonoidHom.ext fun m => ?_
      change _ = g _ * g _
      rw [← map_mul]
      refine congrArg g (congrArg Multiplicative.ofAdd ?_)
      change _ = (Multiplicative.toAdd m - f (Multiplicative.toAdd m) • m₀) +
        (zmultiplesHom M) m₀ (f (Multiplicative.toAdd m))
      simp
      rfl
    change act.smul _ (ψ.app t _) = act.smul g (act.smul _ _)
    rw [e1, e2, ψ.equivariant]
    change act.smul _ (act.smul (e.comp (AddMonoidHom.toMultiplicative f)) _) = _
    rw [← act.mul_smul, ← act.mul_smul]
    refine congrArg (act.smul · _) ?_
    conv_rhs => rw [e3]
    exact mul_right_comm _ _ _

theorem ptZ_liftZ (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) {T : BigFppfOver B S hS}
    (ψ : AttractorPt (actZ act f) posN T) : ptZ act f (liftZ f h ψ) = ψ := by
  refine AttractorPt.ext ?_
  funext T' t y
  change act.smul _ (ψ.app t _) = ψ.app t y
  have e1 : (y.comp (AddMonoidHom.toMultiplicative (hN f))).comp
      (AddMonoidHom.toMultiplicative (retrZ f h)) = 1 := by
    refine MonoidHom.ext fun m => ?_
    have : hN f (retrZ f h (Multiplicative.toAdd m)) = 0 := by
      refine Subtype.ext ?_
      change f (Multiplicative.toAdd m - f (Multiplicative.toAdd m) • m₀) = 0
      simp [h]
    change y (Multiplicative.ofAdd (hN f (retrZ f h (Multiplicative.toAdd m)))) = 1
    rw [this]
    exact map_one y
  have e2 : (y.comp (AddMonoidHom.toMultiplicative (hN f))).comp
      (AddMonoidHom.toMultiplicative (secZ f h)) = y := by
    refine MonoidHom.ext fun b => ?_
    have : hN f (secZ f h (Multiplicative.toAdd b)) = Multiplicative.toAdd b := by
      refine Subtype.ext ?_
      change f (((Multiplicative.toAdd b : posN) : ℤ) • m₀) = _
      simp [h]
    change y (Multiplicative.ofAdd (hN f (secZ f h (Multiplicative.toAdd b)))) = y b
    rw [this]
    rfl
  rw [e1, e2, act.one_smul]

theorem liftZ_ptZ (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) {T : BigFppfOver B S hS}
    (φ : AttractorPt act (posN.comap f) T) : liftZ f h (ptZ act f φ) = φ := by
  refine AttractorPt.ext ?_
  funext T' t a
  change act.smul _ (φ.app t _) = φ.app t a
  rw [← φ.equivariant]
  refine congrArg (φ.app t) (MonoidHom.ext fun n => ?_)
  change a _ * a _ = a n
  rw [← map_mul]
  refine congrArg a (congrArg Multiplicative.ofAdd (Subtype.ext ?_))
  change ((Multiplicative.toAdd n : posN.comap f) : M) - f (Multiplicative.toAdd n : posN.comap f) • m₀ +
    f (Multiplicative.toAdd n : posN.comap f) • m₀ = _
  simp
  rfl

/-- **Proposition 3.31 (ii)** for `Y = ℕ`, `1 ∈ f(M)`. -/
theorem ptZ_bijective (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) (T : BigFppfOver B S hS) :
    Function.Bijective (ptZ act f : AttractorPt act (posN.comap f) T → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨liftZ f h, liftZ_ptZ f h, ptZ_liftZ f h⟩

end Along

section Stages

open AlgMag.DoubleScalar

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) M F) (N : AddSubmonoid M)

/-- `(X^N)^ℕ` for the action of `𝔸(ℤ)` on `X^N` through `f`, on points (`AlgMag.IterPt` with `𝔸(ℤ)`). -/
structure IterZ (f : M →+ ℤ) (T : BigFppfOver B S hS) where
  /-- The value at a point of `𝔸(ℕ)`, a point of `X^N`. -/
  app : ∀ {T' : BigFppfOver B S hS} (_ : T' ⟶ T), APt (fppfO B S hS) posN (op T') → AttractorPt act N T'
  naturality : ∀ {T' T'' : BigFppfOver B S hS} (s : T'' ⟶ T') (t : T' ⟶ T) (b : APt (fppfO B S hS) posN (op T')),
    app (s ≫ t) (APt.res s.op b) = AttractorPt.baseChange s (app t b)
  equivariant : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (h : APt (fppfO B S hS) ℤ (op T'))
    (b : APt (fppfO B S hS) posN (op T')),
    app t (APt.toMagnet posN h * b) =
      (attractorAction act N).smul (h.comp (AddMonoidHom.toMultiplicative f)) (app t b)

variable {act N}

/-- The map of Proposition 3.31, for `X^N`. -/
def iterZ (f : M →+ ℤ) {T : BigFppfOver B S hS} (Ψ : IterPt act N (posN.comap f) T) : IterZ act N f T where
  app t a := Ψ.app t (a.comp (AddMonoidHom.toMultiplicative (hN f)))
  naturality s t a := Ψ.naturality s t (a.comp (AddMonoidHom.toMultiplicative (hN f)))
  equivariant t h a := by
    refine Eq.trans (congrArg (Ψ.app t) (MonoidHom.ext fun _ => rfl))
      (Ψ.equivariant t (h.comp (AddMonoidHom.toMultiplicative f))
        (a.comp (AddMonoidHom.toMultiplicative (hN f))))

/-- The inverse of `iterZ`, when `f(m₀) = 1`. -/
noncomputable def liftIterZ (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) {T : BigFppfOver B S hS}
    (ψ : IterZ act N f T) : IterPt act N (posN.comap f) T where
  app t a := (attractorAction act N).smul (a.comp (AddMonoidHom.toMultiplicative (retrZ f h)))
    (ψ.app t (a.comp (AddMonoidHom.toMultiplicative (secZ f h))))
  naturality s t a := by
    refine Eq.trans ?_ ((attractorAction act N).map_smul s.op _ _).symm
    exact congrArg ((attractorAction act N).smul _) (ψ.naturality s t (a.comp (AddMonoidHom.toMultiplicative (secZ f h))))
  equivariant {T'} t g a := by
    let A := attractorAction act N
    let e : APt (fppfO B S hS) ℤ (op T') := g.comp (AddMonoidHom.toMultiplicative (mulZ m₀))
    let c : APt (fppfO B S hS) M (op T') :=
      g.comp (AddMonoidHom.toMultiplicative ((posN.comap f).subtype.comp (retrZ f h)))
    have e1 : (APt.toMagnet (posN.comap f) g * a).comp (AddMonoidHom.toMultiplicative (secZ f h)) =
        APt.toMagnet posN e * a.comp (AddMonoidHom.toMultiplicative (secZ f h)) :=
      MonoidHom.ext fun _ => rfl
    have e2 : (APt.toMagnet (posN.comap f) g * a).comp (AddMonoidHom.toMultiplicative (retrZ f h)) =
        c * a.comp (AddMonoidHom.toMultiplicative (retrZ f h)) :=
      MonoidHom.ext fun _ => rfl
    have e3 : g = c * e.comp (AddMonoidHom.toMultiplicative f) := by
      refine MonoidHom.ext fun m => ?_
      change _ = g _ * g _
      rw [← map_mul]
      refine congrArg g (congrArg Multiplicative.ofAdd ?_)
      change _ = (Multiplicative.toAdd m - f (Multiplicative.toAdd m) • m₀) +
        (zmultiplesHom M) m₀ (f (Multiplicative.toAdd m))
      simp
      rfl
    change A.smul _ (ψ.app t _) = A.smul g (A.smul _ _)
    rw [e1, e2, ψ.equivariant]
    change A.smul _ (A.smul (e.comp (AddMonoidHom.toMultiplicative f)) _) = _
    refine (A.mul_smul _ _ _).symm.trans (Eq.trans ?_ (A.mul_smul _ _ _))
    refine congrArg (A.smul · _) ?_
    conv_rhs => rw [e3]
    exact mul_right_comm _ _ _

lemma IterZ.ext' {f : M →+ ℤ} {T : BigFppfOver B S hS} {ψ ψ' : IterZ act N f T}
    (h : ∀ {T'} (t : T' ⟶ T) a, ψ.app t a = ψ'.app t a) : ψ = ψ' := by
  cases ψ
  cases ψ'
  congr
  funext T' t a
  exact h t a

lemma iterPt_ext' {L : AddSubmonoid M} {T : BigFppfOver B S hS} {ψ ψ' : IterPt act N L T}
    (h : ∀ {T'} (t : T' ⟶ T) a, ψ.app t a = ψ'.app t a) : ψ = ψ' := by
  cases ψ
  cases ψ'
  congr
  funext T' t a
  exact h t a

theorem iterZ_lift (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) {T : BigFppfOver B S hS}
    (ψ : IterZ act N f T) : iterZ f (liftIterZ f h ψ) = ψ := by
  refine IterZ.ext' fun {T'} t y => ?_
  change (attractorAction act N).smul _ (ψ.app t _) = ψ.app t y
  have e1 : (y.comp (AddMonoidHom.toMultiplicative (hN f))).comp
      (AddMonoidHom.toMultiplicative (retrZ f h)) = 1 := by
    refine MonoidHom.ext fun m => ?_
    have : hN f (retrZ f h (Multiplicative.toAdd m)) = 0 := by
      refine Subtype.ext ?_
      change f (Multiplicative.toAdd m - f (Multiplicative.toAdd m) • m₀) = 0
      simp [h]
    change y (Multiplicative.ofAdd (hN f (retrZ f h (Multiplicative.toAdd m)))) = 1
    rw [this]
    exact map_one y
  have e2 : (y.comp (AddMonoidHom.toMultiplicative (hN f))).comp
      (AddMonoidHom.toMultiplicative (secZ f h)) = y := by
    refine MonoidHom.ext fun b => ?_
    have : hN f (secZ f h (Multiplicative.toAdd b)) = Multiplicative.toAdd b := by
      refine Subtype.ext ?_
      change f (((Multiplicative.toAdd b : posN) : ℤ) • m₀) = _
      simp [h]
    change y (Multiplicative.ofAdd (hN f (secZ f h (Multiplicative.toAdd b)))) = y b
    rw [this]
    rfl
  rw [e1, e2]
  exact (attractorAction act N).one_smul _

theorem lift_iterZ (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) {T : BigFppfOver B S hS}
    (φ : IterPt act N (posN.comap f) T) : liftIterZ f h (iterZ f φ) = φ := by
  refine iterPt_ext' fun {T'} t a => ?_
  change (attractorAction act N).smul _ (φ.app t _) = φ.app t a
  rw [← φ.equivariant]
  refine congrArg (φ.app t) (MonoidHom.ext fun n => ?_)
  change a _ * a _ = a n
  rw [← map_mul]
  refine congrArg a (congrArg Multiplicative.ofAdd (Subtype.ext ?_))
  change ((Multiplicative.toAdd n : posN.comap f) : M) - f (Multiplicative.toAdd n : posN.comap f) • m₀ +
    f (Multiplicative.toAdd n : posN.comap f) • m₀ = _
  simp
  rfl

/-- **Proposition 3.31** for `(X^N)^{f⁻¹(ℕ)}`, `1 ∈ f(M)`. -/
theorem iterZ_bijective (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) (T : BigFppfOver B S hS) :
    Function.Bijective (iterZ f : IterPt act N (posN.comap f) T → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨liftIterZ f h, lift_iterZ f h, iterZ_lift f h⟩

variable [AddMonoid.FG M] [Countable M] {U : BigFppfOver B S hS}
  {aX : AAction (fppfO B S hS) M (yoneda.obj U)}

/-- **§16.4 (ii)**, printed route. For `f₁, f₂ : M → ℤ` with `1` in their image (`M = ℤ²`, the projections, in the
printed case) and `X` a scheme: `X^{N₁ ∩ N₂} = (X^{N₁})^{N₂}` by Proposition 3.32, then `(X^{N₁})^{N₂}` is the
`G_m`-attractor `(X^{N₁})^ℕ` for the action through `f₂` by Proposition 3.31; and `X^{N₁}` is itself the `G_m`-attractor
`X^ℕ` for the action through `f₁`, by Proposition 3.31. -/
theorem sec164_ii_printed (f₁ f₂ : M →+ ℤ) {m₁ m₂ : M} (h₁ : f₁ m₁ = 1) (h₂ : f₂ m₂ = 1)
    (T : BigFppfOver B S hS) :
    Function.Bijective (fun φ : AttractorPt aX (posN.comap f₁ ⊓ posN.comap f₂) T =>
        iterZ f₂ (iterOfInf φ)) ∧
      Function.Bijective (ptZ aX f₁ : AttractorPt aX (posN.comap f₁) T → _) :=
  ⟨(iterZ_bijective f₂ h₂ T).comp (prop332_scheme T), ptZ_bijective f₁ h₁ T⟩

end Stages

end AlgMag.Sec164

#print axioms AlgMag.Sec164.sec164_ii_printed
