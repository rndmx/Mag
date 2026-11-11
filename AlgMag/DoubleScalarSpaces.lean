/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.DoubleScalar

/-!
# Proposition 6.4 of "Algebraic magnetism invariants of a double scalar action" for separated spaces

A. Mayeux, arXiv:2509.04274v3.

## Main results

* `AlgMag.DoubleScalar.prop64_space`: **Proposition 6.4**, `X` a separated algebraic space, `M` a finitely generated
  abelian group, `S` arbitrary: `X^+ = X^N`, both as subfunctors of `X` and through `ptAlong`, bijective.
* `AlgMag.DoubleScalar.ptAlong_bijective_of_primitive`: the form of Proposition 3.31 (ii) of *Algebraic Magnetism*
  needed, `Y = ℕ`, `f` with `1` in its image, for any functor `X` with an action.
* `AlgMag.DoubleScalar.prop62_of_monotone`: the equivalence of (i), (iii), (iv) of **Proposition 6.2**, any action.
* `AlgMag.DoubleScalar.existsUnique_pure_p2`, `AlgMag.DoubleScalar.prop62_p2`: **§6.1, Proposition 6.2** for `ℙ²`.

## The proof of Proposition 6.4

The printed proof applies Proposition 3.31 (ii) to the given `f`. Its statement only asks for some `λ`, and `f` and
its primitive `g` (`f = d g`, `d > 0`) have `f⁻¹(ℕ) = g⁻¹(ℕ)`, so `λ` is taken dual to `g`; if `f = 0`, `g = 0`. Then
no descent is needed. If `g(m₀) = 1`, a point `ψ` of `X^+` gives the point `a ↦ a(m - g(m) m₀)_m • ψ(a(b m₀)_b)` of
`X^{g⁻¹(ℕ)}`. If `g = 0`, then `g⁻¹(ℕ) = M`, `X^M = X`, and separatedness gives that `X^+ → X` is a monomorphism.
The case of the given `f` with `d ≥ 2` is not treated, and not needed.
-/

open CategoryTheory Opposite AlgebraicGeometry

set_option linter.unusedSectionVars false

namespace AlgMag.DoubleScalar

section Primitive

variable {B : BigFppfSite.{0}} {S : AlgebraicGeometry.Scheme.{0}} {hS : B.Contains S}
variable {M : Type} [AddCommGroup M] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type}
variable {act : AAction (fppfO B S hS) M F}

/-- `m ↦ m - f(m) m₀`, into `f⁻¹(ℕ)`. -/
def retrP (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) : M →+ posN.comap f where
  toFun m := ⟨m - f m • m₀, by
    change (0 : ℤ) ≤ f (m - f m • m₀)
    simp [h]⟩
  map_zero' := by ext; simp
  map_add' x y := by
    ext
    simp only [map_add, add_zsmul, AddSubmonoid.coe_add]
    abel

/-- `b ↦ b m₀`, into `f⁻¹(ℕ)`. -/
def secP (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) : posN →+ posN.comap f where
  toFun b := ⟨(b : ℤ) • m₀, by
    change (0 : ℤ) ≤ f ((b : ℤ) • m₀)
    have hb : (0 : ℤ) ≤ (b : ℤ) := b.2
    simpa [h] using hb⟩
  map_zero' := by ext; simp
  map_add' x y := by
    ext
    simp [add_zsmul]

/-- `z ↦ z m₀`. -/
def mulP (m₀ : M) : ℤ →+ M := (zmultiplesHom M) m₀

/-- The point of `X^{f⁻¹(ℕ)}` of a point of `X^+`, when `f(m₀) = 1`. -/
noncomputable def liftP (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) {T : BigFppfOver B S hS}
    (ψ : AttractorPt (actAlong f act) posN T) : AttractorPt act (posN.comap f) T where
  app t a := act.smul (a.comp (AddMonoidHom.toMultiplicative (retrP f h)))
    (ψ.app t (a.comp (AddMonoidHom.toMultiplicative (secP f h))))
  naturality s t a := by
    refine Eq.trans ?_ (act.map_smul s.op _ _).symm
    exact congrArg (act.smul _) (ψ.naturality s t (a.comp (AddMonoidHom.toMultiplicative (secP f h))))
  equivariant {T'} t g a := by
    let e : APt (fppfO B S hS) ℤ (op T') := g.comp (AddMonoidHom.toMultiplicative (mulP m₀))
    let c : APt (fppfO B S hS) M (op T') :=
      g.comp (AddMonoidHom.toMultiplicative ((posN.comap f).subtype.comp (retrP f h)))
    have e1 : (APt.toMagnet (posN.comap f) g * a).comp (AddMonoidHom.toMultiplicative (secP f h)) =
        APt.toMagnet posN e * a.comp (AddMonoidHom.toMultiplicative (secP f h)) :=
      MonoidHom.ext fun _ => rfl
    have e2 : (APt.toMagnet (posN.comap f) g * a).comp (AddMonoidHom.toMultiplicative (retrP f h)) =
        c * a.comp (AddMonoidHom.toMultiplicative (retrP f h)) :=
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

/-- `liftP f h` is a right inverse of `ptAlong`, for `f m₀ = 1`. -/
theorem ptAlong_liftP (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) {T : BigFppfOver B S hS}
    (ψ : AttractorPt (actAlong f act) posN T) : ptAlong act (liftP f h ψ) = ψ := by
  refine AttractorPt.ext ?_
  funext T' t y
  change act.smul _ (ψ.app t _) = ψ.app t y
  have e1 : (y.comp (AddMonoidHom.toMultiplicative (linMagnetHom f posN))).comp
      (AddMonoidHom.toMultiplicative (retrP f h)) = 1 := by
    refine MonoidHom.ext fun m => ?_
    have : linMagnetHom f posN (retrP f h (Multiplicative.toAdd m)) = 0 := by
      refine Subtype.ext ?_
      change f (Multiplicative.toAdd m - f (Multiplicative.toAdd m) • m₀) = 0
      simp [h]
    change y (Multiplicative.ofAdd (linMagnetHom f posN (retrP f h (Multiplicative.toAdd m)))) = 1
    rw [this]
    exact map_one y
  have e2 : (y.comp (AddMonoidHom.toMultiplicative (linMagnetHom f posN))).comp
      (AddMonoidHom.toMultiplicative (secP f h)) = y := by
    refine MonoidHom.ext fun b => ?_
    have : linMagnetHom f posN (secP f h (Multiplicative.toAdd b)) = Multiplicative.toAdd b := by
      refine Subtype.ext ?_
      change f (((Multiplicative.toAdd b : posN) : ℤ) • m₀) = _
      simp [h]
    change y (Multiplicative.ofAdd (linMagnetHom f posN (secP f h (Multiplicative.toAdd b)))) = y b
    rw [this]
    rfl
  rw [e1, e2, act.one_smul]

/-- `liftP f h` is a left inverse of `ptAlong`, for `f m₀ = 1`. -/
theorem liftP_ptAlong (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) {T : BigFppfOver B S hS}
    (φ : AttractorPt act (posN.comap f) T) : liftP f h (ptAlong act φ) = φ := by
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

/-- **Proposition 3.31 (ii)** of *Algebraic Magnetism*, the form needed for Proposition 6.4: `Y = ℕ` and `1` in the
image of `f`. `X` is any functor with an action. -/
theorem ptAlong_bijective_of_primitive (f : M →+ ℤ) {m₀ : M} (h : f m₀ = 1) (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong act : AttractorPt act (posN.comap f) T → AttractorPt (actAlong f act) posN T) :=
  Function.bijective_iff_has_inverse.mpr ⟨liftP f h, liftP_ptAlong f h, ptAlong_liftP f h⟩

end Primitive

/-- `f = d g`, with `g` zero or with `1` in its image; `f⁻¹(ℕ) = g⁻¹(ℕ)`. -/
theorem exists_primitive {M : Type} [AddCommGroup M] (f : M →+ ℤ) :
    ∃ g : M →+ ℤ, posN.comap g = posN.comap f ∧ (g = 0 ∨ ∃ m₀, g m₀ = 1) := by
  by_cases hf : f = 0
  · exact ⟨f, rfl, Or.inl hf⟩
  obtain ⟨d, hd⟩ := Int.subgroup_cyclic f.range
  have hdv : ∀ m, |d| ∣ f m := by
    intro m
    have : f m ∈ AddSubgroup.closure {d} := hd ▸ AddMonoidHom.mem_range.mpr ⟨m, rfl⟩
    rw [AddSubgroup.mem_closure_singleton] at this
    obtain ⟨k, hk⟩ := this
    rw [abs_dvd, ← hk, smul_eq_mul]
    exact dvd_mul_left _ _
  have hd0 : 0 < |d| := by
    refine abs_pos.mpr fun h0 => hf (AddMonoidHom.ext fun m => ?_)
    have := hdv m
    rw [h0, abs_zero, zero_dvd_iff] at this
    exact this
  have hmul : ∀ m, |d| * (f m / |d|) = f m := fun m => Int.mul_ediv_cancel' (hdv m)
  let g : M →+ ℤ :=
    { toFun := fun m => f m / |d|
      map_zero' := by simp
      map_add' := fun x y => by
        rw [map_add, Int.add_ediv_of_dvd_left (hdv x)] }
  refine ⟨g, ?_, Or.inr ?_⟩
  · ext m
    change 0 ≤ f m / |d| ↔ 0 ≤ f m
    conv_rhs => rw [← hmul m]
    exact (mul_nonneg_iff_of_pos_left hd0).symm
  · have hdm : d ∈ f.range := by
      rw [hd]
      exact AddSubgroup.subset_closure rfl
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.mp hdm
    have hg : |d| * g m = d := (hmul m).trans hm
    rcases abs_cases d with ⟨h1, _⟩ | ⟨h1, _⟩
    · refine ⟨m, ?_⟩
      rw [h1] at hg hd0
      have : d * g m = d * 1 := by rw [hg, mul_one]
      exact mul_left_cancel₀ hd0.ne' this
    · refine ⟨-m, ?_⟩
      rw [map_neg]
      rw [h1] at hg
      have hne : -d ≠ 0 := by rw [← h1]; exact hd0.ne'
      have : (-d) * (- g m) = (-d) * 1 := by linarith
      exact mul_left_cancel₀ hne this

section Main

variable {B : BigFppfSite.{0}} {S : AlgebraicGeometry.Scheme.{0}} {hS : B.Contains S}
variable {M : Type} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type}
variable {aX : AAction (fppfO B S hS) M X}

/-- **Proposition 6.4**, the bijection: for `g = 0` or `g` with `1` in its image, `X^{g⁻¹(ℕ)} = X^+`. -/
theorem ptAlong_bijective_space (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) {g : M →+ ℤ}
    (hg : g = 0 ∨ ∃ m₀, g m₀ = 1) (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong aX : AttractorPt aX (posN.comap g) T → AttractorPt (actAlong g aX) posN T) := by
  rcases hg with rfl | ⟨m₀, h⟩
  · refine ⟨fun φ φ' e => ?_, fun ψ => ?_⟩
    · refine attractor_toPoint_injective_sep hX hsep _ T ?_
      rw [← toPoint_ptAlong φ, ← toPoint_ptAlong φ', e]
    · have hle : (⊤ : AddSubmonoid M) ≤ posN.comap (0 : M →+ ℤ) := fun m _ => le_refl (0 : ℤ)
      refine ⟨AttractorPt.ofLE hle ((attractorTopEquiv aX T).symm ψ.toPoint), ?_⟩
      refine attractor_toPoint_injective_sep hX hsep _ T ?_
      rw [toPoint_ptAlong]
      exact (attractorTopEquiv aX T).apply_symm_apply ψ.toPoint
  · exact ptAlong_bijective_of_primitive g h T

/-- **Proposition 6.4.** `S` any base scheme, `M` a finitely generated abelian group, `X` a separated algebraic space
with an action of `D(M)`, `N` lambdafiable. There is `λ : 𝔾_m → D(M)`, dual to `g : M → ℤ`, such that `X^+ = X^N`: the
`𝔾_m`-action through `λ` on the left, the `D(M)`-action on the right. The equality is as subfunctors of `X` (the first
clause); and `X^{g⁻¹(ℕ)} = X^N`, with `ptAlong` an isomorphism `X^{g⁻¹(ℕ)} → X^+` (the last clause). -/
theorem prop64_space (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) {N : AddSubmonoid M}
    (h : IsLambdafiable (attractorImage aX) N) :
    ∃ g : M →+ ℤ, attractorImage (actAlong g aX) posN = attractorImage aX N ∧
      attractorImage aX (posN.comap g) = attractorImage aX N ∧
      ∀ T, Function.Bijective
        (ptAlong aX : AttractorPt aX (posN.comap g) T → AttractorPt (actAlong g aX) posN T) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hc, hg⟩ := exists_primitive f
  have hN : attractorImage aX (posN.comap g) = attractorImage aX N := by rw [hc]; exact hf
  have hb := ptAlong_bijective_space (aX := aX) hX hsep hg
  refine ⟨g, Eq.trans ?_ hN, hN, hb⟩
  funext T
  ext x
  constructor
  · rintro ⟨ψ, rfl⟩
    obtain ⟨χ, rfl⟩ := (hb T).2 ψ
    exact ⟨χ, (toPoint_ptAlong χ).symm⟩
  · rintro ⟨χ, rfl⟩
    exact ⟨ptAlong aX χ, toPoint_ptAlong χ⟩

end Main

/-- **Proposition 6.2**, (i), (iii), (iv). Only `Y` monotone is used, which holds for any action
(`attractorImage_monotone`), with no assumption on `X`. Assertion (ii) needs the purification to exist. -/
theorem prop62_of_monotone {M α : Type*} [AddCommGroup M] [PartialOrder α] {Y : AddSubmonoid M → α}
    (hY : Monotone Y) (f : M →+ ℤ) (N : AddSubmonoid M) :
    List.TFAE [Y (posN.comap f) = Y N, posN.comap f ∈ magnetClass Y N,
      ∃ N' ∈ magnetClass Y N, ∃ N'' ∈ magnetClass Y N, N' ≤ posN.comap f ∧ posN.comap f ≤ N''] := by
  tfae_have 1 → 2 := fun h => h.symm
  tfae_have 2 → 3 := fun h => ⟨_, h, _, h, le_rfl, le_rfl⟩
  tfae_have 3 → 1 := by
    rintro ⟨N', h1, N'', h2, h3, h4⟩
    have h1' : Y N = Y N' := h1
    have h2' : Y N = Y N'' := h2
    refine le_antisymm ?_ ?_
    · rw [h2']
      exact hY h4
    · rw [h1']
      exact hY h3
  tfae_finish

section P2

variable {R : Type} [CommRing R] [Nontrivial R]

/-- **§6.1** for `ℙ²`: `m(a) = ⨆_{N ∈ Π(a)} m^N(a)`, with no hypothesis. -/
theorem existsUnique_pure_p2 (N : AddSubmonoid (ℤ × ℤ)) :
    ∃! P, IsPure (attractorImage (dsAct R)) P ∧ N ∈ magnetClass (attractorImage (dsAct R)) P :=
  existsUnique_pure (attractorOrder_pn wP) N

/-- **Proposition 6.2** for `ℙ²`, with no hypothesis. -/
theorem prop62_p2 (f : ℤ × ℤ →+ ℤ) (N : AddSubmonoid (ℤ × ℤ)) :
    List.TFAE [attractorImage (dsAct R) (posN.comap f) = attractorImage (dsAct R) N,
      purification (attractorImage (dsAct R)) (posN.comap f) = purification (attractorImage (dsAct R)) N,
      posN.comap f ∈ magnetClass (attractorImage (dsAct R)) N,
      ∃ N' ∈ magnetClass (attractorImage (dsAct R)) N, ∃ N'' ∈ magnetClass (attractorImage (dsAct R)) N,
        N' ≤ posN.comap f ∧ posN.comap f ≤ N''] :=
  prop62 (attractorOrder_pn wP) f N

end P2

#print axioms ptAlong_bijective_of_primitive
#print axioms exists_primitive
#print axioms prop64_space
#print axioms prop62_of_monotone
#print axioms existsUnique_pure_p2
#print axioms prop62_p2

end AlgMag.DoubleScalar
