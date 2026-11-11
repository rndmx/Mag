/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec15General

/-!
# Intersections of magnets: Proposition 3.32 (ii), Fact 3.34 (ii)

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §3 and §15.

A point of the iterated attractor `(X^N)^L` is the same as a point of the attractor `X^{N × L}` for the
action of `D(M × M)` on `X` through multiplication, dual to the diagonal `M → M × M`
(`AlgMag.iterEquivBi`). Proposition 5.1 applied to the face of units of `N × L` lifts such a point to an
`S`-affine strongly-FPR atlas, where the statement is the affine one.

The printed proofs do not apply as they stand: the antidiagonal action of `D(N^gp + L^gp)` on
`𝔸(N) × 𝔸(L)` is not free, and `𝔸(⋂ N_l)` is not a colimit of a decreasing system.

## Main results

* `AlgMag.prop332`: **Proposition 3.32 (ii)**, `X^{N ∩ L} → (X^N)^L` is bijective on points.
* `AlgMag.attractorImage_inf_of_eq`: `X^N = X^L` implies `X^{N ∩ L} = X^N`.
* `AlgMag.fact334_finite`: **Fact 3.34 (ii)** for finite families.
* `AlgMag.fact334`: **Fact 3.34 (ii)** for arbitrary families, `S` quasi-compact and the atlas of finite
  type over `S`; this is `AlgMag.attractorOrder_of_atlas`.
* `AlgMag.prop151_of_atlas`: **Proposition 15.1**, without the finiteness assumptions of `fact334`.
* `AlgMag.thm153_of_atlas`: **Theorem 15.3**.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
set_option linter.unusedSectionVars false

namespace AlgMag

section General

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommMonoid M]
variable {F : Cᵒᵖ ⥤ Type u}

/-- The diagonal `M → M × M`. Along it `𝔸(M × M)` acts on `X` by `(g, h) • x = g • (h • x)`. -/
def diagHom (M : Type*) [AddCommMonoid M] : M →+ M × M := AddMonoidHom.prod (.id M) (.id M)

/-- The action of `𝔸(M × M)` on `X` through multiplication. -/
abbrev biAct (act : AAction 𝒪 M F) : AAction 𝒪 (M × M) F := act.comap (diagHom M)

variable {N L : AddSubmonoid M}

/-- The projection `N × L → N`. -/
def pFst : ↥(N.prod L) →+ N where
  toFun p := ⟨p.1.1, p.2.1⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The projection `N × L → L`. -/
def pSnd : ↥(N.prod L) →+ L where
  toFun p := ⟨p.1.2, p.2.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inclusion `N → N × L`. -/
def iFst : N →+ ↥(N.prod L) where
  toFun n := ⟨(n.1, 0), n.2, L.zero_mem⟩
  map_zero' := rfl
  map_add' a b := Subtype.ext (Prod.ext rfl (by simp))

/-- The inclusion `L → N × L`. -/
def iSnd : L →+ ↥(N.prod L) where
  toFun n := ⟨(0, n.1), N.zero_mem, n.2⟩
  map_zero' := rfl
  map_add' a b := Subtype.ext (Prod.ext (by simp) rfl)

/-- The diagonal `K → P`, for `K ⊆ M` and `P ⊆ M × M` containing the diagonal of `K`. -/
def iDiag {K : AddSubmonoid M} {P : AddSubmonoid (M × M)} (hK : ∀ k ∈ K, (k, k) ∈ P) : K →+ P where
  toFun k := ⟨(k.1, k.1), hK _ k.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction along a morphism of magnets. -/
abbrev APt.along {P P' : Type*} [AddCommMonoid P] [AddCommMonoid P'] {U : Cᵒᵖ} (g : P' →+ P)
    (a : APt 𝒪 P U) : APt 𝒪 P' U := a.comp (AddMonoidHom.toMultiplicative g)

/-- A point of `X^K` gives a point of `X^P` for the action through multiplication, by composing with
`𝔸(P) → 𝔸(K)`, `c ↦ (k ↦ c(k, k))`. For `P = N × L`, `K = N ∩ L` this is `(a, b) ↦ ab`. -/
def AttractorPt.toBi {act : AAction 𝒪 M F} {K : AddSubmonoid M} {P : AddSubmonoid (M × M)}
    (hK : ∀ k ∈ K, (k, k) ∈ P) {T : C} (χ : AttractorPt act K T) : AttractorPt (biAct act) P T where
  app t c := χ.app t (APt.along (iDiag hK) c)
  naturality s t c := χ.naturality s t (APt.along (iDiag hK) c)
  equivariant t h c := by
    have : APt.along (iDiag hK) (APt.toMagnet P h * c) =
        APt.toMagnet K (h.comp (AddMonoidHom.toMultiplicative (diagHom M))) *
          APt.along (iDiag hK) c := by
      exact MonoidHom.ext fun p => rfl
    rw [this]
    exact χ.equivariant t _ _

@[simp] lemma AttractorPt.toPoint_toBi {act : AAction 𝒪 M F} {K : AddSubmonoid M}
    {P : AddSubmonoid (M × M)} (hK : ∀ k ∈ K, (k, k) ∈ P) {T : C} (χ : AttractorPt act K T) :
    (χ.toBi hK).toPoint = χ.toPoint := by
  change χ.app (𝟙 T) (APt.along (iDiag hK) 1) = χ.app (𝟙 T) 1
  rw [APt.along, MonoidHom.one_comp]

/-- A point of `X^P` gives a point of `X^{N'}`, along a retraction `σ` of the diagonal which sends `P`
into `N'`. -/
def AttractorPt.ofBi {act : AAction 𝒪 M F} {P : AddSubmonoid (M × M)} {N' : AddSubmonoid M}
    (σ : M × M →+ M) (hσ : ∀ m, σ (m, m) = m) (π : P →+ N') (hπ : ∀ p, (π p : M) = σ p) {T : C}
    (φ : AttractorPt (biAct act) P T) : AttractorPt act N' T where
  app t a := φ.app t (APt.along π a)
  naturality s t a := φ.naturality s t (APt.along π a)
  equivariant t h a := by
    have e1 : APt.along π (APt.toMagnet N' h * a) =
        APt.toMagnet P (h.comp (AddMonoidHom.toMultiplicative σ)) * APt.along π a := by
      refine MonoidHom.ext fun p => ?_
      change h _ * a _ = h _ * a _
      exact congrArg (· * a _) (congrArg h (congrArg Multiplicative.ofAdd (hπ _)))
    have e2 : (h.comp (AddMonoidHom.toMultiplicative σ)).comp
        (AddMonoidHom.toMultiplicative (diagHom M)) = h := by
      refine MonoidHom.ext fun p => ?_
      exact congrArg h (congrArg Multiplicative.ofAdd (hσ (Multiplicative.toAdd p)))
    rw [e1]
    refine (φ.equivariant t _ _).trans ?_
    change act.smul ((h.comp (AddMonoidHom.toMultiplicative σ)).comp
      (AddMonoidHom.toMultiplicative (diagHom M))) _ = _
    rw [e2]

lemma AttractorPt.toPoint_ofBi {act : AAction 𝒪 M F} {P : AddSubmonoid (M × M)}
    {N' : AddSubmonoid M} (σ : M × M →+ M) (hσ : ∀ m, σ (m, m) = m) (π : P →+ N')
    (hπ : ∀ p, (π p : M) = σ p) {T : C} (φ : AttractorPt (biAct act) P T) :
    (φ.ofBi σ hσ π hπ).toPoint = φ.toPoint := by
  change φ.app (𝟙 T) (APt.along π 1) = φ.app (𝟙 T) 1
  rw [APt.along, MonoidHom.one_comp]

/-- A `T`-point of the iterated attractor `(X^N)^L`, for the action of Remark 3.11 on `X^N`. (`X^N` lives
in a larger universe than `X`, so this is spelled out.) -/
@[ext]
structure IterPt (act : AAction 𝒪 M F) (N L : AddSubmonoid M) (T : C) where
  /-- The value at a point of `𝔸(L)`, a point of `X^N`. -/
  app : ∀ {T' : C} (_ : T' ⟶ T), APt 𝒪 L (op T') → AttractorPt act N T'
  naturality : ∀ {T' T'' : C} (s : T'' ⟶ T') (t : T' ⟶ T) (b : APt 𝒪 L (op T')),
    app (s ≫ t) (APt.res s.op b) = AttractorPt.baseChange s (app t b)
  equivariant : ∀ {T' : C} (t : T' ⟶ T) (h : APt 𝒪 M (op T')) (b : APt 𝒪 L (op T')),
    app t (APt.toMagnet L h * b) = (attractorAction act N).smul h (app t b)

variable {act : AAction 𝒪 M F}

/-- The point of `X` underlying a point of `(X^N)^L`. -/
def IterPt.toPoint {T : C} (Ψ : IterPt act N L T) : F.obj (op T) := (Ψ.app (𝟙 T) 1).toPoint

/-- `(a, b) ↦ (n, l) ↦ a(n) b(l)`. -/
abbrev pairPt {U : Cᵒᵖ} (a : APt 𝒪 N U) (b : APt 𝒪 L U) : APt 𝒪 (N.prod L) U :=
  APt.along pFst a * APt.along pSnd b

lemma pairPt_fst {U : Cᵒᵖ} (a : APt 𝒪 N U) (b : APt 𝒪 L U) :
    APt.along iFst (pairPt a b) = a := by
  refine MonoidHom.ext fun n => ?_
  have h : b 1 = 1 := map_one b
  change a _ * b _ = _
  exact (congrArg (a n * ·) h).trans (mul_one _)

lemma pairPt_snd {U : Cᵒᵖ} (a : APt 𝒪 N U) (b : APt 𝒪 L U) :
    APt.along iSnd (pairPt a b) = b := by
  refine MonoidHom.ext fun n => ?_
  have h : a 1 = 1 := map_one a
  change a _ * b _ = _
  exact (congrArg (· * b n) h).trans (one_mul _)

lemma pairPt_eta {U : Cᵒᵖ} (c : APt 𝒪 (N.prod L) U) :
    pairPt (APt.along iFst c) (APt.along iSnd c) = c := by
  refine MonoidHom.ext fun p => ?_
  change c _ * c _ = c p
  rw [← map_mul]
  congr 1
  exact congrArg Multiplicative.ofAdd (Subtype.ext (Prod.ext (add_zero _) (zero_add _)))

/-- From `(X^N)^L` to `X^{N × L}`. -/
def IterPt.toBi {T : C} (Ψ : IterPt act N L T) : AttractorPt (biAct act) (N.prod L) T where
  app t c := (Ψ.app t (APt.along iSnd c)).app (𝟙 _) (APt.along iFst c)
  naturality {T' T''} s t c := by
    have h := Ψ.naturality s t (APt.along iSnd c)
    have e : APt.along iSnd (APt.res s.op c) = APt.res s.op (APt.along iSnd c) := rfl
    rw [e, h]
    change (Ψ.app t (APt.along iSnd c)).app (𝟙 T'' ≫ s) (APt.res s.op (APt.along iFst c)) = _
    have h2 := (Ψ.app t (APt.along iSnd c)).naturality s (𝟙 _) (APt.along iFst c)
    rw [Category.comp_id] at h2
    rw [Category.id_comp]
    exact h2
  equivariant {T'} t h c := by
    let h₁ : APt 𝒪 M (op T') := h.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M M))
    let h₂ : APt 𝒪 M (op T') := h.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M M))
    have e1 : APt.along iFst (APt.toMagnet (N.prod L) h * c) =
        APt.toMagnet N h₁ * APt.along iFst c := by exact MonoidHom.ext fun p => rfl
    have e2 : APt.along iSnd (APt.toMagnet (N.prod L) h * c) =
        APt.toMagnet L h₂ * APt.along iSnd c := by exact MonoidHom.ext fun p => rfl
    have e3 : h.comp (AddMonoidHom.toMultiplicative (diagHom M)) = h₂ * h₁ := by
      refine MonoidHom.ext fun p => ?_
      change _ = h _ * h _
      rw [← map_mul]
      refine congrArg h (congrArg Multiplicative.ofAdd
        (Prod.ext (?_ : Multiplicative.toAdd p = 0 + Multiplicative.toAdd p)
          (?_ : Multiplicative.toAdd p = Multiplicative.toAdd p + 0)))
      · exact (zero_add _).symm
      · exact (add_zero _).symm
    rw [e1, e2, Ψ.equivariant]
    change act.smul (APt.res (𝟙 T').op h₂) ((Ψ.app t (APt.along iSnd c)).app (𝟙 T')
      (APt.toMagnet N h₁ * APt.along iFst c)) = _
    rw [(Ψ.app t (APt.along iSnd c)).equivariant (𝟙 T') h₁]
    have e4 : APt.res (𝟙 T').op h₂ = h₂ := APt.res_id h₂
    rw [e4, ← act.mul_smul, ← e3]
    rfl

/-- From `X^{N × L}` to `(X^N)^L`. -/
def IterPt.ofBi {T : C} (φ : AttractorPt (biAct act) (N.prod L) T) : IterPt act N L T where
  app {T'} t b :=
    { app := fun {T''} s a => φ.app (s ≫ t) (pairPt a (APt.res s.op b))
      naturality := fun {T₁ T₂} r s a => by
        rw [← φ.naturality r (s ≫ t)]
        have e : pairPt (APt.res r.op a) (APt.res (r ≫ s).op b) =
            APt.res r.op (pairPt a (APt.res s.op b)) := by
          have e0 : APt.res (r ≫ s).op b = APt.res r.op (APt.res s.op b) :=
            APt.res_comp s.op r.op b
          rw [e0]
          exact MonoidHom.ext fun p => (map_mul (𝒪.map r.op).hom _ _).symm
        rw [Category.assoc, e]
      equivariant := fun {T''} s h a => by
        have e : pairPt (APt.toMagnet N h * a) (APt.res s.op b) =
            APt.toMagnet (N.prod L) (h.comp (AddMonoidHom.toMultiplicative
              (AddMonoidHom.fst M M))) * pairPt a (APt.res s.op b) := by
          refine MonoidHom.ext fun p => ?_
          exact mul_assoc _ _ _
        rw [e]
        refine (φ.equivariant _ _ _).trans ?_
        have e2 : (h.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))).comp
            (AddMonoidHom.toMultiplicative (diagHom M)) = h := by
          exact MonoidHom.ext fun p => rfl
        change act.smul ((h.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M M))).comp
          (AddMonoidHom.toMultiplicative (diagHom M))) _ = _
        rw [e2] }
  naturality {T' T''} s t b := by
    refine AttractorPt.ext ?_
    funext T₁ r a
    change φ.app (r ≫ s ≫ t) (pairPt a (APt.res r.op (APt.res s.op b))) =
      φ.app ((r ≫ s) ≫ t) (pairPt a (APt.res (r ≫ s).op b))
    have e0 : APt.res (r ≫ s).op b = APt.res r.op (APt.res s.op b) := APt.res_comp s.op r.op b
    rw [Category.assoc, e0]
  equivariant {T'} t h b := by
    refine AttractorPt.ext ?_
    funext T₁ s a
    change φ.app (s ≫ t) (pairPt a (APt.res s.op (APt.toMagnet L h * b))) =
      act.smul (APt.res s.op h) (φ.app (s ≫ t) (pairPt a (APt.res s.op b)))
    have e : pairPt a (APt.res s.op (APt.toMagnet L h * b)) =
        APt.toMagnet (N.prod L) ((APt.res s.op h).comp (AddMonoidHom.toMultiplicative
          (AddMonoidHom.snd M M))) * pairPt a (APt.res s.op b) := by
      refine MonoidHom.ext fun p => ?_
      change a _ * (𝒪.map s.op).hom (h _ * b _) = (𝒪.map s.op).hom (h _) * (a _ * _)
      rw [map_mul, mul_left_comm]
      rfl
    rw [e]
    refine (φ.equivariant _ _ _).trans ?_
    have e2 : ((APt.res s.op h).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd M M))).comp
        (AddMonoidHom.toMultiplicative (diagHom M)) = APt.res s.op h := by
      exact MonoidHom.ext fun p => rfl
    change act.smul (((APt.res s.op h).comp (AddMonoidHom.toMultiplicative
      (AddMonoidHom.snd M M))).comp (AddMonoidHom.toMultiplicative (diagHom M))) _ = _
    rw [e2]

/-- `(X^N)^L = X^{N × L}`, for the action of `D(M × M)` on `X` through multiplication. -/
def iterEquivBi (T : C) : IterPt act N L T ≃ AttractorPt (biAct act) (N.prod L) T where
  toFun := IterPt.toBi
  invFun := IterPt.ofBi
  left_inv Ψ := by
    refine IterPt.ext ?_
    funext T' t b
    refine AttractorPt.ext ?_
    funext T'' s a
    change (Ψ.app (s ≫ t) (APt.along iSnd (pairPt a (APt.res s.op b)))).app (𝟙 _)
      (APt.along iFst (pairPt a (APt.res s.op b))) = (Ψ.app t b).app s a
    rw [pairPt_fst, pairPt_snd, Ψ.naturality]
    change (Ψ.app t b).app (𝟙 _ ≫ s) a = _
    rw [Category.id_comp]
  right_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t c
    change φ.app (𝟙 T' ≫ t) (pairPt (APt.along iFst c) (APt.res (𝟙 T').op (APt.along iSnd c))) =
      φ.app t c
    have e : APt.res (𝟙 T').op (APt.along iSnd c) = APt.along iSnd c := APt.res_id _
    rw [e, pairPt_eta, Category.id_comp]

lemma IterPt.toPoint_toBi {T : C} (Ψ : IterPt act N L T) : Ψ.toBi.toPoint = Ψ.toPoint := by
  change (Ψ.app (𝟙 T) (APt.along iSnd 1)).app (𝟙 T) (APt.along iFst 1) = (Ψ.app (𝟙 T) 1).app (𝟙 T) 1
  rw [APt.along, APt.along, MonoidHom.one_comp, MonoidHom.one_comp]

end General

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
local notation "Sch" => BigFppfOver.toScheme B S hS
attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {f : yoneda.obj U ⟶ X}

/-- **Fact 3.34 (i)** on points, `U` affine over `S`. -/
theorem exists_sInf_of_isAffineHom {s : Set (AddSubmonoid M)} (hne : s.Nonempty)
    {T : BigFppfOver B S hS} (t : (yoneda.obj U).obj (op T))
    (h : ∀ N ∈ s, ∃ φ : AttractorPt aU N T, φ.toPoint = t) :
    ∃ φ : AttractorPt aU (sInf s) T, φ.toPoint = t := by
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  refine exists_toPoint_of_sieve (BigFppfOver.isSheaf_of_type_yoneda_obj U)
    (fun T => toPoint_injective_affine _ T) t _ hcov ?_
  rintro Y g ⟨W, a, b, ⟨i⟩, rfl⟩
  have := hV i
  obtain ⟨φ, hφ⟩ := exists_sInf_affine (aU := aU) hne (T := V i) ((yoneda.obj U).map (π i).op t) (by
    intro N hN
    obtain ⟨χ, hχ⟩ := h N hN
    exact ⟨AttractorPt.baseChange (π i) χ, by rw [AttractorPt.toPoint_baseChange, hχ]⟩)
  refine ⟨AttractorPt.baseChange a φ, ?_⟩
  rw [AttractorPt.toPoint_baseChange, hφ, ← Functor.map_comp_apply, ← op_comp]

/-- A point of `X` fixed for the face `Q` of `D(M × M)` acting through multiplication is fixed by
`D(M/Z)` as soon as a retraction `σ` of the diagonal sends `Q` into `Z`. -/
lemma mem_fixed_of_bi {Q : AddSubgroup (M × M)} {Z : AddSubgroup M} (σ : M × M →+ M)
    (hσ : ∀ m, σ (m, m) = m) (hQ : ∀ p ∈ Q, σ p ∈ Z) {T : BigFppfOver B S hS} {y : X.obj (op T)}
    (hy : y ∈ (fixedPoints (quotientAction (biAct aX) Q)).obj (op T)) :
    y ∈ (fixedPoints (quotientAction aX Z)).obj (op T) := by
  intro T' s h
  let θ : (M × M) ⧸ Q →+ M ⧸ Z := QuotientAddGroup.lift Q ((QuotientAddGroup.mk' Z).comp σ) (by
    intro p hp
    exact (QuotientAddGroup.eq_zero_iff _).mpr (hQ p hp))
  have := hy s (h.comp (AddMonoidHom.toMultiplicative θ))
  have e : (((h.comp (AddMonoidHom.toMultiplicative θ)).comp (AddMonoidHom.toMultiplicative
      (QuotientAddGroup.mk' Q))).comp (AddMonoidHom.toMultiplicative (diagHom M))) =
      h.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z)) := by
    refine MonoidHom.ext fun m => congrArg h (congrArg Multiplicative.ofAdd ?_)
    exact congrArg (QuotientAddGroup.mk' Z) (hσ (Multiplicative.toAdd m))
  change aX.smul ((((h.comp (AddMonoidHom.toMultiplicative θ)).comp (AddMonoidHom.toMultiplicative
      (QuotientAddGroup.mk' Q))).comp (AddMonoidHom.toMultiplicative (diagHom M)))) _ = _ at this
  rw [e] at this
  exact this

/-- The step replacing the quotient in the printed proof of **Proposition 3.32 (ii)**: if
`F : 𝔸(N) × 𝔸(L) → X` is equivariant, its value at the unit lies in `X^{N ∩ L}`. After an étale cover,
`F` lifts to the atlas by Proposition 5.1 for the face of units of `N × L`, and on the atlas it is the
affine statement. Each factor of `D(M) × D(M)` fixes the limit point, hence its lift by the FPR
property. -/
theorem exists_inf_of_bi (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : IsStronglyFPRAtlas aU aX f) {N L : AddSubmonoid M}
    (hb : (N.FG ∧ L.FG) ∨ IsLimitPreserving X) {T : BigFppfOver B S hS}
    (φ : AttractorPt (biAct aX) (N.prod L) T) :
    ∃ χ : AttractorPt aX (N ⊓ L) T, χ.toPoint = φ.toPoint := by
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  let F : EquivariantHom aU aX := ⟨f, hat.atlas.equivariant⟩
  let F₂ : EquivariantHom (biAct aU) (biAct aX) :=
    ⟨f, IsEquivariant.comap hat.atlas.equivariant (diagHom M)⟩
  let Q := unitsSubgroup (N.prod L)
  have hQ : IsFace Q.toAddSubmonoid (N.prod L) := isFace_units _
  let Z₁ := unitsSubgroup N
  let Z₂ := unitsSubgroup L
  let x₀ : AttractorPt (biAct aX) Q.toAddSubmonoid T := AttractorPt.ofFace hQ φ
  let g₀ : yoneda.obj T ⟶ X := yonedaEquiv.symm x₀.toPoint
  let rep := hat.atlas.etale.rep
  let T' := rep.pullback g₀
  let q : T' ⟶ T := rep.snd g₀
  let u : T' ⟶ U := rep.fst' g₀
  have hu : f.app (op T') u = X.map q.op x₀.toPoint := by
    have h2 : yoneda.map u ≫ f = yoneda.map q ≫ g₀ := by
      rw [Functor.relativelyRepresentable.map_fst']
      exact rep.w g₀
    have h3 := congrArg (fun k => k.app (op T') (𝟙 T')) h2
    have h4 : (yoneda.map u ≫ f).app (op T') (𝟙 T') = f.app (op T') u := by
      change f.app (op T') (𝟙 T' ≫ u) = _
      rw [Category.id_comp]
    have h5 : (yoneda.map q ≫ g₀).app (op T') (𝟙 T') = X.map q.op x₀.toPoint := by
      change g₀.app (op T') (𝟙 T' ≫ q) = _
      rw [Category.id_comp]
      simp [g₀, yonedaEquiv_symm_app_apply]
    exact h4.symm.trans (h3.trans h5)
  have hfixQ : X.map q.op x₀.toPoint ∈
      (fixedPoints (quotientAction (biAct aX) Q)).obj (op T') := by
    rw [← AttractorPt.toPoint_baseChange]
    exact (AttractorPt.baseChange q x₀).toPoint_mem_fixedPoints
  have hlift : ∀ Z : AddSubgroup M, X.map q.op x₀.toPoint ∈
      (fixedPoints (quotientAction aX Z)).obj (op T') →
      ∃ w : AttractorPt aU Z.toAddSubmonoid T', w.toPoint = u := by
    intro Z hZ
    have hfix : u ∈ (fixedPoints (quotientAction aU Z)).obj (op T') := by
      refine (isFPR_iff (IsEquivariant.comap (actU := aU) (actX := aX) (f := f)
        hat.atlas.equivariant (QuotientAddGroup.mk' Z))).mp (hat.isStronglyFPR Z) (op T') u ?_
      rw [hu]; exact hZ
    have hcov : ∀ {W : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op W)),
        extSieve (fppfO B S hS) Z a ∈ BigFppfOver.topology B S hS W :=
      fun a => extSieve_mem Z a
    exact ⟨attractorFixedEquivOfCover (BigFppfOver.isSheaf_of_type_yoneda_obj U) hcov T' ⟨u, hfix⟩,
      congrArg Subtype.val ((attractorFixedEquivOfCover (act := aU)
        (BigFppfOver.isSheaf_of_type_yoneda_obj U) hcov T').symm_apply_apply ⟨u, hfix⟩)⟩
  obtain ⟨w₁, hw₁⟩ := hlift Z₁ (mem_fixed_of_bi (AddMonoidHom.fst M M) (fun _ => rfl)
    (fun p hp => by
      obtain ⟨⟨h1, h2⟩, y, ⟨h3, h4⟩, e⟩ := hp
      exact ⟨h1, y.1, h3, congrArg Prod.fst e⟩) hfixQ)
  obtain ⟨w₂, hw₂⟩ := hlift Z₂ (mem_fixed_of_bi (AddMonoidHom.snd M M) (fun _ => rfl)
    (fun p hp => by
      obtain ⟨⟨h1, h2⟩, y, ⟨h3, h4⟩, e⟩ := hp
      exact ⟨h2, y.2, h4, congrArg Prod.snd e⟩) hfixQ)
  obtain ⟨wK, hwK⟩ := exists_sInf_of_isAffineHom (aU := aU)
    (s := {Z₁.toAddSubmonoid, Z₂.toAddSubmonoid}) ⟨_, Or.inl rfl⟩ u (by
      rintro K (rfl | rfl)
      · exact ⟨w₁, hw₁⟩
      · exact ⟨w₂, hw₂⟩)
  have hK : ∀ k ∈ sInf ({Z₁.toAddSubmonoid, Z₂.toAddSubmonoid} : Set (AddSubmonoid M)),
      (k, k) ∈ Q.toAddSubmonoid := by
    intro k hk
    rw [sInf_pair] at hk
    obtain ⟨h1, y1, hy1, e1⟩ := hk.1
    obtain ⟨h2, y2, hy2, e2⟩ := hk.2
    exact ⟨⟨h1, h2⟩, (y1, y2), ⟨hy1, hy2⟩, Prod.ext e1 e2⟩
  let wZ : AttractorPt (biAct aU) Q.toAddSubmonoid T' := wK.toBi hK
  have hpush : AttractorPt.ofFace hQ (AttractorPt.baseChange q φ) = AttractorPt.push F₂ wZ := by
    apply attractor_toPoint_injective_sep hX hsep
    change (AttractorPt.baseChange q x₀).toPoint = f.app (op T') wZ.toPoint
    have e : wZ.toPoint = u := (AttractorPt.toPoint_toBi hK wK).trans hwK
    rw [AttractorPt.toPoint_baseChange, e, hu]
  have hcart : IsFaceCartesian F₂ hQ := by
    rcases hb with ⟨hN, hL⟩ | hl
    · exact isFaceCartesian_of_fg hX hsep F₂ (isEtale_of_atlas hat.atlas) hQ (hN.prod hL)
    · exact isFaceCartesian_of_separated hX hsep hl F₂ (isEtale_of_atlas hat.atlas) hQ
  obtain ⟨w, hw⟩ := (hcart T').2 ⟨(AttractorPt.baseChange q φ, wZ), hpush⟩
  have hw' : AttractorPt.push F₂ w = AttractorPt.baseChange q φ := congrArg (fun p => p.1.1) hw
  let wN : AttractorPt aU N T' := w.ofBi (AddMonoidHom.fst M M) (fun _ => rfl) pFst (fun _ => rfl)
  let wL : AttractorPt aU L T' := w.ofBi (AddMonoidHom.snd M M) (fun _ => rfl) pSnd (fun _ => rfl)
  obtain ⟨v, hv⟩ := exists_sInf_of_isAffineHom (aU := aU) (s := {N, L}) ⟨_, Or.inl rfl⟩ w.toPoint (by
    rintro K (rfl | rfl)
    · exact ⟨wN, AttractorPt.toPoint_ofBi _ _ _ _ _⟩
    · exact ⟨wL, AttractorPt.toPoint_ofBi _ _ _ _ _⟩)
  have hinf : sInf ({N, L} : Set (AddSubmonoid M)) = N ⊓ L := sInf_pair
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  obtain ⟨χ, hχ⟩ := exists_toPoint_of_sieve hsX
    (N := N ⊓ L) (fun T => attractor_toPoint_injective_sep hX hsep _ T) φ.toPoint _
    (Space.sieve_generate_singleton_mem_topology_over B S hS q
      (hat.atlas.surjective.property_snd g₀) (hat.atlas.etale.property_snd g₀)) (by
      rintro Y g ⟨W, a, b, ⟨⟩, rfl⟩
      refine ⟨AttractorPt.baseChange a (AttractorPt.ofLE hinf.le (AttractorPt.push F v)), ?_⟩
      have h1 : (AttractorPt.push F v).toPoint = (AttractorPt.baseChange q φ).toPoint := by
        rw [← hw']
        exact congrArg (f.app (op T')) hv
      rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_ofLE, h1,
        AttractorPt.toPoint_baseChange, ← Functor.map_comp_apply, ← op_comp])
  exact ⟨χ, hχ⟩

/-- `F = f ∘ m`, with `m : 𝔸(N) × 𝔸(L) → 𝔸(N ∩ L)` the multiplication: the map `f ↦ F` of the printed
proof of Proposition 3.32 (ii). -/
noncomputable def iterOfInf {N L : AddSubmonoid M} {T : BigFppfOver B S hS} (χ : AttractorPt aX (N ⊓ L) T) :
    IterPt aX N L T :=
  (iterEquivBi T).symm (χ.toBi (K := N ⊓ L) (P := N.prod L)
    (fun _ hk => ⟨(AddSubmonoid.mem_inf.mp hk).1, (AddSubmonoid.mem_inf.mp hk).2⟩))

/-- **Proposition 3.32 (ii)**: `(X^N)^L = X^{N ∩ L}`. `M` is a finitely generated abelian group, `X` a
separated algebraic space with an `S`-affine strongly-FPR atlas, and `N`, `L` are finitely generated or
`X` is limit preserving. -/
theorem prop332 (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : IsStronglyFPRAtlas aU aX f) {N L : AddSubmonoid M}
    (hb : (N.FG ∧ L.FG) ∨ IsLimitPreserving X) (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T) := by
  constructor
  · intro χ χ' h
    apply attractor_toPoint_injective_sep hX hsep
    have h' := (iterEquivBi T).symm.injective h
    have := congrArg AttractorPt.toPoint h'
    exact (AttractorPt.toPoint_toBi _ χ).symm.trans (this.trans (AttractorPt.toPoint_toBi _ χ'))
  · intro Ψ
    obtain ⟨χ, hχ⟩ := exists_inf_of_bi hX hsep hat hb Ψ.toBi
    refine ⟨χ, ?_⟩
    apply (iterEquivBi T).injective
    rw [iterOfInf, Equiv.apply_symm_apply]
    apply attractor_toPoint_injective_sep hX hsep
    exact (AttractorPt.toPoint_toBi _ χ).trans hχ

/-- If `X^N = X^L` as subfunctors of `X`, every point of `X^N` extends to a point of `(X^N)^L`. -/
theorem exists_iter_of_image_eq (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    {N L : AddSubmonoid M} (h : attractorImage aX N = attractorImage aX L)
    {T : BigFppfOver B S hS} (ψ : AttractorPt aX L T) :
    ∃ Ψ : IterPt aX N L T, Ψ.toPoint = ψ.toPoint := by
  classical
  have hinj := fun T => attractor_toPoint_injective_sep (aX := aX) hX hsep N T
  have hG : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (b : APt (fppfO B S hS) L (op T')),
      ∃ G : AttractorPt aX N T', G.toPoint = ψ.app t b := by
    intro T' t b
    have hm : ψ.app t b ∈ attractorImage aX L T' := by
      refine ⟨(magnetAction aX L).smul b (AttractorPt.baseChange t ψ), ?_⟩
      change ψ.app (𝟙 T' ≫ t) (APt.res (𝟙 T').op b * 1) = _
      have e : APt.res (𝟙 T').op b = b := APt.res_id b
      rw [e, mul_one, Category.id_comp]
    rw [← h] at hm
    exact hm
  choose G hGp using @hG
  refine ⟨⟨fun t b => G t b, ?_, ?_⟩, ?_⟩
  · intro T' T'' s t b
    apply hinj
    rw [hGp, AttractorPt.toPoint_baseChange, hGp, ψ.naturality]
  · intro T' t k b
    apply hinj
    rw [hGp, ψ.equivariant]
    change _ = aX.smul (APt.res (𝟙 T').op k) (G t b).toPoint
    have e : APt.res (𝟙 T').op k = k := APt.res_id k
    rw [e, hGp]
  · change (G (𝟙 T) 1).toPoint = _
    rw [hGp]
    rfl

/-- `X^N = X^L` implies `X^{N ∩ L} = X^N`. The case of two magnets of **Fact 3.34 (ii)**. -/
theorem attractorImage_inf_of_eq (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : IsStronglyFPRAtlas aU aX f) {N L : AddSubmonoid M}
    (hb : (N.FG ∧ L.FG) ∨ IsLimitPreserving X)
    (h : attractorImage aX N = attractorImage aX L) :
    attractorImage aX (N ⊓ L) = attractorImage aX N := by
  refine le_antisymm (attractorImage_monotone aX inf_le_left) ?_
  intro T x hx
  rw [h] at hx
  obtain ⟨ψ, rfl⟩ := hx
  obtain ⟨Ψ, hΨ⟩ := exists_iter_of_image_eq hX hsep h ψ
  obtain ⟨χ, hχ⟩ := exists_inf_of_bi hX hsep hat hb Ψ.toBi
  exact ⟨χ, by rw [hχ, IterPt.toPoint_toBi, hΨ]⟩

/-- **Fact 3.34 (ii)** for a finite family, as in the first step of the printed proof. -/
theorem fact334_finite (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : IsStronglyFPRAtlas aU aX f) (hlim : IsLimitPreserving X) {s : Set (AddSubmonoid M)}
    (hfin : s.Finite) (y) (hne : s.Nonempty) (hy : ∀ N ∈ s, attractorImage aX N = y) :
    attractorImage aX (sInf s) = y := by
  induction s, hfin using Set.Finite.induction_on with
  | empty => exact absurd hne Set.not_nonempty_empty
  | @insert N s' _ _ ih =>
    rw [sInf_insert]
    rcases s'.eq_empty_or_nonempty with rfl | hs'
    · simpa using hy N (Set.mem_insert _ _)
    · have e := ih hs' fun K hK => hy K (Set.mem_insert_of_mem _ hK)
      rw [attractorImage_inf_of_eq hX hsep hat (Or.inr hlim)
        ((hy N (Set.mem_insert _ _)).trans e.symm)]
      exact hy N (Set.mem_insert _ _)

/-- **Fact 3.34 (ii)**, arbitrary family. As in the printed proof one passes to finite subfamilies `J`.
The colimit step is replaced by: `U` has finitely many attractors (Theorem 15.4 (i)), so one `J` already
has `U^{⋂ J} ⊆ U^{N}` for all `N` in the family. -/
theorem fact334 [CompactSpace S] (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : IsStronglyFPRAtlas aU aX f) (hlim : IsLimitPreserving X) (hft : ChartsOfFiniteType X)
    {s : Set (AddSubmonoid M)} (y) (hne : s.Nonempty) (hy : ∀ N ∈ s, attractorImage aX N = y) :
    attractorImage aX (sInf s) = y := by
  obtain ⟨N₀, hN₀⟩ := id hne
  refine le_antisymm ((attractorImage_monotone aX (sInf_le hN₀)).trans_eq (hy N₀ hN₀)) ?_
  have : LocallyOfFiniteType U.hom.hom := hft U f hat.atlas.etale
  have hrange := (thm154_i aU).2
  let 𝓙 : Set (AddSubmonoid M) := {K | ∃ J ⊆ s, J.Finite ∧ J.Nonempty ∧ K = sInf J}
  have hJ : (attractorImage aU '' 𝓙).Finite := hrange.subset (Set.image_subset_range _ _)
  obtain ⟨y₀, ⟨K, hK, rfl⟩, hmin⟩ := hJ.exists_minimal
    ⟨_, N₀, ⟨{N₀}, by simpa using hN₀, Set.finite_singleton _, Set.singleton_nonempty _, by simp⟩, rfl⟩
  obtain ⟨J, hJs, hJf, hJn, rfl⟩ := hK
  have hKN : ∀ N ∈ s, attractorImage aU (sInf J) ≤ attractorImage aU N := by
    intro N hN
    have hmem : attractorImage aU (sInf (insert N J)) ∈ attractorImage aU '' 𝓙 :=
      ⟨_, ⟨insert N J, Set.insert_subset hN hJs, hJf.insert N, Set.insert_nonempty _ _, rfl⟩, rfl⟩
    have hle : attractorImage aU (sInf (insert N J)) ≤ attractorImage aU (sInf J) :=
      attractorImage_monotone aU (sInf_le_sInf (Set.subset_insert _ _))
    exact (hmin hmem hle).trans (attractorImage_monotone aU (sInf_le (Set.mem_insert _ _)))
  have hJy : attractorImage aX (sInf J) = y :=
    fact334_finite hX hsep hat hlim hJf y hJn fun N hN => hy N (hJs hN)
  intro T x hx
  rw [← hJy] at hx
  obtain ⟨ψ, rfl⟩ := hx
  obtain ⟨T', q, w, hs, he, hw⟩ := exists_atlas_lift hX hsep hlim hat ψ
  obtain ⟨v, hv⟩ := exists_sInf_of_isAffineHom (aU := aU) hne w.toPoint fun N hN => by
    obtain ⟨w', hw'⟩ := hKN N hN T' ⟨w, rfl⟩
    exact ⟨w', hw'⟩
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  refine exists_toPoint_of_sieve hsX (fun T => attractor_toPoint_injective_sep hX hsep _ T) _ _
    (Space.sieve_generate_singleton_mem_topology_over B S hS q hs he) ?_
  rintro Y g ⟨W, a, b, ⟨⟩, rfl⟩
  refine ⟨AttractorPt.baseChange a (AttractorPt.push ⟨f, hat.atlas.equivariant⟩ v), ?_⟩
  have h1 : (AttractorPt.push ⟨f, hat.atlas.equivariant⟩ v).toPoint =
      (AttractorPt.baseChange q ψ).toPoint := by
    rw [← hw]
    exact congrArg (f.app (op T')) hv
  rw [AttractorPt.toPoint_baseChange, h1, AttractorPt.toPoint_baseChange,
    ← Functor.map_comp_apply, ← op_comp]

/-- `AttractorOrder` for a separated `X` with an atlas. -/
theorem attractorOrder_of_atlas [CompactSpace S] (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hat : IsStronglyFPRAtlas aU aX f) (hlim : IsLimitPreserving X)
    (hft : ChartsOfFiniteType X) : AttractorOrder (attractorImage aX) where
  monotone := attractorImage_monotone aX
  sInf_of_const _ y hne hy := fact334 hX hsep hat hlim hft y hne hy

/-- **Proposition 15.1**: it uses only the case of two magnets of Fact 3.34. -/
theorem prop151_of_atlas (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hat : IsStronglyFPRAtlas aU aX f) (hlim : IsLimitPreserving X) (N : AddSubmonoid M) :
    IsPure (attractorImage aX) N ↔ ∀ L, L < N → attractorImage aX L < attractorImage aX N := by
  constructor
  · intro h L hL
    exact IsPure.attractorImage_lt aX h hL
  · intro h L e
    by_contra hNL
    have hlt : N ⊓ L < N := lt_of_le_of_ne inf_le_left fun e' => hNL (inf_eq_left.mp e')
    have := h _ hlt
    rw [attractorImage_inf_of_eq hX hsep hat (Or.inr hlim) e] at this
    exact lt_irrefl _ this

/-- **Theorem 15.3**: the bijection between pure magnets and attractors. -/
noncomputable def thm153_of_atlas [CompactSpace S] (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hat : IsStronglyFPRAtlas aU aX f) (hlim : IsLimitPreserving X)
    (hft : ChartsOfFiniteType X) :
    pureMagnets (attractorImage aX) ≃ Set.range (attractorImage aX) :=
  pureEquivRange (attractorOrder_of_atlas hX hsep hat hlim hft)

end Site

end AlgMag

#print axioms AlgMag.prop332
#print axioms AlgMag.attractorImage_inf_of_eq
#print axioms AlgMag.fact334_finite
#print axioms AlgMag.fact334
#print axioms AlgMag.attractorOrder_of_atlas
#print axioms AlgMag.prop151_of_atlas
#print axioms AlgMag.thm153_of_atlas
