/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Functorial
import Mathlib.Tactic.Ring

/-!
# Attractors by stages (Algebraic Magnetism, §16.4)

The identifications of §16.4 are proved here for any functor with an action, with no hypothesis on
`X`: the paper deduces them from Propositions 3.31, 3.32, 3.35, whose hypotheses are not needed for
these particular magnets. Nested attractors need `X^N` to lie in the universe of the ring functor,
so the site is small: `C : Type u`, with `M : Type u` (this contains `BigFppfOver B S hS`).
-/

open CategoryTheory Opposite

universe u

set_option linter.unusedSectionVars false

namespace AlgMag

variable {C : Type u} [Category.{u} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-! ### Restriction of the acting monoid -/

/-- The action of `𝔸(Z)` deduced from an action of `𝔸(M)` through a monoid map `r : M → Z` (the
morphism `𝔸(Z) → 𝔸(M)` dual to `r`). -/
def AAction.along {M Z : Type u} [AddCommMonoid M] [AddCommMonoid Z] {F : Cᵒᵖ ⥤ Type u}
    (act : AAction 𝒪 M F) (r : M →+ Z) : AAction 𝒪 Z F where
  smul h x := act.smul (h.comp (AddMonoidHom.toMultiplicative r)) x
  one_smul x := act.one_smul x
  mul_smul g h x := act.mul_smul (g.comp (AddMonoidHom.toMultiplicative r))
    (h.comp (AddMonoidHom.toMultiplicative r)) x
  map_smul f h x := act.map_smul f _ x

/-! ### Example (ii), (iii): products -/

section Prod

variable {M₁ M₂ : Type u} [AddCommMonoid M₁] [AddCommMonoid M₂] {F : Cᵒᵖ ⥤ Type u}
  (act : AAction 𝒪 (M₁ × M₂) F) (N₁ : AddSubmonoid M₁) (N₂ : AddSubmonoid M₂)

/-- `𝔸(M₁) → 𝔸(M₁ × M₂)`, `a ↦ a ⊠ 1`, or the action of `M₁`: the action of the factor `D(M₁)`. -/
def inlPt {U : Cᵒᵖ} (a : APt 𝒪 M₁ U) : APt 𝒪 (M₁ × M₂) U :=
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst M₁ M₂))

/-- The second factor. -/
def inrPt {U : Cᵒᵖ} (a : APt 𝒪 M₂ U) : APt 𝒪 (M₁ × M₂) U :=
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd M₁ M₂))

/-- `𝔸(M₁)` acting through the first factor (paper: `Z × 0`). -/
def actFst : AAction 𝒪 M₁ F where
  smul h x := act.smul (inlPt h) x
  one_smul x := act.one_smul x
  mul_smul g h x := act.mul_smul (inlPt g) (inlPt h) x
  map_smul f h x := act.map_smul f _ x

/-- `𝔸(M₂)` acting on the first stage `X^{N₁}_{M₁}` through the second factor (Remark 3.11). -/
def actSnd : AAction 𝒪 M₂ (attractor (actFst act) N₁) where
  smul {U} h φ :=
    { app := fun {T'} t a => act.smul (inrPt (APt.res t.op h)) (AttractorPt.app φ t a)
      naturality := fun {T' T''} s t a => by
        rw [AttractorPt.naturality φ s t a, act.map_smul]
        congr 1
        rw [op_comp, APt.res_comp]
        rfl
      equivariant := fun {T'} t k a => by
        rw [AttractorPt.equivariant φ t k a]
        change act.smul _ (act.smul _ _) = act.smul _ (act.smul _ _)
        rw [← act.mul_smul, ← act.mul_smul, mul_comm] }
  one_smul {U} φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    have h1 : inrPt (M₁ := M₁) (APt.res t.op (1 : APt 𝒪 M₂ U)) = 1 := by ext p; simp [inrPt]
    change act.smul (inrPt (APt.res t.op 1)) _ = _
    rw [h1, act.one_smul]
  mul_smul {U} g h φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change act.smul (inrPt (APt.res t.op (g * h))) _ = act.smul _ (act.smul _ _)
    rw [← act.mul_smul]
    congr 1
    rw [APt.res_mul]
    rfl
  map_smul {U V} s h φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change act.smul (inrPt (APt.res (t ≫ s.unop).op h)) _ = act.smul (inrPt (APt.res t.op (APt.res s h))) _
    rw [← APt.res_comp]
    rfl

/-- The inclusion `N₁ → N₁ × N₂`. -/
def inMagnet₁ : N₁ →+ (N₁.prod N₂) :=
  { toFun := fun n => ⟨(n, 0), n.2, N₂.zero_mem⟩, map_zero' := rfl
    map_add' := fun a b => Subtype.ext (Prod.ext rfl (add_zero 0).symm) }

/-- The inclusion `N₂ → N₁ × N₂`. -/
def inMagnet₂ : N₂ →+ (N₁.prod N₂) :=
  { toFun := fun n => ⟨(0, n), N₁.zero_mem, n.2⟩, map_zero' := rfl
    map_add' := fun a b => Subtype.ext (Prod.ext (add_zero 0).symm rfl) }

/-- The first restriction `𝔸(N₁ × N₂) → 𝔸(N₁)`. -/
def cut₁ {U : Cᵒᵖ} (c : APt 𝒪 (N₁.prod N₂) U) : APt 𝒪 N₁ U :=
  c.comp (AddMonoidHom.toMultiplicative (inMagnet₁ N₁ N₂))

/-- The second restriction `𝔸(N₁ × N₂) → 𝔸(N₂)`. -/
def cut₂ {U : Cᵒᵖ} (c : APt 𝒪 (N₁.prod N₂) U) : APt 𝒪 N₂ U :=
  c.comp (AddMonoidHom.toMultiplicative (inMagnet₂ N₁ N₂))

/-- `𝔸(N₁) × 𝔸(N₂) → 𝔸(N₁ × N₂)`. -/
def glue {U : Cᵒᵖ} (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) : APt 𝒪 (N₁.prod N₂) U where
  toFun n := a (Multiplicative.ofAdd ⟨(Multiplicative.toAdd n : N₁.prod N₂).1.1,
      (Multiplicative.toAdd n : N₁.prod N₂).2.1⟩) *
    b (Multiplicative.ofAdd ⟨(Multiplicative.toAdd n : N₁.prod N₂).1.2,
      (Multiplicative.toAdd n : N₁.prod N₂).2.2⟩)
  map_one' := by
    have ha := a.map_one
    have hb := b.map_one
    exact (congrArg₂ (· * ·) ha hb).trans (mul_one 1)
  map_mul' x y := by
    have ha := a.map_mul
      (Multiplicative.ofAdd ⟨(Multiplicative.toAdd x : N₁.prod N₂).1.1,
        (Multiplicative.toAdd x : N₁.prod N₂).2.1⟩)
      (Multiplicative.ofAdd ⟨(Multiplicative.toAdd y : N₁.prod N₂).1.1,
        (Multiplicative.toAdd y : N₁.prod N₂).2.1⟩)
    have hb := b.map_mul
      (Multiplicative.ofAdd ⟨(Multiplicative.toAdd x : N₁.prod N₂).1.2,
        (Multiplicative.toAdd x : N₁.prod N₂).2.2⟩)
      (Multiplicative.ofAdd ⟨(Multiplicative.toAdd y : N₁.prod N₂).1.2,
        (Multiplicative.toAdd y : N₁.prod N₂).2.2⟩)
    refine (congrArg₂ (· * ·) ha hb).trans ?_
    exact mul_mul_mul_comm _ _ _ _

lemma glue_res {U V : Cᵒᵖ} (f : U ⟶ V) (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    glue N₁ N₂ (APt.res f a) (APt.res f b) = APt.res f (glue N₁ N₂ a b) := by
  refine MonoidHom.ext fun n => ?_
  exact (map_mul (𝒪.map f).hom _ _).symm

lemma glue_cut {U : Cᵒᵖ} (c : APt 𝒪 (N₁.prod N₂) U) :
    glue N₁ N₂ (cut₁ N₁ N₂ c) (cut₂ N₁ N₂ c) = c := by
  refine MonoidHom.ext fun n => ?_
  refine (c.map_mul _ _).symm.trans (congrArg c ?_)
  refine Multiplicative.toAdd.injective (Subtype.ext (Prod.ext ?_ ?_))
  · exact add_zero _
  · exact zero_add _

lemma cut₁_glue {U : Cᵒᵖ} (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    cut₁ N₁ N₂ (glue N₁ N₂ a b) = a := by
  refine MonoidHom.ext fun n => ?_
  have h1 : b (Multiplicative.ofAdd (⟨0, N₂.zero_mem⟩ : N₂)) = 1 := b.map_one
  exact (congrArg (_ * ·) h1).trans (mul_one _)

lemma cut₂_glue {U : Cᵒᵖ} (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    cut₂ N₁ N₂ (glue N₁ N₂ a b) = b := by
  refine MonoidHom.ext fun n => ?_
  have h1 : a (Multiplicative.ofAdd (⟨0, N₁.zero_mem⟩ : N₁)) = 1 := a.map_one
  exact (congrArg (· * _) h1).trans (one_mul _)

lemma glue_mul {U : Cᵒᵖ} (h : APt 𝒪 M₁ U) (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    glue N₁ N₂ (APt.toMagnet N₁ h * a) b =
      APt.toMagnet (N₁.prod N₂) (inlPt h) * glue N₁ N₂ a b := by
  refine MonoidHom.ext fun n => ?_
  exact mul_assoc _ _ _

lemma glue_mul' {U : Cᵒᵖ} (h : APt 𝒪 M₂ U) (a : APt 𝒪 N₁ U) (b : APt 𝒪 N₂ U) :
    glue N₁ N₂ a (APt.toMagnet N₂ h * b) =
      APt.toMagnet (N₁.prod N₂) (inrPt h) * glue N₁ N₂ a b := by
  refine MonoidHom.ext fun n => ?_
  exact mul_left_comm _ _ _

lemma split_pt {U : Cᵒᵖ} (h : APt 𝒪 (M₁ × M₂) U) :
    inlPt (h.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M₁ M₂))) *
      inrPt (h.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M₁ M₂))) = h := by
  refine MonoidHom.ext fun n => ?_
  refine (h.map_mul _ _).symm.trans (congrArg h ?_)
  exact Multiplicative.toAdd.injective (Prod.ext (add_zero _) (zero_add _))

lemma AttractorPt.app_congr' {M : Type u} [AddCommMonoid M] {F : Cᵒᵖ ⥤ Type u}
    {act : AAction 𝒪 M F} {N : AddSubmonoid M} {T T' : C}
    (φ : AttractorPt act N T) {t t' : T' ⟶ T} (h : t = t') {a : APt 𝒪 N (op T')} :
    φ.app t a = φ.app t' a := by
  subst h; rfl

/-- The bijection of §16.4 (ii) on points. -/
def stagesEquiv (T : C) :
    AttractorPt act (N₁.prod N₂) T ≃ AttractorPt (actSnd act N₁) N₂ T where
  toFun φ :=
    { app := fun {T'} t b =>
        { app := fun {T''} t' a => φ.app (t' ≫ t) (glue N₁ N₂ a (APt.res t'.op b))
          naturality := fun {T₂ T₃} s t' a => by
            rw [Category.assoc, ← φ.naturality s (t' ≫ t), ← glue_res, ← APt.res_comp]
            rfl
          equivariant := fun {T''} t' k a => by
            rw [glue_mul]
            exact φ.equivariant _ _ _ }
      naturality := fun {T' T''} s t b => by
        refine AttractorPt.ext ?_
        funext T₂ t' a
        change φ.app (t' ≫ s ≫ t) (glue N₁ N₂ a (APt.res t'.op (APt.res s.op b))) =
          φ.app ((t' ≫ s) ≫ t) (glue N₁ N₂ a (APt.res (t' ≫ s).op b))
        rw [Category.assoc, op_comp, APt.res_comp]
      equivariant := fun {T'} t k b => by
        refine AttractorPt.ext ?_
        funext T₂ t' a
        change φ.app (t' ≫ t) (glue N₁ N₂ a (APt.res t'.op (APt.toMagnet N₂ k * b))) =
          act.smul (inrPt (APt.res t'.op k)) (φ.app (t' ≫ t) (glue N₁ N₂ a (APt.res t'.op b)))
        rw [APt.res_mul, ← φ.equivariant, ← glue_mul']
        rfl }
  invFun ψ :=
    { app := fun {T'} t c => AttractorPt.app (ψ.app t (cut₂ N₁ N₂ c)) (𝟙 T') (cut₁ N₁ N₂ c)
      naturality := fun {T' T''} s t c => by
        have e := ψ.naturality s t (cut₂ N₁ N₂ c)
        have e' := congrArg (fun χ : AttractorPt (actFst act) N₁ T'' =>
          χ.app (𝟙 T'') (cut₁ N₁ N₂ (APt.res s.op c))) e
        refine e'.trans ?_
        have n := AttractorPt.naturality (ψ.app t (cut₂ N₁ N₂ c)) s (𝟙 T') (cut₁ N₁ N₂ c)
        refine Eq.trans ?_ n
        change AttractorPt.app (ψ.app t (cut₂ N₁ N₂ c)) (𝟙 T'' ≫ s) (cut₁ N₁ N₂ (APt.res s.op c)) = _
        rw [Category.id_comp, Category.comp_id]
        rfl
      equivariant := fun {T'} t k c => by
        have hc₂ : cut₂ N₁ N₂ (APt.toMagnet (N₁.prod N₂) k * c) =
            APt.toMagnet N₂ (k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M₁ M₂))) *
              cut₂ N₁ N₂ c := rfl
        have hc₁ : cut₁ N₁ N₂ (APt.toMagnet (N₁.prod N₂) k * c) =
            APt.toMagnet N₁ (k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M₁ M₂))) *
              cut₁ N₁ N₂ c := rfl
        rw [hc₂, hc₁]
        set k₁ := k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M₁ M₂))
        set k₂ := k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M₁ M₂))
        have e₂ := congrArg (fun χ : AttractorPt (actFst act) N₁ T' =>
          χ.app (𝟙 T') (APt.toMagnet N₁ k₁ * cut₁ N₁ N₂ c)) (ψ.equivariant t k₂ (cut₂ N₁ N₂ c))
        refine e₂.trans ?_
        change act.smul (inrPt (APt.res (𝟙 T').op k₂)) (AttractorPt.app (ψ.app t (cut₂ N₁ N₂ c)) (𝟙 T')
          (APt.toMagnet N₁ k₁ * cut₁ N₁ N₂ c)) = _
        rw [AttractorPt.equivariant (ψ.app t (cut₂ N₁ N₂ c)) (𝟙 T') k₁ (cut₁ N₁ N₂ c)]
        change act.smul _ (act.smul (inlPt k₁) _) = _
        rw [← act.mul_smul]
        congr 1
        have hk₂ : APt.res (𝟙 T').op k₂ = k₂ := by simp
        rw [hk₂, mul_comm]
        exact split_pt k }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t c
    change φ.app (𝟙 T' ≫ t) (glue N₁ N₂ (cut₁ N₁ N₂ c) (APt.res (𝟙 T').op (cut₂ N₁ N₂ c))) = _
    rw [Category.id_comp]
    simp only [op_id, APt.res_id, glue_cut]
  right_inv ψ := by
    refine AttractorPt.ext ?_
    funext T' t b
    refine AttractorPt.ext ?_
    funext T₂ t' a
    change AttractorPt.app (ψ.app (t' ≫ t) (cut₂ N₁ N₂ (glue N₁ N₂ a (APt.res t'.op b)))) (𝟙 T₂)
      (cut₁ N₁ N₂ (glue N₁ N₂ a (APt.res t'.op b))) = _
    rw [cut₁_glue, cut₂_glue]
    have e := congrArg (fun χ : AttractorPt (actFst act) N₁ T₂ => χ.app (𝟙 T₂) a) (ψ.naturality t' t b)
    refine e.trans ?_
    change AttractorPt.app (ψ.app t b) (𝟙 T₂ ≫ t') a = _
    rw [Category.id_comp]

/-- **§16.4 (ii).** `X^{N₁ × N₂} = (X^{N₁})^{N₂}` for `D(M₁ × M₂)` (or `𝔸(M₁ × M₂)`) acting on any
functor `X`: the first stage is the attractor for the factor `M₁`, the second for the factor `M₂`,
acting on the first stage. For `M₁ = M₂ = ℤ`, `N₁ = N₂ = ℕ` these are two stages of
`G_m`-attractors. -/
def stagesIso : attractor act (N₁.prod N₂) ≅ attractor (actSnd act N₁) N₂ :=
  NatIso.ofComponents (fun U => (stagesEquiv act N₁ N₂ (unop U)).toIso) (fun {U V} s => by
    ext φ
    refine AttractorPt.ext ?_
    funext T' t b
    refine AttractorPt.ext ?_
    funext T₂ t' a
    exact AttractorPt.app_congr' (act := act) (N := N₁.prod N₂) (T := unop U) φ (by simp))

end Prod

/-! ### Example (i): a magnet inside a magnet -/

section Inner

variable {M : Type u} [AddCommMonoid M] {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F)
  {N L : AddSubmonoid M} (hNL : N ≤ L)

/-- `N` seen as a magnet of `L`. -/
abbrev innerMagnet (N L : AddSubmonoid M) : AddSubmonoid L := N.comap L.subtype

/-- `𝔸(N') → 𝔸(N)` where `N' = N` is seen in `L`. -/
def upPt (hNL : N ≤ L) {U : Cᵒᵖ} (b : APt 𝒪 (innerMagnet N L) U) : APt 𝒪 N U :=
  b.comp (AddMonoidHom.toMultiplicative
    { toFun := fun n => ⟨⟨n.1, hNL n.2⟩, n.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl })

/-- `𝔸(N) → 𝔸(N')`. -/
def downPt {U : Cᵒᵖ} (c : APt 𝒪 N U) : APt 𝒪 (innerMagnet N L) U :=
  c.comp (AddMonoidHom.toMultiplicative
    { toFun := fun n => ⟨n.1.1, n.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl })

/-- The bijection of §16.4 (i) on points. -/
def innerEquiv (T : C) :
    AttractorPt act N T ≃ AttractorPt (magnetAction act L) (innerMagnet N L) T where
  toFun φ :=
    { app := fun {T'} t b =>
        { app := fun {T''} t' a =>
            φ.app (t' ≫ t) (APt.restrict hNL a * upPt hNL (APt.res t'.op b))
          naturality := fun {T₂ T₃} s t' a => by
            rw [← φ.naturality s (t' ≫ t), Category.assoc, APt.res_mul, op_comp, APt.res_comp]
            rfl
          equivariant := fun {T''} t' k a => by
            rw [← φ.equivariant]
            congr 1
            refine MonoidHom.ext fun n => ?_
            exact mul_assoc _ _ _ }
      naturality := fun {T' T''} s t b => by
        refine AttractorPt.ext ?_
        funext T₂ t' a
        change φ.app (t' ≫ s ≫ t) (_ * upPt hNL (APt.res t'.op (APt.res s.op b))) =
          φ.app ((t' ≫ s) ≫ t) (_ * upPt hNL (APt.res (t' ≫ s).op b))
        rw [Category.assoc, op_comp, APt.res_comp]
      equivariant := fun {T'} t k b => by
        refine AttractorPt.ext ?_
        funext T₂ t' a
        change φ.app (t' ≫ t) (APt.restrict hNL a *
            upPt hNL (APt.res t'.op (APt.toMagnet (innerMagnet N L) k * b))) =
          φ.app (t' ≫ t) (APt.restrict hNL (APt.res t'.op k * a) * upPt hNL (APt.res t'.op b))
        congr 1
        refine MonoidHom.ext fun n => ?_
        have key : ∀ (x : 𝒪.obj (op T₂)) (y w : 𝒪.obj (op T')), x * (𝒪.map t'.op).hom (y * w) =
            ((𝒪.map t'.op).hom y * x) * (𝒪.map t'.op).hom w := by
          intro x y w
          rw [map_mul]
          ring
        exact key _ _ _ }
  invFun ψ :=
    { app := fun {T'} t c => AttractorPt.app (ψ.app t (downPt c)) (𝟙 T') 1
      naturality := fun {T' T''} s t c => by
        have e := congrArg (fun χ : AttractorPt act L T'' => χ.app (𝟙 T'') 1)
          (ψ.naturality s t (downPt c))
        refine e.trans ?_
        have n := AttractorPt.naturality (ψ.app t (downPt c)) s (𝟙 T') 1
        have h1 : APt.res (𝒪 := 𝒪) (P := L) s.op 1 = 1 := by ext p; simp
        rw [h1, Category.comp_id] at n
        refine Eq.trans ?_ n
        change AttractorPt.app (ψ.app t (downPt c)) (𝟙 T'' ≫ s) 1 = _
        rw [Category.id_comp]
      equivariant := fun {T'} t k c => by
        have hc : downPt (APt.toMagnet N k * c) =
            APt.toMagnet (innerMagnet N L) (APt.toMagnet L k) * downPt c := rfl
        rw [hc]
        have e := congrArg (fun χ : AttractorPt act L T' => χ.app (𝟙 T') 1)
          (ψ.equivariant t (APt.toMagnet L k) (downPt c))
        refine e.trans ?_
        change AttractorPt.app (ψ.app t (downPt c)) (𝟙 T') (APt.res (𝟙 T').op (APt.toMagnet L k) * 1) = _
        have h1 : APt.res (𝟙 T').op (APt.toMagnet L k) * 1 = APt.toMagnet L k * 1 := by simp
        rw [h1]
        exact AttractorPt.equivariant (ψ.app t (downPt c)) (𝟙 T') k 1 }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t c
    change φ.app (𝟙 T' ≫ t) (APt.restrict hNL 1 * upPt hNL (APt.res (𝟙 T').op (downPt c))) = _
    have e : APt.restrict hNL (1 : APt 𝒪 L (op T')) * upPt hNL (APt.res (𝟙 T').op (downPt c)) = c := by
      rw [APt.restrict_one, one_mul]
      simp only [op_id, APt.res_id]
      rfl
    rw [e, Category.id_comp]
  right_inv ψ := by
    refine AttractorPt.ext ?_
    funext T' t b
    refine AttractorPt.ext ?_
    funext T₂ t' a
    change AttractorPt.app (ψ.app (t' ≫ t)
      (downPt (APt.restrict hNL a * upPt hNL (APt.res t'.op b)))) (𝟙 T₂) 1 = _
    have hd : downPt (APt.restrict hNL a * upPt hNL (APt.res t'.op b)) =
        APt.toMagnet (innerMagnet N L) a * APt.res t'.op b := rfl
    rw [hd]
    have e := congrArg (fun χ : AttractorPt act L T₂ => χ.app (𝟙 T₂) 1)
      (ψ.equivariant (t' ≫ t) a (APt.res t'.op b))
    refine e.trans ?_
    change AttractorPt.app (ψ.app (t' ≫ t) (APt.res t'.op b)) (𝟙 T₂) (APt.res (𝟙 T₂).op a * 1) = _
    have e' := congrArg (fun χ : AttractorPt act L T₂ => χ.app (𝟙 T₂) (APt.res (𝟙 T₂).op a * 1))
      (ψ.naturality t' t b)
    refine e'.trans ?_
    change AttractorPt.app (ψ.app t b) (𝟙 T₂ ≫ t') (APt.res (𝟙 T₂).op a * 1) = _
    have h1 : APt.res (𝟙 T₂).op a * 1 = a := by simp
    rw [h1, Category.id_comp]

/-- **§16.4 (i)**, second step: for magnets `N ⊆ L`, `X^N = (X^L)^N`, the outer attractor being for
`𝔸(L)` acting on `X^L` as in Remark 3.12. With `L = ℤα`, `N = [α⟩` the outer stage is an attractor
for `D(ℤα)` (see `attractorTransportIso` for `D(ℤα) = G_m`). No hypothesis on `X`, `M`. -/
def innerIso : attractor act N ≅ attractor (magnetAction act L) (innerMagnet N L) :=
  NatIso.ofComponents (fun U => (innerEquiv act hNL (unop U)).toIso) (fun {U V} s => by
    ext φ
    refine AttractorPt.ext ?_
    funext T' t b
    refine AttractorPt.ext ?_
    funext T₂ t' a
    exact AttractorPt.app_congr' (act := act) (N := N) (T := unop U) φ (by simp))

end Inner

section Fixed

variable {M : Type u} [AddCommGroup M] {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F)
  (L : AddSubmonoid M) (r : M →+ L) (hr : ∀ l : L, r l = l)

/-- **§16.4 (i)**, first step (Proposition 3.35), when `L` is a retract of the group `M`: `X^L` is
the functor of fixed points of `D(M/L)`, that is of the characters of `M` trivial on `L`. -/
def retractFixedEquiv (T : C) :
    AttractorPt act L T ≃ {x : F.obj (op T) // ∀ {T' : C} (t : T' ⟶ T) (h : APt 𝒪 M (op T')),
      APt.toMagnet L h = 1 → act.smul h (F.map t.op x) = F.map t.op x} where
  toFun φ := ⟨φ.toPoint, fun {T'} t h hh => by
    have hn := φ.naturality t (𝟙 T) 1
    have h1 : APt.res (𝒪 := 𝒪) (P := L) t.op 1 = 1 := by ext p; simp
    rw [h1, Category.comp_id] at hn
    change act.smul h (F.map t.op (φ.app (𝟙 T) 1)) = F.map t.op (φ.app (𝟙 T) 1)
    rw [← hn, ← φ.equivariant, hh, one_mul]⟩
  invFun x :=
    { app := fun {T'} t a => act.smul (a.comp (AddMonoidHom.toMultiplicative r)) (F.map t.op x.1)
      naturality := fun {T' T''} s t a => by
        rw [act.map_smul, ← Functor.map_comp_apply]
        rfl
      equivariant := fun {T'} t k a => by
        let c : APt 𝒪 M (op T') := k.comp (AddMonoidHom.toMultiplicative
          (AddMonoidHom.id M - L.subtype.comp r))
        have hc : APt.toMagnet L c = 1 := by
          refine MonoidHom.ext fun l => ?_
          have : ((Multiplicative.toAdd l : L) : M) - ((r (Multiplicative.toAdd l : L) : L) : M) = 0 := by
            rw [hr]; exact sub_self _
          refine (congrArg k (Multiplicative.toAdd.injective this)).trans k.map_one
        have hk : k = c * (APt.toMagnet L k).comp (AddMonoidHom.toMultiplicative r) := by
          refine MonoidHom.ext fun m => ?_
          refine Eq.trans (congrArg k ?_) (k.map_mul _ _)
          exact Multiplicative.toAdd.injective (sub_add_cancel _ _).symm
        have hfix := x.2 t c hc
        have hd : ((APt.toMagnet L k * a).comp (AddMonoidHom.toMultiplicative r)) =
          (APt.toMagnet L k).comp (AddMonoidHom.toMultiplicative r) *
            a.comp (AddMonoidHom.toMultiplicative r) := rfl
        rw [hd, ← act.mul_smul k]
        conv_rhs => rw [hk, mul_assoc, mul_comm c, act.mul_smul, hfix] }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change act.smul (a.comp (AddMonoidHom.toMultiplicative r)) (F.map t.op (φ.app (𝟙 T) 1)) = φ.app t a
    have hn := φ.naturality t (𝟙 T) 1
    have h1 : APt.res (𝒪 := 𝒪) (P := L) t.op 1 = 1 := by ext p; simp
    rw [h1, Category.comp_id] at hn
    rw [← hn, ← φ.equivariant]
    congr 1
    refine MonoidHom.ext fun l => ?_
    exact (mul_one _).trans (congrArg a (congrArg Multiplicative.ofAdd (hr _)))
  right_inv x := by
    refine Subtype.ext ?_
    change act.smul ((1 : APt 𝒪 L (op T)).comp (AddMonoidHom.toMultiplicative r)) (F.map (𝟙 T).op x.1) = x.1
    have h1 : (1 : APt 𝒪 L (op T)).comp (AddMonoidHom.toMultiplicative r) = 1 := by ext p; simp
    rw [h1, act.one_smul]
    simp

end Fixed

/-! ### Change of the acting monoid along an isomorphism, `G_m`, and towers -/

section Transport

variable {L Z : Type u} [AddCommMonoid L] [AddCommMonoid Z] {F : Cᵒᵖ ⥤ Type u}
  (act : AAction 𝒪 L F) (e : Z ≃+ L) (Y : AddSubmonoid Z)

/-- `Y.map e → Y`. -/
def tDown : Y.map e.toAddMonoidHom →+ Y where
  toFun n := ⟨e.symm n.1, by
    obtain ⟨y, hy, h⟩ := n.2
    have h' : e y = n.1 := h
    rw [← h']; simpa using hy⟩
  map_zero' := Subtype.ext (map_zero e.symm)
  map_add' a b := Subtype.ext (map_add e.symm _ _)

/-- `Y → Y.map e`. -/
def tUp : Y →+ Y.map e.toAddMonoidHom where
  toFun n := ⟨e n.1, n.1, n.2, rfl⟩
  map_zero' := Subtype.ext (map_zero e)
  map_add' a b := Subtype.ext (map_add e _ _)

/-- The bijection of `attractorTransportIso` on points. -/
def transportEquiv (T : C) :
    AttractorPt act (Y.map e.toAddMonoidHom) T ≃ AttractorPt (act.along e.symm.toAddMonoidHom) Y T where
  toFun φ :=
    { app := fun t b => φ.app t (b.comp (AddMonoidHom.toMultiplicative (tDown e Y)))
      naturality := fun s t b => φ.naturality s t (b.comp (AddMonoidHom.toMultiplicative (tDown e Y)))
      equivariant := fun t h b => by
        refine Eq.trans (congrArg (φ.app t) ?_) (φ.equivariant t
          (h.comp (AddMonoidHom.toMultiplicative e.symm.toAddMonoidHom)) _)
        rfl }
  invFun ψ :=
    { app := fun t a => ψ.app t (a.comp (AddMonoidHom.toMultiplicative (tUp e Y)))
      naturality := fun s t a => ψ.naturality s t (a.comp (AddMonoidHom.toMultiplicative (tUp e Y)))
      equivariant := fun {T'} t h a => by
        have h2 := ψ.equivariant t (h.comp (AddMonoidHom.toMultiplicative e.toAddMonoidHom))
          (a.comp (AddMonoidHom.toMultiplicative (tUp e Y)))
        refine Eq.trans (congrArg (ψ.app t) ?_) (h2.trans ?_)
        · rfl
        · change act.smul _ _ = _
          congr 1
          refine MonoidHom.ext fun l => congrArg h ?_
          exact congrArg Multiplicative.ofAdd (e.apply_symm_apply _) }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    refine congrArg (φ.app t) (MonoidHom.ext fun n => congrArg a ?_)
    exact congrArg Multiplicative.ofAdd (Subtype.ext (e.apply_symm_apply _))
  right_inv ψ := by
    refine AttractorPt.ext ?_
    funext T' t b
    refine congrArg (ψ.app t) (MonoidHom.ext fun n => congrArg b ?_)
    exact congrArg Multiplicative.ofAdd (Subtype.ext (e.symm_apply_apply _))

/-- **§16.4.** An isomorphism `e : Z ≃ L` of monoids identifies the attractors for `𝔸(L)` and for
`𝔸(Z)`. With `Z = ℤ`, `L = ℤα` (`α` not torsion), `Y = ℕ`: the attractor for `D(ℤα)` of `[α⟩` is a
`G_m`-attractor. -/
def attractorTransportIso :
    attractor act (Y.map e.toAddMonoidHom) ≅ attractor (act.along e.symm.toAddMonoidHom) Y :=
  NatIso.ofComponents (fun U => (transportEquiv act e Y (unop U)).toIso) (fun {U V} s => by
    ext φ
    refine AttractorPt.ext ?_
    funext T' t b
    rfl)

end Transport

section Tower

/-- The magnet `ℕ ⊆ ℤ` (`ℤ` lifted to the universe of the site). -/
def natMagnet : AddSubmonoid (ULift.{u} ℤ) where
  carrier := {x | 0 ≤ x.down}
  zero_mem' := le_refl (0 : ℤ)
  add_mem' {a b} ha hb := add_nonneg (show (0 : ℤ) ≤ a.down from ha) (show (0 : ℤ) ≤ b.down from hb)

/-- `ℤ^r`. -/
def ZP : ℕ → Type u
  | 0 => PUnit
  | r + 1 => ULift.{u} ℤ × ZP r

/-- The monoid structure on `ℤ^r`. -/
@[instance_reducible] def ZP.inst : ∀ r, AddCommMonoid (ZP.{u} r)
  | 0 => inferInstanceAs (AddCommMonoid PUnit)
  | r + 1 => @Prod.instAddCommMonoid _ _ _ (ZP.inst r)

instance (r : ℕ) : AddCommMonoid (ZP.{u} r) := ZP.inst r

/-- `ℕ^r ⊆ ℤ^r`. -/
def NP : ∀ r, AddSubmonoid (ZP.{u} r)
  | 0 => ⊤
  | r + 1 => natMagnet.prod (NP r)

/-- A succession of `r` attractors under `G_m` from `X` to `Y`. -/
inductive GmTower : (Cᵒᵖ ⥤ Type u) → (Cᵒᵖ ⥤ Type u) → ℕ → Prop
  | nil (X) : GmTower X X 0
  | step {X Y r} (a : AAction 𝒪 (ULift.{u} ℤ) X) :
      GmTower (attractor a natMagnet) Y r → GmTower X Y (r + 1)

/-- `X^⊤ = X` as functors (Fact 3.6). -/
def attractorTopIso {M : Type u} [AddCommMonoid M] {F : Cᵒᵖ ⥤ Type u} (act : AAction 𝒪 M F) :
    attractor act ⊤ ≅ F :=
  NatIso.ofComponents (fun U => (attractorTopEquiv act (unop U)).toIso) (fun {U V} s => by
    ext φ
    exact AttractorPt.toPoint_baseChange s.unop φ)

/-- **§16.4 (iii).** If `M = ℤ^r` and `N = ℕ^r`, then `X ↦ X^N` is realized as `r` stages of
`G_m`-attractors, for any functor `X` with an action of `𝔸(ℤ^r)` (in particular `D(ℤ^r)`). -/
theorem exists_gmTower : ∀ (r : ℕ) (X : Cᵒᵖ ⥤ Type u) (act : AAction 𝒪 (ZP.{u} r) X),
    ∃ Y, GmTower (𝒪 := 𝒪) X Y r ∧ Nonempty (Y ≅ attractor act (NP r))
  | 0, X, act => ⟨X, .nil X, ⟨(attractorTopIso act).symm⟩⟩
  | r + 1, X, act => by
    obtain ⟨Y, hY, ⟨i⟩⟩ := exists_gmTower r _ (actSnd act natMagnet)
    exact ⟨Y, .step (actFst act) hY, ⟨i ≪≫ (stagesIso act natMagnet (NP r)).symm⟩⟩

end Tower

end AlgMag
