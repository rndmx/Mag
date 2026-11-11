/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SecLeftover1510
import AlgMag.Sec16Remaining
import AlgMag.Sec3Leftover33

/-!
# Algebraic Magnetism: Example 15.10 (ii), §16.4 (ii) in printed form, Example 3.33 at the origin

* `AlgMag.Leftover.ex1510_ii_Zn`: Example 15.10 (ii) for `G = ℤⁿ`, `S` any nonempty scheme.
* `AlgMag.Leftover.ex1510_ii_empty`: for `S = ∅` all attractors agree and `Π(a) = {0}`.
* `AlgMag.S16R.prodTopEquiv`: `X^{N₁ × M₂}_{M₁ × M₂} = X^{N₁}_{M₁}`, the second equality of §16.4 (ii).
* `AlgMag.S16R.prod_inf_prod`: `(N₁ × M₂) ∩ (M₁ × N₂) = N₁ × N₂`, the magnets of its first equality.
* `AlgMag.GB.ex333_zero_unique`: Example 3.33: `X^{(ℕ×0)∩(0×ℕ)}(T)` is the single point `0`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

namespace AlgMag.Leftover

open AlgMag.GB

variable {S : Scheme.{u}}

/-- **Example 15.10 (ii)** as printed, `S` any nonempty scheme: `D(ℤⁿ)_S` acting on itself by
multiplication has `Π(a) = {0, ℤⁿ}`. -/
theorem ex1510_ii_Zn (n : ℕ) [Nonempty S] :
    pureMagnets (attractorImage (aAction (⊤ : AddSubmonoid (ULift.{u} (Fin n → ℤ))) S)) = {⊥, ⊤} := by
  cases n with
  | succ n => exact ex1510_ii
  | zero =>
    have hs : ∀ K : AddSubmonoid (ULift.{u} (Fin 0 → ℤ)), K = ⊥ := fun K =>
      Subsingleton.elim _ _
    ext N
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact fun _ => Or.inl (hs N)
    · intro _
      rw [hs N]
      exact isPure_bot

/-- **Example 15.10 (ii)**, the empty base: all attractors agree, so `Π(a) = {0}`, which is not
`{0, G}` for `G ≠ 0`. The printed statement needs `S` nonempty. -/
theorem ex1510_ii_empty {G : Type u} [AddCommGroup G] [IsEmpty S] :
    pureMagnets (attractorImage (aAction (⊤ : AddSubmonoid G) S)) = {⊥} := by
  have hall : ∀ K L : AddSubmonoid G, attractorImage (aAction (⊤ : AddSubmonoid G) S) K =
      attractorImage (aAction (⊤ : AddSubmonoid G) S) L := by
    intro K L
    funext T
    haveI : IsEmpty T.left := ⟨fun y => isEmptyElim (T.hom y)⟩
    ext x
    exact ⟨fun _ => mem_image_of_isEmpty L x, fun _ => mem_image_of_isEmpty K x⟩
  ext N
  simp only [Set.mem_singleton_iff]
  constructor
  · exact fun hN => le_bot_iff.mp (hN ⊥ (hall N ⊥))
  · rintro rfl
    exact isPure_bot

end AlgMag.Leftover

namespace AlgMag.S16R

variable {C : Type*} [Category.{u} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M₁ M₂ : Type u} [AddCommMonoid M₁] [AddCommMonoid M₂] {F : Cᵒᵖ ⥤ Type u}
  (act : AAction 𝒪 (M₁ × M₂) F) (N₁ : AddSubmonoid M₁)

/-- The second coordinate of a point of `𝔸(N₁ × M₂)`. -/
def top₂ {U : Cᵒᵖ} (c : APt 𝒪 (N₁.prod (⊤ : AddSubmonoid M₂)) U) : APt 𝒪 M₂ U :=
  c.comp (AddMonoidHom.toMultiplicative
    { toFun := fun m => ⟨(0, m), N₁.zero_mem, trivial⟩, map_zero' := rfl
      map_add' := fun a b => Subtype.ext (Prod.ext (add_zero 0).symm rfl) })

variable {N₁} in
lemma toMagnet_top₂ {U : Cᵒᵖ} (c : APt 𝒪 (N₁.prod (⊤ : AddSubmonoid M₂)) U) :
    APt.toMagnet (⊤ : AddSubmonoid M₂) (top₂ N₁ c) * 1 = cut₂ N₁ ⊤ c :=
  MonoidHom.ext fun _ => mul_one _

/-- **§16.4 (ii)**, second equality, on points, any site and any `X`:
`X^{N₁ × M₂}_{M₁ × M₂} = X^{N₁}_{M₁}`: the point `f` over `𝔸(N₁) × 𝔸(M₂)` is determined by
`f(a, b) = (1, b) · f(a, 1)`. -/
def prodTopEquiv (T : C) :
    AttractorPt act (N₁.prod (⊤ : AddSubmonoid M₂)) T ≃ AttractorPt (actFst act) N₁ T where
  toFun φ :=
    { app := fun {T'} t a => φ.app t (glue N₁ ⊤ a 1)
      naturality := fun {T' T''} s t a => by
        rw [← φ.naturality s t, ← glue_res]
        congr 2
        exact MonoidHom.ext fun _ => (map_one (𝒪.map s.op).hom).symm
      equivariant := fun {T'} t h a => by
        rw [glue_mul]
        exact φ.equivariant t _ _ }
  invFun ψ :=
    { app := fun {T'} t c => act.smul (inrPt (top₂ N₁ c)) (ψ.app t (cut₁ N₁ ⊤ c))
      naturality := fun {T' T''} s t c => by
        rw [act.map_smul, ← ψ.naturality s t]
        rfl
      equivariant := fun {T'} t k c => by
        have hc₁ : cut₁ N₁ ⊤ (APt.toMagnet (N₁.prod ⊤) k * c) =
            APt.toMagnet N₁ (k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M₁ M₂))) *
              cut₁ N₁ ⊤ c := rfl
        rw [hc₁, ψ.equivariant]
        change act.smul _ (act.smul (inlPt (M₂ := M₂)
          (k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M₁ M₂)))) _) = _
        refine (act.mul_smul _ _ _).symm.trans (Eq.trans ?_ (act.mul_smul _ _ _))
        congr 1
        have hs := split_pt k
        have h2 : inrPt (M₁ := M₁) (top₂ N₁ (APt.toMagnet (N₁.prod ⊤) k * c)) =
            inrPt (M₁ := M₁) (k.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M₁ M₂))) *
              inrPt (M₁ := M₁) (top₂ N₁ c) := MonoidHom.ext fun _ => rfl
        rw [h2]
        conv_rhs => rw [← hs]
        ac_rfl }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t c
    change act.smul _ (φ.app t (glue N₁ ⊤ (cut₁ N₁ ⊤ c) 1)) = _
    rw [← φ.equivariant, ← glue_mul', toMagnet_top₂, glue_cut]
  right_inv ψ := by
    refine AttractorPt.ext ?_
    funext T' t a
    change act.smul (inrPt (top₂ N₁ (glue N₁ ⊤ a 1))) (ψ.app t (cut₁ N₁ ⊤ (glue N₁ ⊤ a 1))) = _
    rw [cut₁_glue]
    have h1 : inrPt (top₂ N₁ (glue N₁ ⊤ a 1)) = (1 : APt 𝒪 (M₁ × M₂) (op T')) := by
      refine MonoidHom.ext fun n => ?_
      have ha : a (Multiplicative.ofAdd (⟨0, N₁.zero_mem⟩ : N₁)) = 1 := a.map_one
      exact (congrArg (· * _) ha).trans (one_mul _)
    rw [h1, act.one_smul]

/-- `prodTopEquiv` commutes with base change. -/
lemma prodTopEquiv_baseChange {T T' : C} (s : T' ⟶ T)
    (φ : AttractorPt act (N₁.prod (⊤ : AddSubmonoid M₂)) T) :
    prodTopEquiv act N₁ T' (φ.baseChange s) = (prodTopEquiv act N₁ T φ).baseChange s :=
  rfl

variable (N₂ : AddSubmonoid M₂)

/-- The magnets of the first equality of **§16.4 (ii)**: `(N₁ × M₂) ∩ (M₁ × N₂) = N₁ × N₂`. -/
theorem prod_inf_prod : N₁.prod ⊤ ⊓ (⊤ : AddSubmonoid M₁).prod N₂ = N₁.prod N₂ := by
  ext x
  simp [AddSubmonoid.mem_prod]

end AlgMag.S16R

namespace AlgMag.GB

open Classical in
/-- The point `(0, 0)` of `𝔸²`, in coordinates. -/
noncomputable def ex333ZeroPt {S : Scheme.{u}} (T : Over S) : APt (overO S) Q2.{u} (op T) where
  toFun n := if Multiplicative.toAdd n = 0 then 1 else 0
  map_one' := if_pos rfl
  map_mul' a b := by
    by_cases ha : Multiplicative.toAdd a = 0
    · by_cases hb : Multiplicative.toAdd b = 0
      · have : Multiplicative.toAdd (a * b) = 0 := by
          rw [toAdd_mul, ha, hb, add_zero]
        simp only [ha, hb, this, if_true, mul_one]
      · have : Multiplicative.toAdd (a * b) ≠ 0 := by
          rw [toAdd_mul, ha, zero_add]; exact hb
        simp only [hb, this, if_false, mul_zero]
    · have : Multiplicative.toAdd (a * b) ≠ 0 := by
        intro h
        apply ha
        rw [toAdd_mul] at h
        have h1 : ((Multiplicative.toAdd a).1.down.1 + (Multiplicative.toAdd b).1.down.1 : ℤ) = 0 :=
          congrArg (fun z : Q2.{u} => z.1.down.1) h
        have h2 : ((Multiplicative.toAdd a).1.down.2 + (Multiplicative.toAdd b).1.down.2 : ℤ) = 0 :=
          congrArg (fun z : Q2.{u} => z.1.down.2) h
        have pa : (0 : ℤ) ≤ (Multiplicative.toAdd a).1.down.1 := (Multiplicative.toAdd a).2.1
        have pb : (0 : ℤ) ≤ (Multiplicative.toAdd b).1.down.1 := (Multiplicative.toAdd b).2.1
        have qa : (0 : ℤ) ≤ (Multiplicative.toAdd a).1.down.2 := (Multiplicative.toAdd a).2.2
        have qb : (0 : ℤ) ≤ (Multiplicative.toAdd b).1.down.2 := (Multiplicative.toAdd b).2.2
        refine Subtype.ext (ULift.ext _ _ (Prod.ext ?_ ?_))
        · change (Multiplicative.toAdd a).1.down.1 = (0 : ℤ); omega
        · change (Multiplicative.toAdd a).1.down.2 = (0 : ℤ); omega
      simp only [ha, this, if_false, zero_mul]

/-- **Example 3.33**, end: `X^{(ℕ×0)∩(0×ℕ)} = 0_{𝔸²_S}`: over any `T`, exactly one point of `𝔸²` lies
in this attractor, the origin. -/
theorem ex333_zero_unique {S : Scheme.{u}} (T : Over S) :
    ∃! t : T ⟶ A Q2.{u} S,
      ∃ φ : AttractorPt (aAction Q2.{u} S) (X2.{u} ⊓ Y2.{u}) T, φ.toPoint = t := by
  have H : ∀ t : T ⟶ A Q2.{u} S,
      (∃ φ : AttractorPt (aAction Q2.{u} S) (X2.{u} ⊓ Y2.{u}) T, φ.toPoint = t) ↔
        pts T t = ex333ZeroPt T := by
    intro t
    rw [exists_att_A_iff, X2_inf_Y2]
    constructor
    · intro h
      refine MonoidHom.ext fun n => ?_
      by_cases h0 : Multiplicative.toAdd n = 0
      · have e : n = 1 := h0
        subst e
        exact (map_one _).trans (map_one (ex333ZeroPt T)).symm
      · refine (h (Multiplicative.toAdd n) fun hm => h0 (Subtype.ext (AddSubmonoid.mem_bot.mp hm))).trans ?_
        exact (if_neg h0).symm
    · intro h n hn
      rw [h]
      exact if_neg fun h0 => hn (AddSubmonoid.mem_bot.mpr (congrArg Subtype.val h0))
  refine ⟨(pts T).symm (ex333ZeroPt T), (H _).2 ((pts T).apply_symm_apply _), fun y hy => ?_⟩
  exact (pts T).injective (((H y).1 hy).trans ((pts T).apply_symm_apply _).symm)

end AlgMag.GB

#print axioms AlgMag.Leftover.ex1510_ii_Zn
#print axioms AlgMag.Leftover.ex1510_ii_empty
#print axioms AlgMag.S16R.prodTopEquiv
#print axioms AlgMag.S16R.prod_inf_prod
#print axioms AlgMag.GB.ex333_zero_unique
