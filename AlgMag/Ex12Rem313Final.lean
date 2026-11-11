/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover12
import AlgMag.Sec3Leftover313

/-!
# Algebraic Magnetism, Example 1.2: `V^N = ⨁_{n ∈ N} V_n ⊂ V` for arbitrary weight spaces

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Example 1.2 (p. 130).

`E` is any `M`-graded `𝒪_S`-module `E = ⨁_m E_m` (in particular `E = 𝒪_S^n` with a linear action of
`𝔸(M)_S` whose weight spaces `E_m` are only direct summands, not free), `V = V(E)`. The printed statement
is that `V^N` is the sub-object `⨁_{n ∈ N} V_n` of `V`. Here: the morphism `V^N → V` (evaluation at the unit)
is injective on `T`-points, natural in `T`, and its image is exactly the set of `ξ : E → p_* 𝒪_T` killing
every `E_m` with `m ∉ N`, i.e. `V(E_N) ⊂ V(E)` via the projection `E → E_N`.

Remark 3.13: the printed sanitary check holds "under some working assumptions", which the text does not
fix. Its precise instance is `AlgMag.GB.rem313` (X affine over S, via Proposition 3.31 (i)); beyond the
affine case Proposition 3.31 for the monoid map `N → M` (`N` not a group) is not available, so no further
statement is added here.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

noncomputable section

namespace AlgMag.VB

open AlgMag.GB

open scoped Classical

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M] (G : GrMod S M) (N : AddSubmonoid M)

/-- The projection `E → E_N`, killing the `E_m` with `m ∉ N`. -/
def GrMod.projN : G.E ⟶ G.EN N :=
  G.desc fun m => if h : m ∈ N then G.ιN N ⟨m, h⟩ else 0

/-- A morphism out of `E_N` from its components. -/
def GrMod.descN {Q : S.Modules} (c : ∀ n : N, G.P n ⟶ Q) : G.EN N ⟶ Q := Sigma.desc c

lemma GrMod.ιN_descN {Q : S.Modules} (c : ∀ n : N, G.P n ⟶ Q) (n : N) :
    G.ιN N n ≫ G.descN N c = c n := Sigma.ι_desc _ _

@[reassoc]
lemma GrMod.ι_projN_of_mem {m : M} (h : m ∈ N) : G.ι m ≫ G.projN N = G.ιN N ⟨m, h⟩ := by
  rw [GrMod.projN, G.ι_desc]; exact dif_pos h

@[reassoc]
lemma GrMod.ι_projN_of_not_mem {m : M} (h : m ∉ N) : G.ι m ≫ G.projN N = 0 := by
  rw [GrMod.projN, G.ι_desc]; exact dif_neg h

variable {G N}

/-- The underlying point of a point of `V(E)^N` is `E → E_N → p_* 𝒪_T`. -/
theorem toPoint_eq_projN {T : Over S} (φ : AttractorPt (vAction G) N T) :
    φ.toPoint = G.projN N ≫ ptTo φ := by
  refine G.hom_ext fun m => ?_
  have h := app_eq φ (𝟙 T) 1 m
  change G.ι m ≫ ah φ (𝟙 T) 1 = _
  rw [h]
  unfold ptComp
  by_cases hm : m ∈ N
  · rw [dif_pos hm, G.ι_projN_of_mem_assoc N hm, resO_id, Category.id_comp]
    have : mulO T ((1 : APt (overO S) N (op T)) (Multiplicative.ofAdd ⟨m, hm⟩)) = 𝟙 _ := mulO_one T
    rw [this, Category.comp_id]
  · rw [dif_neg hm, G.ι_projN_of_not_mem_assoc N hm, zero_comp]

variable (G N)

/-- `V(E_N) = {ξ : E → p_* 𝒪_T | ξ kills E_m for m ∉ N}`, by precomposition with `E → E_N`. -/
def homENSubEquiv (T : Over S) :
    (G.EN N ⟶ pO T) ≃ {ξ : G.E ⟶ pO T // ∀ m, m ∉ N → G.ι m ≫ ξ = 0} where
  toFun l := ⟨G.projN N ≫ l, fun m hm => by rw [G.ι_projN_of_not_mem_assoc N hm, zero_comp]⟩
  invFun ξ := G.descN N fun n : N => G.ι n ≫ ξ.1
  left_inv l := by
    refine G.EN_ext N fun n => ?_
    rw [G.ιN_descN, G.ι_projN_of_mem_assoc N n.2]
  right_inv ξ := by
    apply Subtype.ext
    refine G.hom_ext fun m => ?_
    change G.ι m ≫ G.projN N ≫ G.descN N _ = _
    by_cases hm : m ∈ N
    · rw [G.ι_projN_of_mem_assoc N hm, G.ιN_descN]
    · rw [G.ι_projN_of_not_mem_assoc N hm, zero_comp]
      exact (ξ.2 m hm).symm

/-- **Example 1.2**, any graded `E` (weight spaces arbitrary direct summands), `S` any scheme, `T` any
`S`-scheme: `V(E)^N(T) ≃ {ξ ∈ V(E)(T) | ξ|_{E_m} = 0 for m ∉ N}`, i.e. `V^N = ⨁_{n ∈ N} V_n ⊂ V`. -/
def ex12_sub (T : Over S) :
    AttractorPt (vAction G) N T ≃ {ξ : G.E ⟶ pO T // ∀ m, m ∉ N → G.ι m ≫ ξ = 0} :=
  (vAttractorEquiv G N T).trans (homENSubEquiv G N T)

/-- The identification of Example 1.2 is the morphism `V^N → V` (evaluation at the unit): `V^N` is
the sub-functor `⨁_{n ∈ N} V_n` of `V`. -/
theorem ex12_sub_val {T : Over S} (φ : AttractorPt (vAction G) N T) :
    (ex12_sub G N T φ).1 = φ.toPoint :=
  (toPoint_eq_projN φ).symm

/-- `V^N → V` is a monomorphism of functors. -/
theorem ex12_toPoint_injective (T : Over S) :
    Function.Injective (AttractorPt.toPoint : AttractorPt (vAction G) N T → (G.E ⟶ pO T)) := by
  intro φ ψ h
  apply (ex12_sub G N T).injective
  apply Subtype.ext
  rw [ex12_sub_val, ex12_sub_val, h]

/-- A point `ξ` of `V` lies in `V^N` iff it kills every `E_m` with `m ∉ N`. -/
theorem ex12_mem_iff {T : Over S} (ξ : G.E ⟶ pO T) :
    (∃ φ : AttractorPt (vAction G) N T, φ.toPoint = ξ) ↔ ∀ m, m ∉ N → G.ι m ≫ ξ = 0 := by
  constructor
  · rintro ⟨φ, rfl⟩
    rw [← ex12_sub_val]
    exact (ex12_sub G N T φ).2
  · intro h
    refine ⟨(ex12_sub G N T).symm ⟨ξ, h⟩, ?_⟩
    rw [← ex12_sub_val, Equiv.apply_symm_apply]

/-- Naturality in `T` of Example 1.2. -/
theorem ex12_sub_baseChange {T T' : Over S} (s : T' ⟶ T) (φ : AttractorPt (vAction G) N T) :
    (ex12_sub G N T' (φ.baseChange s)).1 = (ex12_sub G N T φ).1 ≫ resO s := by
  change G.projN N ≫ vAttractorEquiv G N T' (φ.baseChange s) =
    (G.projN N ≫ vAttractorEquiv G N T φ) ≫ resO s
  rw [vAttractorEquiv_baseChange, Category.assoc]

end AlgMag.VB

#print axioms AlgMag.VB.ex12_sub
#print axioms AlgMag.VB.ex12_sub_val
#print axioms AlgMag.VB.ex12_mem_iff
#print axioms AlgMag.VB.ex12_toPoint_injective
#print axioms AlgMag.VB.ex12_sub_baseChange
