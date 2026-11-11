/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Torsor.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Smooth.Basic

/-!
# Equivariant infinitesimal deformations

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §10.

Propositions 10.1 and Corollary 10.3 are **not** formalized in the stated generality: the sheaf
`Hom(a^*Ω_{Y/Z}, C_{X/X'})` for algebraic spaces and its torsor `P` (Tags 061A, 061C) do not exist
in the Stacks library. Moreover, as printed they need `X'` affine: the proof picks a global section of
`P`, and formal smoothness only gives one over affines. Two pieces are proved:

* `exists_fixed_of_H1_eq_zero`: the group-theoretic part of the proof of Proposition 10.1, for
  abstract functors `G`, `D`, `P`.
* `exists_graded_lift`: Corollary 10.3 when all four spaces are affine. The proof is direct (no
  cohomology) and needs no finiteness.
-/

open CategoryTheory Opposite Limits

universe v u

namespace AlgMag.Deformations

/-! ### The torsor step of Proposition 10.1 -/

section Torsor

variable {C : Type*} [Category.{v} C]
variable (G D : Cᵒᵖ ⥤ Type u) [∀ U, Group (G.obj U)] [∀ U, AddCommGroup (D.obj U)]
variable (P : Cᵒᵖ ⥤ Type u) [∀ U, AddTorsor (D.obj U) (P.obj U)]

/-- The data used in the proof of Proposition 10.1: a group functor `G` acting on an abelian group
functor `D` and, compatibly, on a `D`-torsor `P`. In the paper, `D = p_* Hom(a^*Ω_{Y/Z}, C_{X/X'})`
and `P` is the sheaf of lifts. -/
structure EquivariantTorsor where
  map_mul : ∀ {U V : Cᵒᵖ} (s : U ⟶ V) (g h : G.obj U), G.map s (g * h) = G.map s g * G.map s h
  map_add : ∀ {U V : Cᵒᵖ} (s : U ⟶ V) (v w : D.obj U), D.map s (v + w) = D.map s v + D.map s w
  map_vadd : ∀ {U V : Cᵒᵖ} (s : U ⟶ V) (v : D.obj U) (a : P.obj U),
    P.map s (v +ᵥ a) = D.map s v +ᵥ P.map s a
  /-- The action on `D`. -/
  actD : ∀ {U : Cᵒᵖ}, G.obj U → D.obj U → D.obj U
  /-- The action on `P`. -/
  actP : ∀ {U : Cᵒᵖ}, G.obj U → P.obj U → P.obj U
  actD_add : ∀ {U : Cᵒᵖ} (g : G.obj U) (v w : D.obj U), actD g (v + w) = actD g v + actD g w
  actD_mul : ∀ {U : Cᵒᵖ} (g h : G.obj U) (v : D.obj U), actD (g * h) v = actD g (actD h v)
  actP_mul : ∀ {U : Cᵒᵖ} (g h : G.obj U) (a : P.obj U), actP (g * h) a = actP g (actP h a)
  actD_map : ∀ {U V : Cᵒᵖ} (s : U ⟶ V) (g : G.obj U) (v : D.obj U),
    D.map s (actD g v) = actD (G.map s g) (D.map s v)
  actP_map : ∀ {U V : Cᵒᵖ} (s : U ⟶ V) (g : G.obj U) (a : P.obj U),
    P.map s (actP g a) = actP (G.map s g) (P.map s a)
  /-- `g • a + g • v = g • (a + v)` (Tag 0618 in the paper). -/
  act_vadd : ∀ {U : Cᵒᵖ} (g : G.obj U) (v : D.obj U) (a : P.obj U),
    actP g (v +ᵥ a) = actD g v +ᵥ actP g a

variable {G D P}

/-- `H¹(G, D) = 0` in the functorial sense of Definition 9.4: every natural 1-cocycle
`G(T) → D(T)` is the coboundary of a section `v` of `D` over the final object `S`.

This is **not** linked to the formula complex of `AlgMag.Hochschild`. -/
def H1Vanishes (E : EquivariantTorsor G D P) {S : C} (hS : IsTerminal S) : Prop :=
  ∀ c : ∀ U : Cᵒᵖ, G.obj U → D.obj U,
    (∀ {U V : Cᵒᵖ} (s : U ⟶ V) (g : G.obj U), D.map s (c U g) = c V (G.map s g)) →
    (∀ (U : Cᵒᵖ) (g h : G.obj U), c U (g * h) = c U g + E.actD g (c U h)) →
    ∃ v : D.obj (op S), ∀ (T : C) (g : G.obj (op T)),
      c (op T) g = E.actD g (D.map (hS.from T).op v) - D.map (hS.from T).op v

/-- **Proposition 10.1, final step of the proof**, for abstract functors. If `H¹(G, D) = 0` and `P`
has a section over `S`, then `P` has a `G`-fixed section over `S`: the element `a - v` of the
paper. -/
theorem exists_fixed_of_H1_eq_zero (E : EquivariantTorsor G D P) {S : C} (hS : IsTerminal S)
    (h : H1Vanishes E hS) (a : P.obj (op S)) :
    ∃ b : P.obj (op S), ∀ (T : C) (g : G.obj (op T)),
      E.actP g (P.map (hS.from T).op b) = P.map (hS.from T).op b := by
  let aU : ∀ U : Cᵒᵖ, P.obj U := fun U => P.map (hS.from (unop U)).op a
  have haU : ∀ {U V : Cᵒᵖ} (s : U ⟶ V), P.map s (aU U) = aU V := by
    intro U V s
    change P.map s (P.map _ a) = P.map _ a
    rw [← Functor.map_comp_apply]
    have : (hS.from (unop U)).op ≫ s = (hS.from (unop V)).op :=
      Quiver.Hom.unop_inj (hS.hom_ext _ _)
    rw [this]
  have hmapsub : ∀ {U V : Cᵒᵖ} (s : U ⟶ V) (x y : P.obj U),
      D.map s (x -ᵥ y) = P.map s x -ᵥ P.map s y := by
    intro U V s x y
    rw [eq_comm, ← eq_vadd_iff_vsub_eq, ← E.map_vadd, vsub_vadd]
  have hactsub : ∀ {U : Cᵒᵖ} (g : G.obj U) (x y : P.obj U),
      E.actD g (x -ᵥ y) = E.actP g x -ᵥ E.actP g y := by
    intro U g x y
    rw [eq_comm, ← eq_vadd_iff_vsub_eq, ← E.act_vadd, vsub_vadd]
  obtain ⟨v, hv⟩ := h (fun U g => E.actP g (aU U) -ᵥ aU U)
    (fun {U V} s g => by
      rw [hmapsub, E.actP_map, haU])
    (fun U g k => by
      rw [hactsub, E.actP_mul, add_comm, vsub_add_vsub_cancel])
  refine ⟨(-v) +ᵥ a, fun T g => ?_⟩
  set w := D.map (hS.from T).op v with hw
  have hneg : ∀ {U V : Cᵒᵖ} (s : U ⟶ V) (x : D.obj U), D.map s (-x) = -D.map s x := by
    intro U V s x
    have h0 := E.map_add s x (-x)
    have h1 : D.map s 0 = 0 := by
      have := E.map_add s (0 : D.obj U) 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    rw [add_neg_cancel, h1] at h0
    exact (neg_eq_of_add_eq_zero_right h0.symm).symm
  have hnegD : E.actD g (-w) = -E.actD g w := by
    have h0 := E.actD_add g w (-w)
    have h1 : E.actD g 0 = 0 := by
      have := E.actD_add g (0 : D.obj (op T)) 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    rw [add_neg_cancel, h1] at h0
    exact (neg_eq_of_add_eq_zero_right h0.symm).symm
  have hc : E.actP g (aU (op T)) = (E.actD g w - w) +ᵥ aU (op T) := by
    rw [← hv T g, vsub_vadd]
  change E.actP g (P.map (hS.from T).op ((-v) +ᵥ a)) = P.map (hS.from T).op ((-v) +ᵥ a)
  rw [E.map_vadd, hneg, ← hw, E.act_vadd, hnegD]
  change _ +ᵥ E.actP g (aU (op T)) = (-w) +ᵥ aU (op T)
  rw [hc, vadd_vadd]
  congr 1
  abel

end Torsor

/-! ### The graded lifting theorem: Corollary 10.3, affine case -/

section Graded

variable {M : Type*} [AddCancelCommMonoid M] [DecidableEq M]
variable {A E : Type*} [CommRing A] [CommRing E]
variable {σA σE : Type*} [SetLike σA A] [AddSubgroupClass σA A] [SetLike σE E]
  [AddSubgroupClass σE E]
variable (𝒜 : M → σA) [GradedRing 𝒜] (ℰ : M → σE) [GradedRing ℰ]

/-- `γ = ∑ₘ prₘ ∘ g ∘ prₘ`, the degree-preserving part of an additive map. -/
noncomputable def degreePart (g : A →+ E) : A →+ E :=
  (DirectSum.toAddMonoid fun m =>
    (GradedRing.proj ℰ m).comp (g.comp (AddSubgroupClass.subtype (𝒜 m)))).comp
    (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

lemma degreePart_of_mem (g : A →+ E) {m : M} {a : A} (ha : a ∈ 𝒜 m) :
    degreePart 𝒜 ℰ g a = GradedRing.proj ℰ m (g a) := by
  simp only [degreePart, AddMonoidHom.comp_apply]
  change DirectSum.toAddMonoid _ (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
  rfl

variable {𝒜 ℰ}

/-- **Corollary 10.3 when `X, X', Y, Z` are affine** (ring form). `Y = Spec A → Z = Spec B` is
formally smooth; `X' = Spec E`, `X = Spec E'`, with `π : E → E'` surjective with square zero kernel
(the first order thickening); `α : A → E'` and `β : B → E` are compatible and equivariant.
Then there is an equivariant lift `γ : A → E`, obtained as the degree-preserving part of any lift.

Equivariance is expressed by the gradings (Proposition 2.22): `β` by `hB`, `γ` by the last
conjunct, and `α` by the existence of homogeneous lifts `hα`, which together with `hK`
is what `π` graded and surjective in each degree gives (`E'` need not carry a grading here).
`M` is only assumed cancellative: no finite generation, no finiteness on `A`. -/
theorem exists_graded_lift {B : Type*} [CommRing B] [Algebra B A] [Algebra.FormallySmooth B A]
    {E' : Type*} [CommRing E'] (π : E →+* E') (hπ : Function.Surjective π)
    (hsq : ∀ x y, π x = 0 → π y = 0 → x * y = 0)
    (hK : ∀ k x, π x = 0 → π (GradedRing.proj ℰ k x) = 0)
    (α : A →+* E') (β : B →+* E) (hc : ∀ b, π (β b) = α (algebraMap B A b))
    (hα : ∀ (m : M) (a : A), a ∈ 𝒜 m → ∃ e ∈ ℰ m, π e = α a)
    (hB : ∀ b : B, b ∈ AddSubmonoid.closure
      {b : B | ∃ m : M, algebraMap B A b ∈ 𝒜 m ∧ β b ∈ ℰ m}) :
    ∃ γ : A →+* E, (∀ a, π (γ a) = α a) ∧ (∀ b, γ (algebraMap B A b) = β b) ∧
      ∀ (m : M) (a : A), a ∈ 𝒜 m → γ a ∈ ℰ m := by
  classical
  -- a non-equivariant lift, from formal smoothness
  let _ : Algebra B E := β.toAlgebra
  have hβ : ∀ b, algebraMap B E b = β b := fun _ => rfl
  let K : Ideal E := RingHom.ker π
  have hK2 : K ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    exact (Ideal.mem_bot).2 (hsq x y hx hy)
  let e' : (E ⧸ K) ≃+* E' := RingHom.quotientKerEquivOfSurjective hπ
  have he' : ∀ x, e' (Ideal.Quotient.mk K x) = π x := fun x => rfl
  let α' : A →ₐ[B] E ⧸ K :=
    { toRingHom := (e'.symm : E' →+* E ⧸ K).comp α
      commutes' := fun b => by
        change e'.symm (α (algebraMap B A b)) = Ideal.Quotient.mk K (β b)
        rw [← hc, ← he', RingEquiv.symm_apply_apply] }
  let g : A →ₐ[B] E := Algebra.FormallySmooth.lift K ⟨2, hK2⟩ α'
  have hg : ∀ a, π (g a) = α a := fun a => by
    have := congrArg (fun h : A →ₐ[B] E ⧸ K => e' (h a))
      (Algebra.FormallySmooth.comp_lift K ⟨2, hK2⟩ α')
    change e' (Ideal.Quotient.mk K (g a)) = e' (e'.symm (α a)) at this
    rwa [he', RingEquiv.apply_symm_apply] at this
  have hgb : ∀ b, g (algebraMap B A b) = β b := fun b => g.commutes b
  let d : A →+ E := degreePart 𝒜 ℰ (g : A →+* E).toAddMonoidHom
  have hd : ∀ {m : M} {a : A}, a ∈ 𝒜 m → d a = GradedRing.proj ℰ m (g a) :=
    fun ha => degreePart_of_mem 𝒜 ℰ _ ha
  have hprojmem : ∀ (m : M) (x : E), GradedRing.proj ℰ m x ∈ ℰ m := fun m x => by
    rw [GradedRing.proj_apply]; exact SetLike.coe_mem _
  have hprojself : ∀ {m : M} {x : E}, x ∈ ℰ m → GradedRing.proj ℰ m x = x := fun hx => by
    rw [GradedRing.proj_apply]; exact DirectSum.decompose_of_mem_same ℰ hx
  -- writing `g a` as a homogeneous element plus an element of the kernel
  have hsplit : ∀ {m : M} {a : A}, a ∈ 𝒜 m →
      ∃ e ∈ ℰ m, ∃ j, π j = 0 ∧ g a = e + j ∧ d a = e + GradedRing.proj ℰ m j := by
    intro m a ha
    obtain ⟨e, he, hea⟩ := hα m a ha
    refine ⟨e, he, g a - e, ?_, by abel, ?_⟩
    · rw [map_sub, hg, hea, sub_self]
    · rw [hd ha, map_sub, hprojself he]; abel
  have hdmul : ∀ {m m' : M} {a a' : A}, a ∈ 𝒜 m → a' ∈ 𝒜 m' → d (a * a') = d a * d a' := by
    intro m m' a a' ha ha'
    obtain ⟨e, he, j, hj, hga, hda⟩ := hsplit ha
    obtain ⟨e', he', j', hj', hga', hda'⟩ := hsplit ha'
    have hmul : a * a' ∈ 𝒜 (m + m') := SetLike.GradedMul.mul_mem ha ha'
    have hL : ∀ {x y : E} {k k' : M}, x ∈ ℰ k →
        GradedRing.proj ℰ (k + k') (x * y) = x * GradedRing.proj ℰ k' y := by
      intro x y k k' hx
      simp only [GradedRing.proj_apply]
      exact DirectSum.coe_decompose_mul_add_of_left_mem ℰ hx
    have hR : ∀ {x y : E} {k k' : M}, y ∈ ℰ k' →
        GradedRing.proj ℰ (k + k') (x * y) = GradedRing.proj ℰ k x * y := by
      intro x y k k' hy
      simp only [GradedRing.proj_apply]
      exact DirectSum.coe_decompose_mul_add_of_right_mem ℰ hy
    have h00 : j * j' = 0 := hsq _ _ hj hj'
    have h01 : GradedRing.proj ℰ m j * GradedRing.proj ℰ m' j' = 0 :=
      hsq _ _ (hK _ _ hj) (hK _ _ hj')
    rw [hd hmul, map_mul, hga, hga', hda, hda']
    have : (e + j) * (e' + j') = e * e' + e * j' + j * e' + j * j' := by ring
    rw [this, h00, add_zero, map_add, map_add, hprojself (SetLike.GradedMul.mul_mem he he'),
      hL he, hR he']
    linear_combination -h01
  have hmulall : ∀ a a' : A, d (a * a') = d a * d a' := by
    intro a a'
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | homogeneous x =>
      induction a' using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => simp
      | homogeneous y => exact hdmul x.2 y.2
      | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]
    | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_mul]
  have hone : d 1 = 1 := by
    rw [hd (SetLike.GradedOne.one_mem : (1 : A) ∈ 𝒜 0), map_one, hprojself SetLike.GradedOne.one_mem]
  have hπd : ∀ a, π (d a) = α a := by
    intro a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous i x =>
      obtain ⟨e, he, j, hj, hgx, hda⟩ := hsplit x.2
      rw [hda, map_add, hK _ _ hj, add_zero]
      have := hg x
      rw [hgx, map_add, hj, add_zero] at this
      exact this
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  refine ⟨{ toFun := d, map_one' := hone, map_mul' := hmulall, map_zero' := map_zero d,
            map_add' := map_add d }, hπd, ?_, fun m a ha => ?_⟩
  · intro b
    change d (algebraMap B A b) = β b
    induction hB b using AddSubmonoid.closure_induction with
    | mem b hb =>
      obtain ⟨m, h1, h2⟩ := hb
      rw [hd h1, hgb, hprojself h2]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add]
  · change d a ∈ ℰ m
    rw [hd ha]
    exact hprojmem m _

end Graded

end AlgMag.Deformations
