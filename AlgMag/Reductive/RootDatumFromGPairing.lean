/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootDatumFromG
import AlgMag.Reductive.GluePrereqs

/-!
# The root datum of a split reductive group, constructed from `G`

`SplitReductiveData.WithReflections π`: split reductive data, `X` finite free, and for each
root `α` a `k̄`-point `n_α ∈ N_G(T)(k̄)` acting on `X` by a reflection `σ` at `α`
(`σ α = -α`, `(1 - σ)X ⊆ ℤα`). From this:

* `exists_refl`: `s_α := σ ∈ W` (by `normalizer_cover`), `refl_eq`: it is the unique
  reflection at `α` in `W`;
* `corootHom α : X →+ ℤ`, the unique `α^∨` with `s_α x = x - ⟨x, α^∨⟩α`, `⟨α, α^∨⟩ = 2`;
* `corootHom_refl`: `(s_α β)^∨ = β^∨ ∘ s_α`;
* `rootPairing : RootPairing (roots π) ℤ X X^∨`, a root datum with `range root = Φ`
  (`range_root_rootPairing`), reflections the `s_α` (`reflection_rootPairing`), and Weyl group
  inside `W` (`exists_weyl_of_weylGroup_rootPairing`);
* `toWithRootDatum`: `WithRootDatum` from reducedness, a base and `W ⊆ W(Φ)`;
* `WithRootDatum.toWithReflections`: conversely `WithRootDatum` gives `WithReflections`;
* `WithReflections.ofNeOne`: `σ α = -α` need not be assumed, only `σ ≠ 1`.
-/

suppress_compilation

open Set Function Module TauCeti WithConv Magnetism

namespace AlgMag.Reductive

open LatticeReflection AlgMag.Weyl

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- `σ` acts on `X` by a reflection at `α`: `σ α = -α` and `(1 - σ)X ⊆ ℤα`. -/
def IsReflectionOn (σ : X ≃* X) (α : Additive X) : Prop :=
  actW σ α = -α ∧ ∀ x, x - actW σ x ∈ AddSubgroup.zmultiples α

/-- Split reductive data with a point of `N_G(T)(k̄)` acting by a reflection at
each root. -/
structure SplitReductiveData.WithReflections (π : H →ₐc[k] MonoidAlgebra k X) extends
    SplitReductiveData π where
  /-- `n_α ∈ N_G(T)(k̄)` acting on `X` by a reflection at `α`. -/
  exists_normalizing_refl : ∀ α ∈ roots π, ∃ (g : WithConv (H →ₐ[k] AlgebraicClosure k))
    (σ : X ≃* X), IsNormalizingWith π (AlgebraicClosure k) g σ ∧ IsReflectionOn σ α

omit [DecidableEq X] in
lemma ne_zero_of_mem_roots {π : H →ₐc[k] MonoidAlgebra k X} {α : Additive X}
    (hα : α ∈ roots π) : α ≠ 0 := by
  rintro rfl
  exact hα.1 rfl

namespace SplitReductiveData.WithReflections

variable {π : H →ₐc[k] MonoidAlgebra k X} (D : SplitReductiveData.WithReflections π)
variable [Module.IsTorsionFree ℤ (Additive X)]

instance finiteW : Finite D.W := D.finite

instance finiteRoots : Finite (roots π) := (finite_roots (π := π)).to_subtype

omit [Module.IsTorsionFree ℤ (Additive X)] in
lemma smul_zsmul' (w : D.W) (c : ℤ) (y : Additive X) : w • (c • y) = c • (w • y) :=
  map_zsmul (DistribSMul.toAddMonoidHom (Additive X) w) c y

omit [Module.IsTorsionFree ℤ (Additive X)] in
/-- **`s_α ∈ W`**: the reflection of `n_α` lies in the Weyl group (`normalizer_cover`). -/
theorem exists_refl {α : Additive X} (hα : α ∈ roots π) :
    ∃ w : D.W, w • α = -α ∧ IsReflAt w α := by
  obtain ⟨g, σ, hg, hσ1, hσ2⟩ := D.exists_normalizing_refl α hα
  obtain ⟨hσW, -⟩ := D.normalizer_cover g σ hg
  exact ⟨⟨σ, hσW⟩, hσ1, hσ2⟩

/-- The reflection `s_α ∈ W`. -/
noncomputable def refl (α : roots π) : D.W := (D.exists_refl α.2).choose

omit [Module.IsTorsionFree ℤ (Additive X)] in
lemma refl_smul_self (α : roots π) : D.refl α • (α : Additive X) = -α :=
  (D.exists_refl α.2).choose_spec.1

omit [Module.IsTorsionFree ℤ (Additive X)] in
lemma isReflAt_refl (α : roots π) : IsReflAt (D.refl α) (α : Additive X) :=
  (D.exists_refl α.2).choose_spec.2

/-- The coroot `α^∨ ∈ X_*(T) = Hom(X, ℤ)`. -/
noncomputable def corootHom (α : roots π) : Additive X →+ ℤ :=
  coroot (ne_zero_of_mem_roots α.2) (D.isReflAt_refl α)

/-- `s_α x = x - ⟨x, α^∨⟩ α`. -/
lemma refl_smul (α : roots π) (x : Additive X) :
    D.refl α • x = x - D.corootHom α x • (α : Additive X) :=
  smul_eq_sub_coroot _ _ x

/-- `⟨α, α^∨⟩ = 2`. -/
lemma corootHom_self (α : roots π) : D.corootHom α α = 2 :=
  coroot_self _ _ (D.refl_smul_self α)

/-- **Uniqueness of `α^∨`**: any `f` with `w x = x - f(x) α` for some `w ∈ W` and `f α = 2` is
`α^∨`. -/
theorem corootHom_unique (α : roots π) {w : D.W} {f : Additive X →+ ℤ}
    (hw : ∀ x, w • x = x - f x • (α : Additive X)) (hf : f α = 2) : D.corootHom α = f :=
  coroot_unique (ne_zero_of_mem_roots α.2) (D.refl_smul α) hw (D.corootHom_self α) hf

/-- **Uniqueness of `s_α`**: an element of `W` acting by a reflection at `α` is `s_α`. -/
theorem refl_eq (α : roots π) {w : D.W} (hw1 : w • (α : Additive X) = -α)
    (hw2 : IsReflAt w (α : Additive X)) : w = D.refl α := by
  have hα := ne_zero_of_mem_roots α.2
  exact refl_unique (fun w w' h => weyl_ext h) hα (smul_eq_sub_coroot hα hw2) (D.refl_smul α)
    (coroot_self hα hw2 hw1) (D.corootHom_self α)

lemma refl_smul_refl_smul (α : roots π) (x : Additive X) : D.refl α • D.refl α • x = x := by
  rw [D.refl_smul α (D.refl α • x), D.refl_smul α x, map_sub, map_zsmul, D.corootHom_self,
    smul_eq_mul]
  module

omit [Module.IsTorsionFree ℤ (Additive X)] in
/-- `W` preserves `Φ`. -/
lemma smul_mem_roots (w : D.W) {β : Additive X} (hβ : β ∈ roots π) : w • β ∈ roots π :=
  D.roots_stable _ w.2 β hβ

/-- `s_α β`. -/
def reflRoot (α β : roots π) : roots π := ⟨D.refl α • (β : Additive X), D.smul_mem_roots _ β.2⟩

lemma refl_conj_smul (α β : roots π) (x : Additive X) :
    (D.refl α * D.refl β * D.refl α) • x =
      x - ((D.corootHom β).comp (DistribSMul.toAddMonoidHom (Additive X) (D.refl α)) x) •
        (D.reflRoot α β : Additive X) := by
  rw [mul_smul, mul_smul, D.refl_smul β (D.refl α • x), smul_sub, D.smul_zsmul',
    D.refl_smul_refl_smul]
  rfl

/-- **`(s_α β)^∨ = β^∨ ∘ s_α`**. -/
theorem corootHom_refl (α β : roots π) :
    D.corootHom (D.reflRoot α β) =
      (D.corootHom β).comp (DistribSMul.toAddMonoidHom (Additive X) (D.refl α)) := by
  refine D.corootHom_unique _ (D.refl_conj_smul α β) ?_
  show D.corootHom β (D.refl α • D.refl α • (β : Additive X)) = 2
  rw [D.refl_smul_refl_smul, D.corootHom_self]

/-- The coroot determines the root. -/
lemma corootHom_injective : Injective D.corootHom := by
  intro α β h
  have hβ := D.refl_smul β
  rw [← h] at hβ
  refine Subtype.ext (root_eq_of_coroot_eq (D.refl_smul α) hβ (D.corootHom_self α) ?_)
  rw [h]
  exact D.corootHom_self β

/-- The coroots as linear forms `X →ₗ[ℤ] ℤ`. -/
def corootEmb : roots π ↪ Module.Dual ℤ (Additive X) :=
  ⟨fun α => (D.corootHom α).toIntLinearMap, fun _ _ h =>
    D.corootHom_injective (AddMonoidHom.ext fun x => LinearMap.congr_fun h x)⟩

lemma corootEmb_apply (α : roots π) (x : Additive X) : D.corootEmb α x = D.corootHom α x := rfl

variable [Module.Finite ℤ (Additive X)]

/-- **The root datum of `G`**, built from the reflections `s_α ∈ W`. -/
def rootPairing : RootPairing (roots π) ℤ (Additive X) (Module.Dual ℤ (Additive X)) :=
  RootPairing.mk' (Module.Dual.eval ℤ (Additive X)) (Embedding.subtype _) D.corootEmb
    (fun α => by simp [corootEmb_apply, D.corootHom_self])
    (by
      rintro α - ⟨β, rfl⟩
      refine ⟨D.reflRoot α β, ?_⟩
      show D.refl α • (β : Additive X) = _
      rw [preReflection_apply, D.refl_smul]
      rfl)
    (by
      rintro α - ⟨β, rfl⟩
      refine ⟨D.reflRoot α β, LinearMap.ext fun x => ?_⟩
      rw [preReflection_apply, corootEmb_apply, D.corootHom_refl]
      simp only [AddMonoidHom.coe_comp, comp_apply, DistribSMul.toAddMonoidHom_apply,
        D.refl_smul, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.Dual.eval_apply, Embedding.coe_subtype, corootEmb_apply, smul_eq_mul]
      ring)

/-- The roots of the root datum are the roots of `G`. -/
theorem range_root_rootPairing : range D.rootPairing.root = roots π :=
  Subtype.range_coe

/-- The coroots of the root datum are the `α^∨`. -/
theorem coroot_rootPairing (α : roots π) (x : Additive X) :
    D.rootPairing.coroot α x = D.corootHom α x := rfl

/-- The reflections of the root datum are the `s_α ∈ W`. -/
theorem reflection_rootPairing (α : roots π) (x : Additive X) :
    D.rootPairing.reflection α x = D.refl α • x := by
  rw [RootPairing.reflection_apply, D.refl_smul]
  rfl

/-- The Weyl group of the root datum acts on `X` through `W`. -/
theorem exists_weyl_of_weylGroup_rootPairing (g : D.rootPairing.weylGroup) :
    ∃ w : D.W, ∀ m : Additive X, (g : D.rootPairing.Aut) • m = w • m := by
  obtain ⟨g, hg⟩ := g
  induction hg using RootPairing.weylGroup.induction with
  | mem i =>
    exact ⟨D.refl i, fun m => by
      rw [← D.reflection_rootPairing]
      rfl⟩
  | one => exact ⟨1, fun m => by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨w, hw⟩ := ihx
    obtain ⟨w', hw'⟩ := ihy
    exact ⟨w * w', fun m => by rw [mul_smul, mul_smul, hw', hw]⟩

/-- **`WithRootDatum` from `G`**: the root datum is `rootPairing`; the remaining inputs are
reducedness, a base, and `W ⊆ W(Φ)` (the inclusion `W(Φ) ⊆ W` is
`exists_weyl_of_weylGroup_rootPairing`). -/
def toWithRootDatum [D.rootPairing.IsReduced] (b : D.rootPairing.Base)
    (hW : ∀ w : D.W, ∃ g : D.rootPairing.weylGroup,
      ∀ m : Additive X, (g : D.rootPairing.Aut) • m = w • m) :
    SplitReductiveData.WithRootDatum π where
  toSplitReductiveData := D.toSplitReductiveData
  ι := roots π
  N := Module.Dual ℤ (Additive X)
  P := D.rootPairing
  b := b
  range_root := D.range_root_rootPairing
  weyl_eq := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨w, hw⟩ := D.exists_weyl_of_weylGroup_rootPairing g
      exact ⟨w, AddMonoidHom.ext fun m => (hw m).symm⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨g, hg⟩ := hW w
      exact ⟨g, AddMonoidHom.ext fun m => hg m⟩

end SplitReductiveData.WithReflections

/-- **`WithRootDatum` implies `WithReflections`**: the reflections `s_β ∈ W` of a compatible root
datum, with their representatives `n_{s_β} ∈ N_G(T)(k)`, are the new input. -/
def SplitReductiveData.WithRootDatum.toWithReflections {π : H →ₐc[k] MonoidAlgebra k X}
    (D' : SplitReductiveData.WithRootDatum π) : SplitReductiveData.WithReflections π where
  toSplitReductiveData := D'.toSplitReductiveData
  exists_normalizing_refl α hα := by
    rw [← D'.range_root] at hα
    obtain ⟨i, rfl⟩ := hα
    refine ⟨toAlgClosure (D'.rep (D'.refl i)), D'.refl i,
      IsNormalizingWith.mapValue (π := π) (φ := Algebra.ofId k (AlgebraicClosure k))
        (D'.rep_normalizing _), ?_, ?_⟩
    · exact (D'.refl_smul i _).trans (D'.P.reflection_apply_self i)
    · exact D'.sub_refl_smul_mem i

/-- **`WithReflections` with `s_α α = -α` derived**: it suffices that `n_α` act by a nontrivial
`σ` with `(1 - σ)X ⊆ ℤα` (`smul_self_eq_neg`, `W` finite and faithful). -/
def SplitReductiveData.WithReflections.ofNeOne {π : H →ₐc[k] MonoidAlgebra k X}
    [Module.IsTorsionFree ℤ (Additive X)] (D : SplitReductiveData π)
    (h : ∀ α ∈ roots π, ∃ (g : WithConv (H →ₐ[k] AlgebraicClosure k)) (σ : X ≃* X),
      IsNormalizingWith π (AlgebraicClosure k) g σ ∧ σ ≠ 1 ∧
        ∀ x, x - actW σ x ∈ AddSubgroup.zmultiples α) :
    SplitReductiveData.WithReflections π where
  toSplitReductiveData := D
  exists_normalizing_refl α hα := by
    obtain ⟨g, σ, hg, hσ1, hσ2⟩ := h α hα
    obtain ⟨hσW, -⟩ := D.normalizer_cover g σ hg
    have : Finite D.W := D.finite
    have hne : (⟨σ, hσW⟩ : D.W) ≠ 1 := fun h1 => hσ1 (congrArg Subtype.val h1)
    exact ⟨g, σ, hg, smul_self_eq_neg (G := D.W) (w := ⟨σ, hσW⟩) (fun _ _ h => weyl_ext h)
      (ne_zero_of_mem_roots hα) hσ2 hne, hσ2⟩

end AlgMag.Reductive
