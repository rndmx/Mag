/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.CategoryTheory.Sites.Over
import AlgMag.Foundations
import AlgMag.GeneralBase
import AlgMag.GeneralBaseSheaf
import AlgMag.Sec9Hochschild

/-!
# Hochschild cohomology of monoid functors, over a general base

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §9.

The first part (Definitions 9.2, 9.4, 9.5, 9.7, Remarks 9.6, 9.8, Propositions 9.9, 9.10) holds on any
category `C` with a presheaf of rings `𝒪`, hence for the objects over any base, algebraic spaces
included. The second part (Propositions 9.1, 9.11, 9.12, 9.13, Remark 9.14) is for `C = Sch/B` with
`B` a scheme, a quasi-coherent module `F`, and `M` any commutative monoid.

## Main definitions

* `AlgMag.S9.PMod`, `AlgMag.S9.HModule`: Definition 9.2.
* `AlgMag.S9.Cochain`, `AlgMag.S9.delta`: Definitions 9.4, 9.5.
* `AlgMag.S9.Zn`, `AlgMag.S9.Bn`, `AlgMag.S9.Hn`: Definition 9.7.
* `AlgMag.S9.IsQCoh`: quasi-coherent modules on the big site of a scheme.
* `AlgMag.S9.Sec`: the sections of the sheaf `⨁ F_m`.

## Main results

* `AlgMag.S9.delta_delta`: Remark 9.6.
* `AlgMag.S9.mem_Z1_iff`, `AlgMag.S9.mem_B1_iff`: Remark 9.8.
* `AlgMag.S9.homAtEquivHomPush`, `AlgMag.S9.homAtEquivHomPush_pull`: Proposition 9.9.
* `AlgMag.S9.hModuleEquivCoaction`, `AlgMag.S9.hModuleEquivCoactionA`, `AlgMag.S9.coactionOf`:
  Proposition 9.10.
* `AlgMag.S9.hModuleEquivDecomp`: Proposition 9.11, corrected wording.
* `AlgMag.S9.cochainEquivSec`, `AlgMag.S9.cochainLinearEquiv`, `AlgMag.S9.delta_phiC`:
  Proposition 9.12.
* `AlgMag.S9.H1_subsingleton`: Proposition 9.13.
* `AlgMag.S9.Hn_subsingleton`: Remark 9.14, the conjecture of the paper, for all `n ≥ 1`.
-/

universe v u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option linter.deprecated false

section BarAndSite

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped BigOperators

namespace AlgMag.S9

/-! ### The bar differential, for a monoid acting on an abelian group -/

section Bar

variable {G E : Type*} [Monoid G] [AddCommGroup E] [DistribMulAction G E]

/-- `(w₀,…,wₙ) ↦ (w₀,…,wᵢwᵢ₊₁,…,wₙ)`. -/
def merge {n : ℕ} (i : Fin n) (w : Fin (n + 1) → G) : Fin n → G := fun l =>
  if (l : ℕ) < i then w l.castSucc
  else if (l : ℕ) = i then w l.castSucc * w l.succ else w l.succ

/-- The bar differential of Definition 9.4, on one set of points. -/
def dl {n : ℕ} (f : (Fin n → G) → E) : (Fin (n + 1) → G) → E := fun g =>
  g 0 • f (fun i => g i.succ) +
    ∑ i : Fin n, ((-1 : ℤ) ^ ((i : ℕ) + 1)) • f (merge i g) +
    ((-1 : ℤ) ^ (n + 1)) • f (fun i => g i.castSucc)

/-- The word `(w₁,…,wₙ)` inside `(w₀,…,wₙ₊₁)`. -/
abbrev mid {n : ℕ} (w : Fin (n + 2) → G) : Fin n → G := fun i => w i.castSucc.succ

/-- `f ↦ w₀ • f(w₁,…,wₙ)`, ignoring the last letter: on such functions `δ` is the alternating sum
of the mergings of adjacent letters. -/
def phi {n : ℕ} (f : (Fin n → G) → E) : (Fin (n + 2) → G) → E := fun w => w 0 • f (mid w)

/-- The alternating sum of the mergings of adjacent letters. -/
def mu {k : ℕ} (W : (Fin (k + 1) → G) → E) : (Fin (k + 2) → G) → E := fun w =>
  ∑ a : Fin (k + 1), ((-1 : ℤ) ^ (a : ℕ)) • W (merge a w)

private lemma alt_sq' {H : Type*} [AddCommGroup H] (n : ℕ) (t : Fin (n + 1) → Fin (n + 2) → H)
    (h : ∀ (i : Fin (n + 1)) (j : Fin (n + 1)), j ≤ i → t i j.castSucc = t j i.succ) :
    ∑ i : Fin (n + 1), ∑ j : Fin (n + 2), (((-1 : ℤ) ^ (i : ℕ)) * (-1) ^ (j : ℕ)) • t i j = 0 := by
  simp only [← Finset.sum_product']
  let S : Finset (Fin (n + 1) × Fin (n + 2)) := {ij | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : Fin (n + 1) × Fin (n + 2), ij ∈ S → Fin (n + 1) × Fin (n + 2) := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    refine ⟨by simpa [φ] using congr_arg Prod.snd h, ?_⟩
    have := congr_arg (fun p => (p.1 : ℕ)) h
    ext
    simpa [φ] using this
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp at hij'
    · simp only [S, Finset.mem_filter_univ, Fin.val_castSucc, Fin.val_pred]
      omega
    · simp [φ]
  · rintro ⟨i, j⟩ hij
    have hij' : (j : ℕ) ≤ i := (Finset.mem_filter.mp hij).2
    have hlt : (j : ℕ) < n + 1 := by have := i.2; omega
    have hj : j = (⟨j, hlt⟩ : Fin (n + 1)).castSucc := rfl
    dsimp only [φ]
    have ht : t i j = t (Fin.castLT j hlt) i.succ := by
      conv_lhs => rw [hj]
      exact h i _ hij'
    rw [ht, ← neg_smul]
    congr 1
    simp only [Fin.val_castLT, Fin.val_succ, pow_succ]
    ring

private lemma contract_contract {k : ℕ} (a b : Fin (k + 1)) (h : a ≤ b) (w : Fin (k + 3) → G) :
    merge b (merge a.castSucc w) =
      merge a (merge b.succ w) := by
  have h' : (a : ℕ) ≤ b := h
  funext l
  simp only [merge, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first
    | omega
    | rfl
    | exact mul_assoc _ _ _

private lemma mu_mu {k : ℕ} (W : (Fin (k + 1) → G) → E) (w : Fin (k + 3) → G) :
    mu (mu W) w = 0 := by
  have e : mu (mu W) w = ∑ b : Fin (k + 1), ∑ a : Fin (k + 2),
      (((-1 : ℤ) ^ (b : ℕ)) * (-1) ^ (a : ℕ)) •
        W (merge b (merge a w)) := by
    simp only [mu, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  rw [e]
  apply alt_sq'
  intro b a h
  rw [contract_contract a b h]

private lemma merge_zero_zero {n : ℕ} (w : Fin (n + 2) → G) :
    merge (0 : Fin (n + 1)) w 0 = w 0 * w 1 := by
  simp [merge]

private lemma merge_succ_zero {n : ℕ} (a : Fin n) (w : Fin (n + 2) → G) :
    merge a.succ w 0 = w 0 := by
  simp [merge]

private lemma mid_merge_zero {n : ℕ} (w : Fin (n + 3) → G) :
    mid (merge (0 : Fin (n + 2)) w) = fun i => mid w i.succ := by
  funext i
  simp only [mid, merge, Fin.val_castSucc, Fin.val_succ, Fin.val_zero]
  split_ifs <;> first | omega | rfl | contradiction

private lemma mid_merge_mid {n : ℕ} (i : Fin n) (w : Fin (n + 3) → G) :
    mid (merge i.castSucc.succ w) = merge i (mid w) := by
  funext l
  simp only [mid, merge, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | omega | rfl | contradiction

private lemma mid_merge_last {n : ℕ} (w : Fin (n + 3) → G) :
    mid (merge (Fin.last n).succ w) = fun i => mid w i.castSucc := by
  funext l
  have := l.2
  simp only [mid, merge, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
  split_ifs <;> first | omega | rfl | contradiction

private lemma phi_dl {n : ℕ} (f : (Fin n → G) → E) (w : Fin (n + 3) → G) :
    phi (dl f) w = mu (phi f) w := by
  simp only [phi, dl, mu]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [merge_zero_zero, merge_succ_zero, mid_merge_zero, mid_merge_mid, mid_merge_last,
    Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    smul_add, Finset.smul_sum, mul_smul]
  simp only [smul_comm (w 0) ((-1 : ℤ) ^ _)]
  rw [add_assoc]
  rfl

/-- **Remark 9.6**, on one set of points: `δ ∘ δ = 0`. -/
theorem dl_dl {n : ℕ} (f : (Fin n → G) → E) : dl (dl f) = 0 := by
  have key : phi (dl (dl f)) = 0 := by
    funext w
    have : phi (dl f) = mu (phi f) := funext (phi_dl f)
    rw [phi_dl, this]
    exact mu_mu _ w
  funext m
  have h := congrFun key (Fin.cons 1 (Fin.snoc m 1))
  have h0 : mid (Fin.cons 1 (Fin.snoc m 1) : Fin (n + 1 + 1 + 2) → G) = m := by
    funext i
    simp [mid]
  simpa [phi, h0] using h

end Bar

/-! ### Modules with an action of a monoid functor -/

section Site

variable {C : Type*} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})

/-- An `𝒪`-module on `C` (presheaf; the sheaf condition is imposed separately, see
`AlgMag.S9.IsQCoh`): the module `F(T)` over `𝒪(T)` for every `T`, with semilinear restrictions. -/
structure PMod where
  /-- the values -/
  obj : Cᵒᵖ → Type u
  [grp : ∀ U, AddCommGroup (obj U)]
  [mod : ∀ U, Module (𝒪.obj U) (obj U)]
  /-- restriction -/
  map : ∀ {U V : Cᵒᵖ}, (U ⟶ V) → obj U →+ obj V
  map_smul : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (r : 𝒪.obj U) (x : obj U),
    map f (r • x) = (𝒪.map f).hom r • map f x
  map_id : ∀ (U : Cᵒᵖ) (x : obj U), map (𝟙 U) x = x
  map_comp : ∀ {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (x : obj U),
    map (f ≫ g) x = map g (map f x)

attribute [instance] PMod.grp PMod.mod

variable {𝒪}

/-- The underlying presheaf of sets of an `𝒪`-module. -/
def PMod.toPresheaf (F : PMod 𝒪) : Cᵒᵖ ⥤ Type u where
  obj := F.obj
  map f := ↾ F.map f
  map_id U := by ext x; exact F.map_id U x
  map_comp f g := by ext x; exact F.map_comp f g x

/-- **Definition 9.2.** An `H`-`𝒪`-module structure on `F`: `H(T)` acts `𝒪(T)`-linearly on `F(T)`,
compatibly with restriction. -/
structure HModule (H : Cᵒᵖ ⥤ MonCat.{u}) (F : PMod 𝒪) where
  /-- the action -/
  smul : ∀ {U : Cᵒᵖ}, H.obj U → F.obj U → F.obj U
  one_smul : ∀ {U : Cᵒᵖ} (x : F.obj U), smul 1 x = x
  mul_smul : ∀ {U : Cᵒᵖ} (g h : H.obj U) (x : F.obj U), smul (g * h) x = smul g (smul h x)
  smul_add : ∀ {U : Cᵒᵖ} (g : H.obj U) (x y : F.obj U), smul g (x + y) = smul g x + smul g y
  smul_smul : ∀ {U : Cᵒᵖ} (g : H.obj U) (a : 𝒪.obj U) (x : F.obj U),
    smul g (a • x) = a • smul g x
  map_smul : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (g : H.obj U) (x : F.obj U),
    F.map f (smul g x) = smul ((H.map f).hom g) (F.map f x)

variable {H : Cᵒᵖ ⥤ MonCat.{u}} {F : PMod 𝒪}

lemma HModule.smul_zero (A : HModule H F) {U : Cᵒᵖ} (g : H.obj U) : A.smul g (0 : F.obj U) = 0 := by
  have := A.smul_add g 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

/-- The action of `H(U)` on `F(U)`, as a `DistribMulAction`. -/
@[reducible] def HModule.dma (A : HModule H F) (U : Cᵒᵖ) : DistribMulAction (H.obj U) (F.obj U) where
  smul := A.smul
  one_smul := A.one_smul
  mul_smul := A.mul_smul
  smul_zero := A.smul_zero
  smul_add := A.smul_add

variable (H F)

/-- **Definition 9.4** (`V = B`) and **Definition 9.5** (any `V`): the `n`-cochains
`Cⁿ(H|_V, F|_V)`, natural transformations `Hⁿ → F` on the objects over `V`. -/
@[ext]
structure Cochain (V : C) (n : ℕ) where
  /-- the value at a point of `Hⁿ` over `t : T ⟶ V` -/
  app : ∀ {T : C} (_ : T ⟶ V), (Fin n → H.obj (op T)) → F.obj (op T)
  naturality : ∀ {T T' : C} (s : T' ⟶ T) (t : T ⟶ V) (g : Fin n → H.obj (op T)),
    app (s ≫ t) (fun i => (H.map s.op).hom (g i)) = F.map s.op (app t g)

variable {H F}

namespace Cochain

variable {V : C} {n : ℕ}

instance : Zero (Cochain H F V n) := ⟨⟨fun _ _ => 0, fun _ _ _ => (map_zero _).symm⟩⟩
instance : Add (Cochain H F V n) :=
  ⟨fun a b => ⟨fun t g => a.app t g + b.app t g, fun s t g => by
    rw [a.naturality, b.naturality, map_add]⟩⟩
instance : Neg (Cochain H F V n) :=
  ⟨fun a => ⟨fun t g => - a.app t g, fun s t g => by rw [a.naturality, map_neg]⟩⟩

@[simp] lemma zero_app {T : C} (t : T ⟶ V) (g : Fin n → H.obj (op T)) :
    (0 : Cochain H F V n).app t g = 0 := rfl
@[simp] lemma add_app (a b : Cochain H F V n) {T : C} (t : T ⟶ V) (g : Fin n → H.obj (op T)) :
    (a + b).app t g = a.app t g + b.app t g := rfl
@[simp] lemma neg_app (a : Cochain H F V n) {T : C} (t : T ⟶ V) (g : Fin n → H.obj (op T)) :
    (-a).app t g = - a.app t g := rfl

instance : AddCommGroup (Cochain H F V n) where
  add_assoc a b c := by ext T t g; exact add_assoc _ _ _
  zero_add a := by ext T t g; exact zero_add _
  add_zero a := by ext T t g; exact add_zero _
  add_comm a b := by ext T t g; exact add_comm _ _
  neg_add_cancel a := by ext T t g; exact neg_add_cancel _
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The `𝒪(V)`-module structure of Definition 9.4: `(r • c)(T) = r|_T • c(T)`. -/
instance : SMul (𝒪.obj (op V)) (Cochain H F V n) :=
  ⟨fun r c => ⟨fun t g => (𝒪.map t.op).hom r • c.app t g, fun s t g => by
    rw [c.naturality, F.map_smul, op_comp, 𝒪.map_comp]; rfl⟩⟩

@[simp] lemma smul_app (r : 𝒪.obj (op V)) (a : Cochain H F V n) {T : C} (t : T ⟶ V)
    (g : Fin n → H.obj (op T)) : (r • a).app t g = (𝒪.map t.op).hom r • a.app t g := rfl

instance : Module (𝒪.obj (op V)) (Cochain H F V n) where
  one_smul a := by ext T t g; simp
  mul_smul r r' a := by ext T t g; simp [mul_smul]
  smul_zero r := by ext T t g; simp
  smul_add r a b := by ext T t g; simp
  add_smul r r' a := by ext T t g; simp [add_smul]
  zero_smul a := by ext T t g; simp

/-- The functoriality in `V` of Definition 9.5: restriction of cochains. -/
def res {V' : C} (s : V' ⟶ V) (c : Cochain H F V n) : Cochain H F V' n where
  app t g := c.app (t ≫ s) g
  naturality r t g := by rw [Category.assoc]; exact c.naturality r (t ≫ s) g

end Cochain

/-- **Definition 9.4**: over a terminal object `B`, cochains are the natural transformations from
`Hⁿ` to `F`. -/
def cochainEquivNatTrans {B : C} (hB : Limits.IsTerminal B) (n : ℕ) :
    Cochain H F B n ≃ {c : ∀ T : C, (Fin n → H.obj (op T)) → F.obj (op T) //
      ∀ {T T' : C} (s : T' ⟶ T) (g : Fin n → H.obj (op T)),
        c T' (fun i => (H.map s.op).hom (g i)) = F.map s.op (c T g)} where
  toFun c := ⟨fun T g => c.app (hB.from T) g, fun {T T'} s g => by
    rw [← c.naturality]; exact congrArg (fun k => c.app k _) (hB.hom_ext _ _)⟩
  invFun c := ⟨fun {T} _ g => c.1 T g, fun s _ g => c.2 s g⟩
  left_inv c := by
    ext T t g
    change c.app (hB.from T) g = c.app t g
    rw [hB.hom_ext (hB.from T) t]
  right_inv c := rfl

variable (A : HModule H F)

private lemma map_merge {U U' : Cᵒᵖ} (f : U ⟶ U') {n : ℕ} (i : Fin n) (g : Fin (n + 1) → H.obj U) :
    (fun l => (H.map f).hom (merge i g l)) = merge i (fun l => (H.map f).hom (g l)) := by
  funext l
  simp only [merge]
  split_ifs <;> simp

/-- The value of `δ c`, by the formula of Definition 9.4. -/
def deltaFun {V : C} {n : ℕ} (c : Cochain H F V n) {T : C} (t : T ⟶ V)
    (g : Fin (n + 1) → H.obj (op T)) : F.obj (op T) :=
  A.smul (g 0) (c.app t fun i => g i.succ) +
    ∑ i : Fin n, ((-1 : ℤ) ^ ((i : ℕ) + 1)) • c.app t (merge i g) +
    ((-1 : ℤ) ^ (n + 1)) • c.app t (fun i => g i.castSucc)

lemma deltaFun_eq_dl {V : C} {n : ℕ} (c : Cochain H F V n) {T : C} (t : T ⟶ V)
    (g : Fin (n + 1) → H.obj (op T)) :
    deltaFun A c t g = letI := A.dma (op T); dl (c.app t) g := rfl

lemma HModule.smul_sub_zsmul (A : HModule H F) {U : Cᵒᵖ} (g : H.obj U) (k : ℤ) (x : F.obj U) :
    A.smul g (k • x) = k • A.smul g x := by
  letI := A.dma U
  exact smul_comm g k x

/-- **Definition 9.4**: the `𝒪(V)`-linear differential `δ : Cⁿ → Cⁿ⁺¹`. -/
def delta {V : C} {n : ℕ} : Cochain H F V n →ₗ[𝒪.obj (op V)] Cochain H F V (n + 1) where
  toFun c :=
    { app := fun t g => deltaFun A c t g
      naturality := fun {T T'} s t g => by
        simp only [deltaFun]
        rw [map_add, map_add, map_sum, map_zsmul, A.map_smul, ← c.naturality]
        have h1 : ∀ i : Fin n, F.map s.op (((-1 : ℤ) ^ ((i : ℕ) + 1)) • c.app t (merge i g)) =
            ((-1 : ℤ) ^ ((i : ℕ) + 1)) •
              c.app (s ≫ t) (merge i fun l => (H.map s.op).hom (g l)) := fun i => by
          rw [map_zsmul, ← c.naturality, ← map_merge]
        simp only [h1, ← c.naturality] }
  map_add' a b := by
    ext T t g
    simp only [deltaFun, Cochain.add_app, A.smul_add, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' r a := by
    ext T t g
    simp only [deltaFun, Cochain.smul_app, A.smul_smul, RingHom.id_apply, smul_add,
      Finset.smul_sum]
    simp only [smul_comm ((𝒪.map t.op).hom r) ((-1 : ℤ) ^ _)]

@[simp] lemma delta_app {V : C} {n : ℕ} (c : Cochain H F V n) {T : C} (t : T ⟶ V)
    (g : Fin (n + 1) → H.obj (op T)) : (delta A c).app t g = deltaFun A c t g := rfl

/-- `δ` is compatible with restriction (Definition 9.5: a morphism of `𝒪`-modules). -/
lemma delta_res {V V' : C} (s : V' ⟶ V) {n : ℕ} (c : Cochain H F V n) :
    delta A (c.res s) = (delta A c).res s := rfl

/-- **Remark 9.6**: `δ ∘ δ = 0`. -/
theorem delta_delta {V : C} {n : ℕ} (c : Cochain H F V n) : delta A (delta A c) = 0 := by
  ext T t g
  letI := A.dma (op T)
  exact congrFun (dl_dl (c.app t)) g

/-- **Definition 9.7**: `Zⁿ`. -/
def Zn (V : C) (n : ℕ) : Submodule (𝒪.obj (op V)) (Cochain H F V n) :=
  LinearMap.ker (delta A)

/-- **Definition 9.7**: `B⁰ = 0`, `Bⁿ⁺¹ = im δ`. -/
def Bn (V : C) : ∀ n : ℕ, Submodule (𝒪.obj (op V)) (Cochain H F V n)
  | 0 => ⊥
  | _ + 1 => LinearMap.range (delta A)

lemma Bn_le_Zn (V : C) (n : ℕ) : Bn A V n ≤ Zn A V n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨x, rfl⟩
    exact delta_delta A x

/-- **Definition 9.7**: `Hⁿ_monoid(H|_V, F|_V) = Zⁿ / Bⁿ`. -/
abbrev Hn (V : C) (n : ℕ) : Type _ :=
  (Zn A V n) ⧸ (Bn A V n).comap (Zn A V n).subtype

/-- `Hⁿ⁺¹ = 0` as soon as all cocycles are coboundaries. -/
lemma Hn_subsingleton_of (V : C) (n : ℕ)
    (h : ∀ c : Cochain H F V (n + 1), delta A c = 0 → ∃ e, delta A e = c) :
    Subsingleton (Hn A V (n + 1)) := by
  refine ⟨fun a b => ?_⟩
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.Quotient.eq]
      exact h _ (x - y).2

lemma tuple1_ext {X : Type*} {a b : Fin 1 → X} (h : a 0 = b 0) : a = b := by
  funext i
  rw [Subsingleton.elim i 0, h]

/-- `δ` on `C¹`. -/
lemma deltaFun_one {V : C} (c : Cochain H F V 1) {T : C} (t : T ⟶ V)
    (x : Fin 2 → H.obj (op T)) :
    deltaFun A c t x = A.smul (x 0) (c.app t ![x 1]) - c.app t ![x 0 * x 1] + c.app t ![x 0] := by
  simp only [deltaFun, Fin.sum_univ_one]
  have h1 : (fun i : Fin 1 => x i.succ) = ![x 1] := tuple1_ext rfl
  have h2 : merge (0 : Fin 1) x = ![x 0 * x 1] := tuple1_ext (by simp [merge])
  have h3 : (fun i : Fin 1 => x i.castSucc) = ![x 0] := tuple1_ext rfl
  rw [h1, h2, h3]
  simp [sub_eq_add_neg, pow_succ]

/-- **Remark 9.8**: `Z¹` is the set of `c` with `c(gg') = c(g) + g • c(g')`. -/
theorem mem_Z1_iff {V : C} (c : Cochain H F V 1) :
    c ∈ Zn A V 1 ↔ ∀ {T : C} (t : T ⟶ V) (g g' : H.obj (op T)),
      c.app t ![g * g'] = c.app t ![g] + A.smul g (c.app t ![g']) := by
  constructor
  · intro hc T t g g'
    have h : deltaFun A c t ![g, g'] = 0 := by
      have := congrArg (fun e : Cochain H F V 2 => e.app t ![g, g']) (LinearMap.mem_ker.mp hc)
      exact this
    rw [deltaFun_one] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [add_comm]
    exact (sub_eq_zero.mp (by rw [← h]; abel)).symm
  · intro h
    refine LinearMap.mem_ker.mpr ?_
    ext T t x
    change deltaFun A c t x = 0
    rw [deltaFun_one, h]
    abel

/-- **Remark 9.8**: `B¹` is the set of `g ↦ g • v - v`, `v ∈ F(V)`. -/
theorem mem_B1_iff {V : C} (c : Cochain H F V 1) :
    c ∈ Bn A V 1 ↔ ∃ v : F.obj (op V), ∀ {T : C} (t : T ⟶ V) (g : H.obj (op T)),
      c.app t ![g] = A.smul g (F.map t.op v) - F.map t.op v := by
  have hd : ∀ (e : Cochain H F V 0) {T : C} (t : T ⟶ V) (x : Fin 1 → H.obj (op T)),
      deltaFun A e t x = A.smul (x 0) (e.app t Fin.elim0) - e.app t Fin.elim0 := by
    intro e T t x
    simp only [deltaFun, Fin.sum_univ_zero]
    have h1 : (fun i : Fin 0 => x i.succ) = Fin.elim0 := Subsingleton.elim _ _
    have h3 : (fun i : Fin 0 => x i.castSucc) = Fin.elim0 := Subsingleton.elim _ _
    rw [h1, h3]
    simp [sub_eq_add_neg]
  have hnat : ∀ (e : Cochain H F V 0) {T : C} (t : T ⟶ V),
      e.app t Fin.elim0 = F.map t.op (e.app (𝟙 V) Fin.elim0) := by
    intro e T t
    rw [← e.naturality]
    simp only [Category.comp_id]
    exact congrArg (e.app t) (Subsingleton.elim _ _)
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨e.app (𝟙 V) Fin.elim0, fun {T} t g => ?_⟩
    change deltaFun A e t ![g] = _
    rw [hd, hnat e t]
    rfl
  · rintro ⟨v, hv⟩
    refine ⟨⟨fun t _ => F.map t.op v, fun s t g => ?_⟩, ?_⟩
    · rw [op_comp, F.map_comp]
    · ext T t x
      change deltaFun A _ t x = _
      rw [hd]
      have : x = ![x 0] := tuple1_ext rfl
      rw [this, hv]
      rfl

/-! ### Propositions 9.9 and 9.10

Here `C` has finite products (the fibre products over the base, when `C = Sch/B`). For `X` over `B`
with structure morphism `f`, `(f_* f^* G)(T) = G(T ×_B X)`; Proposition 9.1 identifies this with
`G ⊗ 𝒜` (`AlgMag.S9.IsQCoh.base_change_prod` below). The hypotheses "flat, finitely presented" of the
paper are not needed. -/

section Products

variable [CartesianMonoidalCategory C]

variable (F) in
/-- `Hom_𝒪(F, G)(X)`: the morphisms of `𝒪`-modules `F|_X → G|_X`. -/
@[ext]
structure HomAt (G : PMod 𝒪) (X : C) where
  /-- the value at `x : T ⟶ X` -/
  app : ∀ {T : C} (_ : T ⟶ X), F.obj (op T) →ₗ[𝒪.obj (op T)] G.obj (op T)
  naturality : ∀ {T T' : C} (s : T' ⟶ T) (x : T ⟶ X) (v : F.obj (op T)),
    app (s ≫ x) (F.map s.op v) = G.map s.op (app x v)

/-- The pull-back `Hom_𝒪(F, G)(X) → Hom_𝒪(F, G)(X')` along `m : X' ⟶ X`. -/
def HomAt.pull {G : PMod 𝒪} {X X' : C} (m : X' ⟶ X) (φ : HomAt F G X) : HomAt F G X' where
  app x := φ.app (x ≫ m)
  naturality s x v := by rw [Category.assoc]; exact φ.naturality s (x ≫ m) v

variable (F) in
/-- `Hom_𝒪(F, f_* f^* G)`: for `X` over the base, the morphisms of `𝒪`-modules from `F` to
`T ↦ G(T × X)`; by Proposition 9.1 this `𝒪`-module is `G ⊗ 𝒜`. -/
@[ext]
structure HomPush (G : PMod 𝒪) (X : C) where
  /-- the value at `T` -/
  app : ∀ T : C, F.obj (op T) →+ G.obj (op (T ⊗ X))
  map_smul : ∀ (T : C) (r : 𝒪.obj (op T)) (v : F.obj (op T)),
    app T (r • v) = (𝒪.map (fst T X).op).hom r • app T v
  naturality : ∀ {T T' : C} (s : T' ⟶ T) (v : F.obj (op T)),
    app T' (F.map s.op v) = G.map (s ▷ X).op (app T v)

/-- The map `(Id_G ⊗ m^♯)` of Proposition 9.9: pull-back along `T × X' → T × X`. -/
def HomPush.push {G : PMod 𝒪} {X X' : C} (m : X' ⟶ X) (ψ : HomPush F G X) : HomPush F G X' where
  app T := (G.map (T ◁ m).op).comp (ψ.app T)
  map_smul T r v := by
    simp only [AddMonoidHom.comp_apply]
    rw [ψ.map_smul, G.map_smul, ← CommRingCat.comp_apply, ← 𝒪.map_comp, ← op_comp]
    simp
  naturality {T T'} s v := by
    simp only [AddMonoidHom.comp_apply]
    rw [ψ.naturality, ← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp]
    congr 2
    simp [whisker_exchange]

/-- **Proposition 9.9**: `Hom_𝒪(F, G)(X) = Hom_𝒪(F, G ⊗ 𝒜)`, with `G ⊗ 𝒜 = f_* f^* G`
(Proposition 9.1). -/
def homAtEquivHomPush (G : PMod 𝒪) (X : C) : HomAt F G X ≃ HomPush F G X where
  toFun φ :=
    { app := fun T => (φ.app (snd T X)).toAddMonoidHom.comp (F.map (fst T X).op)
      map_smul := fun T r v => by
        simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
        rw [F.map_smul, map_smul]
      naturality := fun {T T'} s v => by
        simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
        rw [← φ.naturality, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
        simp }
  invFun ψ :=
    { app := fun {T} x =>
        { toFun := fun v => G.map (lift (𝟙 T) x).op (ψ.app T v)
          map_add' := fun a b => by simp
          map_smul' := fun r v => by
            rw [ψ.map_smul, G.map_smul, ← CommRingCat.comp_apply, ← 𝒪.map_comp, ← op_comp]
            simp }
      naturality := fun {T T'} s x v => by
        change G.map _ (ψ.app T' (F.map s.op v)) = G.map _ (G.map _ _)
        have e : lift (𝟙 T') (s ≫ x) ≫ (s ▷ X) = s ≫ lift (𝟙 T) x := by ext <;> simp
        rw [ψ.naturality, ← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp, e] }
  left_inv φ := by
    ext T x v
    change G.map _ (φ.app (snd T X) (F.map (fst T X).op v)) = _
    rw [← φ.naturality, ← F.map_comp, ← op_comp]
    simp [F.map_id]
  right_inv ψ := by
    ext T v
    change G.map (lift (𝟙 (T ⊗ X)) (snd T X)).op (ψ.app (T ⊗ X) (F.map (fst T X).op v)) = _
    have e : lift (𝟙 (T ⊗ X)) (snd T X) ≫ (fst T X ▷ X) = 𝟙 _ := by ext <;> simp
    rw [ψ.naturality, ← G.map_comp, ← op_comp, e]
    exact G.map_id _ _

/-- **Proposition 9.9**, second assertion: the map induced by `m : X' ⟶ X` corresponds to
`(Id_G ⊗ m^♯)`. -/
theorem homAtEquivHomPush_pull (G : PMod 𝒪) {X X' : C} (m : X' ⟶ X) (φ : HomAt F G X) :
    homAtEquivHomPush G X' (φ.pull m) = (homAtEquivHomPush G X φ).push m := by
  ext T v
  change φ.app (snd T X' ≫ m) (F.map (fst T X').op v) =
    G.map (T ◁ m).op (φ.app (snd T X) (F.map (fst T X).op v))
  rw [← φ.naturality, ← F.map_comp, ← op_comp]
  simp

variable {Y : C} (r : (H ⋙ forget MonCat).RepresentableBy Y)

/-- The point of `H` of a morphism to the representing object `Y`. -/
def repPt {T : C} (f : T ⟶ Y) : H.obj (op T) := r.homEquiv f

/-- The morphism to `Y` of a point of `H`. -/
def repSym {T : C} (g : H.obj (op T)) : T ⟶ Y := r.homEquiv.symm g

@[simp] lemma repPt_repSym {T : C} (g : H.obj (op T)) : repPt r (repSym r g) = g :=
  r.homEquiv.apply_symm_apply g

@[simp] lemma repSym_repPt {T : C} (f : T ⟶ Y) : repSym r (repPt r f) = f :=
  r.homEquiv.symm_apply_apply f

lemma repPt_comp {T T' : C} (s : T' ⟶ T) (f : T ⟶ Y) :
    repPt r (s ≫ f) = (H.map s.op).hom (repPt r f) :=
  r.homEquiv_comp s f

lemma comp_repSym {T T' : C} (s : T' ⟶ T) (g : H.obj (op T)) :
    s ≫ repSym r g = repSym r ((H.map s.op).hom g) := by
  apply r.homEquiv.injective
  change repPt r _ = repPt r _
  rw [repPt_comp, repPt_repSym, repPt_repSym]

/-- **Proposition 9.10**, comodule side: an `𝒪`-comodule structure `ρ : F → F ⊗ 𝒜` on `F` for the
monoid `H` represented by `Y`, with `F ⊗ 𝒜 = f_* f^* F` (Proposition 9.1). -/
structure CoactionPush where
  /-- `ρ` -/
  ρ : HomPush F F Y
  /-- `(ρ ⊗ Id) ∘ ρ = (Id ⊗ Δ) ∘ ρ`: at the point `(t, h, g)` of `T × Y × Y`, both are `(gh) • v` -/
  coassoc : ∀ (T : C) (v : F.obj (op T)),
    ρ.app (T ⊗ Y) (ρ.app T v) =
      F.map (lift (fst (T ⊗ Y) Y ≫ fst T Y) (repSym r
        (repPt r (snd (T ⊗ Y) Y) * repPt r (fst (T ⊗ Y) Y ≫ snd T Y)))).op (ρ.app T v)
  /-- `(Id ⊗ ε) ∘ ρ = Id` -/
  counit : ∀ (T : C) (v : F.obj (op T)),
    F.map (lift (𝟙 T) (repSym r (1 : H.obj (op T)))).op (ρ.app T v) = v

lemma HModule.ext' {A B : HModule H F}
    (h : ∀ (U : Cᵒᵖ) (g : H.obj U) (x : F.obj U), A.smul g x = B.smul g x) : A = B := by
  cases A with
  | mk a _ _ _ _ _ =>
    cases B with
    | mk b _ _ _ _ _ =>
      have : @a = @b := by
        funext U g x
        exact h U g x
      subst this
      rfl

lemma CoactionPush.ext' {A B : CoactionPush (F := F) r} (h : A.ρ = B.ρ) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- **Proposition 9.10**: `H`-`𝒪`-module structures on `F` correspond to comodule structures
`F → F ⊗ 𝒜`, the action being `g • v = (id, g)^* ρ(v)`. Here `H` is any monoid functor represented by
`Y`; quasi-coherence, flatness and finite presentation are only used in the paper to rewrite
`f_* f^* F` as `F ⊗ 𝒜`. -/
def hModuleEquivCoaction : HModule H F ≃ CoactionPush (F := F) r where
  toFun A :=
    { ρ :=
      { app := fun T =>
          { toFun := fun v => A.smul (repPt r (snd T Y)) (F.map (fst T Y).op v)
            map_zero' := by rw [map_zero, A.smul_zero]
            map_add' := fun a b => by rw [map_add, A.smul_add] }
        map_smul := fun T a v => by
          change A.smul _ (F.map _ _) = _ • A.smul _ (F.map _ _)
          rw [F.map_smul, A.smul_smul]
        naturality := fun {T T'} s v => by
          change A.smul _ (F.map _ (F.map _ v)) = F.map _ (A.smul _ (F.map _ v))
          rw [A.map_smul, ← repPt_comp, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
          simp }
      coassoc := fun T v => by
        change A.smul (repPt r (snd (T ⊗ Y) Y)) (F.map (fst (T ⊗ Y) Y).op
          (A.smul (repPt r (snd T Y)) (F.map (fst T Y).op v))) =
          F.map _ (A.smul (repPt r (snd T Y)) (F.map (fst T Y).op v))
        rw [A.map_smul, A.map_smul, ← A.mul_smul, ← repPt_comp, ← repPt_comp, ← F.map_comp,
          ← F.map_comp, ← op_comp, ← op_comp]
        simp only [lift_fst, lift_snd, repPt_repSym]
      counit := fun T v => by
        change F.map _ (A.smul (repPt r (snd T Y)) (F.map (fst T Y).op v)) = v
        rw [A.map_smul, ← repPt_comp, ← F.map_comp, ← op_comp]
        simp only [lift_fst, lift_snd, repPt_repSym, op_id]
        rw [F.map_id, A.one_smul] }
  invFun R :=
    { smul := fun {U} g x =>
        F.map (lift (𝟙 (unop U)) (repSym r g)).op (R.ρ.app (unop U) x)
      one_smul := fun {U} x => R.counit (unop U) x
      mul_smul := fun {U} g h x => by
        let T := unop U
        change F.map (lift (𝟙 T) (repSym r (g * h))).op (R.ρ.app T x) =
          F.map (lift (𝟙 T) (repSym r g)).op (R.ρ.app T
            (F.map (lift (𝟙 T) (repSym r h)).op (R.ρ.app T x)))
        rw [R.ρ.naturality, R.coassoc, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
        congr 2
        apply Quiver.Hom.unop_inj
        dsimp only [Quiver.Hom.unop_op]
        refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
        · simp
        · simp only [Category.assoc, lift_snd, comp_repSym, map_mul, ← repPt_comp]
          simp
      smul_add := fun {U} g x y => by simp only [map_add]
      smul_smul := fun {U} g a x => by
        rw [R.ρ.map_smul, F.map_smul, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
        simp only [lift_fst, op_id]
        have e : (𝒪.map (𝟙 (op (unop U)))).hom a = a := by rw [𝒪.map_id]; rfl
        exact congrArg (· • _) e
      map_smul := fun {U V} f g x => by
        change F.map f.unop.op _ = F.map (lift (𝟙 (unop V)) (repSym r ((H.map f.unop.op).hom g))).op
          (R.ρ.app (unop V) (F.map f.unop.op x))
        rw [R.ρ.naturality, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
        congr 2
        apply Quiver.Hom.unop_inj
        dsimp only [Quiver.Hom.unop_op]
        refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
        · simp
        · simp [comp_repSym] }
  left_inv A := by
    refine HModule.ext' fun U g x => ?_
    change F.map _ (A.smul (repPt r (snd (unop U) Y)) (F.map (fst (unop U) Y).op x)) = _
    rw [A.map_smul, ← repPt_comp, ← F.map_comp, ← op_comp]
    simp only [lift_fst, lift_snd, repPt_repSym, op_id]
    rw [F.map_id]
  right_inv R := by
    refine CoactionPush.ext' r ?_
    ext T v
    change F.map (lift (𝟙 (T ⊗ Y)) (repSym r (repPt r (snd T Y)))).op
      (R.ρ.app (T ⊗ Y) (F.map (fst T Y).op v)) = _
    have e : lift (𝟙 (T ⊗ Y)) (snd T Y) ≫ (fst T Y ▷ Y) = 𝟙 _ := by ext <;> simp
    rw [repSym_repPt, R.ρ.naturality, ← F.map_comp, ← op_comp, e]
    exact F.map_id _ _

/-- **Proposition 9.10**: the action is `g • v = (id, g)^* ρ(v)`. -/
lemma hModuleEquivCoaction_symm_smul (R : CoactionPush (F := F) r) {T : C} (g : H.obj (op T))
    (v : F.obj (op T)) :
    ((hModuleEquivCoaction r).symm R).smul g v =
      F.map (lift (𝟙 T) (repSym r g)).op (R.ρ.app T v) := rfl

end Products

end Site
end AlgMag.S9

end BarAndSite

/-! ### Quasi-coherent modules on the big site of a scheme -/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

open scoped Classical

namespace AlgMag.S9

section BC

variable {R R' E E' : Type*} [CommRing R] [CommRing R'] [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R' E']

/-- `f : E → E'`, semilinear along `φ : R → R'`, exhibits `E'` as the base change `E ⊗_R R'`. -/
def IsBC (φ : R →+* R') (f : E →+ E') (hf : ∀ (r : R) (x : E), f (r • x) = φ r • f x) : Prop :=
  letI := φ.toAlgebra
  letI : Module R E' := Module.compHom E' φ
  haveI : IsScalarTower R R' E' := ⟨fun r s x => by
    change (φ r * s) • x = φ r • s • x
    rw [mul_smul]⟩
  IsBaseChange R' ({ toFun := f, map_add' := f.map_add, map_smul' := hf } : E →ₗ[R] E')

/-- A base change along `φ : R → R'`, when `R'` has an `R`-basis `b`: `E'` is free over `E` on `b`. -/
theorem IsBC.bijective {φ : R →+* R'} {f : E →+ E'} {hf : ∀ (r : R) (x : E), f (r • x) = φ r • f x}
    (h : IsBC φ f hf) {ι : Type*} (b : ι → R')
    (hb : Function.Bijective (fun y : ι →₀ R => y.sum fun i r => φ r * b i)) :
    Function.Bijective (fun x : ι →₀ E => x.sum fun i e => b i • f e) := by
  letI := φ.toAlgebra
  letI : Module R E' := Module.compHom E' φ
  haveI : IsScalarTower R R' E' := ⟨fun r s x => by
    change (φ r * s) • x = φ r • s • x
    rw [mul_smul]⟩
  let L : (ι →₀ R) →ₗ[R] R' := Finsupp.lsum R fun i => LinearMap.toSpanSingleton R R' (b i)
  have hL : ∀ y, L y = y.sum fun i r => φ r * b i := fun y => by
    simp only [L, Finsupp.lsum_apply, LinearMap.toSpanSingleton_apply]
    rfl
  have hLb : Function.Bijective L := by
    have : (L : (ι →₀ R) → R') = fun y => y.sum fun i r => φ r * b i := funext hL
    rw [this]
    exact hb
  let B : Module.Basis ι R R' := Module.Basis.ofRepr (LinearEquiv.ofBijective L hLb).symm
  have hB : ∀ i, B i = b i := fun i => by
    change (LinearEquiv.ofBijective L hLb) (Finsupp.single i 1) = b i
    simp [hL, map_one]
  have h' : IsBaseChange R' ({ toFun := f, map_add' := f.map_add, map_smul' := hf } : E →ₗ[R] E') := h
  let e : (ι →₀ E) ≃ E' :=
    (TensorProduct.equivFinsuppOfBasisLeft B).toEquiv.symm.trans h'.equiv.toEquiv
  have he : ∀ x, e x = x.sum fun i e => b i • f e := fun x => by
    change h'.equiv ((TensorProduct.equivFinsuppOfBasisLeft B).symm x) = _
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IsBaseChange.equiv_tmul, hB]
    rfl
  have : (fun x : ι →₀ E => x.sum fun i e => b i • f e) = e := funext fun x => (he x).symm
  rw [this]
  exact e.bijective

end BC

variable {S : Scheme.{u}}

/-- **Quasi-coherent** modules on the big site of `S`: Zariski sheaves whose restriction along a
morphism of affine schemes `T' → T` is the base change `F(T') = F(T) ⊗_{Γ(T)} Γ(T')`. (These are the
quasi-coherent `𝒪`-modules of the fppf site: fppf descent then holds automatically, and is not used
below, so that the results below hold in this greater generality.) -/
structure IsQCoh (F : PMod (GB.overO S)) : Prop where
  sheaf : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F.toPresheaf
  base_change : ∀ {T T' : Over S} (s : T' ⟶ T) [IsAffine T.left] [IsAffine T'.left],
    IsBC ((GB.overO S).map s.op).hom (F.map s.op) (F.map_smul s.op)

variable {F : PMod (GB.overO S)}

/-- The sieve generated by an open cover of `T`. -/
def coverSieve (T : Over S) (𝒰 : Scheme.OpenCover.{u} T.left) : Sieve T where
  arrows W f := ∃ (i : 𝒰.I₀) (u : W.left ⟶ 𝒰.X i), f.left = u ≫ 𝒰.f i
  downward_closed := by
    rintro W W' f ⟨i, u, hu⟩ g
    exact ⟨i, g.left ≫ u, by simp [hu]⟩

lemma coverSieve_mem (T : Over S) (𝒰 : Scheme.OpenCover.{u} T.left) :
    coverSieve T 𝒰 ∈ Scheme.zariskiTopology.over S T := by
  rw [GrothendieckTopology.mem_over_iff]
  refine Scheme.mem_grothendieckTopology_iff.mpr ⟨𝒰, ?_⟩
  rintro W f ⟨i⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨i, 𝟙 _, by simp⟩

/-- The piece of `T` given by `𝒰.X i`. -/
def coverPiece (T : Over S) (𝒰 : Scheme.OpenCover.{u} T.left) (i : 𝒰.I₀) : Over S := Over.mk (𝒰.f i ≫ T.hom)

/-- The inclusion of a piece. -/
def coverHom (T : Over S) (𝒰 : Scheme.OpenCover.{u} T.left) (i : 𝒰.I₀) : coverPiece T 𝒰 i ⟶ T :=
  Over.homMk (𝒰.f i)

lemma sep_cover (hF : IsQCoh F) (T : Over S) (𝒰 : Scheme.OpenCover.{u} T.left) {y y' : F.obj (op T)}
    (h : ∀ i, F.map (coverHom T 𝒰 i).op y = F.map (coverHom T 𝒰 i).op y') : y = y' := by
  refine (hF.sheaf _ (coverSieve_mem T 𝒰)).isSeparatedFor.ext fun W f hf => ?_
  obtain ⟨i, u, hu⟩ := hf
  let u' : W ⟶ coverPiece T 𝒰 i := Over.homMk u (by
    change u ≫ 𝒰.f i ≫ T.hom = W.hom
    rw [← Category.assoc, ← hu]
    exact Over.w f)
  have e : f = u' ≫ coverHom T 𝒰 i := Over.OverMorphism.ext hu
  change F.map f.op y = F.map f.op y'
  rw [e, op_comp, F.map_comp, F.map_comp, h]

/-- Two sections agreeing on all affine schemes over `T` are equal. -/
lemma sep_affine (hF : IsQCoh F) (T : Over S) {y y' : F.obj (op T)}
    (h : ∀ (A : Over S) (a : A ⟶ T) [IsAffine A.left], F.map a.op y = F.map a.op y') : y = y' := by
  refine sep_cover hF T T.left.affineCover fun i => ?_
  haveI : IsAffine (coverPiece T T.left.affineCover i).left := by
    change IsAffine (T.left.affineCover.X i)
    infer_instance
  exact h _ _

/-- **Gluing over affines**: a compatible family of sections over all affine schemes over `T` comes
from a unique section over `T`. -/
theorem affine_glue (hF : IsQCoh F) (T : Over S)
    (val : ∀ (A : Over S) (a : A ⟶ T) [IsAffine A.left], F.obj (op A))
    (compat : ∀ (A A' : Over S) (s : A' ⟶ A) (a : A ⟶ T) [IsAffine A.left] [IsAffine A'.left],
      val A' (s ≫ a) = F.map s.op (val A a)) :
    ∃! v : F.obj (op T), ∀ (A : Over S) (a : A ⟶ T) [IsAffine A.left], F.map a.op v = val A a := by
  let 𝒰 := T.left.affineCover
  have hA : ∀ i, IsAffine (coverPiece T 𝒰 i).left := fun i => by
    change IsAffine (𝒰.X i)
    infer_instance
  let aff : Sieve T :=
    { arrows := fun W f => ∃ (A : Over S) (_ : IsAffine A.left) (u : W ⟶ A) (a : A ⟶ T), u ≫ a = f
      downward_closed := by
        rintro W W' f ⟨A, hA, u, a, rfl⟩ g
        exact ⟨A, hA, g ≫ u, a, Category.assoc _ _ _⟩ }
  have hmem : aff ∈ Scheme.zariskiTopology.over S T := by
    refine GrothendieckTopology.superset_covering _ ?_ (coverSieve_mem T 𝒰)
    rintro W f ⟨i, u, hu⟩
    refine ⟨coverPiece T 𝒰 i, hA i, Over.homMk u ?_, coverHom T 𝒰 i, Over.OverMorphism.ext hu.symm⟩
    change u ≫ 𝒰.f i ≫ T.hom = W.hom
    rw [← Category.assoc, ← hu]
    exact Over.w f
  have sh := hF.sheaf _ hmem
  let x : Presieve.FamilyOfElements F.toPresheaf aff.arrows := fun W f hf =>
    haveI := hf.choose_spec.choose
    F.map hf.choose_spec.choose_spec.choose.op
      (val hf.choose hf.choose_spec.choose_spec.choose_spec.choose)
  have hx : ∀ {W} (f : W ⟶ T) (hf : aff.arrows f) (A : Over S) [IsAffine A.left] (u : W ⟶ A)
      (a : A ⟶ T), u ≫ a = f → x f hf = F.map u.op (val A a) := by
    intro W f hf A _ u a hua
    obtain ⟨A₀, hA₀, u₀, a₀, h₀⟩ := id hf
    have key : ∀ (A' : Over S) [IsAffine A'.left] (u' : W ⟶ A') (a' : A' ⟶ T), u' ≫ a' = f →
        ∀ (A'' : Over S) [IsAffine A''.left] (u'' : W ⟶ A'') (a'' : A'' ⟶ T), u'' ≫ a'' = f →
        F.map u'.op (val A' a') = F.map u''.op (val A'' a'') := by
      intro A' _ u' a' h' A'' _ u'' a'' h''
      refine sep_affine hF W fun E e _ => ?_
      change F.map e.op (F.map u'.op _) = F.map e.op (F.map u''.op _)
      rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, ← compat, ← compat]
      congr 1
      rw [Category.assoc, Category.assoc, h', h'']
    haveI := hf.choose_spec.choose
    exact key _ _ _ hf.choose_spec.choose_spec.choose_spec.choose_spec _ u a hua
  have hc : x.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
    obtain ⟨A₁, hA₁, u₁, a₁, e₁⟩ := id h₁
    obtain ⟨A₂, hA₂, u₂, a₂, e₂⟩ := id h₂
    change F.map g₁.op (x f₁ h₁) = F.map g₂.op (x f₂ h₂)
    rw [hx f₁ h₁ A₁ u₁ a₁ e₁, hx f₂ h₂ A₂ u₂ a₂ e₂]
    refine sep_affine hF Z fun E e _ => ?_
    simp only [← F.map_comp, ← op_comp]
    rw [← compat, ← compat]
    congr 1
    subst e₁ e₂
    simp only [Category.assoc] at comm ⊢
    rw [comm]
  refine ⟨sh.amalgamate x hc, fun A a _ => ?_, fun v hv => ?_⟩
  · have ha : aff.arrows a := ⟨A, inferInstance, 𝟙 A, a, Category.id_comp a⟩
    have := sh.valid_glue hc a ha
    refine Eq.trans this ?_
    rw [hx a ha A (𝟙 A) a (Category.id_comp a), op_id, F.map_id]
  · refine sep_affine hF T fun A a _ => ?_
    rw [hv]
    have ha : aff.arrows a := ⟨A, inferInstance, 𝟙 A, a, Category.id_comp a⟩
    have := sh.valid_glue hc a ha
    refine Eq.symm (Eq.trans this ?_)
    rw [hx a ha A (𝟙 A) a (Category.id_comp a), op_id, F.map_id]

/-! ### The universal point: cochains over an affine scheme -/

section Eval

variable {N : Type u} [AddCommMonoid N]

/-- `x = ∑ f_m X^m ↦ ∑ a(m) • f_m|_T`, for `x ∈ ⨁_{m ∈ N} F(V)`, `t : T ⟶ V`, `a ∈ 𝔸(N)(T)`. -/
def evalE {V T : Over S} (t : T ⟶ V) (a : APt (GB.overO S) N (op T)) :
    (N →₀ F.obj (op V)) →+ F.obj (op T) :=
  Finsupp.liftAddHom fun m =>
    { toFun := fun f => a (Multiplicative.ofAdd m) • F.map t.op f
      map_zero' := by simp
      map_add' := fun f f' => by simp [smul_add] }

@[simp] lemma evalE_single {V T : Over S} (t : T ⟶ V) (a : APt (GB.overO S) N (op T)) (m : N)
    (f : F.obj (op V)) :
    evalE t a (Finsupp.single m f) = a (Multiplicative.ofAdd m) • F.map t.op f := by
  simp [evalE]

lemma evalE_res {V T T' : Over S} (s : T' ⟶ T) (t : T ⟶ V) (a : APt (GB.overO S) N (op T))
    (x : N →₀ F.obj (op V)) :
    evalE (s ≫ t) (APt.res s.op a) x = F.map s.op (evalE t a x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single m f =>
    rw [evalE_single, evalE_single, F.map_smul, op_comp, F.map_comp]
    rfl

variable (F N) in
/-- The natural maps `𝔸(N) → F` over `V`. -/
@[ext]
structure NC (V : Over S) where
  /-- the values -/
  app : ∀ {T : Over S} (_ : T ⟶ V), APt (GB.overO S) N (op T) → F.obj (op T)
  naturality : ∀ {T T' : Over S} (s : T' ⟶ T) (t : T ⟶ V) (a : APt (GB.overO S) N (op T)),
    app (s ≫ t) (APt.res s.op a) = F.map s.op (app t a)

/-- Restriction of natural maps. -/
def NC.res {V V' : Over S} (s : V' ⟶ V) (c : NC F N V) : NC F N V' where
  app t a := c.app (t ≫ s) a
  naturality r t a := by rw [Category.assoc]; exact c.naturality r (t ≫ s) a

/-- `x ↦ (a ↦ ∑ a(m) • f_m)`. -/
def phiN {V : Over S} (x : N →₀ F.obj (op V)) : NC F N V where
  app t a := evalE t a x
  naturality s t a := evalE_res s t a x

variable (S N) in
/-- The Hopf algebra `Γ(V)[N]`. -/
abbrev Dring (V : Over S) : CommRingCat.{u} :=
  CommRingCat.of (AddMonoidAlgebra Γ(V.left, ⊤) N)

/-- `Γ(V) → Γ(V)[N]`. -/
def Dalg (V : Over S) : Γ(V.left, ⊤) ⟶ Dring S N V :=
  CommRingCat.ofHom (algebraMap Γ(V.left, ⊤) (AddMonoidAlgebra Γ(V.left, ⊤) N))

variable (W : Over S) [IsAffine W.left]

/-- `Spec Γ(W)[N] → W`, for `W` affine. -/
def pr0 : Spec (Dring S N W) ⟶ W.left :=
  Spec.map (Dalg W) ≫ W.left.isoSpec.inv

variable (N) in
/-- `𝔸(N)_W`, for `W` affine: `Spec Γ(W)[N]`, as a scheme over `S`. -/
def Yobj : Over S := Over.mk (pr0 (N := N) W ≫ W.hom)

instance : IsAffine (Yobj N W).left := by
  change IsAffine (Spec (Dring S N W))
  infer_instance

variable (N) in
/-- `𝔸(N)_W → W`. -/
def Ypr : Yobj N W ⟶ W := Over.homMk (pr0 W)

/-- The identification `Γ(W)[N] → Γ(𝔸(N)_W)`. -/
def Yiota : Dring S N W ⟶ Γ((Yobj N W).left, ⊤) :=
  (Scheme.ΓSpecIso (Dring S N W)).inv

lemma Yiota_bijective : Function.Bijective (Yiota (N := N) W) := by
  have : IsIso (Scheme.ΓSpecIso (Dring S N W)).inv := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

/-- The ring map `Γ(W) → Γ(𝔸(N)_W)` of `Ypr` is the inclusion of constants. -/
lemma Ypr_map : (Ypr N W).left.appTop = Dalg W ≫ Yiota W := by
  have h1 : pr0 (N := N) W ≫ W.left.toSpecΓ = Spec.map (Dalg W) := by
    have e : W.left.toSpecΓ = W.left.isoSpec.hom := rfl
    rw [e, pr0, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h2 := GB.homSpecEquiv_comp (pr0 (N := N) W) W.left.toSpecΓ
  have h3 := GB.homSpecEquiv_map (T := Spec (Dring S N W)) (Dalg (N := N) W) (𝟙 _)
  rw [Category.id_comp, ← h1, h2] at h3
  have h4 : GB.homSpecEquiv W.left _ W.left.toSpecΓ = 𝟙 _ := by
    simp [GB.homSpecEquiv, Scheme.toSpecΓ_appTop]
  rw [h4, Category.id_comp] at h3
  refine h3.trans ?_
  congr 1

variable {W}

/-- The ring map `Γ(W)[N] → Γ(T)` of a point `a` of `𝔸(N)` over `t : T ⟶ W`. -/
def rhoOf {T : Over S} (t : T ⟶ W) (a : APt (GB.overO S) N (op T)) :
    Dring S N W ⟶ Γ(T.left, ⊤) :=
  CommRingCat.ofHom (AddMonoidAlgebra.liftNCRingHom t.left.appTop.hom a
    (fun _ _ => Commute.all _ _))

lemma rhoOf_single {T : Over S} (t : T ⟶ W) (a : APt (GB.overO S) N (op T)) (m : N)
    (r : Γ(W.left, ⊤)) :
    (rhoOf t a).hom (AddMonoidAlgebra.single m r) =
      t.left.appTop.hom r * (show Γ(T.left, ⊤) from a (Multiplicative.ofAdd m)) :=
  AddMonoidAlgebra.liftNC_single _ _ m r

lemma Dalg_rhoOf {T : Over S} (t : T ⟶ W) (a : APt (GB.overO S) N (op T)) :
    Dalg W ≫ rhoOf t a = t.left.appTop := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  change (rhoOf t a).hom (AddMonoidAlgebra.single 0 r) = _
  rw [rhoOf_single]
  have : (show Γ(T.left, ⊤) from a (Multiplicative.ofAdd (0 : N))) = 1 := a.map_one
  rw [this]
  exact mul_one _

lemma k_pr0 {T : Over S} (t : T ⟶ W) (a : APt (GB.overO S) N (op T)) :
    (T.left.toSpecΓ ≫ Spec.map (rhoOf t a)) ≫ pr0 W = t.left := by
  rw [pr0, Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp, Dalg_rhoOf,
    ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
  have e : W.left.toSpecΓ = W.left.isoSpec.hom := rfl
  rw [e, Iso.hom_inv_id, Category.comp_id]

/-- The classifying morphism of a point `a` of `𝔸(N)` over `t : T ⟶ W`. -/
def classify {T : Over S} (t : T ⟶ W) (a : APt (GB.overO S) N (op T)) : T ⟶ Yobj N W :=
  Over.homMk (T.left.toSpecΓ ≫ Spec.map (rhoOf t a))
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ W.hom) (k_pr0 t a)).trans (Over.w t)))

lemma classify_pr {T : Over S} (t : T ⟶ W) (a : APt (GB.overO S) N (op T)) :
    classify t a ≫ Ypr N W = t :=
  Over.OverMorphism.ext (k_pr0 t a)

lemma classify_map {T : Over S} (t : T ⟶ W) (a : APt (GB.overO S) N (op T)) :
    Yiota W ≫ (classify t a).left.appTop = rhoOf t a :=
  (GB.homSpecEquiv T.left _).right_inv (rhoOf t a)

variable (N W) in
/-- The character `χ^m ∈ Γ(𝔸(N)_W)`. -/
def uch (m : N) : Γ((Yobj N W).left, ⊤) := (Yiota W).hom (AddMonoidAlgebra.single m 1)

variable (N W) in
/-- The universal point of `𝔸(N)` over `𝔸(N)_W`. -/
def univ : APt (GB.overO S) N (op (Yobj N W)) :=
  (show Multiplicative N →* Γ((Yobj N W).left, ⊤) from
    { toFun := fun m => uch N W (Multiplicative.toAdd m)
      map_one' := map_one (Yiota (N := N) W).hom
      map_mul' := fun m m' => by
        simp only [uch]
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
        rfl })

lemma res_classify_univ {T : Over S} (t : T ⟶ W) (a : APt (GB.overO S) N (op T)) :
    APt.res (classify t a).op (univ N W) = a := by
  refine MonoidHom.ext fun m => ?_
  have h := congrArg (fun k => k.hom (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1))
    (classify_map t a)
  refine h.trans ?_
  rw [rhoOf_single, map_one, one_mul]
  rfl

lemma theta_basis :
    Function.Bijective (fun y : N →₀ Γ(W.left, ⊤) => y.sum fun m r =>
      ((Ypr N W).left.appTop.hom r) * uch N W m) := by
  let B := AddMonoidAlgebra.basis N Γ(W.left, ⊤)
  have e : (fun y : N →₀ Γ(W.left, ⊤) => y.sum fun m r =>
      ((Ypr N W).left.appTop.hom r) * uch N W m) =
      (Yiota (N := N) W) ∘ B.repr.symm := by
    funext y
    simp only [Function.comp, Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
    rw [Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Ypr_map, Algebra.smul_def, map_mul]
    have hB : B m = AddMonoidAlgebra.single m 1 := by simp [B]
    rw [hB]
    rfl
  rw [e]
  exact (Yiota_bijective W).comp B.repr.symm.bijective

/-- `θ`: `⨁_{m ∈ N} F(W) → F(𝔸(N)_W)`, `f X^m ↦ χ^m f|`, is bijective: this is quasi-coherence, since
`Γ(𝔸(N)_W)` is free over `Γ(W)` on the characters. -/
theorem theta_bijective (hF : IsQCoh F) :
    Function.Bijective (fun x : N →₀ F.obj (op W) => evalE (Ypr N W) (univ N W) x) := by
  have h := IsBC.bijective (hF.base_change (Ypr N W)) (uch N W) (theta_basis (N := N))
  exact h

/-- A natural map `𝔸(N) → F` over `W` is determined by its value at the universal point. -/
lemma NC.eq_of_univ {c c' : NC F N W} (h : c.app (Ypr N W) (univ N W) = c'.app (Ypr N W) (univ N W)) :
    c = c' := by
  ext T t a
  have e : ∀ c : NC F N W, c.app t a = F.map (classify t a).op (c.app (Ypr N W) (univ N W)) := by
    intro c
    rw [← c.naturality, res_classify_univ, classify_pr]
  rw [e c, e c', h]

/-- **Proposition 9.12** over an affine scheme: natural maps `𝔸(N) → F` are `⨁_{m ∈ N} F(W)`. -/
theorem phiN_bijective (hF : IsQCoh F) : Function.Bijective (phiN (F := F) (N := N) (V := W)) := by
  constructor
  · intro x y h
    apply (theta_bijective (N := N) hF).1
    exact congrArg (fun c : NC F N W => c.app (Ypr N W) (univ N W)) h
  · intro c
    obtain ⟨x, hx⟩ := (theta_bijective (N := N) hF).2 (c.app (Ypr N W) (univ N W))
    exact ⟨x, NC.eq_of_univ hx⟩

end Eval

end AlgMag.S9

/-! ### Proposition 9.12: sections of the sheaf `⨁ F_m` -/

namespace AlgMag.S9

open CategoryTheory Opposite AlgebraicGeometry

open scoped Classical

section Sections

variable {S : Scheme.{u}} {F : PMod (GB.overO S)} {N : Type u} [AddCommMonoid N]

/-- Restriction of a family of coefficients. -/
def resF {V V' : Over S} (s : V' ⟶ V) (x : N →₀ F.obj (op V)) : N →₀ F.obj (op V') :=
  x.mapRange (F.map s.op) (map_zero _)

@[simp] lemma resF_apply {V V' : Over S} (s : V' ⟶ V) (x : N →₀ F.obj (op V)) (m : N) :
    resF s x m = F.map s.op (x m) := rfl

lemma evalE_resF {V V' T : Over S} (s : V' ⟶ V) (t : T ⟶ V') (a : APt (GB.overO S) N (op T))
    (x : N →₀ F.obj (op V)) : evalE t a (resF s x) = evalE (t ≫ s) a x := by
  induction x using Finsupp.induction_linear with
  | zero => simp [resF]
  | add p q hp hq =>
    have : resF s (p + q) = resF s p + resF s q := by
      ext m; simp
    rw [this, map_add, map_add, hp, hq]
  | single m f =>
    have : resF s (Finsupp.single m f) = Finsupp.single m (F.map s.op f) := by
      simp [resF]
    rw [this, evalE_single, evalE_single, op_comp, F.map_comp]

lemma phiN_res {V V' : Over S} (s : V' ⟶ V) (x : N →₀ F.obj (op V)) :
    (phiN x).res s = phiN (F := F) (resF s x) := by
  ext T t a
  exact (evalE_resF s t a x).symm

lemma NC.res_comp {V V' V'' : Over S} (s : V' ⟶ V) (s' : V'' ⟶ V') (c : NC F N V) :
    c.res (s' ≫ s) = (c.res s).res s' := by
  ext T t a
  change c.app (t ≫ s' ≫ s) a = c.app ((t ≫ s') ≫ s) a
  rw [Category.assoc]

/-- A value at the identity of an arrow to `V`. -/
lemma NC.app_eq_res_id {V A : Over S} (c : NC F N V) (a : A ⟶ V) (b : APt (GB.overO S) N (op A)) :
    c.app a b = (c.res a).app (𝟙 A) b := by
  change _ = c.app (𝟙 A ≫ a) b
  rw [Category.id_comp]

/-- `F` separated: natural maps agreeing over all affine schemes are equal. -/
lemma NC.ext_affine (hF : IsQCoh F) {V : Over S} {c c' : NC F N V}
    (h : ∀ (A : Over S) (a : A ⟶ V) [IsAffine A.left], c.res a = c'.res a) : c = c' := by
  ext T t a
  refine sep_affine hF T fun A e _ => ?_
  rw [← c.naturality, ← c'.naturality, NC.app_eq_res_id c, NC.app_eq_res_id c', h]

/-- **Proposition 9.12, first assertion**: a section over `V` of the sheaf `⨁_{m ∈ N} F_m`. Its
value on a quasi-compact scheme is the literal direct sum, so that a section is a compatible family
of finitely supported families over the affine schemes `A → V`. -/
@[ext]
structure Sec (F : PMod (GB.overO S)) (N : Type u) [AddCommMonoid N] (V : Over S) where
  /-- the value on `a : A ⟶ V` -/
  val : ∀ (A : Over S) (a : A ⟶ V) [IsAffine A.left], N →₀ F.obj (op A)
  compat : ∀ (A A' : Over S) (s : A' ⟶ A) (a : A ⟶ V) [IsAffine A.left] [IsAffine A'.left],
    val A' (s ≫ a) = resF s (val A a)

variable (hF : IsQCoh F)

include hF

/-- The inverse of `phiN`, over an affine scheme. -/
def phiInv {W : Over S} [IsAffine W.left] (c : NC F N W) : N →₀ F.obj (op W) :=
  (phiN_bijective hF).2 c |>.choose

lemma phiN_phiInv {W : Over S} [IsAffine W.left] (c : NC F N W) : phiN (phiInv hF c) = c :=
  ((phiN_bijective hF).2 c).choose_spec

lemma phiInv_phiN {W : Over S} [IsAffine W.left] (x : N →₀ F.obj (op W)) :
    phiInv hF (phiN x) = x :=
  (phiN_bijective hF).1 (phiN_phiInv hF _)

/-- A natural map gives a section of `⨁ F_m`. -/
def secOf {V : Over S} (c : NC F N V) : Sec F N V where
  val A a _ := phiInv hF (c.res a)
  compat A A' s a _ _ := by
    refine (phiN_bijective hF).1 ?_
    rw [phiN_phiInv, ← phiN_res, phiN_phiInv, NC.res_comp]

/-- The section glued from a compatible family. -/
def glueV (T : Over S) (val : ∀ (A : Over S) (a : A ⟶ T) [IsAffine A.left], F.obj (op A))
    (compat : ∀ (A A' : Over S) (s : A' ⟶ A) (a : A ⟶ T) [IsAffine A.left] [IsAffine A'.left],
      val A' (s ≫ a) = F.map s.op (val A a)) : F.obj (op T) :=
  (affine_glue hF T val compat).choose

lemma glueV_spec (T : Over S) (val : ∀ (A : Over S) (a : A ⟶ T) [IsAffine A.left], F.obj (op A))
    (compat : ∀ (A A' : Over S) (s : A' ⟶ A) (a : A ⟶ T) [IsAffine A.left] [IsAffine A'.left],
      val A' (s ≫ a) = F.map s.op (val A a)) (A : Over S) (a : A ⟶ T) [IsAffine A.left] :
    F.map a.op (glueV hF T val compat) = val A a :=
  (affine_glue hF T val compat).choose_spec.1 A a

omit hF in
lemma ofSec_compat {V : Over S} (σ : Sec F N V) {T : Over S} (t : T ⟶ V)
    (a : APt (GB.overO S) N (op T)) (A A' : Over S) (s : A' ⟶ A) (e : A ⟶ T) [IsAffine A.left]
    [IsAffine A'.left] :
    evalE (𝟙 A') (APt.res (s ≫ e).op a) (σ.val A' ((s ≫ e) ≫ t)) =
      F.map s.op (evalE (𝟙 A) (APt.res e.op a) (σ.val A (e ≫ t))) := by
  rw [Category.assoc, σ.compat, evalE_resF, op_comp, APt.res_comp, ← evalE_res]
  simp

/-- A section of `⨁ F_m` gives a natural map. -/
def ofSec {V : Over S} (σ : Sec F N V) : NC F N V where
  app {T} t a := glueV hF T (fun A e _ => evalE (𝟙 A) (APt.res e.op a) (σ.val A (e ≫ t)))
    (fun A A' s e _ _ => ofSec_compat σ t a A A' s e)
  naturality {T T'} s t a := by
    refine sep_affine hF T' fun A e _ => ?_
    rw [glueV_spec, ← F.map_comp, ← op_comp, glueV_spec, op_comp, APt.res_comp]
    simp only [Category.assoc]

lemma ofSec_app_spec {V : Over S} (σ : Sec F N V) {T : Over S} (t : T ⟶ V)
    (b : APt (GB.overO S) N (op T)) {E : Over S} (e : E ⟶ T) [IsAffine E.left] :
    F.map e.op ((ofSec hF σ).app t b) = evalE (𝟙 E) (APt.res e.op b) (σ.val E (e ≫ t)) :=
  glueV_spec hF T _ (fun A A' s e _ _ => ofSec_compat σ t b A A' s e) E e

lemma ofSec_res {V : Over S} (σ : Sec F N V) {A : Over S} (a : A ⟶ V) [IsAffine A.left] :
    (ofSec hF σ).res a = phiN (σ.val A a) := by
  ext T t b
  refine sep_affine hF T fun E e _ => ?_
  change F.map e.op ((ofSec hF σ).app (t ≫ a) b) = F.map e.op (evalE t b (σ.val A a))
  rw [ofSec_app_spec, ← evalE_res, ← Category.assoc, σ.compat A E (e ≫ t) a, evalE_resF]
  simp

/-- **Proposition 9.12, first assertion**, for `𝔸(N)`: natural maps `𝔸(N)|_V → F|_V` are the sections
over `V` of `⨁_{m ∈ N} F_m`, for any `V`. -/
def ncEquivSec (V : Over S) : NC F N V ≃ Sec F N V where
  toFun := secOf hF
  invFun := ofSec hF
  left_inv c := by
    refine NC.ext_affine hF fun A a _ => ?_
    rw [ofSec_res]
    exact phiN_phiInv hF _
  right_inv σ := by
    refine Sec.ext ?_
    funext A a inst
    change phiInv hF ((ofSec hF σ).res a) = _
    rw [ofSec_res, phiInv_phiN]

lemma secOf_val_phiN_res {V : Over S} (c : NC F N V) {A : Over S} (a : A ⟶ V) [IsAffine A.left] :
    phiN ((secOf hF c).val A a) = c.res a :=
  phiN_phiInv hF _

/-- The coefficient at `m` of a section of `⨁ F_m`. -/
def coef {V : Over S} (σ : Sec F N V) (m : N) : F.obj (op V) :=
  glueV hF V (fun A a _ => σ.val A a m) (fun A A' s a _ _ => by rw [σ.compat, resF_apply])

lemma coef_spec {V : Over S} (σ : Sec F N V) (m : N) {A : Over S} (a : A ⟶ V) [IsAffine A.left] :
    F.map a.op (coef hF σ m) = σ.val A a m :=
  glueV_spec hF V _ _ A a

lemma coef_finite {V : Over S} [CompactSpace V.left] (σ : Sec F N V) :
    (Function.support (coef hF σ)).Finite := by
  let 𝒰 : Scheme.OpenCover.{u} V.left := V.left.affineCover.finiteSubcover
  have hA : ∀ i, IsAffine (coverPiece V 𝒰 i).left := fun i => by
    change IsAffine (V.left.affineCover.X _)
    infer_instance
  have hfin : (⋃ i : 𝒰.I₀, ((σ.val _ (coverHom V 𝒰 i)).support : Set N)).Finite :=
    Set.finite_iUnion fun i => Finset.finite_toSet _
  refine hfin.subset fun m hm => ?_
  by_contra hc
  apply hm
  refine sep_cover hF V 𝒰 fun i => ?_
  rw [coef_spec, map_zero]
  by_contra hne
  exact hc (Set.mem_iUnion.mpr ⟨i, by simpa using hne⟩)

/-- **Proposition 9.12**, quasi-compact case: a section of `⨁ F_m` over `V` quasi-compact is an
element of the literal direct sum. -/
def xOf {V : Over S} [CompactSpace V.left] (σ : Sec F N V) : N →₀ F.obj (op V) :=
  Finsupp.ofSupportFinite (coef hF σ) (coef_finite hF σ)

lemma resF_xOf {V : Over S} [CompactSpace V.left] (σ : Sec F N V) {A : Over S} (a : A ⟶ V)
    [IsAffine A.left] : resF a (xOf hF σ) = σ.val A a := by
  ext m
  exact coef_spec hF σ m a

/-- **Proposition 9.12**, quasi-compact case: `phiN` is a bijection from `⨁_{m ∈ N} F(V)` to the
natural maps `𝔸(N)|_V → F|_V`. Only the quasi-compactness of `V` is used. -/
theorem phiN_bijective_compact {V : Over S} [CompactSpace V.left] :
    Function.Bijective (phiN (F := F) (N := N) (V := V)) := by
  constructor
  · intro x y h
    ext m
    refine sep_affine hF V fun A a _ => ?_
    have h1 : resF a x = resF a y := by
      refine (phiN_bijective hF).1 ?_
      rw [← phiN_res, ← phiN_res, h]
    exact congrArg (fun z => z m) h1
  · intro c
    refine ⟨xOf hF (secOf hF c), NC.ext_affine hF fun A a _ => ?_⟩
    rw [phiN_res, resF_xOf, secOf_val_phiN_res]

end Sections

end AlgMag.S9

/-! ### Cochains of `𝔸(M)`, comodules, and the differential -/

namespace AlgMag.S9

open CategoryTheory Opposite AlgebraicGeometry

open scoped Classical

section AM

variable {S : Scheme.{u}} {F : PMod (GB.overO S)} {M : Type u} [AddCommMonoid M]

lemma evalE_smul {N : Type u} [AddCommMonoid N] {V T : Over S} (t : T ⟶ V)
    (a : APt (GB.overO S) N (op T)) (r : (GB.overO S).obj (op V)) (x : N →₀ F.obj (op V)) :
    evalE t a (r • x) = ((GB.overO S).map t.op).hom r • evalE t a x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]
  | single m f =>
    rw [Finsupp.smul_single, evalE_single, evalE_single, F.map_smul, smul_comm]

/-- `(g₁,…,gₙ) ↦ (m ↦ ∏ gᵢ(mᵢ))`: `𝔸(M)ⁿ = 𝔸(Mⁿ)`. -/
def toPt {T : Over S} {n : ℕ} (g : Fin n → APt (GB.overO S) M (op T)) :
    APt (GB.overO S) (Fin n → M) (op T) where
  toFun m := ∏ i, g i (Multiplicative.ofAdd (Multiplicative.toAdd m i))
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← map_mul]
    rfl

@[simp] lemma toPt_ofAdd {T : Over S} {n : ℕ} (g : Fin n → APt (GB.overO S) M (op T))
    (m : Fin n → M) :
    toPt g (Multiplicative.ofAdd m) = ∏ i, g i (Multiplicative.ofAdd (m i)) := rfl

/-- The components of a point of `𝔸(Mⁿ)`. -/
def ofPt {T : Over S} {n : ℕ} (a : APt (GB.overO S) (Fin n → M) (op T)) :
    Fin n → APt (GB.overO S) M (op T) := fun i =>
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ => M) i))

lemma toPt_ofPt {T : Over S} {n : ℕ} (a : APt (GB.overO S) (Fin n → M) (op T)) :
    toPt (ofPt a) = a := by
  refine MonoidHom.ext fun m => ?_
  change ∏ i, a (Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd m i))) = a m
  rw [← map_prod, ← ofAdd_sum, Finset.univ_sum_single]
  rfl

lemma ofPt_toPt {T : Over S} {n : ℕ} (g : Fin n → APt (GB.overO S) M (op T)) :
    ofPt (toPt g) = g := by
  funext i
  refine MonoidHom.ext fun m => ?_
  change ∏ j, g j (Multiplicative.ofAdd ((Pi.single i (Multiplicative.toAdd m) : Fin n → M) j)) = _
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

lemma toPt_res {T T' : Over S} (s : T' ⟶ T) {n : ℕ} (g : Fin n → APt (GB.overO S) M (op T)) :
    toPt (fun i => APt.res s.op (g i)) = APt.res s.op (toPt g) := by
  refine MonoidHom.ext fun m => ?_
  simp [toPt]

/-- The monoid functor `𝔸(M)_S`. -/
abbrev Hm (M : Type u) [AddCommMonoid M] (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ MonCat.{u} :=
  GB.ptsFunctor M S

/-- `Cⁿ(𝔸(M), F)` is the set of natural maps `𝔸(Mⁿ) → F`. -/
def cochainEquivNC (V : Over S) (n : ℕ) : Cochain (Hm M S) F V n ≃ NC F (Fin n → M) V where
  toFun c :=
    { app := fun t a => c.app t (ofPt a)
      naturality := fun s t a => c.naturality s t (ofPt a) }
  invFun c :=
    { app := fun t g => c.app t (toPt g)
      naturality := fun s t g =>
        (congrArg (c.app (s ≫ t)) (toPt_res s g)).trans (c.naturality s t (toPt g)) }
  left_inv c := by
    ext T t g
    exact congrArg (c.app t) (ofPt_toPt g)
  right_inv c := by
    ext T t a
    exact congrArg (c.app t) (toPt_ofPt a)

/-- The map `⨁_{m ∈ Mⁿ} F(V) → Cⁿ(𝔸(M)_V, F)`: `f X^{m₁}⋯X^{mₙ}` is the cochain
`(g₁,…,gₙ) ↦ g₁(m₁)⋯gₙ(mₙ) f`. -/
def phiC (V : Over S) (n : ℕ) :
    ((Fin n → M) →₀ F.obj (op V)) →ₗ[(GB.overO S).obj (op V)] Cochain (Hm M S) F V n where
  toFun x := (cochainEquivNC V n).symm (phiN x)
  map_add' x y := by
    ext T t g
    exact map_add (evalE t (toPt g)) x y
  map_smul' r x := by
    ext T t g
    exact evalE_smul t (toPt g) r x

lemma phiC_app (V : Over S) (n : ℕ) (x : (Fin n → M) →₀ F.obj (op V)) {T : Over S} (t : T ⟶ V)
    (g : Fin n → APt (GB.overO S) M (op T)) :
    (phiC V n x).app t g = evalE t (toPt g) x := rfl

lemma phiC_res {V V' : Over S} (s : V' ⟶ V) (n : ℕ) (x : (Fin n → M) →₀ F.obj (op V)) :
    (phiC V n x).res s = phiC V' n (resF s x) := by
  ext T t g
  exact (evalE_resF s t _ x).symm

variable (hF : IsQCoh F)

include hF

/-- **Proposition 9.12, first assertion**: for any `V`,
`Cⁿ(𝔸(M)_B, F)(V) = (⨁_{(m₁,…,mₙ)} F X^{m₁}⋯X^{mₙ})(V)`. -/
def cochainEquivSec (V : Over S) (n : ℕ) : Cochain (Hm M S) F V n ≃ Sec F (Fin n → M) V :=
  (cochainEquivNC V n).trans (ncEquivSec hF V)

/-- **Proposition 9.12**, quasi-compact case: `Cⁿ(𝔸(M)_B, F)(V) = ⨁_{m ∈ Mⁿ} F_m(V)` as
`𝒪(V)`-modules. -/
theorem phiC_bijective (V : Over S) [CompactSpace V.left] (n : ℕ) :
    Function.Bijective (phiC (F := F) (M := M) V n) :=
  (cochainEquivNC V n).symm.bijective.comp (phiN_bijective_compact hF)

/-- **Proposition 9.12**, quasi-compact case, as an isomorphism. -/
def cochainLinearEquiv (V : Over S) [CompactSpace V.left] (n : ℕ) :
    ((Fin n → M) →₀ F.obj (op V)) ≃ₗ[(GB.overO S).obj (op V)] Cochain (Hm M S) F V n :=
  LinearEquiv.ofBijective (phiC V n) (phiC_bijective hF V n)

omit hF

lemma cochain_ext_affine (hF : IsQCoh F) {V : Over S} {n : ℕ} {c c' : Cochain (Hm M S) F V n}
    (h : ∀ (A : Over S) (a : A ⟶ V) [IsAffine A.left], c.res a = c'.res a) : c = c' := by
  apply (cochainEquivNC V n).injective
  refine NC.ext_affine hF fun A a _ => ?_
  ext T t b
  exact congrArg (fun k : Cochain (Hm M S) F A n => k.app t (ofPt b)) (h A a)

/-! ### Comodule structure on sections (Proposition 9.10 for `𝔸(M)`) -/

variable (A : HModule (Hm M S) F)

/-- The action of a point of `𝔸(M)`. -/
def asmul {T : Over S} (a : APt (GB.overO S) M (op T)) (x : F.obj (op T)) : F.obj (op T) :=
  A.smul (U := op T) a x

lemma asmul_add {T : Over S} (a : APt (GB.overO S) M (op T)) (x y : F.obj (op T)) :
    asmul A a (x + y) = asmul A a x + asmul A a y := A.smul_add _ _ _

lemma asmul_zero {T : Over S} (a : APt (GB.overO S) M (op T)) :
    asmul A a (0 : F.obj (op T)) = 0 := A.smul_zero _

lemma asmul_smul {T : Over S} (a : APt (GB.overO S) M (op T)) (r : (GB.overO S).obj (op T))
    (x : F.obj (op T)) : asmul A a (r • x) = r • asmul A a x := A.smul_smul _ _ _

lemma asmul_one {T : Over S} (x : F.obj (op T)) :
    asmul A (1 : APt (GB.overO S) M (op T)) x = x := A.one_smul x

lemma asmul_mul {T : Over S} (g h : APt (GB.overO S) M (op T)) (x : F.obj (op T)) :
    asmul A (g * h) x = asmul A g (asmul A h x) := A.mul_smul _ _ _

lemma asmul_map {T T' : Over S} (s : T' ⟶ T) (a : APt (GB.overO S) M (op T)) (x : F.obj (op T)) :
    F.map s.op (asmul A a x) = asmul A (APt.res s.op a) (F.map s.op x) := A.map_smul _ _ _

lemma asmul_sum {ι : Type*} {T : Over S} (g : APt (GB.overO S) M (op T)) (s : Finset ι)
    (f : ι → F.obj (op T)) : asmul A g (∑ i ∈ s, f i) = ∑ i ∈ s, asmul A g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using asmul_zero A g
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, asmul_add, ih]

/-- The orbit map `g ↦ g • v|_T`. -/
def orbit {V : Over S} (v : F.obj (op V)) : NC F M V where
  app t a := asmul A a (F.map t.op v)
  naturality s t a := by
    rw [asmul_map, ← F.map_comp, ← op_comp]

/-- `ρ`, on the sections over `V` quasi-compact (Proposition 9.10): `ρ(v) = ∑ ρ_m(v) X^m` is the
unique element such that `g • v = ∑ g(m) ρ_m(v)`. -/
def rhoV (hF : IsQCoh F) {V : Over S} [CompactSpace V.left] (v : F.obj (op V)) : M →₀ F.obj (op V) :=
  ((phiN_bijective_compact hF (N := M) (V := V)).2 (orbit A v)).choose

variable {A}

lemma smul_eq_evalE (hF : IsQCoh F) {V : Over S} [CompactSpace V.left] (v : F.obj (op V))
    {T : Over S} (t : T ⟶ V) (a : APt (GB.overO S) M (op T)) :
    asmul A a (F.map t.op v) = evalE t a (rhoV A hF v) :=
  (congrArg (fun c : NC F M V => c.app t a)
    ((phiN_bijective_compact hF (N := M) (V := V)).2 (orbit A v)).choose_spec).symm

lemma rhoV_eq (hF : IsQCoh F) {V : Over S} [CompactSpace V.left] (v : F.obj (op V))
    (x : M →₀ F.obj (op V))
    (h : ∀ {T : Over S} (t : T ⟶ V) (a : APt (GB.overO S) M (op T)),
      evalE t a x = asmul A a (F.map t.op v)) : rhoV A hF v = x := by
  refine (phiN_bijective_compact hF (N := M) (V := V)).1 ?_
  ext T t a
  change evalE t a (rhoV A hF v) = evalE t a x
  rw [h, smul_eq_evalE hF]

lemma evalE_sum {N : Type u} [AddCommMonoid N] {V T : Over S} (t : T ⟶ V)
    (a : APt (GB.overO S) N (op T)) (x : N →₀ F.obj (op V)) :
    evalE t a x = x.sum fun m f => a (Multiplicative.ofAdd m) • F.map t.op f := by
  rfl

/-- The left component `g` of a point of `𝔸(M × M)`. -/
def ptL {T : Over S} (a : APt (GB.overO S) (M × M) (op T)) : APt (GB.overO S) M (op T) :=
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M M))

/-- The right component `h` of a point of `𝔸(M × M)`. -/
def ptR {T : Over S} (a : APt (GB.overO S) (M × M) (op T)) : APt (GB.overO S) M (op T) :=
  a.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M M))

lemma pt_pair {T : Over S} (a : APt (GB.overO S) (M × M) (op T)) (m k : M) :
    a (Multiplicative.ofAdd (m, k)) =
      ptL a (Multiplicative.ofAdd m) * ptR a (Multiplicative.ofAdd k) := by
  rw [ptL, ptR, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
  congr 1
  change Multiplicative.ofAdd (m, k) = Multiplicative.ofAdd ((m, 0) + (0, k))
  simp

/-- **Proposition 9.10** for `𝔸(M)`, on sections over `V` quasi-compact: an action gives an
`𝒪(V)[M]`-comodule structure on `F(V)`, the two formulas being `g • v = ∑ g(m) ρ_m(v)`. -/
def coactionOf (hF : IsQCoh F) (A : HModule (Hm M S) F) (V : Over S) [CompactSpace V.left] :
    Hochschild.Coaction ((GB.overO S).obj (op V)) M (F.obj (op V)) where
  ρ :=
    { toFun := rhoV A hF
      map_add' := fun v w => by
        refine rhoV_eq hF _ _ fun t a => ?_
        rw [map_add, map_add, ← smul_eq_evalE, ← smul_eq_evalE, asmul_add]
      map_smul' := fun r v => by
        refine rhoV_eq hF _ _ fun t a => ?_
        rw [RingHom.id_apply, evalE_smul, ← smul_eq_evalE, F.map_smul, asmul_smul] }
  coassoc := fun v => by
    refine (phiN_bijective_compact hF (N := M × M) (V := V)).1 ?_
    ext T t a
    change evalE t a _ = evalE t a _
    set x := rhoV A hF v with hx
    have key1 : ∀ (k : M) (z : M →₀ F.obj (op V)),
        evalE t a (z.mapDomain fun m => (m, k)) =
          ptR a (Multiplicative.ofAdd k) • evalE t (ptL a) z := by
      intro k z
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq => simp only [Finsupp.mapDomain_add, map_add, smul_add, hp, hq]
      | single m f =>
        rw [Finsupp.mapDomain_single, evalE_single, evalE_single, pt_pair, mul_comm, mul_smul]
    have key2 : ∀ z : M →₀ F.obj (op V),
        evalE t a (z.mapDomain fun m => (m, m)) = evalE t (ptL a * ptR a) z := by
      intro z
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq => simp only [Finsupp.mapDomain_add, map_add, hp, hq]
      | single m f =>
        rw [Finsupp.mapDomain_single, evalE_single, evalE_single, pt_pair]
        rfl
    change evalE t a (x.sum fun k y => (rhoV A hF y).mapDomain fun m => (m, k)) =
      evalE t a (x.mapDomain fun m => (m, m))
    rw [key2, ← smul_eq_evalE hF v, Finsupp.sum, map_sum]
    simp only [key1, ← smul_eq_evalE hF]
    have hmul := asmul_mul A (ptL a) (ptR a) (F.map t.op v)
    refine Eq.trans ?_ hmul.symm
    rw [smul_eq_evalE hF v t (ptR a), evalE_sum, Finsupp.sum, asmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (asmul_smul A (ptL a) _ _).symm
  counit := fun v => by
    have h := smul_eq_evalE (A := A) hF v (𝟙 V) 1
    have h1 : asmul A (1 : APt (GB.overO S) M (op V)) (F.map (𝟙 V).op v) = v := by
      rw [op_id, F.map_id, asmul_one]
    rw [h1, evalE_sum] at h
    refine Eq.trans ?_ h.symm
    refine Finsupp.sum_congr fun m _ => ?_
    rw [op_id, F.map_id]
    change _ = (1 : (GB.overO S).obj (op V)) • _
    rw [one_smul]

end AM

end AlgMag.S9

/-! ### Proposition 9.12, the differential; Proposition 9.13, Remark 9.14 -/

namespace AlgMag.S9

open CategoryTheory Opposite AlgebraicGeometry

open scoped Classical

section Diff

variable {S : Scheme.{u}} {F : PMod (GB.overO S)} {M : Type u} [AddCommMonoid M]

open Hochschild in
private lemma toPt_cons {T : Over S} {n : ℕ} (g : Fin (n + 1) → APt (GB.overO S) M (op T)) (k : M)
    (m : Fin n → M) :
    toPt g (Multiplicative.ofAdd (consW k m)) =
      g 0 (Multiplicative.ofAdd k) * toPt (fun i => g i.succ) (Multiplicative.ofAdd m) := by
  simp only [toPt_ofAdd]
  rw [Fin.prod_univ_succ]
  simp [consW]

open Hochschild in
private lemma toPt_snoc {T : Over S} {n : ℕ} (g : Fin (n + 1) → APt (GB.overO S) M (op T))
    (m : Fin n → M) :
    toPt g (Multiplicative.ofAdd (snoc0 m)) =
      toPt (fun i => g i.castSucc) (Multiplicative.ofAdd m) := by
  simp only [toPt_ofAdd]
  rw [Fin.prod_univ_castSucc]
  simp only [snoc0, Fin.snoc_last, Fin.snoc_castSucc, ofAdd_zero, map_one, mul_one]

private lemma val_predAbove' {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (Fin.predAbove p i : ℕ) = if (p : ℕ) < i then (i : ℕ) - 1 else i := by
  unfold Fin.predAbove
  by_cases h : p.castSucc < i
  · have h' : (p : ℕ) < i := by simpa [Fin.lt_def] using h
    simp [h, h']
  · have h' : ¬ (p : ℕ) < i := by simpa [Fin.lt_def] using h
    simp [h, h']

private lemma val_succAbove' {n : ℕ} (i l : Fin n) :
    (i.castSucc.succAbove l : ℕ) = if (l : ℕ) < i then (l : ℕ) else l + 1 := by
  unfold Fin.succAbove
  by_cases h : (l : ℕ) < i
  · have h' : l.castSucc < i.castSucc := h
    rw [if_pos h', if_pos h]
    rfl
  · have h' : ¬ l.castSucc < i.castSucc := h
    rw [if_neg h', if_neg h]
    rfl

open Hochschild in
private lemma toPt_dup {T : Over S} {n : ℕ} (i : Fin n)
    (g : Fin (n + 1) → APt (GB.overO S) M (op T)) (m : Fin n → M) :
    toPt g (Multiplicative.ofAdd (dupWord i m)) =
      toPt (merge i g) (Multiplicative.ofAdd m) := by
  simp only [toPt_ofAdd, dupWord, Function.comp]
  rw [Fin.prod_univ_succAbove _ i.castSucc]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun l => merge i g l _) (Finset.mem_univ i)]
  have hp : ∀ l : Fin n, Fin.predAbove i (i.castSucc.succAbove l) = l := by
    intro l
    ext
    rw [val_predAbove', val_succAbove']
    split_ifs <;> omega
  simp only [hp]
  have hpi : Fin.predAbove i i.castSucc = i := by
    ext
    rw [val_predAbove']
    simp
  rw [hpi, ← mul_assoc]
  congr 1
  · have : i.castSucc.succAbove i = i.succ := by
      ext
      rw [val_succAbove']
      simp
    rw [this]
    simp only [merge, lt_irrefl, if_false, if_true]
    rfl
  · refine Finset.prod_congr rfl fun l hl => ?_
    have hne : (l : ℕ) ≠ i := fun h => (Finset.ne_of_mem_erase hl) (Fin.ext h)
    have e : merge i g l = g (i.castSucc.succAbove l) := by
      simp only [merge]
      by_cases h : (l : ℕ) < i
      · rw [if_pos h]
        congr 1
        ext
        rw [val_succAbove', if_pos h]
        rfl
      · rw [if_neg h, if_neg hne]
        congr 1
        ext
        rw [val_succAbove', if_neg h]
        rfl
    rw [e]

variable (hF : IsQCoh F) (A : HModule (Hm M S) F)

private lemma delta_phiC_single (V : Over S) [CompactSpace V.left] (n : ℕ) (m : Fin n → M)
    (f : F.obj (op V)) {T : Over S} (t : T ⟶ V) (g : Fin (n + 1) → APt (GB.overO S) M (op T)) :
    deltaFun A (phiC V n (Finsupp.single m f)) t g =
      evalE t (toPt g) ((coactionOf hF A V).delta n (Finsupp.single m f)) := by
  rw [Hochschild.Coaction.delta_single, map_add, map_add, map_sum, map_zsmul]
  have hmap : ∀ (z : M →₀ F.obj (op V)),
      evalE t (toPt g) (z.mapDomain fun k => Hochschild.consW k m) =
        toPt (fun i => g i.succ) (Multiplicative.ofAdd m) • evalE t (g 0) z := by
    intro z
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [Finsupp.mapDomain_add, map_add, smul_add, hp, hq]
    | single k y =>
      rw [Finsupp.mapDomain_single, evalE_single, evalE_single, toPt_cons, mul_comm, mul_smul]
  have h1 := smul_eq_evalE (A := A) hF f t (g 0)
  have h2 : A.smul (U := op T) (g 0) (toPt (fun i => g i.succ) (Multiplicative.ofAdd m) • F.map t.op f) =
      toPt (fun i => g i.succ) (Multiplicative.ofAdd m) • evalE t (g 0) (rhoV A hF f) := by
    rw [← h1]
    exact asmul_smul A (g 0) _ _
  simp only [deltaFun, phiC_app, evalE_single, map_zsmul, toPt_snoc, toPt_dup]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (h2.trans (hmap _).symm)
    (Finset.sum_congr rfl fun i _ => congrArg (fun y => ((-1 : ℤ) ^ ((i : ℕ) + 1)) • y)
      ((phiC_app V n _ t (merge i g)).trans (evalE_single t _ m f)))) rfl

/-- **Proposition 9.12, second assertion**: on quasi-compact objects, the differential of
Definition 9.4 is given by the formula
`f X^{m₁}⋯X^{mₙ} ↦ ρ(f) X^{m₁}⋯X^{mₙ} + ∑ (-1)^i f X^{m₁}⋯Δ(X^{mᵢ})⋯X^{mₙ} + (-1)^{n+1} f X^{m₁}⋯X^{mₙ} X^0`,
that is `AlgMag.Hochschild.Coaction.delta`. -/
theorem delta_phiC (V : Over S) [CompactSpace V.left] (n : ℕ) (x : (Fin n → M) →₀ F.obj (op V)) :
    delta A (phiC V n x) = phiC V (n + 1) ((coactionOf hF A V).delta n x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single m f =>
    ext T t g
    exact delta_phiC_single hF A V n m f t g

lemma phiC_eq (B : Over S) (n : ℕ) (y : (Fin n → M) →₀ F.obj (op B)) :
    phiC B n y = (cochainEquivNC B n).symm (phiN y) := rfl

lemma equivNC_res_symm {V B : Over S} {n : ℕ} (c' : NC F (Fin n → M) V) (a : B ⟶ V) :
    cochainEquivNC B n (((cochainEquivNC V n).symm c').res a) = c'.res a := by
  ext T t b
  exact congrArg (c'.app (t ≫ a)) (toPt_ofPt b)

/-- A cochain over an affine scheme is its section. -/
lemma phiC_sec {V : Over S} {n : ℕ} (c : Cochain (Hm M S) F V n) {B : Over S} (a : B ⟶ V)
    [IsAffine B.left] : phiC B n ((cochainEquivSec hF V n c).val B a) = c.res a := by
  rw [phiC_eq, Equiv.symm_apply_eq]
  exact secOf_val_phiN_res hF (cochainEquivNC V n c) a

lemma res_symm_sec {V : Over S} {n : ℕ} (τ : Sec F (Fin n → M) V) {B : Over S} (a : B ⟶ V)
    [IsAffine B.left] : ((cochainEquivSec hF V n).symm τ).res a = phiC B n (τ.val B a) := by
  rw [phiC_eq, Equiv.eq_symm_apply]
  exact (equivNC_res_symm _ a).trans (ofSec_res hF τ a)

include hF

/-- **Proposition 9.13 and Remark 9.14**: over any `V`, with no assumption on `V`, every cocycle in
degree `n + 1` is a coboundary. -/
theorem exists_delta_eq (V : Over S) (n : ℕ) (c : Cochain (Hm M S) F V (n + 1))
    (hc : delta A c = 0) : ∃ e, delta A e = c := by
  let σ := cochainEquivSec hF V (n + 1) c
  have hx : ∀ (B : Over S) (a : B ⟶ V) [IsAffine B.left],
      (coactionOf hF A B).delta (n + 1) (σ.val B a) = 0 := by
    intro B a _
    refine (phiC_bijective hF B (n + 2)).1 ?_
    rw [← delta_phiC, phiC_sec, map_zero, delta_res, hc]
    rfl
  let τ : Sec F (Fin n → M) V :=
    { val := fun B a _ =>
        ((-1 : ℤ) ^ (n + 1)) • Hochschild.lastCoeff M (F.obj (op B)) ((GB.overO S).obj (op B)) n
          (σ.val B a)
      compat := fun B B' s a _ _ => by
        rw [σ.compat]
        ext u
        change ((-1 : ℤ) ^ (n + 1)) • F.map s.op _ = F.map s.op (((-1 : ℤ) ^ (n + 1)) • _)
        rw [map_zsmul]
        rfl }
  refine ⟨(cochainEquivSec hF V n).symm τ, cochain_ext_affine hF fun B a _ => ?_⟩
  rw [← delta_res, res_symm_sec, delta_phiC hF A, ← phiC_sec hF c a]
  congr 1
  exact ((coactionOf hF A B).eq_delta_of_cocycle n _ (hx B a)).symm

/-- **Proposition 9.13**: `H¹_monoid(𝔸(M)_B, F) = 0`, for any base and any object `V`. -/
theorem H1_subsingleton (V : Over S) : Subsingleton (Hn A V 1) :=
  Hn_subsingleton_of A V 0 (exists_delta_eq hF A V 0)

/-- **Remark 9.14** (the paper's conjecture, proved): `Hⁿ_monoid(𝔸(M)_B, F) = 0` for all `n ≥ 1`, for
any base and any object `V`. -/
theorem Hn_subsingleton (V : Over S) (n : ℕ) : Subsingleton (Hn A V (n + 1)) :=
  Hn_subsingleton_of A V n (exists_delta_eq hF A V n)

end Diff

end AlgMag.S9

/-! ### Proposition 9.11 -/

namespace AlgMag.S9

open CategoryTheory Opposite AlgebraicGeometry

open scoped Classical

section P911

variable {S : Scheme.{u}} {F : PMod (GB.overO S)} {M : Type u} [AddCommMonoid M]

variable (F M) in
/-- **Proposition 9.11**, corrected wording: a family `(ρ_m)_{m ∈ M}` in `Hom_𝒪(F, F)` of orthogonal
idempotents, such that `∑ ρ_m = Id` and, **at each section** over an affine scheme, only finitely
many of the `ρ_m` are nonzero. The printed "only finitely many of the `(ρ_m)` are nonzero locally" is
false: see `AlgMag.Hochschild.regular_comp_ne_zero`. -/
structure Decomp where
  /-- `ρ_m`, on `T` -/
  comp : M → ∀ T : Over S, F.obj (op T) →ₗ[(GB.overO S).obj (op T)] F.obj (op T)
  natural : ∀ (m : M) {T T' : Over S} (s : T' ⟶ T) (v : F.obj (op T)),
    comp m T' (F.map s.op v) = F.map s.op (comp m T v)
  finite : ∀ (T : Over S) [IsAffine T.left] (v : F.obj (op T)),
    (Function.support fun m => comp m T v).Finite
  same : ∀ (m : M) (T : Over S) (v : F.obj (op T)), comp m T (comp m T v) = comp m T v
  ne : ∀ (m k : M) (T : Over S) (v : F.obj (op T)), k ≠ m → comp m T (comp k T v) = 0
  sum : ∀ (T : Over S) [IsAffine T.left] (v : F.obj (op T)), ∑ᶠ m, comp m T v = v

variable (hF : IsQCoh F) (A : HModule (Hm M S) F)

lemma orbit_res {V V' : Over S} (s : V' ⟶ V) (v : F.obj (op V)) :
    (orbit A v).res s = orbit A (F.map s.op v) := by
  ext T t a
  change asmul A a (F.map (t ≫ s).op v) = asmul A a (F.map t.op (F.map s.op v))
  rw [op_comp, F.map_comp]

/-- The component `ρ_m(v)` of `v ∈ F(T)`, for any `T`: glued from the affine schemes over `T`. -/
def compOf (m : M) {T : Over S} (v : F.obj (op T)) : F.obj (op T) :=
  coef hF (secOf hF (orbit A v)) m

lemma map_compOf (m : M) {T E : Over S} (e : E ⟶ T) [IsAffine E.left] (v : F.obj (op T)) :
    F.map e.op (compOf hF A m v) = rhoV A hF (F.map e.op v) m := by
  rw [compOf, coef_spec]
  have : (secOf hF (orbit A v)).val E e = rhoV A hF (F.map e.op v) := by
    refine (phiN_bijective hF).1 ?_
    rw [secOf_val_phiN_res, orbit_res]
    exact ((phiN_bijective_compact hF (N := M) (V := E)).2 (orbit A _)).choose_spec.symm
  rw [this]

lemma compOf_affine (m : M) {T : Over S} [IsAffine T.left] (v : F.obj (op T)) :
    compOf hF A m v = rhoV A hF v m := by
  have := map_compOf hF A m (𝟙 T) v
  rw [op_id, F.map_id, F.map_id] at this
  exact this

lemma rhoV_comp (m k : M) {E : Over S} [IsAffine E.left] (w : F.obj (op E)) :
    rhoV A hF (rhoV A hF w k) m = open Classical in if m = k then rhoV A hF w k else 0 :=
  (coactionOf hF A E).comp_comp m k w

/-- **Proposition 9.11**, from the action to the family. -/
def decompOf : Decomp F M where
  comp m T :=
    { toFun := compOf hF A m
      map_add' := fun v w => by
        refine sep_affine hF T fun E e _ => ?_
        rw [map_compOf, map_add, map_add, map_compOf, map_compOf]
        exact congrArg (fun z : M →₀ F.obj (op E) => z m)
          ((coactionOf hF A E).ρ.map_add _ _)
      map_smul' := fun r v => by
        refine sep_affine hF T fun E e _ => ?_
        rw [RingHom.id_apply, map_compOf, F.map_smul, F.map_smul, map_compOf]
        exact congrArg (fun z : M →₀ F.obj (op E) => z m)
          ((coactionOf hF A E).ρ.map_smul _ _) }
  natural m {T T'} s v := by
    change compOf hF A m _ = F.map s.op (compOf hF A m v)
    refine sep_affine hF T' fun E e _ => ?_
    have h := map_compOf hF A m (e ≫ s) v
    rw [op_comp, F.map_comp, F.map_comp] at h
    rw [map_compOf hF A m e]
    exact h.symm
  finite T _ v := by
    have hs : (Function.support fun m => compOf hF A m v) ⊆ (rhoV A hF v).support := by
      intro m hm
      have : compOf hF A m v ≠ 0 := hm
      rw [compOf_affine] at this
      simpa using this
    exact (Finset.finite_toSet _).subset hs
  same m T v := by
    change compOf hF A m (compOf hF A m v) = compOf hF A m v
    refine sep_affine hF T fun E e _ => ?_
    rw [map_compOf, map_compOf, rhoV_comp]
    simp
  ne m k T v h := by
    change compOf hF A m (compOf hF A k v) = 0
    refine sep_affine hF T fun E e _ => ?_
    rw [map_compOf, map_compOf, rhoV_comp, map_zero, if_neg (Ne.symm h)]
  sum T _ v := by
    change ∑ᶠ m, compOf hF A m v = v
    simp only [compOf_affine]
    have hs : (Function.support fun m => rhoV A hF v m) ⊆ (rhoV A hF v).support := by
      intro m hm
      simpa using hm
    rw [finsum_eq_sum_of_support_subset _ hs]
    exact (coactionOf hF A T).counit v

/-- The family `ρ_m` at quasi-compact objects is also finite at each section. -/
theorem decompOf_finite_of_compact {T : Over S} [CompactSpace T.left] (v : F.obj (op T)) :
    (Function.support fun m => compOf hF A m v).Finite :=
  coef_finite hF _

variable (D : Decomp F M)

/-- The element `∑ ρ_m(w) X^m`, for `w` a section over an affine scheme. -/
def tval {E : Over S} [IsAffine E.left] (w : F.obj (op E)) : M →₀ F.obj (op E) :=
  Finsupp.ofSupportFinite (fun m => D.comp m E w) (D.finite E w)

@[simp] lemma tval_apply {E : Over S} [IsAffine E.left] (w : F.obj (op E)) (m : M) :
    tval D w m = D.comp m E w := rfl

lemma tval_res {E E' : Over S} [IsAffine E.left] [IsAffine E'.left] (s : E' ⟶ E)
    (w : F.obj (op E)) : tval D (F.map s.op w) = resF s (tval D w) := by
  ext m
  exact D.natural m s w

/-- The section of `⨁ F_m` of `v ∈ F(T)`. -/
def tsec {T : Over S} (v : F.obj (op T)) : Sec F M T where
  val E e _ := tval D (F.map e.op v)
  compat E E' s e _ _ := by
    rw [op_comp, F.map_comp, tval_res]

include hF in
/-- **Proposition 9.11**, from the family to the action. -/
def dsmul {T : Over S} (g : APt (GB.overO S) M (op T)) (v : F.obj (op T)) : F.obj (op T) :=
  (ofSec hF (tsec D v)).app (𝟙 T) g

lemma map_dsmul {T E : Over S} (e : E ⟶ T) [IsAffine E.left] (g : APt (GB.overO S) M (op T))
    (v : F.obj (op T)) :
    F.map e.op (dsmul hF D g v) = evalE (𝟙 E) (APt.res e.op g) (tval D (F.map e.op v)) := by
  rw [dsmul, ofSec_app_spec]
  change evalE _ _ (tval D (F.map (e ≫ 𝟙 T).op v)) = _
  rw [Category.comp_id]

/-- `evalE` at the identity. -/
lemma evalE_id {E : Over S} (a : APt (GB.overO S) M (op E)) (x : M →₀ F.obj (op E)) :
    evalE (𝟙 E) a x = x.sum fun m f => a (Multiplicative.ofAdd m) • f := by
  rw [evalE_sum]
  refine Finsupp.sum_congr fun m _ => ?_
  rw [op_id, F.map_id]

lemma comp_evalE_tval (m : M) {E : Over S} [IsAffine E.left] (a : APt (GB.overO S) M (op E))
    (w : F.obj (op E)) :
    D.comp m E (evalE (𝟙 E) a (tval D w)) = a (Multiplicative.ofAdd m) • D.comp m E w := by
  rw [evalE_id, Finsupp.sum, map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single m]
  · simp only [tval_apply, D.same]
  · intro k _ hk
    simp only [tval_apply, D.ne m k E w hk, smul_zero]
  · intro hm
    have : D.comp m E w = 0 := by simpa using hm
    simp [this]

lemma evalE_tval_mul {E : Over S} [IsAffine E.left] (g h : APt (GB.overO S) M (op E))
    (w : F.obj (op E)) :
    evalE (𝟙 E) (g * h) (tval D w) = evalE (𝟙 E) g (tval D (evalE (𝟙 E) h (tval D w))) := by
  have hs : (tval D (evalE (𝟙 E) h (tval D w))).support ⊆ (tval D w).support := by
    intro m hm
    rw [Finsupp.mem_support_iff] at hm ⊢
    intro h0
    apply hm
    change D.comp m E _ = 0
    rw [comp_evalE_tval]
    have : D.comp m E w = 0 := h0
    rw [this, smul_zero]
  rw [evalE_id, evalE_id, Finsupp.sum, Finsupp.sum, Finset.sum_subset hs]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [tval_apply D (evalE _ _ _), comp_evalE_tval, smul_smul]
    rfl
  · intro m _ hm
    rw [Finsupp.notMem_support_iff.mp hm, smul_zero]

lemma dsmul_one {T : Over S} (v : F.obj (op T)) :
    dsmul hF D (1 : APt (GB.overO S) M (op T)) v = v := by
  refine sep_affine hF T fun E e _ => ?_
  rw [map_dsmul, evalE_id]
  have h1 : APt.res e.op (1 : APt (GB.overO S) M (op T)) = 1 := by
    refine MonoidHom.ext fun p => ?_
    simp
  rw [h1]
  have hs : (Function.support fun m => D.comp m E (F.map e.op v)) ⊆
      (tval D (F.map e.op v)).support := by
    intro m hm
    simpa using hm
  conv_rhs => rw [← D.sum E (F.map e.op v), finsum_eq_sum_of_support_subset _ hs]
  refine Finset.sum_congr rfl fun m _ => ?_
  change (1 : (GB.overO S).obj (op E)) • _ = _
  rw [one_smul]
  rfl

lemma dsmul_mul {T : Over S} (g h : APt (GB.overO S) M (op T)) (v : F.obj (op T)) :
    dsmul hF D (g * h) v = dsmul hF D g (dsmul hF D h v) := by
  refine sep_affine hF T fun E e _ => ?_
  rw [map_dsmul, map_dsmul, map_dsmul, APt.res_mul, evalE_tval_mul]

lemma dsmul_add {T : Over S} (g : APt (GB.overO S) M (op T)) (v w : F.obj (op T)) :
    dsmul hF D g (v + w) = dsmul hF D g v + dsmul hF D g w := by
  refine sep_affine hF T fun E e _ => ?_
  have h : tval D (F.map e.op (v + w)) = tval D (F.map e.op v) + tval D (F.map e.op w) := by
    ext m
    rw [map_add]
    exact (D.comp m E).map_add _ _
  rw [map_add (F.map e.op) (dsmul hF D g v), map_dsmul, map_dsmul, map_dsmul, h, map_add]

lemma dsmul_smul {T : Over S} (g : APt (GB.overO S) M (op T)) (a : (GB.overO S).obj (op T))
    (v : F.obj (op T)) : dsmul hF D g (a • v) = a • dsmul hF D g v := by
  refine sep_affine hF T fun E e _ => ?_
  rw [F.map_smul, map_dsmul, map_dsmul, F.map_smul]
  have : tval D (((GB.overO S).map e.op).hom a • F.map e.op v) =
      ((GB.overO S).map e.op).hom a • tval D (F.map e.op v) := by
    ext m
    exact (D.comp m E).map_smul _ _
  rw [this, evalE_smul]
  have e1 : ((GB.overO S).map (𝟙 E).op).hom (((GB.overO S).map e.op).hom a) =
      ((GB.overO S).map e.op).hom a := by
    rw [op_id, (GB.overO S).map_id]
    rfl
  rw [e1]

lemma dsmul_map {T T' : Over S} (s : T' ⟶ T) (g : APt (GB.overO S) M (op T)) (v : F.obj (op T)) :
    F.map s.op (dsmul hF D g v) = dsmul hF D (APt.res s.op g) (F.map s.op v) := by
  refine sep_affine hF T' fun E e _ => ?_
  rw [← F.map_comp, ← op_comp, map_dsmul, map_dsmul, op_comp, F.map_comp, APt.res_comp]

/-- **Proposition 9.11**, the action of the family. -/
def actionOf : HModule (Hm M S) F where
  smul {U} g v := dsmul hF D (T := unop U) g v
  one_smul {U} v := dsmul_one hF D (T := unop U) v
  mul_smul {U} g h v := dsmul_mul hF D (T := unop U) g h v
  smul_add {U} g v w := dsmul_add hF D (T := unop U) g v w
  smul_smul {U} g a v := dsmul_smul hF D (T := unop U) g a v
  map_smul {U V} f g v := dsmul_map hF D f.unop (T := unop U) g v

lemma actionOf_smul {T : Over S} (g : APt (GB.overO S) M (op T)) (v : F.obj (op T)) :
    asmul (actionOf hF D) g v = dsmul hF D g v := rfl

lemma evalE_tval_eq {E T : Over S} [IsAffine E.left] (t : T ⟶ E) (a : APt (GB.overO S) M (op T))
    (w : F.obj (op E)) : evalE t a (tval D w) = dsmul hF D a (F.map t.op w) := by
  refine sep_affine hF T fun E' e _ => ?_
  rw [← evalE_res, map_dsmul, ← F.map_comp, ← op_comp, tval_res, evalE_resF, Category.id_comp]

lemma rhoV_actionOf {E : Over S} [IsAffine E.left] (w : F.obj (op E)) :
    rhoV (actionOf hF D) hF w = tval D w :=
  rhoV_eq hF w _ fun t a => evalE_tval_eq hF D t a w

lemma dsmul_decompOf {T : Over S} (g : APt (GB.overO S) M (op T)) (x : F.obj (op T)) :
    dsmul hF (decompOf hF A) g x = asmul A g x := by
  refine sep_affine hF T fun E e _ => ?_
  have : tval (decompOf hF A) (F.map e.op x) = rhoV A hF (F.map e.op x) := by
    ext m
    exact compOf_affine hF A m _
  rw [map_dsmul, this, asmul_map, ← smul_eq_evalE, op_id, F.map_id]

/-- **Proposition 9.11** (corrected wording): `𝔸(M)_B`-`𝒪_B`-module structures on a quasi-coherent
`F` correspond to families `(ρ_m)` of orthogonal idempotents of sum the identity, finitely many
nonzero at each section. `M` is any commutative monoid and `B` any scheme. -/
def hModuleEquivDecomp : HModule (Hm M S) F ≃ Decomp F M where
  toFun := decompOf hF
  invFun := actionOf hF
  left_inv A := by
    exact HModule.ext' fun U g x => dsmul_decompOf hF A (T := unop U) g x
  right_inv D := by
    cases D with
    | mk comp natural finite same ne sum =>
      have : (fun (m : M) (T : Over S) => (decompOf hF (actionOf hF
          ⟨comp, natural, finite, same, ne, sum⟩)).comp m T) = comp := by
        funext m T
        refine LinearMap.ext fun v => ?_
        refine sep_affine hF T fun E e _ => ?_
        change F.map e.op (compOf hF _ m v) = _
        rw [map_compOf, rhoV_actionOf]
        exact natural m e v
      simp only [decompOf] at this ⊢
      congr

end P911

end AlgMag.S9

/-! ### Complements: Propositions 9.1, 9.10 for `𝔸(M)`, and the structure sheaf -/

namespace AlgMag.S9

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

open scoped Classical

section Compl

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {F : PMod (GB.overO S)}

lemma isAffine_prod (T X : Over S) [IsAffine T.left] [IsAffineHom X.hom] :
    IsAffine (T ⊗ X).left := by
  change IsAffine (Limits.pullback T.hom X.hom)
  exact isAffine_of_isAffineHom (Limits.pullback.fst T.hom X.hom)

/-- **Proposition 9.1**, on an affine scheme `T` over `S`, for `f : X → S` affine: the restriction
`F(T) → (f_* f^* F)(T) = F(T ×_S X)` is the base change along `Γ(T) → Γ(T ×_S X)`; that is,
`f_* f^* F = F ⊗_{𝒪} 𝒜`. -/
theorem IsQCoh.base_change_prod (hF : IsQCoh F) (T X : Over S) [IsAffine T.left]
    [IsAffineHom X.hom] :
    haveI := isAffine_prod T X
    IsBC ((GB.overO S).map (fst T X).op).hom (F.map (fst T X).op) (F.map_smul (fst T X).op) :=
  haveI := isAffine_prod T X
  hF.base_change (fst T X)

/-- **Proposition 9.10** for `H = 𝔸(M)_S`, in the form `F → f_* f^* F`. -/
def hModuleEquivCoactionA (M : Type u) [AddCommMonoid M] :
    HModule (Hm M S) F ≃ CoactionPush (F := F) (GB.ptsRepr M S) :=
  hModuleEquivCoaction (GB.ptsRepr M S)

variable (S) in
/-- The structure sheaf `𝒪`, as an `𝒪`-module. -/
def structureMod : PMod (GB.overO S) where
  obj U := (GB.overO S).obj U
  grp U := inferInstance
  mod U := inferInstance
  map f := ((GB.overO S).map f).hom.toAddMonoidHom
  map_smul f r x := map_mul ((GB.overO S).map f).hom r x
  map_id U x := by simp
  map_comp f g x := by simp

/-- `𝔸¹(T) = Γ(T)`: monoid maps from `ℕ` are their value at `1`. -/
def ptsNatEquiv (T : Over S) :
    APt (GB.overO S) (ULift.{u} ℕ) (op T) ≃ (GB.overO S).obj (op T) where
  toFun a := a (Multiplicative.ofAdd (ULift.up 1))
  invFun r :=
    { toFun := fun m => r ^ (Multiplicative.toAdd m).down
      map_one' := pow_zero r
      map_mul' := fun a b => pow_add r _ _ }
  left_inv a := by
    refine MonoidHom.ext fun m => ?_
    obtain ⟨⟨k⟩, rfl⟩ := Multiplicative.ofAdd.surjective m
    change a (Multiplicative.ofAdd (ULift.up 1)) ^ k = a (Multiplicative.ofAdd (ULift.up k))
    induction k with
    | zero => exact (pow_zero _).trans (a.map_one).symm
    | succ k ih =>
      rw [pow_succ, ih, ← map_mul]
      rfl
  right_inv r := pow_one r

/-- `𝒪` is quasi-coherent. -/
theorem isQCoh_structureMod : IsQCoh (structureMod S) where
  sheaf := by
    let e : yoneda.obj (GB.A (ULift.{u} ℕ) S) ≅ (structureMod S).toPresheaf :=
      NatIso.ofComponents (fun T => Equiv.toIso ((GB.pts (unop T)).trans (ptsNatEquiv (unop T))))
        (by
          intro T T' f
          ext x
          change ptsNatEquiv _ (GB.pts _ (f.unop ≫ x)) = _
          rw [GB.pts_comp]
          rfl)
    exact Presieve.isSheaf_iso _ e (GB.isSheaf_yoneda_over (GB.A (ULift.{u} ℕ) S))
  base_change {T T'} s _ _ := by
    letI := ((GB.overO S).map s.op).hom.toAlgebra
    exact IsBaseChange.linearMap ((GB.overO S).obj (op T)) ((GB.overO S).obj (op T'))

end Compl

end AlgMag.S9

