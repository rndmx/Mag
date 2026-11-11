/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Prop101General6

/-!
# Proposition 10.1 for a general affine flat `G`: the cocycle and the invariant lift

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Proposition 10.1 and its proof (pp. 168–169).
Setting: `S = Spec R` affine, `G = Spec H` with `H` a commutative Hopf `R`-algebra, `X' = Spec A₁`
affine (agreed erratum), `X = Spec A`, `Y`, `Z` schemes over `S` with `S`-actions of `G`.

Given a lift `α`, the printed proof takes the 1-cocycle `c(g) = g · α - α` of `G` with values in
`F = p_* Hom(a^*Ω_{Y/Z}, C_{X/X'})`. It is determined by its universal value
`c₀ = u · α_H - α_H ∈ F(H)`, `u = id_H ∈ G(H)`, which satisfies the Hochschild cocycle identity
`Δ^* c₀ = i₁^* c₀ + i₁ · i₂^* c₀` in `F(H ⊗ H)` (`cocycle_identity`). The hypothesis `H¹ = 0` is stated
directly in this Hochschild form (`HochschildH1Vanish`): every such `c` is `u · v_H - v_H` for some
`v ∈ F(S)`. Then `β = α - v` is invariant under `G(T)` for every `T = Spec B` (`exists_invariant_PB`).
-/

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts AlgMag.Prop101General Algebra.TensorProduct

attribute [local instance] Stacks.Smooth.moduleMulOpposite

variable {R : Type u} [CommRing R] {Hh : Type u} [CommRing Hh] [HopfAlgebra R Hh]

/-- `i₁ · i₂ = Δ` in `G(H ⊗ H)`. -/
lemma cmul_inl_inr :
    cmul (includeLeft (R := R) (S := R) (A := Hh) (B := Hh)) (includeRight (R := R) (A := Hh) (B := Hh)) =
      Bialgebra.comulAlgHom R Hh := by
  rw [cmul, AlgHom.convMul_def]
  simp only [WithConv.ofConv_toConv]
  have : (lmul' R).comp (Algebra.TensorProduct.map (includeLeft (R := R) (S := R) (A := Hh) (B := Hh))
      (includeRight (R := R) (A := Hh) (B := Hh))) = AlgHom.id R (Hh ⊗[R] Hh) := by
    refine Algebra.TensorProduct.ext ?_ ?_ <;> ext <;> simp
  rw [← AlgHom.comp_assoc, this, AlgHom.id_comp]

lemma ofId_comp {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (e : B →ₐ[R] B') :
    e.comp (Algebra.ofId R B) = Algebra.ofId R B' :=
  AlgHom.ext fun r => by simp

variable {A₁ A : Type u} [CommRing A₁] [CommRing A] [Algebra R A₁] [Algebra R A] {φ : A₁ →ₐ[R] A}
  [IsThick φ]
  {Y Z : Scheme.{u}} {f : Y ⟶ Z} {a : Spec (CommRingCat.of A) ⟶ Y} {b : Spec (CommRingCat.of A₁) ⟶ Z}
  (c₁ : Coact (R := R) Hh A₁) (c₀ : Coact (R := R) Hh A)
  (hφρ : (Algebra.TensorProduct.map (AlgHom.id R Hh) φ).comp c₁.ρ = c₀.ρ.comp φ)
  {πZ : Z ⟶ Spec (CommRingCat.of R)}
  (αY : GAct R Hh Y (f ≫ πZ)) (αZ : GAct R Hh Z πZ)
  (hf : ∀ {E : Type u} [CommRing E] (g : Hh →+* E) (z : Spec (CommRingCat.of E) ⟶ Y)
    (hz : z ≫ f ≫ πZ = sp (g.comp (algebraMap R Hh))) (hz' : (z ≫ f) ≫ πZ = sp (g.comp (algebraMap R Hh))),
    αY.act g z hz ≫ f = αZ.act g (z ≫ f) hz')
  (hbS : b ≫ πZ = sp (algebraMap R A₁))
  (w : a ≫ f = sp φ.toRingHom ≫ b)
  (haE : ∀ {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B)
    (hz : aB (R := R) (B := B) a ≫ f ≫ πZ =
      sp (((includeLeft (R := R) (S := R) (A := B) (B := A)).toRingHom.comp g.toRingHom).comp (algebraMap R Hh))),
    sp (tau c₀ g).toRingHom ≫ aB (R := R) a =
      αY.act ((includeLeft (R := R) (S := R) (A := B) (B := A)).toRingHom.comp g.toRingHom) (aB a) hz)
  (hbE : ∀ {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B)
    (hz : bB (R := R) (B := B) b ≫ πZ = sp ((pt₁ (A₁ := A₁) g).comp (algebraMap R Hh))),
    sp (tau c₁ g).toRingHom ≫ bB (R := R) b = αZ.act (pt₁ g) (bB b) hz)

/-- **`H¹(G, F) = 0`, Hochschild form**: every `c ∈ F(H)` with `Δ^* c = i₁^* c + i₁ · i₂^* c` in
`F(H ⊗ H)` is a coboundary `u · v_H - v_H`, `v ∈ F(S)`. -/
def HochschildH1Vanish : Prop :=
  ∀ c : FB φ Hh f a,
    pullF (Bialgebra.comulAlgHom R Hh) c =
        pullF (includeLeft (R := R) (S := R) (A := Hh) (B := Hh)) c +
          gactF c₁ c₀ hφρ αY αZ hf hbS w haE (includeLeft (R := R) (S := R) (A := Hh) (B := Hh))
            (pullF (includeRight (R := R) (A := Hh) (B := Hh)) c) →
      ∃ v : FB φ R f a,
        c = gactF c₁ c₀ hφρ αY αZ hf hbS w haE (AlgHom.id R Hh) (pullF (Algebra.ofId R Hh) v) -
          pullF (Algebra.ofId R Hh) v

lemma diffB_add {B : Type u} [CommRing B] [Algebra R B] (x y z : PB φ B f a b) :
    diffB B w x y + diffB B w y z = diffB B w x z :=
  diffL_add _ _ _ _ x y z

lemma diffB_self {B : Type u} [CommRing B] [Algebra R B] (x : PB φ B f a b) : diffB B w x x = 0 :=
  diffL_self _ _ _ _ x

lemma diffB_swap {B : Type u} [CommRing B] [Algebra R B] (x y : PB φ B f a b) :
    diffB B w y x = - diffB B w x y := by
  have := diffB_add w x y x
  rw [diffB_self] at this
  exact eq_neg_of_add_eq_zero_right this

/-- The universal value of the cocycle: `c₀ = u · α_H - α_H`. -/
noncomputable def cocyc (α : PB φ R f a b) : FB φ Hh f a :=
  diffB Hh w (gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE (AlgHom.id R Hh) (pullP (Algebra.ofId R Hh) α))
    (pullP (Algebra.ofId R Hh) α)

/-- `c(g) = g · α_T - α_T` is pulled back from `c₀` along `g`. -/
lemma pull_cocyc {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B) (α : PB φ R f a b) :
    pullF g (cocyc c₁ c₀ hφρ αY αZ hf hbS w haE hbE α) =
      diffB B w (gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE g (pullP (Algebra.ofId R B) α))
        (pullP (Algebra.ofId R B) α) := by
  rw [cocyc, ← diffB_pull w, pullP_gact, pullP_comp, ofId_comp, AlgHom.comp_id]

/-- **The Hochschild cocycle identity** for `c₀`. -/
theorem cocycle_identity (α : PB φ R f a b) :
    pullF (Bialgebra.comulAlgHom R Hh) (cocyc c₁ c₀ hφρ αY αZ hf hbS w haE hbE α) =
      pullF (includeLeft (R := R) (S := R) (A := Hh) (B := Hh)) (cocyc c₁ c₀ hφρ αY αZ hf hbS w haE hbE α) +
        gactF c₁ c₀ hφρ αY αZ hf hbS w haE (includeLeft (R := R) (S := R) (A := Hh) (B := Hh))
          (pullF (includeRight (R := R) (A := Hh) (B := Hh)) (cocyc c₁ c₀ hφρ αY αZ hf hbS w haE hbE α)) := by
  rw [pull_cocyc, pull_cocyc, pull_cocyc, ← diffB_gact, ← cmul_inl_inr, gact_mul, add_comm, diffB_add]

/-- **The end of the printed proof**: under `H¹ = 0`, `β = α - v` is invariant under `G(T)` for every
`T = Spec B`. -/
theorem exists_invariant_PB (hH1 : HochschildH1Vanish c₁ c₀ hφρ αY αZ hf hbS w haE) (α : PB φ R f a b) :
    ∃ β : PB φ R f a b, ∀ {B : Type u} [CommRing B] [Algebra R B] (g : Hh →ₐ[R] B),
      gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE g (pullP (Algebra.ofId R B) β) = pullP (Algebra.ofId R B) β := by
  obtain ⟨v, hv⟩ := hH1 _ (cocycle_identity c₁ c₀ hφρ αY αZ hf hbS w haE hbE α)
  obtain ⟨β, hβ⟩ : ∃ β, diffB R w β α = -v := ⟨_, diffL_addL _ _ _ _ α (-v)⟩
  have hαβ : diffB R w α β = v := by rw [diffB_swap, hβ, neg_neg]
  let η := Algebra.ofId R Hh
  let u := AlgHom.id R Hh
  have hu : gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE u (pullP η β) = pullP η β := by
    refine Pl_eq_of_diffL (psB_surj φ Hh) (psB_N φ Hh) (psB_sq φ Hh) (wB f a b w) _ _ ?_
    change diffB Hh w _ _ = 0
    have s₁ := diffB_add w (gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE u (pullP η β))
      (gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE u (pullP η α)) (pullP η β)
    have s₂ := diffB_add w (gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE u (pullP η α)) (pullP η α) (pullP η β)
    rw [← s₁, ← s₂, diffB_gact, diffB_pull, diffB_pull, hαβ]
    change gactF c₁ c₀ hφρ αY αZ hf hbS w haE u (pullF η (diffB R w β α)) +
      (cocyc c₁ c₀ hφρ αY αZ hf hbS w haE hbE α + pullF η v) = 0
    rw [hβ, hv]
    have hn : pullF η (-v) = - pullF η v := map_neg (AddMonoidHom.mk' (pullF (φ := φ) (f := f) (a := a) η)
      (pullF_add η)) v
    have hg : gactF c₁ c₀ hφρ αY αZ hf hbS w haE u (- pullF η v) =
        - gactF c₁ c₀ hφρ αY αZ hf hbS w haE u (pullF η v) :=
      map_neg (AddMonoidHom.mk' (gactF c₁ c₀ hφρ αY αZ hf hbS w haE u) (gactF_add _ _ _ _ _ _ _ _ _ u)) _
    rw [hn, hg]
    abel
  refine ⟨β, fun {B} _ _ g => ?_⟩
  have e₁ : pullP (Algebra.ofId R B) β = pullP g (pullP η β) := by rw [pullP_comp, ofId_comp]
  have e₂ := pullP_gact c₁ c₀ hφρ αY αZ hf hbS w haE hbE g u (pullP η β)
  rw [hu, AlgHom.comp_id] at e₂
  rw [e₁, ← e₂]

end AlgMag.Sec10Printed
