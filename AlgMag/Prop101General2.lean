/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Prop101General

/-!
# Proposition 10.1 for a general affine flat `G`: functoriality of the torsor

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), proof of Proposition 10.1 (p. 169).
Setting of this series of files: `S = Spec R` affine and `X'` affine (agreed erratum). A morphism of
first order thickenings `(s₁, s) : (A₁ → A) → (A₁' → A')` pulls lifts back and pulls back
`Hom(a^*Ω, C)`; the difference of lifts commutes with these pullbacks, and the pullback on `F` is
additive. Applied to `B ⊗ A₁ → B' ⊗ A₁` this is the functoriality of the torsor in `T = Spec B`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts

attribute [local instance] Stacks.Smooth.moduleMulOpposite

section PullSq

variable {A A' : Type u} [CommRing A] [CommRing A'] (s : A →+* A')
  {N N' : Type u} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A' N']

/-- `A[N] → A'[N']` along a semilinear `σ`. -/
noncomputable def sqM (σ : N →+ N') (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n) :
    Sq A N →+* Sq A' N' :=
  Stacks.Smooth.sqZeroMap s σ hσ

variable {s}

@[simp] lemma sqM_fst (σ : N →+ N') (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n) (x : Sq A N) :
    (sqM s σ hσ x).fst = s x.fst :=
  Stacks.Smooth.sqZeroMap_fst _ _ _ x
@[simp] lemma sqM_snd (σ : N →+ N') (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n) (x : Sq A N) :
    (sqM s σ hσ x).snd = σ x.snd :=
  Stacks.Smooth.sqZeroMap_snd _ _ _ x

lemma sFst_sqM (σ : N →+ N') (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n) :
    (sFst N').comp (sqM s σ hσ) = s.comp (sFst N) :=
  RingHom.ext fun _ => by simp

lemma sqM_inl (σ : N →+ N') (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n) :
    (sqM s σ hσ).comp (sInl N) = (sInl N').comp s :=
  RingHom.ext fun _ => sq_ext (by simp) (by simp)

lemma sqM_sMap {N₁ N₁' : Type u} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₁'] [Module A' N₁']
    (σ : N →+ N') (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n)
    (σ₁ : N₁ →+ N₁') (hσ₁ : ∀ (r : A) (n : N₁), σ₁ (r • n) = s r • σ₁ n)
    (u : N →ₗ[A] N₁) (u' : N' →ₗ[A'] N₁') (h : ∀ n, u' (σ n) = σ₁ (u n)) :
    (sMap u').comp (sqM s σ hσ) = (sqM s σ₁ hσ₁).comp (sMap u) :=
  RingHom.ext fun _ => sq_ext (by simp) (by simp [h])

end PullSq

section PullL

variable {A A' : Type u} [CommRing A] [CommRing A'] {s : A →+* A'}
  {N N' : Type u} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A' N']
  {Y Z : Scheme.{u}} {f : Y ⟶ Z} {a : Spec (CommRingCat.of A) ⟶ Y} {a' : Spec (CommRingCat.of A') ⟶ Y}
  {P : Type u} [AddCommGroup P]

/-- Pullback of `Hom(a^*Ω, N)` along `(s, σ)`. -/
noncomputable def L.pull (ha : sp s ≫ a = a') (σ : N →+ N')
    (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n) (x : L f a N P) : L f a' N' P :=
  ⟨sp (mr P (sqM s σ hσ)) ≫ x.1, by
    rw [sp_mr_assoc, sFst_sqM, ← sp_mr_assoc, x.2.1, sp_cs_map, ha], by
    rw [Category.assoc, x.2.2, sp_mr_assoc, sqM_inl, ← sp_mr_assoc, sp_cs_map, ← ha, Category.assoc]⟩

lemma L.pull_val (ha : sp s ≫ a = a') (σ : N →+ N')
    (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n) (x : L f a N P) :
    (L.pull ha σ hσ x).1 = sp (mr P (sqM s σ hσ)) ≫ x.1 := rfl

lemma L.pull_map {N₁ N₁' : Type u} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₁'] [Module A' N₁']
    (ha : sp s ≫ a = a') (σ : N →+ N') (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n)
    (σ₁ : N₁ →+ N₁') (hσ₁ : ∀ (r : A) (n : N₁), σ₁ (r • n) = s r • σ₁ n)
    (u : N →ₗ[A] N₁) (u' : N' →ₗ[A'] N₁') (h : ∀ n, u' (σ n) = σ₁ (u n)) (x : L f a N P) :
    (L.pull ha σ hσ x).map u' = L.pull ha σ₁ hσ₁ (x.map u) := by
  refine L.ext' ?_
  rw [L.map_val, L.pull_val, L.pull_val, L.map_val, sp_mr_assoc, sqM_sMap σ hσ σ₁ hσ₁ u u' h,
    ← sp_mr_assoc]

/-- The pullback of `F` is additive. -/
lemma L.pull_add (ha : sp s ≫ a = a') (σ : N →+ N') (hσ : ∀ (r : A) (n : N), σ (r • n) = s r • σ n)
    (x y : L f a N P) :
    L.pull ha σ hσ (x + y) = L.pull ha σ hσ x + L.pull ha σ hσ y := by
  let σ₂ : N × N →+ N' × N' := σ.prodMap σ
  have hσ₂ : ∀ (r : A) (n : N × N), σ₂ (r • n) = s r • σ₂ n :=
    fun r n => Prod.ext (hσ r n.1) (hσ r n.2)
  have e : L.pair (L.pull ha σ hσ x) (L.pull ha σ hσ y) = L.pull ha σ₂ hσ₂ (L.pair x y) := by
    refine L.pair_eq ?_ ?_
    · rw [L.pull_map ha σ₂ hσ₂ σ hσ (LinearMap.fst A N N) (LinearMap.fst A' N' N') (fun _ => rfl),
        L.map_fst_pair]
    · rw [L.pull_map ha σ₂ hσ₂ σ hσ (LinearMap.snd A N N) (LinearMap.snd A' N' N') (fun _ => rfl),
        L.map_snd_pair]
  rw [L.add_def, L.add_def, e,
    L.pull_map ha σ₂ hσ₂ σ hσ (LinearMap.fst A N N + LinearMap.snd A N N)
      (LinearMap.fst A' N' N' + LinearMap.snd A' N' N') (fun n => (map_add σ n.1 n.2).symm)]

end PullL

section PullPl

variable {A₁ A A₁' A' : Type u} [CommRing A₁] [CommRing A] [CommRing A₁'] [CommRing A']
  {φ : A₁ →+* A} {φ' : A₁' →+* A'} (hs : Function.Surjective φ) (hs' : Function.Surjective φ')
  [Module A (RingHom.ker φ)] [Module A' (RingHom.ker φ')]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
  (hN' : ∀ (x : A₁') (n : RingHom.ker φ'), ((φ' x • n : RingHom.ker φ') : A₁') = x * n)
  (hq' : ∀ x y, φ' x = 0 → φ' y = 0 → x * y = 0)
  {s₁ : A₁ →+* A₁'} {s : A →+* A'} (hc : φ'.comp s₁ = s.comp φ)
  {Y Z : Scheme.{u}} {f : Y ⟶ Z} {a : Spec (CommRingCat.of A) ⟶ Y} {a' : Spec (CommRingCat.of A') ⟶ Y}
  {b : Spec (CommRingCat.of A₁) ⟶ Z} {b' : Spec (CommRingCat.of A₁') ⟶ Z}
  (ha : sp s ≫ a = a') (hb : sp s₁ ≫ b = b')
  {P : Type u} [AddCommGroup P]

/-- `s₁` on the ideals. -/
noncomputable def kσ : RingHom.ker φ →+ RingHom.ker φ' where
  toFun n := ⟨s₁ (n : A₁), by
    rw [RingHom.mem_ker, ← RingHom.comp_apply, hc, RingHom.comp_apply, RingHom.mem_ker.1 n.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero s₁)
  map_add' n n' := Subtype.ext (map_add s₁ (n : A₁) (n' : A₁))

include hs hN hN' in
lemma kσ_smul (r : A) (n : RingHom.ker φ) : kσ hc (r • n) = s r • kσ hc n := by
  obtain ⟨x, rfl⟩ := hs r
  refine Subtype.ext ?_
  have e : s (φ x) = φ' (s₁ x) := by rw [← RingHom.comp_apply, ← hc, RingHom.comp_apply]
  change s₁ ((φ x • n : RingHom.ker φ) : A₁) = ((s (φ x) • kσ hc n : RingHom.ker φ') : A₁')
  rw [hN, e, hN', map_mul]
  rfl

/-- Pullback of lifts. -/
noncomputable def Pl.pull (x : Pl φ f a b P) : Pl φ' f a' b' P :=
  ⟨sp (mr P s₁) ≫ x.1, by
    rw [sp_mr_assoc, hc, ← sp_mr_assoc, x.2.1, sp_cs_map, ha], by
    rw [Category.assoc, x.2.2, sp_cs_map, hb]⟩

lemma Pl.pull_val (x : Pl φ f a b P) : (Pl.pull hc ha hb x).1 = sp (mr P s₁) ≫ x.1 := rfl

/-- `s₁ × s₁` on `A₁ ×_A A₁`. -/
noncomputable def dM : Dd φ →+* Dd φ' :=
  RingHom.codRestrict ((s₁.comp (d₁ φ)).prod (s₁.comp (d₂ φ))) (Dd φ') (fun z => by
    change φ' (s₁ (d₁ φ z)) = φ' (s₁ (d₂ φ z))
    rw [← RingHom.comp_apply φ', hc, RingHom.comp_apply, ← RingHom.comp_apply φ' s₁, hc,
      RingHom.comp_apply]
    exact congrArg s z.2)

lemma d₁_dM : (d₁ φ').comp (dM hc) = s₁.comp (d₁ φ) := rfl
lemma d₂_dM : (d₂ φ').comp (dM hc) = s₁.comp (d₂ φ) := rfl

lemma qq_dM : (qq hN' hq').comp (dM hc) =
    (sqM s (kσ hc) (kσ_smul hs hN hN' hc)).comp (qq hN hq) :=
  RingHom.ext fun z => sq_ext (by
      rw [RingHom.comp_apply, RingHom.comp_apply, qq_fst, sqM_fst, qq_fst]
      change φ' (s₁ (d₁ φ z)) = s (φ (d₁ φ z))
      rw [← RingHom.comp_apply φ', hc, RingHom.comp_apply]) (by
      rw [RingHom.comp_apply, RingHom.comp_apply, qq_snd, sqM_snd, qq_snd]
      refine Subtype.ext ?_
      change s₁ (d₁ φ z) - s₁ (d₂ φ z) = s₁ (d₁ φ z - d₂ φ z)
      rw [map_sub])

/-- **The difference commutes with pullback** (functoriality of the printed torsor). -/
theorem diffL_pull (w : a ≫ f = sp φ ≫ b) (w' : a' ≫ f = sp φ' ≫ b') (x y : Pl φ f a b P) :
    diffL hs' hN' hq' w' (Pl.pull hc ha hb x) (Pl.pull hc ha hb y) =
      L.pull ha (kσ hc) (kσ_smul hs hN hN' hc) (diffL hs hN hq w x y) := by
  refine L.ext' ?_
  have e : gD hs' (Pl.pull hc ha hb x) (Pl.pull hc ha hb y) = sp (mr P (dM hc)) ≫ gD hs x y := by
    refine gD_ext hs' ?_ ?_
    · rw [gD_1, sp_mr_assoc, d₁_dM, ← sp_mr_assoc, gD_1]; rfl
    · rw [gD_2, sp_mr_assoc, d₂_dM, ← sp_mr_assoc, gD_2]; rfl
  rw [diffL_val, e, sp_mr_assoc, qq_dM hs hN hq hN' hq', ← sp_mr_assoc, L.pull_val, diffL_val]

end PullPl

end AlgMag.Sec10Printed

