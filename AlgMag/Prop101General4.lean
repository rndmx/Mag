/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Prop101General3

/-!
# Proposition 10.1 for a general affine flat `G`: the action of `G` on `Y`, `Z` and on lifts

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), proof of Proposition 10.1 (p. 169).
Setting: `S = Spec R` affine, `G = Spec H`, `X'` affine. An `S`-action of `G` on a scheme `W` over `S`
is given on points: a point `g : H → E` of `G` and a point `z : Spec E → W` over the same point of
`S` give `g · z`, naturally in `E`, unital and associative. Postcomposition with `g_Y` sends a lift
of `(a, b)` to a lift of `(g_Y a, g_Z b)`, and commutes with the difference of lifts.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts

attribute [local instance] Stacks.Smooth.moduleMulOpposite

variable {R : Type u} [CommRing R] {Hh : Type u} [CommRing Hh] [HopfAlgebra R Hh]

/-- A point of `G` over a point `σ` of `S`, multiplied: `g * g'`. -/
noncomputable def convR {E : Type u} [CommRing E] (g g' : Hh →+* E)
    (h : g.comp (algebraMap R Hh) = g'.comp (algebraMap R Hh)) : Hh →+* E :=
  letI := (g.comp (algebraMap R Hh)).toAlgebra
  let G : Hh →ₐ[R] E := { g with commutes' := fun r => rfl }
  let G' : Hh →ₐ[R] E := { g' with commutes' := fun r => (RingHom.congr_fun h r).symm }
  (WithConv.ofConv (WithConv.toConv G * WithConv.toConv G')).toRingHom

/-- The unit point `σ ∘ ε`. -/
noncomputable def unitR (Hh : Type u) [CommRing Hh] [HopfAlgebra R Hh] {E : Type u} [CommRing E] (σ : R →+* E) : Hh →+* E :=
  σ.comp (Bialgebra.counitAlgHom R Hh).toRingHom

lemma unitR_alg {E : Type u} [CommRing E] (σ : R →+* E) : (unitR Hh σ).comp (algebraMap R Hh) = σ :=
  RingHom.ext fun r => by simp [unitR]

variable (R Hh) in
/-- **An `S`-action of `G = Spec H` on `W`**, on points over `S = Spec R`. -/
structure GAct (W : Scheme.{u}) (πW : W ⟶ Spec (CommRingCat.of R)) where
  act : ∀ {E : Type u} [CommRing E] (g : Hh →+* E) (z : Spec (CommRingCat.of E) ⟶ W),
    z ≫ πW = sp (g.comp (algebraMap R Hh)) → (Spec (CommRingCat.of E) ⟶ W)
  over : ∀ {E : Type u} [CommRing E] (g : Hh →+* E) (z : Spec (CommRingCat.of E) ⟶ W)
    (hz : z ≫ πW = sp (g.comp (algebraMap R Hh))),
    act g z hz ≫ πW = sp (g.comp (algebraMap R Hh))
  nat : ∀ {E E' : Type u} [CommRing E] [CommRing E'] (r : E →+* E') (g : Hh →+* E)
    (z : Spec (CommRingCat.of E) ⟶ W) (hz : z ≫ πW = sp (g.comp (algebraMap R Hh)))
    (hz' : (sp r ≫ z) ≫ πW = sp ((r.comp g).comp (algebraMap R Hh))),
    sp r ≫ act g z hz = act (r.comp g) (sp r ≫ z) hz'
  one : ∀ {E : Type u} [CommRing E] (σ : R →+* E) (z : Spec (CommRingCat.of E) ⟶ W)
    (hz : z ≫ πW = sp ((unitR Hh σ).comp (algebraMap R Hh))),
    act (unitR Hh σ) z hz = z
  mul : ∀ {E : Type u} [CommRing E] (g g' : Hh →+* E)
    (h : g.comp (algebraMap R Hh) = g'.comp (algebraMap R Hh)) (z : Spec (CommRingCat.of E) ⟶ W)
    (hz : z ≫ πW = sp ((convR g g' h).comp (algebraMap R Hh)))
    (hz' : z ≫ πW = sp (g'.comp (algebraMap R Hh)))
    (hz'' : act g' z hz' ≫ πW = sp (g.comp (algebraMap R Hh))),
    act (convR g g' h) z hz = act g (act g' z hz') hz''

namespace GAct

variable {W : Scheme.{u}} {πW : W ⟶ Spec (CommRingCat.of R)} (α : GAct R Hh W πW)

lemma act_congr {E : Type u} [CommRing E] {g g' : Hh →+* E} {z z' : Spec (CommRingCat.of E) ⟶ W}
    (hg : g = g') (hzz : z = z') (hz : z ≫ πW = sp (g.comp (algebraMap R Hh)))
    (hz' : z' ≫ πW = sp (g'.comp (algebraMap R Hh))) : α.act g z hz = α.act g' z' hz' := by
  subst hg hzz; rfl

lemma hz_pull {E E' : Type u} [CommRing E] [CommRing E'] (r : E →+* E') (g : Hh →+* E)
    (z : Spec (CommRingCat.of E) ⟶ W) (hz : z ≫ πW = sp (g.comp (algebraMap R Hh))) :
    (sp r ≫ z) ≫ πW = sp ((r.comp g).comp (algebraMap R Hh)) := by
  rw [Category.assoc, hz, ← sp_comp, RingHom.comp_assoc]

/-- Naturality, with the proof obligation discharged. -/
lemma nat' {E E' : Type u} [CommRing E] [CommRing E'] (r : E →+* E') (g : Hh →+* E)
    (z : Spec (CommRingCat.of E) ⟶ W) (hz : z ≫ πW = sp (g.comp (algebraMap R Hh))) :
    sp r ≫ α.act g z hz = α.act (r.comp g) (sp r ≫ z) (hz_pull r g z hz) :=
  α.nat r g z hz _

end GAct

/-! ### Postcomposition with `g_Y` on lifts -/

section Post

variable {A₁ A : Type u} [CommRing A₁] [CommRing A] {φ : A₁ →+* A} (hs : Function.Surjective φ)
  [Module A (RingHom.ker φ)]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
  {Y Z : Scheme.{u}} {f : Y ⟶ Z} {πZ : Z ⟶ Spec (CommRingCat.of R)}
  (αY : GAct R Hh Y (f ≫ πZ)) (αZ : GAct R Hh Z πZ)
  (hf : ∀ {E : Type u} [CommRing E] (g : Hh →+* E) (z : Spec (CommRingCat.of E) ⟶ Y)
    (hz : z ≫ f ≫ πZ = sp (g.comp (algebraMap R Hh))) (hz' : (z ≫ f) ≫ πZ = sp (g.comp (algebraMap R Hh))),
    αY.act g z hz ≫ f = αZ.act g (z ≫ f) hz')
  (p₁ : Hh →+* A₁)
  {a : Spec (CommRingCat.of A) ⟶ Y} {b : Spec (CommRingCat.of A₁) ⟶ Z}
  (hbS : b ≫ πZ = sp (p₁.comp (algebraMap R Hh)))
  {P : Type u} [AddCommGroup P]

include hbS in
lemma Pl_over (x : Pl φ f a b P) :
    x.1 ≫ f ≫ πZ = sp (((cs A₁ P).comp p₁).comp (algebraMap R Hh)) := by
  rw [← Category.assoc, x.2.2, Category.assoc, hbS, ← sp_comp, RingHom.comp_assoc]

include hbS in
lemma a_over (w : a ≫ f = sp φ ≫ b) :
    a ≫ f ≫ πZ = sp ((φ.comp p₁).comp (algebraMap R Hh)) := by
  rw [← Category.assoc, w, Category.assoc, hbS, ← sp_comp, RingHom.comp_assoc]

/-- `g_Y ∘ x` on lifts. -/
noncomputable def Pl.post (w : a ≫ f = sp φ ≫ b) (x : Pl φ f a b P) :
    Pl φ f (αY.act (φ.comp p₁) a (a_over p₁ hbS w)) (αZ.act p₁ b hbS) P :=
  ⟨αY.act ((cs A₁ P).comp p₁) x.1 (Pl_over p₁ hbS x), by
    rw [αY.nat', αY.nat']
    refine αY.act_congr ?_ x.2.1 _ _
    rw [← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc], by
    rw [hf _ _ _ (by rw [Category.assoc]; exact Pl_over p₁ hbS x), αZ.nat']
    exact αZ.act_congr rfl x.2.2 _ _⟩

lemma Pl.post_val (w : a ≫ f = sp φ ≫ b) (x : Pl φ f a b P) :
    (Pl.post αY αZ hf p₁ hbS w x).1 = αY.act ((cs A₁ P).comp p₁) x.1 (Pl_over p₁ hbS x) := rfl

variable {N N' : Type u} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
  (p₀ : Hh →+* A) (haS : a ≫ f ≫ πZ = sp (p₀.comp (algebraMap R Hh)))

include haS in
lemma L_over (x : L f a N P) :
    x.1 ≫ f ≫ πZ = sp (((cs (Sq A N) P).comp ((sInl N).comp p₀)).comp (algebraMap R Hh)) := by
  rw [← Category.assoc, x.2.2]
  simp only [Category.assoc]
  rw [haS, ← sp_comp, ← sp_comp, ← RingHom.comp_assoc, mr_cs]

/-- `g_Y ∘ ℓ` on `Hom(a^*Ω, N)`. -/
noncomputable def L.post (x : L f a N P) : L f (αY.act p₀ a haS) N P :=
  ⟨αY.act ((cs (Sq A N) P).comp ((sInl N).comp p₀)) x.1 (L_over p₀ haS x), by
    rw [αY.nat', αY.nat']
    refine αY.act_congr ?_ x.2.1 _ _
    rw [← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc]
    congr 1, by
    rw [hf _ _ _ (by rw [Category.assoc]; exact L_over p₀ haS x),
      hf _ _ _ (by rw [Category.assoc]; exact haS), αZ.nat', αZ.nat']
    refine αZ.act_congr ?_ ?_ _ _
    · rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, mr_cs]
    · rw [x.2.2]⟩

lemma L.post_val (x : L f a N P) :
    (L.post αY αZ hf p₀ haS x).1 = αY.act ((cs (Sq A N) P).comp ((sInl N).comp p₀)) x.1 (L_over p₀ haS x) :=
  rfl

lemma L.post_map (u : N →ₗ[A] N') (x : L f a N P) :
    (L.post αY αZ hf p₀ haS x).map u = L.post αY αZ hf p₀ haS (x.map u) := by
  refine L.ext' ?_
  rw [L.map_val, L.post_val, L.post_val, αY.nat']
  refine αY.act_congr ?_ rfl _ _
  rw [← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc]
  congr 1
  rw [← RingHom.comp_assoc, sMap_inl]

lemma L.post_add (x y : L f a N P) :
    L.post αY αZ hf p₀ haS (x + y) = L.post αY αZ hf p₀ haS x + L.post αY αZ hf p₀ haS y := by
  have e : L.pair (L.post αY αZ hf p₀ haS x) (L.post αY αZ hf p₀ haS y) =
      L.post αY αZ hf p₀ haS (L.pair x y) := by
    refine L.pair_eq ?_ ?_
    · rw [L.post_map, L.map_fst_pair]
    · rw [L.post_map, L.map_snd_pair]
  rw [L.add_def, L.add_def, e, L.post_map]

include hf hbS in
lemma w_post (w : a ≫ f = sp φ ≫ b) :
    αY.act (φ.comp p₁) a (a_over p₁ hbS w) ≫ f = sp φ ≫ αZ.act p₁ b hbS := by
  rw [hf _ _ _ (by rw [Category.assoc]; exact a_over p₁ hbS w), αZ.nat']
  exact αZ.act_congr rfl w _ _

include hs hN hq hbS in
lemma gD_over (w : a ≫ f = sp φ ≫ b) (x y : Pl φ f a b P) :
    gD hs x y ≫ f ≫ πZ = sp (((cs (Dd φ) P).comp ((dΔ φ).comp p₁)).comp (algebraMap R Hh)) := by
  rw [← Category.assoc, gD_f, Category.assoc, Category.assoc, hbS, ← sp_comp, ← sp_comp,
    ← RingHom.comp_assoc, mr_cs]

/-- **The difference commutes with `g_Y`.** -/
theorem diffL_post (w : a ≫ f = sp φ ≫ b) (x y : Pl φ f a b P) :
    diffL hs hN hq (w_post αY αZ hf p₁ hbS w) (Pl.post αY αZ hf p₁ hbS w x) (Pl.post αY αZ hf p₁ hbS w y) =
      L.post αY αZ hf (φ.comp p₁) (a_over p₁ hbS w) (diffL hs hN hq w x y) := by
  refine L.ext' ?_
  have e : gD hs (Pl.post αY αZ hf p₁ hbS w x) (Pl.post αY αZ hf p₁ hbS w y) =
      αY.act ((cs (Dd φ) P).comp ((dΔ φ).comp p₁)) (gD hs x y) (gD_over hs hN hq p₁ hbS w x y) := by
    refine gD_ext hs ?_ ?_
    · rw [gD_1, Pl.post_val, αY.nat']
      refine αY.act_congr ?_ (gD_1 hs x y).symm _ _
      rw [← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc]
      rfl
    · rw [gD_2, Pl.post_val, αY.nat']
      refine αY.act_congr ?_ (gD_2 hs x y).symm _ _
      rw [← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc]
      rfl
  rw [diffL_val, e, αY.nat', L.post_val]
  refine αY.act_congr ?_ (diffL_val hs hN hq w x y).symm _ _
  rw [← RingHom.comp_assoc, mr_cs, RingHom.comp_assoc]
  congr 1
  rw [← RingHom.comp_assoc, qq_Δ, RingHom.comp_assoc]

end Post

end AlgMag.Sec10Printed
