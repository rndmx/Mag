/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge3Desc

/-!
# The sheaf property of `famPMod`

`fam_isSheafFor`: a sieve containing, over each affine, a finite flat surjective family of affines.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace AlgMag.B3

open AlgMag.S9B AlgMag.S9 AlgebraicGeometry.Space

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace Bs S hS Bsp}
  {𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB}

/-- `R` contains, over each affine, a finite flat surjective family of affines. -/
def Cov {T : SB Bsp} (R : Sieve T) : Prop :=
  ∀ {A : SB Bsp} (_ : IsAffine A.left) (a : A ⟶ T), ∃ (I : Type (u + 1)) (_ : Finite I)
    (Ai : I → SB Bsp) (t : ∀ i, Ai i ⟶ A), (∀ i, IsAffine (Ai i).left) ∧
      (∀ i, Flat (SB.Hom.left (t i))) ∧ (∀ x : A.left, ∃ i, x ∈ Set.range (SB.Hom.left (t i))) ∧
      ∀ i, R.arrows (t i ≫ a)

section
variable {T : SB Bsp} {R : Sieve T} (x : ∀ {Y : SB Bsp} (f : Y ⟶ T), R.arrows f → Fam 𝓜 Y)
  (hx : ∀ {Y Y' : SB Bsp} (f : Y ⟶ T) (hf : R.arrows f) (g : Y' ⟶ Y),
    Fam.res g (x f hf) = x (g ≫ f) (R.downward_closed hf g))

include hx

lemma x_key {Y Y' : SB Bsp} (hY : IsAffine Y.left) (hY' : IsAffine Y'.left) (f : Y ⟶ T)
    (hf : R.arrows f) (g : Y' ⟶ Y) {V : AffineEtale Bs S hS Bsp} (w : Y ⟶ cB V) (w' : Y' ⟶ cB V)
    (hc : w' ≫ cBm (𝟙 V) = g ≫ w) :
    ρ 𝓜 g (𝟙 V) hc ((x f hf).val hY (𝟙 Y) w) =
      (x (g ≫ f) (R.downward_closed hf g)).val hY' (𝟙 Y') w' := by
  rw [(x f hf).compat hY' hY (𝟙 Y) w w' g (𝟙 V) hc, ← hx f hf g]
  change (x f hf).val hY' (g ≫ 𝟙 Y) w' = (x f hf).val hY' (𝟙 Y' ≫ g) w'
  rw [Category.comp_id, Category.id_comp]

omit hx in
lemma x_congr {Y : SB Bsp} {f f' : Y ⟶ T} (e : f = f') (hf : R.arrows f) (hf' : R.arrows f') :
    x f hf = x f' hf' := by subst e; rfl

/-- The reading of `z` over `R` is the given family. -/
def Char {A : SB Bsp} (a : A ⟶ T) {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) (z : Dv 𝓜 v) : Prop :=
  ∀ (A' : SB Bsp) (hA' : IsAffine A'.left) (b : A' ⟶ A) (h : R.arrows (b ≫ a)),
    ρ 𝓜 b (𝟙 V) (sq1 b v) z = (x (b ≫ a) h).val hA' (𝟙 A') (b ≫ v)

theorem char_unique (hR : Cov R) {A : SB Bsp} (hA : IsAffine A.left) (a : A ⟶ T)
    {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) {z z' : Dv 𝓜 v} (h : Char x a v z)
    (h' : Char x a v z') : z = z' := by
  obtain ⟨I, hI, Ai, t, hAi, hfl, hsu, hin⟩ := hR hA a
  obtain ⟨y, -, hu⟩ := FDesc 𝓜 hA v Ai t hAi hfl hsu
    (fun i => (x (t i ≫ a) (hin i)).val (hAi i) (𝟙 _) (t i ≫ v))
    (fun i j A'' hA'' p q e v'' h1 h2 => by
      rw [x_key x hx (hAi i) hA'' _ _ p _ v'' h1, x_key x hx (hAi j) hA'' _ _ q _ v'' h2]
      have e' : p ≫ t i ≫ a = q ≫ t j ≫ a := by
        rw [← Category.assoc, ← Category.assoc, e]
      rw [x_congr x e' _ (e' ▸ R.downward_closed (hin i) p)])
  rw [hu z fun i => h _ (hAi i) (t i) (hin i), hu z' fun i => h' _ (hAi i) (t i) (hin i)]

theorem char_exists (hR : Cov R) {A : SB Bsp} (hA : IsAffine A.left) (a : A ⟶ T)
    {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V) : ∃ z : Dv 𝓜 v, Char x a v z := by
  obtain ⟨I, hI, Ai, t, hAi, hfl, hsu, hin⟩ := hR hA a
  obtain ⟨z, hz, -⟩ := FDesc 𝓜 hA v Ai t hAi hfl hsu
    (fun i => (x (t i ≫ a) (hin i)).val (hAi i) (𝟙 _) (t i ≫ v))
    (fun i j A'' hA'' p q e v'' h1 h2 => by
      rw [x_key x hx (hAi i) hA'' _ _ p _ v'' h1, x_key x hx (hAi j) hA'' _ _ q _ v'' h2]
      have e' : p ≫ t i ≫ a = q ≫ t j ≫ a := by
        rw [← Category.assoc, ← Category.assoc, e]
      rw [x_congr x e' _ (e' ▸ R.downward_closed (hin i) p)])
  refine ⟨z, fun A' hA' b h => ?_⟩
  have hw := fun i => sb_isPullback b (t i)
  obtain ⟨y, hy1, hy2⟩ := FDesc 𝓜 hA' (b ≫ v) (fun i => sbPb b (t i)) (fun i => sbFst b (t i))
    (fun i => isAffine_of_isPullback (hw i) hA' (hAi i) hA)
    (fun i => flat_of_isPullback (hw i) (hfl i))
    (fun p => by
      obtain ⟨i, y, hy⟩ := hsu (SB.Hom.left b p)
      obtain ⟨w, h1, -⟩ := exists_pt_of_isPullback (hw i) p y hy.symm
      exact ⟨i, w, h1⟩)
    (fun i => (x (sbFst b (t i) ≫ b ≫ a) (R.downward_closed h _)).val
      (isAffine_of_isPullback (hw i) hA' (hAi i) hA) (𝟙 _) (sbFst b (t i) ≫ b ≫ v))
    (fun i j A'' hA'' p q e v'' h1 h2 => by
      have hAW := fun i => isAffine_of_isPullback (hw i) hA' (hAi i) hA
      rw [x_key x hx (hAW i) hA'' _ _ p _ v'' h1, x_key x hx (hAW j) hA'' _ _ q _ v'' h2]
      have e' : p ≫ sbFst b (t i) ≫ b ≫ a = q ≫ sbFst b (t j) ≫ b ≫ a := by
        rw [← Category.assoc, e, Category.assoc]
      rw [x_congr x e' _ (e' ▸ R.downward_closed (R.downward_closed h _) p)])
  refine (hy2 _ fun i => ?_).trans (hy2 _ fun i => ?_).symm
  · have hAW := isAffine_of_isPullback (hw i) hA' (hAi i) hA
    rw [ρ_comp]
    have e0 : sbFst b (t i) ≫ b = sbSnd b (t i) ≫ t i := (hw i).w
    have h3 := congrArg (ρ 𝓜 (sbSnd b (t i)) (𝟙 V)
      (show (sbFst b (t i) ≫ b ≫ v) ≫ cBm (𝟙 V) = _ by
        rw [sq1, ← Category.assoc, e0, Category.assoc])) (hz i)
    rw [ρ_comp] at h3
    refine (ρ_congr 𝓜 e0 rfl _ _ z).trans (h3.trans ?_)
    rw [x_key x hx (hAi i) hAW _ _ (sbSnd b (t i)) _ _ _]
    have e' : sbSnd b (t i) ≫ t i ≫ a = sbFst b (t i) ≫ b ≫ a := by
      rw [← Category.assoc, ← e0, Category.assoc]
    rw [x_congr x e' _ (R.downward_closed h _)]
  · have hAW := isAffine_of_isPullback (hw i) hA' (hAi i) hA
    exact x_key x hx hA' hAW (b ≫ a) h (sbFst b (t i)) (b ≫ v) _ (sq1 _ _)

/-- **Gluing compatible families.** -/
theorem fam_glue (hR : Cov R) : ∃! w : Fam 𝓜 T, ∀ {Y : SB Bsp} (f : Y ⟶ T) (hf : R.arrows f),
    Fam.res f w = x f hf := by
  let val : ∀ {A : SB Bsp} (_ : IsAffine A.left) (_ : A ⟶ T) {V : AffineEtale Bs S hS Bsp}
      (v : A ⟶ cB V), Dv 𝓜 v := fun hA a _ v => (char_exists x hx hR hA a v).choose
  have hval : ∀ {A : SB Bsp} (hA : IsAffine A.left) (a : A ⟶ T) {V : AffineEtale Bs S hS Bsp}
      (v : A ⟶ cB V), Char x a v (val hA a v) := fun hA a _ v =>
    (char_exists x hx hR hA a v).choose_spec
  let w : Fam 𝓜 T := ⟨val, fun {A' A} hA' hA a {V' V} v v' s φ hc => by
    refine char_unique x hx hR hA' (s ≫ a) v' (fun A'' hA'' b' h => ?_) (hval hA' (s ≫ a) v')
    rw [ρ_comp]
    have ha : (b' ≫ s) ≫ a = b' ≫ s ≫ a := Category.assoc _ _ _
    have h' : R.arrows ((b' ≫ s) ≫ a) := ha ▸ h
    have h0 := hval hA a v A'' hA'' (b' ≫ s) h'
    have hc' : (b' ≫ v') ≫ cBm φ = 𝟙 A'' ≫ (b' ≫ s) ≫ v := by
      rw [Category.assoc, hc, Category.id_comp, Category.assoc]
    have h1 := congrArg (ρ 𝓜 (𝟙 A'') φ hc') h0
    rw [ρ_comp, (x _ h').compat hA'' hA'' (𝟙 A'') _ (b' ≫ v') (𝟙 A'') φ hc'] at h1
    have e1 := x_congr x ha h' h
    refine Eq.trans (ρ_congr 𝓜 (by simp) (by simp) _ _ _) (h1.trans ?_)
    rw [Category.id_comp]
    exact congrArg (fun X : Fam 𝓜 A'' => X.val hA'' (𝟙 A'') (b' ≫ v')) e1⟩
  refine ⟨w, fun {Y} f hf => Fam.ext fun {A} hA a {V} v => ?_, fun w' hw' => Fam.ext fun {A} hA a {V} v => ?_⟩
  · have hb : v ≫ cBm (𝟙 V) = 𝟙 A ≫ 𝟙 A ≫ v := by simp [cBm_id]
    have hf0 : (𝟙 A ≫ v) ≫ cBm (𝟙 V) = 𝟙 A ≫ v := by simp [cBm_id]
    have inj : ∀ p q : Dv 𝓜 v, ρ 𝓜 (𝟙 A) (𝟙 V) hf0 p = ρ 𝓜 (𝟙 A) (𝟙 V) hf0 q → p = q := by
      intro p q h
      have h2 := congrArg (ρ 𝓜 (𝟙 A) (𝟙 V) hb) h
      rw [ρ_comp, ρ_comp] at h2
      have e : ∀ r : Dv 𝓜 v, ρ 𝓜 (𝟙 A ≫ 𝟙 A) (𝟙 V ≫ 𝟙 V) (comp_sq hf0 hb) r = r := fun r =>
        (ρ_congr 𝓜 (by simp) (by simp) _ (sq1' v) r).trans (ρ_id 𝓜 _ r)
      rwa [e, e] at h2
    apply inj
    have h1 := hval hA (a ≫ f) v A hA (𝟙 A) (by
      rw [Category.id_comp]; exact R.downward_closed hf a)
    refine h1.trans ?_
    rw [(x f hf).compat hA hA a v (𝟙 A ≫ v) (𝟙 A) (𝟙 V) hf0]
    have e3 := x_congr x (Category.id_comp (a ≫ f)) (R.downward_closed (R.downward_closed hf a) (𝟙 A) |> fun h => by simpa using h) (R.downward_closed hf a)
    exact (congrArg (fun X : Fam 𝓜 A => X.val hA (𝟙 A) (𝟙 A ≫ v)) e3).trans
      (congrArg (fun X : Fam 𝓜 A => X.val hA (𝟙 A) (𝟙 A ≫ v)) (hx f hf a).symm)
  · refine char_unique x hx hR hA a v (fun A' hA' b h => ?_) (hval hA a v)
    refine (w'.compat hA' hA a v (b ≫ v) b (𝟙 V) (sq1 b v)).trans ?_
    refine Eq.trans ?_ (congrArg (fun X : Fam 𝓜 A' => X.val hA' (𝟙 A') (b ≫ v)) (hw' (b ≫ a) h))
    change w'.val hA' (b ≫ a) (b ≫ v) = w'.val hA' (𝟙 A' ≫ b ≫ a) (b ≫ v)
    rw [Category.id_comp]

end

/-- **The sheaf property of `famPMod`.** -/
theorem fam_isSheafFor (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB) {T : SB Bsp} {R : Sieve T} (hR : Cov R) :
    Presieve.IsSheafFor (famPMod 𝓜).toPresheaf R.arrows := by
  intro xs hxs
  have hsc := (Presieve.compatible_iff_sieveCompatible xs).1 hxs
  obtain ⟨w, hw, hu⟩ := fam_glue (𝓜 := 𝓜) (fun {Y} f hf => famE 𝓜 Y (xs f hf))
    (fun {Y Y'} f hf g => by
      rw [hsc f g hf]
      exact (famE_map g _).symm) hR
  refine ⟨(famE 𝓜 T).symm w, fun {Y} f hf => ?_, fun w' hw' => ?_⟩
  · apply (famE 𝓜 Y).injective
    refine (famE_map f _).trans ?_
    rw [AddEquiv.apply_symm_apply]
    exact hw f hf
  · apply (famE 𝓜 T).injective
    rw [AddEquiv.apply_symm_apply]
    refine hu _ fun {Y} f hf => ?_
    rw [← hw' f hf]
    exact (famE_map f _).symm

end AlgMag.B3
