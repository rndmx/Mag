/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10LiftsRing
import AlgMag.GeneralBaseCore
import AlgMag.Foundations

/-!
# Equivariant lifts over an affine thickening, by integration

Mayeux, *Algebraic Magnetism*, Corollary 10.3, schemes only, `X'` affine. Given any lift `α` of the
non equivariant problem, the integral over `D(M)` of `g⁻¹ α g` is an equivariant lift. The integral
is formed with the Milnor square of `avgRing`, so the target `Y` is an arbitrary scheme. `M` is any
commutative group (the integral uses `-m`); the lemmas before it hold for a commutative monoid.
This replaces the use of Proposition 9.13 in the printed proof.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgMag.Lifts

open AlgMag.GB

section Milnor

variable {R' A C B : Type u} [CommRing R'] [CommRing A] [CommRing C] [CommRing B]
  {p : R' →+* A} {q : R' →+* C} {i : A →+* B} {j : C →+* B}

lemma hse_comp {W : Scheme.{u}} {E F : Type u} [CommRing E] [CommRing F]
    (t : W ⟶ Spec (CommRingCat.of E)) (r : F →+* E) :
    homSpecEquiv W (CommRingCat.of F) (t ≫ sp r) =
      CommRingCat.ofHom r ≫ homSpecEquiv W (CommRingCat.of E) t := by
  change (Scheme.ΓSpecIso _).inv ≫ (t ≫ sp r).appTop = CommRingCat.ofHom r ≫
    (Scheme.ΓSpecIso _).inv ≫ t.appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc,
    Scheme.ΓSpecIso_inv_naturality]

/-- Under a Milnor square with `q` surjective and `ker i = p (ker q)`, morphisms out of `Spec R'`
are compatible pairs. -/
lemma milnor_test (H : MilnorData p q i j) (hqs : Function.Surjective q)
    (hker : ∀ y, i y = 0 → ∃ z, p z = y ∧ q z = 0) {Y : Scheme.{u}}
    {f : Spec (CommRingCat.of A) ⟶ Y} {g : Spec (CommRingCat.of C) ⟶ Y}
    (hs : sp i ≫ f = sp j ≫ g) {W : Scheme.{u}} (u' : W ⟶ Spec (CommRingCat.of A))
    (v : W ⟶ Spec (CommRingCat.of C)) (huv : u' ≫ sp p = v ≫ sp q) : u' ≫ f = v ≫ g := by
  let U : A →+* Γ(W, ⊤) := (homSpecEquiv W (CommRingCat.of A) u').hom
  let V : C →+* Γ(W, ⊤) := (homSpecEquiv W (CommRingCat.of C) v).hom
  have hUV : ∀ z, U (p z) = V (q z) := by
    intro z
    have e : homSpecEquiv W _ (u' ≫ sp p) = homSpecEquiv W _ (v ≫ sp q) := by rw [huv]
    rw [hse_comp, hse_comp] at e
    exact congrArg (fun k => k.hom z) e
  have hkU : ∀ y, i y = 0 → U y = 0 := by
    intro y hy
    obtain ⟨z, rfl, hz⟩ := hker y hy
    rw [hUV, hz, map_zero]
  let w₀ : B →+* Γ(W, ⊤) := RingHom.liftOfSurjective i H.surj ⟨U, hkU⟩
  have hw₀ : ∀ x, w₀ (i x) = U x := fun x => by
    exact RingHom.liftOfRightInverse_comp_apply i (Function.surjInv H.surj) _ ⟨U, hkU⟩ x
  let w : W ⟶ Spec (CommRingCat.of B) := (homSpecEquiv W (CommRingCat.of B)).symm (CommRingCat.ofHom w₀)
  have hspec : ∀ {E : Type u} [CommRing E] (r : E →+* B) (t : W ⟶ Spec (CommRingCat.of E)),
      (∀ x, w₀ (r x) = (homSpecEquiv W _ t).hom x) → w ≫ sp r = t := by
    intro E _ r t hx
    apply (homSpecEquiv W (CommRingCat.of E)).injective
    ext x
    have h2 : (homSpecEquiv W (CommRingCat.of B) w) = CommRingCat.ofHom w₀ :=
      (homSpecEquiv W (CommRingCat.of B)).apply_symm_apply _
    rw [hse_comp, h2]
    exact hx x
  have h₁ : w ≫ sp i = u' := hspec i u' hw₀
  have h₂ : w ≫ sp j = v := by
    refine hspec j v fun x => ?_
    obtain ⟨z, rfl⟩ := hqs x
    rw [← H.comm, hw₀, hUV]
  rw [← h₁, ← h₂, Category.assoc, Category.assoc, hs]

/-- The push-out property of the Milnor square. -/
lemma milnor_desc (H : MilnorData p q i j) (hqs : Function.Surjective q)
    (hker : ∀ y, i y = 0 → ∃ z, p z = y ∧ q z = 0) {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of A) ⟶ Y) (g : Spec (CommRingCat.of C) ⟶ Y)
    (hs : sp i ≫ f = sp j ≫ g) : ∃! h : Spec (CommRingCat.of R') ⟶ Y, sp p ≫ h = f ∧ sp q ≫ h = g :=
  H.isLocalPO.existsUnique f g fun u v huv => milnor_test H hqs hker hs u v huv

/-- Joint injectivity of the Milnor square on morphisms. -/
lemma milnor_ext (H : MilnorData p q i j) {Y : Scheme.{u}}
    {h₁ h₂ : Spec (CommRingCat.of R') ⟶ Y} (e₁ : sp p ≫ h₁ = sp p ≫ h₂)
    (e₂ : sp q ≫ h₁ = sp q ≫ h₂) : h₁ = h₂ := by
  refine (H.isLocalPO.existsUnique (sp p ≫ h₁) (sp q ≫ h₁) fun u v huv => ?_).unique
    ⟨rfl, rfl⟩ ⟨e₁.symm, e₂.symm⟩
  rw [← Category.assoc, huv, Category.assoc]

end Milnor

section RingMaps

variable {M : Type u} [AddCommMonoid M] {D D₀ E E₀ F : Type u} [CommRing D] [CommRing D₀] [CommRing E]
  [CommRing E₀] [CommRing F]

lemma map_map_apply (g : E →+* F) (h : D →+* E) (k : D →+* F) (hk : ∀ a, g (h a) = k a)
    (w : AddMonoidAlgebra D M) : AddMonoidAlgebra.mapRingHom M g (AddMonoidAlgebra.mapRingHom M h w) =
      AddMonoidAlgebra.mapRingHom M k w := by
  ext m
  simp [AddMonoidAlgebra.coeff_mapRingHom, hk]

lemma map_cst (g : D →+* E) (a : D) : AddMonoidAlgebra.mapRingHom M g (cst D M a) = cst E M (g a) := by
  simp [cst, AddMonoidAlgebra.singleZeroRingHom]

lemma diag_cst (a : D) : diag D M (cst D M a) = cst _ M (cst D M a) := by
  simpa [cst, AddMonoidAlgebra.singleZeroRingHom] using diag_single (0 : M) a

lemma map_diag (g : D →+* E) (w : AddMonoidAlgebra D M) :
    AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom M g) (diag D M w) =
      diag E M (AddMonoidAlgebra.mapRingHom M g w) := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single m a => simp [diag_single]

lemma coeff_diag (w : AddMonoidAlgebra D M) : (diag D M w).coeff 0 = cst D M (w.coeff 0) := by
  classical
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single m a =>
    rw [diag_single]
    by_cases hm : m = 0
    · subst hm
      simp [cst, AddMonoidAlgebra.singleZeroRingHom]
    · have h₁ : (AddMonoidAlgebra.single m (AddMonoidAlgebra.single m a)).coeff (0 : M) = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hm)
      have h₂ : (AddMonoidAlgebra.single m a : AddMonoidAlgebra D M).coeff (0 : M) = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hm)
      rw [h₁, h₂, map_zero]

/-- A ring map of `avgRing`s. -/
noncomputable def avgMap (φ₁ : D →+* D₀) (φ₂ : E →+* E₀) (x : D₀ →+* E₀)
    (y : AddMonoidAlgebra D M →+* AddMonoidAlgebra E M)
    (h : ∀ p : avgRing (M := M) φ₁, AddMonoidAlgebra.mapRingHom M φ₂ (y (avgSnd φ₁ p)) =
      cst E₀ M (x (avgFst φ₁ p))) : avgRing (M := M) φ₁ →+* avgRing (M := M) φ₂ :=
  RingHom.codRestrict ((x.comp (avgFst φ₁)).prod (y.comp (avgSnd φ₁))) _ (fun p => (h p).symm)

end RingMaps

section Main

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]

/-- `Spec R` as an `S`-scheme. -/
noncomputable abbrev Ov {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ S) : Over S := Over.mk s

/-- `Spec` of a ring map, over `S`. -/
noncomputable def ovHom {R R₁ : Type u} [CommRing R] [CommRing R₁] (g : R →+* R₁)
    {s : Spec (CommRingCat.of R) ⟶ S} {s₁ : Spec (CommRingCat.of R₁) ⟶ S} (h : sp g ≫ s = s₁) :
    Ov s₁ ⟶ Ov s := Over.homMk (sp g) h

lemma ovHom_comp {R R₁ R₂ : Type u} [CommRing R] [CommRing R₁] [CommRing R₂] (g : R →+* R₁)
    (g₁ : R₁ →+* R₂) {s : Spec (CommRingCat.of R) ⟶ S} {s₁ : Spec (CommRingCat.of R₁) ⟶ S}
    {s₂ : Spec (CommRingCat.of R₂) ⟶ S} (h : sp g ≫ s = s₁) (h₁ : sp g₁ ≫ s₁ = s₂)
    (h₂ : sp (g₁.comp g) ≫ s = s₂) : ovHom g₁ h₁ ≫ ovHom g h = ovHom (g₁.comp g) h₂ := by
  refine Over.OverMorphism.ext ?_
  exact (sp_comp g g₁).symm

lemma ovHom_congr {R R₁ : Type u} [CommRing R] [CommRing R₁] {g g₁ : R →+* R₁} (e : g = g₁)
    {s : Spec (CommRingCat.of R) ⟶ S} {s₁ : Spec (CommRingCat.of R₁) ⟶ S} (h : sp g ≫ s = s₁)
    (h₁ : sp g₁ ≫ s = s₁) : ovHom g h = ovHom g₁ h₁ := by
  subst e; rfl

/-- The point of `𝔸(M)` over `Spec R` given by a monoid map to `R`. -/
noncomputable def eOf {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ S)
    (e : Multiplicative M →* R) : APt (overO S) M (op (Ov s)) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom).comp e

lemma res_eOf {R R₁ : Type u} [CommRing R] [CommRing R₁] (g : R →+* R₁)
    {s : Spec (CommRingCat.of R) ⟶ S} {s₁ : Spec (CommRingCat.of R₁) ⟶ S} (h : sp g ≫ s = s₁)
    (e : Multiplicative M →* R) :
    APt.res (ovHom g h).op (eOf s e) = eOf s₁ (g.toMonoidHom.comp e) := by
  ext m
  have := congrArg (fun k => k.hom (e m))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact this.symm

/-- The action, on morphisms into `Y`. -/
noncomputable abbrev sm {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) {T : Over S}
    (h : APt (overO S) M (op T)) (x : T ⟶ Y) : T ⟶ Y := aY.smul (U := op T) h x

lemma comp_sm {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) {T T₁ : Over S} (g : T₁ ⟶ T)
    (h : APt (overO S) M (op T)) (x : T ⟶ Y) :
    g ≫ sm aY h x = sm aY (APt.res g.op h) (g ≫ x) := aY.map_smul g.op h x

lemma sm_sm {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) {T : Over S}
    (h k : APt (overO S) M (op T)) (x : T ⟶ Y) : sm aY h (sm aY k x) = sm aY (h * k) x :=
  (aY.mul_smul h k x).symm

lemma sm_one {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) {T : Over S} (x : T ⟶ Y) :
    sm aY 1 x = x := aY.one_smul x

variable {A₁ A : Type u} [CommRing A₁] [CommRing A]

/-- The universal point of `𝔸(M)`. -/
noncomputable abbrev eU (R : Type u) [CommRing R] (M : Type u) [AddCommMonoid M] :
    Multiplicative M →* AddMonoidAlgebra R M := AddMonoidAlgebra.of R M

lemma ker_map_lift (φ : A₁ →+* A) (y : AddMonoidAlgebra A₁ M)
    (hy : AddMonoidAlgebra.mapRingHom M φ y = 0) :
    ∃ z : avgRing (M := M) φ, avgSnd φ z = y ∧ avgFst φ z = 0 :=
  ⟨⟨(0, y), by
    change cst A M 0 = AddMonoidAlgebra.mapRingHom M φ y
    rw [hy, map_zero]⟩, rfl, rfl⟩

/-- Push-out property of `avgRing`, on morphisms to `Y`. -/
lemma avg_desc (φ : A₁ →+* A) (hs : Function.Surjective φ) {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of (AddMonoidAlgebra A₁ M)) ⟶ Y) (g : Spec (CommRingCat.of A) ⟶ Y)
    (h : sp (AddMonoidAlgebra.mapRingHom M φ) ≫ f = sp (cst A M) ≫ g) :
    ∃! k : Spec (CommRingCat.of (avgRing (M := M) φ)) ⟶ Y, sp (avgSnd φ) ≫ k = f ∧ sp (avgFst φ) ≫ k = g :=
  milnor_desc (milnor_avg φ hs) (avgFst_surjective φ hs) (fun y hy => ker_map_lift φ y hy) f g h

lemma sp_id' {R : Type u} [CommRing R] : sp (RingHom.id R) = 𝟙 _ := by
  rw [sp, CommRingCat.ofHom_id, Spec.map_id]

lemma sp_sq {R R₁ R₂ R₃ : Type u} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {g : R →+* R₁} {g₁ : R₁ →+* R₂} {g₃ : R →+* R₃} {g₄ : R₃ →+* R₂}
    (e : g₁.comp g = g₄.comp g₃) : sp g₁ ≫ sp g = sp g₄ ≫ sp g₃ := by
  rw [← sp_comp, ← sp_comp, e]

/-- Squares of `ovHom`. -/
lemma ov_sq {R R₁ R₂ R₃ : Type u} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {g : R →+* R₁} {g₁ : R₁ →+* R₂} {g₃ : R →+* R₃} {g₄ : R₃ →+* R₂}
    {s : Spec (CommRingCat.of R) ⟶ S} {s₁ : Spec (CommRingCat.of R₁) ⟶ S}
    {s₂ : Spec (CommRingCat.of R₂) ⟶ S} {s₃ : Spec (CommRingCat.of R₃) ⟶ S}
    (h : sp g ≫ s = s₁) (h₁ : sp g₁ ≫ s₁ = s₂) (h₃ : sp g₃ ≫ s = s₃) (h₄ : sp g₄ ≫ s₃ = s₂)
    (e : g₁.comp g = g₄.comp g₃) : ovHom g₁ h₁ ≫ ovHom g h = ovHom g₄ h₄ ≫ ovHom g₃ h₃ :=
  Over.OverMorphism.ext (sp_sq e)

lemma eOf_congr {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ S)
    {e e₁ : Multiplicative M →* R} (h : e = e₁) : eOf s e = eOf s e₁ := by rw [h]

lemma eOf_mul {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ S)
    (e e₁ : Multiplicative M →* R) : eOf s (e * e₁) = eOf s e * eOf s e₁ := by
  ext m
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom _ _

lemma hof {D E : Type u} [CommRing D] [CommRing E] (g : D →+* E) :
    (AddMonoidAlgebra.mapRingHom M g).toMonoidHom.comp (eU D M) = eU E M := by
  ext m
  simp [eU]

/-- The structure of `Spec (avgRing φ)` over `S`. -/
noncomputable def sU (φ : A₁ →+* A) (t : Spec (CommRingCat.of A₁) ⟶ S) :
    Spec (CommRingCat.of (avgRing (M := M) φ)) ⟶ S := sp (avgCst φ) ≫ t

lemma hP (φ : A₁ →+* A) (t : Spec (CommRingCat.of A₁) ⟶ S) :
    sp (avgSnd (M := M) φ) ≫ sU φ t = sp (cst A₁ M) ≫ t := by
  rw [sU, ← Category.assoc, ← sp_comp, avgSnd_cst]

lemma hQ (φ : A₁ →+* A) (t : Spec (CommRingCat.of A₁) ⟶ S) :
    sp (avgFst (M := M) φ) ≫ sU φ t = sp φ ≫ t := by
  rw [sU, ← Category.assoc, ← sp_comp, avgFst_cst]

/-- `Spec D[M] → Spec (avgRing φ)` over `S`. -/
noncomputable def pU (φ : A₁ →+* A) (t : Spec (CommRingCat.of A₁) ⟶ S) :
    Ov (sp (cst A₁ M) ≫ t) ⟶ Ov (sU (M := M) φ t) := Over.homMk (sp (avgSnd φ)) (hP φ t)

/-- `Spec D₀ → Spec (avgRing φ)` over `S`. -/
noncomputable def qU (φ : A₁ →+* A) (t : Spec (CommRingCat.of A₁) ⟶ S) :
    Ov (sp φ ≫ t) ⟶ Ov (sU (M := M) φ t) := Over.homMk (sp (avgFst φ)) (hQ φ t)

/-- Equality of morphisms out of `Spec (avgRing φ)` over `S`. -/
lemma ovU_ext (φ : A₁ →+* A) (hs : Function.Surjective φ) (t : Spec (CommRingCat.of A₁) ⟶ S)
    {Y : Over S} {x y : Ov (sU (M := M) φ t) ⟶ Y}
    (e₁ : pU (M := M) φ t ≫ x = pU (M := M) φ t ≫ y)
    (e₂ : qU (M := M) φ t ≫ x = qU (M := M) φ t ≫ y) : x = y :=
  Over.OverMorphism.ext (milnor_ext (milnor_avg (M := M) φ hs)
    (congrArg (fun z => z.left) e₁) (congrArg (fun z => z.left) e₂))

/-- Descent to `Spec (avgRing φ)` over `S`. -/
lemma ovU_desc (φ : A₁ →+* A) (hs : Function.Surjective φ) (t : Spec (CommRingCat.of A₁) ⟶ S)
    {Y : Over S} (β : Ov (sp (cst A₁ M) ≫ t) ⟶ Y) (a : Ov (sp φ ≫ t) ⟶ Y)
    (h : sp (AddMonoidAlgebra.mapRingHom M φ) ≫ β.left = sp (cst A M) ≫ a.left) :
    ∃ x : Ov (sU (M := M) φ t) ⟶ Y, pU (M := M) φ t ≫ x = β ∧
      qU (M := M) φ t ≫ x = a := by
  obtain ⟨k, ⟨hk1, hk2⟩, -⟩ := avg_desc φ hs β.left a.left h
  have hkw : k ≫ Y.hom = sU φ t := by
    refine milnor_ext (milnor_avg (M := M) φ hs) ?_ ?_
    · rw [← Category.assoc, hk1, hP]
      exact Over.w β
    · rw [← Category.assoc, hk2, hQ]
      exact Over.w a
  exact ⟨Over.homMk k hkw, Over.OverMorphism.ext hk1, Over.OverMorphism.ext hk2⟩

section Second

variable (φ : A₁ →+* A) (t : Spec (CommRingCat.of A₁) ⟶ S) (ρ : A₁ →+* AddMonoidAlgebra A₁ M)
  (ρ₀ : A →+* AddMonoidAlgebra A M) (hρt : sp ρ ≫ t = sp (cst A₁ M) ≫ t)
  (hρφ : ∀ a, AddMonoidAlgebra.mapRingHom M φ (ρ a) = ρ₀ (φ a))

/-- `D(M)` coacting on the variable of `avgRing`: `(x, w) ↦ (ρ₀ x, ρ w)`. -/
noncomputable def τ₂ : avgRing (M := M) φ →+* avgRing (M := M) (AddMonoidAlgebra.mapRingHom M φ) :=
  avgMap φ (AddMonoidAlgebra.mapRingHom M φ) ρ₀ (AddMonoidAlgebra.mapRingHom M ρ) (fun p => by
    rw [(map_map_apply (AddMonoidAlgebra.mapRingHom M φ) ρ (ρ₀.comp φ) hρφ _).trans
      (map_map_apply ρ₀ φ (ρ₀.comp φ) (fun _ => rfl) _).symm, avg_prop φ p, map_cst])

/-- The multiplication of `D(M)` on `avgRing`: `(x, w) ↦ (x, diag w)`. -/
noncomputable def μ₂ : avgRing (M := M) φ →+* avgRing (M := M) (AddMonoidAlgebra.mapRingHom M φ) :=
  avgMap φ (AddMonoidAlgebra.mapRingHom M φ) (cst A M) (diag A₁ M) (fun p => by
    rw [map_diag, avg_prop φ p, diag_cst])

include hρt in
lemma hτ₂ : sp (τ₂ φ ρ ρ₀ hρφ) ≫ sU (M := M) φ t =
    sU (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t) := by
  have hc : (τ₂ φ ρ ρ₀ hρφ).comp (avgCst φ) = (avgCst (AddMonoidAlgebra.mapRingHom M φ)).comp ρ :=
    RingHom.ext fun x => Subtype.ext (Prod.ext (hρφ x).symm (map_cst ρ x))
  rw [sU, sU, ← Category.assoc, sp_sq hc, Category.assoc, hρt]

lemma hμ₂ : sp (μ₂ (M := M) φ) ≫ sU (M := M) φ t =
    sU (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t) := by
  have hc : (μ₂ (M := M) φ).comp (avgCst φ) =
      (avgCst (AddMonoidAlgebra.mapRingHom M φ)).comp (cst A₁ M) :=
    RingHom.ext fun x => Subtype.ext (Prod.ext (map_cst φ x).symm (diag_cst x))
  rw [sU, sU, ← Category.assoc, sp_sq hc, Category.assoc]

include hρt in
lemma hτs : sp (AddMonoidAlgebra.mapRingHom M ρ) ≫ sp (cst A₁ M) ≫ t =
    sp (cst (AddMonoidAlgebra A₁ M) M) ≫ sp (cst A₁ M) ≫ t := by
  rw [← Category.assoc, sp_sq (g₃ := ρ) (g₄ := cst _ M) (RingHom.ext fun x => map_cst ρ x),
    Category.assoc, hρt]

lemma hμs : sp (diag A₁ M) ≫ sp (cst A₁ M) ≫ t =
    sp (cst (AddMonoidAlgebra A₁ M) M) ≫ sp (cst A₁ M) ≫ t := by
  rw [← Category.assoc, ← Category.assoc, sp_sq (g₃ := cst A₁ M) (g₄ := cst _ M)
    (RingHom.ext fun x => diag_cst x)]


lemma hμe : (diag A₁ M).toMonoidHom.comp (eU A₁ M) =
    (cst (AddMonoidAlgebra A₁ M) M).toMonoidHom.comp (eU A₁ M) * eU (AddMonoidAlgebra A₁ M) M := by
  refine MonoidHom.ext fun m => ?_
  change diag A₁ M (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1) =
    AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1) *
      AddMonoidAlgebra.single (Multiplicative.toAdd m) 1
  rw [diag_single, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

end Second

lemma tri {C : Type*} [Category C] {P Q R W V : C} {u : P ⟶ Q} {v : Q ⟶ W} {w : P ⟶ R} {x : R ⟶ W}
    (sq : u ≫ v = w ≫ x) (z : W ⟶ V) : u ≫ v ≫ z = w ≫ x ≫ z :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ z) sq).trans (Category.assoc _ _ _))

end Main

section MainGroup

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] {A₁ A : Type u} [CommRing A₁] [CommRing A]

/-- The inverse point. -/
noncomputable def pinv {U : (Over S)ᵒᵖ} (h : APt (overO S) M U) : APt (overO S) M U := h.comp invMonoidHom

lemma pinv_mul_self {U : (Over S)ᵒᵖ} (h : APt (overO S) M U) : pinv h * h = 1 := by
  have : ∀ n : Multiplicative M, h n⁻¹ * h n = 1 := fun n => by
    rw [← map_mul, inv_mul_cancel, map_one]
  ext m
  exact this _

lemma pinv_mul {U : (Over S)ᵒᵖ} (h k : APt (overO S) M U) : pinv (h * k) = pinv h * pinv k := by
  ext m; rfl

lemma res_pinv {U V : (Over S)ᵒᵖ} (g : U ⟶ V) (h : APt (overO S) M U) :
    APt.res g (pinv h) = pinv (APt.res g h) := rfl

lemma sm_pinv_sm {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) {T : Over S}
    (h : APt (overO S) M (op T)) (x : T ⟶ Y) : sm aY (pinv h) (sm aY h x) = x := by
  rw [sm_sm, pinv_mul_self, sm_one]

lemma hI (φ : A₁ →+* A) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (t : Spec (CommRingCat.of A₁) ⟶ S) : sp (avgInt (M := M) φ hq) ≫ sU φ t = t := by
  rw [sU, ← Category.assoc, ← sp_comp, avgInt_cst, sp_id', Category.id_comp]

/-- The integral `Spec D → Spec (avgRing φ)` over `S`. -/
noncomputable def iU (φ : A₁ →+* A) (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
    (t : Spec (CommRingCat.of A₁) ⟶ S) : Ov t ⟶ Ov (sU (M := M) φ t) :=
  Over.homMk (sp (avgInt φ hq)) (hI φ hq t)

/-- The first order `★` identity: `e₂⁻¹ • (β ∘ τ) = β ∘ μ` for `β = e⁻¹ • (α ∘ ρ)`. -/
lemma star_identity (t : Spec (CommRingCat.of A₁) ⟶ S)
    (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (hρt : sp ρ ≫ t = sp (cst A₁ M) ≫ t)
    (hco : ∀ a, AddMonoidAlgebra.mapRingHom M ρ (ρ a) = diag A₁ M (ρ a))
    {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y)) (α : Ov t ⟶ Y) :
    sm aY (pinv (eOf (sp (cst (AddMonoidAlgebra A₁ M) M) ≫ sp (cst A₁ M) ≫ t)
        ((cst (AddMonoidAlgebra A₁ M) M).toMonoidHom.comp (eU A₁ M))))
      (ovHom (AddMonoidAlgebra.mapRingHom M ρ) (hτs t ρ hρt) ≫
        sm aY (pinv (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M))) (ovHom ρ hρt ≫ α)) =
    ovHom (diag A₁ M) (hμs t) ≫
        sm aY (pinv (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M))) (ovHom ρ hρt ≫ α) := by
  have hx : ovHom (AddMonoidAlgebra.mapRingHom M ρ) (hτs t ρ hρt) ≫ ovHom ρ hρt ≫ α =
      ovHom (diag A₁ M) (hμs t) ≫ ovHom ρ hρt ≫ α := by
    have sq : ovHom (AddMonoidAlgebra.mapRingHom M ρ) (hτs t ρ hρt) ≫ ovHom ρ hρt =
        ovHom (diag A₁ M) (hμs t) ≫ ovHom ρ hρt :=
      Over.OverMorphism.ext (sp_sq (RingHom.ext hco))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ α) sq).trans (Category.assoc _ _ _))
  rw [comp_sm, comp_sm, res_pinv, res_pinv, res_eOf, res_eOf, hof, hμe, eOf_mul, sm_sm, pinv_mul, hx]

/-- The equivariance step. -/
lemma equivariance_step (φ : A₁ →+* A) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (t : Spec (CommRingCat.of A₁) ⟶ S)
    (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
    (hρt : sp ρ ≫ t = sp (cst A₁ M) ≫ t)
    (hρφ : ∀ a, AddMonoidAlgebra.mapRingHom M φ (ρ a) = ρ₀ (φ a))
    (hco : ∀ a, AddMonoidAlgebra.mapRingHom M ρ (ρ a) = diag A₁ M (ρ a))
    {Y : Over S} (aY : AAction (overO S) M (yoneda.obj Y))
    (a : Ov (sp φ ≫ t) ⟶ Y) (α : Ov t ⟶ Y)
    (h₀ρ : sp ρ₀ ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (h₀c : sp (cst A M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (ha : ovHom ρ₀ h₀ρ ≫ a = sm aY (eOf _ (eU A M)) (ovHom (cst A M) h₀c ≫ a))
    (βt : Ov (sU (M := M) φ t) ⟶ Y)
    (hβ : pU (M := M) φ t ≫ βt =
      sm aY (pinv (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M))) (ovHom ρ hρt ≫ α))
    (hβa : qU (M := M) φ t ≫ βt = a) :
    ovHom ρ hρt ≫ iU (M := M) φ hq t ≫ βt =
      sm aY (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M))
        (ovHom (cst A₁ M) rfl ≫ iU (M := M) φ hq t ≫ βt) := by
  have hs₂ := map_surjective (M := M) φ hs
  have hq₂ := map_sq_zero (M := M) φ hq
  let τU : Ov (sU (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t)) ⟶ Ov (sU (M := M) φ t) := Over.homMk (sp (τ₂ φ ρ ρ₀ hρφ)) (hτ₂ φ t ρ ρ₀ hρt hρφ)
  let μU : Ov (sU (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t)) ⟶ Ov (sU (M := M) φ t) := Over.homMk (sp (μ₂ (M := M) φ)) (hμ₂ φ t)
  let c₂ := avgCst (M := M) (AddMonoidAlgebra.mapRingHom M φ)
  let e₂U := eOf (sU (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t))
    (c₂.toMonoidHom.comp (eU A₁ M))
  have hLR : sm aY (pinv e₂U) (τU ≫ βt) = μU ≫ βt := by
    refine ovU_ext _ hs₂ _ ?_ ?_
    · have e₁ : APt.res (pU (M := M) (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t)).op e₂U =
          eOf (sp (cst (AddMonoidAlgebra A₁ M) M) ≫ sp (cst A₁ M) ≫ t)
            ((cst (AddMonoidAlgebra A₁ M) M).toMonoidHom.comp (eU A₁ M)) := res_eOf _ _ _
      have e₂ := tri (u := pU (M := M) (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t)) (v := τU)
        (w := ovHom (AddMonoidAlgebra.mapRingHom M ρ) (hτs t ρ hρt)) (x := pU (M := M) φ t)
        (Over.OverMorphism.ext (sp_sq rfl)) βt
      have e₃ := tri (u := pU (M := M) (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t)) (v := μU)
        (w := ovHom (diag A₁ M) (hμs t)) (x := pU (M := M) φ t)
        (Over.OverMorphism.ext (sp_sq rfl)) βt
      refine (comp_sm aY _ _ _).trans ?_
      rw [res_pinv, e₁, e₂, e₃, hβ]
      exact star_identity t ρ hρt hco aY α
    · have e₁ : APt.res (qU (M := M) (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t)).op e₂U =
          eOf (sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t) (eU A M) :=
        (res_eOf _ _ _).trans (eOf_congr _ (hof φ))
      have e₂ := tri (u := qU (M := M) (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t)) (v := τU)
        (w := ovHom ρ₀ h₀ρ) (x := qU (M := M) φ t) (Over.OverMorphism.ext (sp_sq rfl)) βt
      have e₃ := tri (u := qU (M := M) (AddMonoidAlgebra.mapRingHom M φ) (sp (cst A₁ M) ≫ t)) (v := μU)
        (w := ovHom (cst A M) h₀c) (x := qU (M := M) φ t) (Over.OverMorphism.ext (sp_sq rfl)) βt
      refine (comp_sm aY _ _ _).trans ?_
      rw [res_pinv, e₁, e₂, e₃, hβa, ha, sm_pinv_sm]
  have hfin := congrArg (fun z => iU (M := M) _ hq₂ (sp (cst A₁ M) ≫ t) ≫ z) hLR
  have eJ : APt.res (iU (M := M) _ hq₂ (sp (cst A₁ M) ≫ t)).op e₂U =
      eOf (sp (cst A₁ M) ≫ t) (eU A₁ M) := (res_eOf _ _ _).trans (eOf_congr _ (by
        refine MonoidHom.ext fun m => ?_
        exact RingHom.congr_fun (avgInt_cst _ hq₂) _))
  have e₂ := tri (u := iU (M := M) _ hq₂ (sp (cst A₁ M) ≫ t)) (v := τU)
    (w := ovHom ρ hρt) (x := iU (M := M) φ hq t)
    (Over.OverMorphism.ext (sp_sq (RingHom.ext fun p =>
      AddMonoidAlgebra.coeff_mapRingHom ρ (avgSnd φ p) 0))) βt
  have e₃ := tri (u := iU (M := M) _ hq₂ (sp (cst A₁ M) ≫ t)) (v := μU)
    (w := ovHom (cst A₁ M) rfl) (x := iU (M := M) φ hq t)
    (Over.OverMorphism.ext (sp_sq (RingHom.ext fun p => coeff_diag (avgSnd φ p)))) βt
  have h₂ : sm aY (pinv (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M))) (ovHom ρ hρt ≫ iU (M := M) φ hq t ≫ βt) =
      ovHom (cst A₁ M) rfl ≫ iU (M := M) φ hq t ≫ βt := by
    refine Eq.trans ?_ (hfin.trans e₃)
    refine Eq.trans ?_ (comp_sm aY _ _ _).symm
    rw [res_pinv, eJ, e₂]
  rw [← h₂, sm_sm, mul_comm, pinv_mul_self, sm_one]

/-- **Integration over `D(M)`.** From any lift `α` over the affine `Spec A₁` of a square with
equivariant sides, the integral of `g⁻¹ α g` is an equivariant lift. Schemes only. The coaction of
`Spec A₁` is `ρ`, coassociative; no counit is needed. `f` need not be smooth. -/
theorem exists_equivariant_of_lift (φ : A₁ →+* A) (hs : Function.Surjective φ)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (t : Spec (CommRingCat.of A₁) ⟶ S)
    (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
    (hρt : sp ρ ≫ t = sp (cst A₁ M) ≫ t)
    (hρφ : ∀ a, AddMonoidAlgebra.mapRingHom M φ (ρ a) = ρ₀ (φ a))
    (hco : ∀ a, AddMonoidAlgebra.mapRingHom M ρ (ρ a) = diag A₁ M (ρ a))
    {Y Z : Over S} (aY : AAction (overO S) M (yoneda.obj Y))
    (aZ : AAction (overO S) M (yoneda.obj Z)) (f : Y ⟶ Z)
    (hf : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ Y),
      sm aY h x ≫ f = sm aZ h (x ≫ f))
    (a : Ov (sp φ ≫ t) ⟶ Y) (b : Ov t ⟶ Z) (α : Ov t ⟶ Y)
    (hαa : ovHom φ rfl ≫ α = a) (hαb : α ≫ f = b)
    (h₀ρ : sp ρ₀ ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (h₀c : sp (cst A M) ≫ sp φ ≫ t = sp (AddMonoidAlgebra.mapRingHom M φ) ≫ sp (cst A₁ M) ≫ t)
    (ha : ovHom ρ₀ h₀ρ ≫ a = sm aY (eOf _ (eU A M)) (ovHom (cst A M) h₀c ≫ a))
    (hb : ovHom ρ hρt ≫ b = sm aZ (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M)) (ovHom (cst A₁ M) rfl ≫ b)) :
    ∃ l : Ov t ⟶ Y, ovHom φ rfl ≫ l = a ∧ l ≫ f = b ∧
      ovHom ρ hρt ≫ l = sm aY (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M)) (ovHom (cst A₁ M) rfl ≫ l) := by
  have hrd : ovHom (AddMonoidAlgebra.mapRingHom M φ) rfl ≫
      sm aY (pinv (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M))) (ovHom ρ hρt ≫ α) = ovHom (cst A M) h₀c ≫ a := by
    have h1 : ovHom (AddMonoidAlgebra.mapRingHom M φ) rfl ≫ ovHom ρ hρt ≫ α = ovHom ρ₀ h₀ρ ≫ a := by
      have sq : ovHom (AddMonoidAlgebra.mapRingHom M φ) rfl ≫ ovHom ρ hρt = ovHom ρ₀ h₀ρ ≫ ovHom φ rfl :=
        Over.OverMorphism.ext (sp_sq (RingHom.ext hρφ))
      calc _ = (ovHom (AddMonoidAlgebra.mapRingHom M φ) rfl ≫ ovHom ρ hρt) ≫ α := (Category.assoc _ _ _).symm
        _ = (ovHom ρ₀ h₀ρ ≫ ovHom φ rfl) ≫ α := by rw [sq]
        _ = ovHom ρ₀ h₀ρ ≫ a := by rw [Category.assoc, hαa]
    rw [comp_sm, res_pinv, res_eOf, hof, h1, ha, sm_pinv_sm]
  have hβf : sm aY (pinv (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M))) (ovHom ρ hρt ≫ α) ≫ f =
      ovHom (cst A₁ M) rfl ≫ b := by
    rw [hf, Category.assoc, hαb, hb, sm_pinv_sm]
  obtain ⟨βt, hβ, hβa⟩ := ovU_desc φ hs t
    (sm aY (pinv (eOf (sp (cst A₁ M) ≫ t) (eU A₁ M))) (ovHom ρ hρt ≫ α)) a
    (congrArg (fun z => z.left) hrd)
  refine ⟨iU (M := M) φ hq t ≫ βt, ?_, ?_, ?_⟩
  · rw [← hβa, ← Category.assoc]
    congr 1
    refine Over.OverMorphism.ext ?_
    change sp φ ≫ sp _ = sp _
    rw [← sp_comp, φ_avgInt]
  · let cU : Ov (sU (M := M) φ t) ⟶ Ov t := Over.homMk (sp (avgCst φ)) rfl
    have h₁ : βt ≫ f = cU ≫ b := by
      refine ovU_ext φ hs t ?_ ?_
      · rw [← Category.assoc, hβ, hβf, ← Category.assoc]
        congr 1
        refine Over.OverMorphism.ext ?_
        change sp _ = sp _ ≫ sp _
        rw [← sp_comp, avgSnd_cst]
      · rw [← Category.assoc, hβa, ← hαa, Category.assoc, hαb, ← Category.assoc]
        congr 1
        refine Over.OverMorphism.ext ?_
        change sp _ = sp _ ≫ sp _
        rw [← sp_comp, avgFst_cst]
    rw [Category.assoc, h₁, ← Category.assoc]
    have : iU (M := M) φ hq t ≫ cU = 𝟙 _ := Over.OverMorphism.ext (by
      change sp _ ≫ sp _ = 𝟙 _
      rw [← sp_comp, avgInt_cst, sp_id'])
    rw [this, Category.id_comp]
  · exact equivariance_step φ hs hq t ρ ρ₀ hρt hρφ hco aY a α h₀ρ h₀c ha βt hβ hβa

end MainGroup

end AlgMag.Lifts
