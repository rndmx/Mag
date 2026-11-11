/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDExistMain
import AlgMag.SpacesDescentUnique

/-!
# Lemma D, Steps 3 (ii) and 4: the chart `W' = W ×_X U`, and factoring through degree `0`

In the proof of Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Step 3 (ii): `W' = W ×_X U`, for `f : U → X` étale, is an object of the site, étale over `W`, with its universal
property. -/
theorem SDLocS_chart {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    {W : BigFppfOver B S hS} (x : X.obj (op W)) :
    ∃ (W' : BigFppfOver B S hS) (p : W' ⟶ W) (s : W' ⟶ U), Etale ((SCH).map p) ∧
      f.app (op W') s = X.map p.op x ∧
      ∀ {T : BigFppfOver B S hS} (a : T ⟶ W) (b : T ⟶ U), X.map a.op x = f.app (op T) b →
        ∃! l : T ⟶ W', l ≫ p = a ∧ l ≫ s = b := by
  let g : yoneda.obj W ⟶ X := yonedaEquiv.symm x
  have hgapp : ∀ {T : BigFppfOver B S hS} (a : T ⟶ W), g.app (op T) a = X.map a.op x := fun a => by
    simp [g, yonedaEquiv_symm_app_apply]
  have key : ∀ {T : BigFppfOver B S hS} (a : T ⟶ W) (b : T ⟶ U), X.map a.op x = f.app (op T) b →
      yoneda.map b ≫ f = yoneda.map a ≫ g := by
    intro T a b hab
    ext T' (t : T'.unop ⟶ T)
    have h1 : f.app (op T'.unop) (t ≫ b) = X.map t.op (f.app (op T) b) :=
      NatTrans.naturality_apply f t.op b
    have h2 := hgapp (t ≫ a)
    change f.app (op T'.unop) (t ≫ b) = g.app (op T'.unop) (t ≫ a)
    rw [h1, h2, ← hab, op_comp, Functor.map_comp_apply]
  have hrep := hf.1
  have hw := hrep.isPullback' g
  refine ⟨hrep.pullback g, hrep.snd g, hrep.fst' g, hf.2 g _ _ (hrep.isPullback g), ?_, ?_⟩
  · have h := congrArg (fun φ : yoneda.obj (hrep.pullback g) ⟶ X => φ.app (op (hrep.pullback g)) (𝟙 _)) hw.w
    change f.app (op (hrep.pullback g)) (𝟙 (hrep.pullback g) ≫ hrep.fst' g) =
      g.app (op (hrep.pullback g)) (𝟙 (hrep.pullback g) ≫ hrep.snd g) at h
    rw [Category.id_comp, Category.id_comp] at h
    rw [h, hgapp]
  · intro T a b hab
    refine ⟨hrep.lift' b a (key a b hab), ⟨hrep.lift'_snd .., hrep.lift'_fst ..⟩, ?_⟩
    rintro l ⟨h1, h2⟩
    exact hrep.hom_ext' (by rw [h2, hrep.lift'_fst]) (by rw [h1, hrep.lift'_snd])

/-- Step 4: an invariant map from a graded affine `W` to an affine object `U` factors through the invariants. -/
theorem SDLocS_factor {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ] [UniqueSums Γ]
    {c : Coact A Γ} {ι : A₀ →+* A} (hι : c.IsInv ι) {W Q U : BigFppfOver B S hS} (π : W ⟶ Q)
    (i : (SCH).obj W ≅ Spec (.of A)) (i₀ : (SCH).obj Q ≅ Spec (.of A₀))
    (hπ : (SCH).map π ≫ i₀.hom = i.hom ≫ sp ι) (g : W ⟶ U)
    (hg : IsInvariantF c (i.inv ≫ (SCH).map g)) :
    ∃ f : Q ⟶ U, π ≫ f = g := by
  obtain ⟨f, hf⟩ := exists_desc_of_torsionFree hι hg
  have hsplit := hι.isSplit
  let f' : (SCH).obj Q ⟶ (SCH).obj U := i₀.hom ≫ f
  have hπ' : i.inv ≫ (SCH).map π = sp ι ≫ i₀.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hwf : (SCH).map π ≫ f' = (SCH).map g := by
    change (SCH).map π ≫ i₀.hom ≫ f = _
    rw [← Category.assoc, hπ, Category.assoc, hf, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hcancel : ∀ {Z : Scheme.{u}} (a b : (SCH).obj Q ⟶ Z), (SCH).map π ≫ a = (SCH).map π ≫ b → a = b := by
    intro Z a b hab
    have h1 : i₀.inv ≫ a = i₀.inv ≫ b := by
      refine desc_unique hsplit ?_
      rw [← Category.assoc, ← Category.assoc, ← hπ', Category.assoc, Category.assoc, hab]
    rwa [cancel_epi] at h1
  refine ⟨overHom f' (hcancel _ _ ?_), toScheme_map_injective ?_⟩
  · have e2 : (SCH).map g ≫ U.hom.hom = W.hom.hom := site_w g
    have e3 : (SCH).map π ≫ Q.hom.hom = W.hom.hom := site_w π
    rw [← Category.assoc, hwf, e2, e3]
  · rw [CategoryTheory.Functor.map_comp]
    exact hwf

/-- `X`-points of an affine chart: Step 4 reduces the local factorization to an invariant map to a chart. -/
theorem SDLocS_point_of_factor {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ] [UniqueSums Γ]
    {c : Coact A Γ} {ι : A₀ →+* A} (hι : c.IsInv ι) {W Q U : BigFppfOver B S hS} (π : W ⟶ Q)
    (i : (SCH).obj W ≅ Spec (.of A)) (i₀ : (SCH).obj Q ≅ Spec (.of A₀))
    (hπ : (SCH).map π ≫ i₀.hom = i.hom ≫ sp ι) (g : W ⟶ U)
    (hg : IsInvariantF c (i.inv ≫ (SCH).map g)) (u : X.obj (op U)) :
    ∃ y : X.obj (op Q), X.map π.op y = X.map g.op u := by
  obtain ⟨f, rfl⟩ := SDLocS_factor hι π i i₀ hπ g hg
  exact ⟨X.map f.op u, by rw [op_comp, Functor.map_comp_apply]⟩

/-- Step 3 (ii), the lifted action: if `a, a'` have the same image in `X`, a lift of `a` to `W'` determines the lift of `a'`
with the same projection to `U`. -/
theorem SDLocS_lift_action {U W W' T : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X) {x : X.obj (op W)}
    (p : W' ⟶ W) (s : W' ⟶ U) (hps : f.app (op W') s = X.map p.op x)
    (hu : ∀ {T : BigFppfOver B S hS} (a : T ⟶ W) (b : T ⟶ U), X.map a.op x = f.app (op T) b →
        ∃! l : T ⟶ W', l ≫ p = a ∧ l ≫ s = b)
    (a a' : T ⟶ W) (haa : X.map a.op x = X.map a'.op x) (l : T ⟶ W') (hl : l ≫ p = a) :
    ∃! l' : T ⟶ W', l' ≫ p = a' ∧ l' ≫ s = l ≫ s := by
  refine hu a' (l ≫ s) ?_
  have h1 : f.app (op T) (l ≫ s) = X.map l.op (f.app (op W') s) :=
    NatTrans.naturality_apply f l.op s
  rw [h1, hps, ← haa, ← hl, op_comp, Functor.map_comp_apply]

/-- What remains of Part B, Steps 3 (i)-(v) and the spreading of Step 4: near each point of `𝔸(P₀)_T`, for the étale
topology, `x` comes from a chart `U` through a map which is invariant for a grading presenting `W ×_Q V → V`. -/
def SDLocS_InvChart (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (Γ : Type u) [AddCommGroup Γ] : Prop :=
  ∀ {P P₀ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    (δ : P →+ Γ) (j : P₀ →+ P), Function.Injective j → (∀ p, δ p = 0 ↔ p ∈ Set.range j) →
    ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (x : X.obj (op (specObj P T))), IsInvPt X δ x →
    ∀ q : (SCH).obj (specObj P₀ T), ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj V))
      (e : V ⟶ specObj P₀ T), Etale ((SCH).map e) ∧ q ∈ Set.range ((SCH).map e) ∧
      ∃ (A A₀ : Type u) (_ : CommRing A) (_ : CommRing A₀) (c : Coact A Γ) (ι : A₀ →+* A) (_ : c.IsInv ι)
        (i : (SCH).obj (pullback (specAlong T j) e) ≅ Spec (.of A)) (i₀ : (SCH).obj V ≅ Spec (.of A₀))
        (_ : (SCH).map (pullback.snd (specAlong T j) e) ≫ i₀.hom = i.hom ≫ sp ι)
        (U : BigFppfOver B S hS) (u : X.obj (op U)) (g : pullback (specAlong T j) e ⟶ U),
        IsInvariantF c (i.inv ≫ (SCH).map g) ∧ X.map g.op u = X.map (pullback.fst (specAlong T j) e).op x

/-- Step 4: `SDExist_LocalFactor` from an invariant chart. -/
theorem SDLocS_localFactor {Γ : Type u} [AddCommGroup Γ] [UniqueSums Γ] (h : SDLocS_InvChart X Γ) :
    SDExist_LocalFactor X Γ := by
  intro P P₀ _ _ _ _ δ j hj hk T _ x hx q
  obtain ⟨V, hV, e, he, hq, A, A₀, _, _, c, ι, hι, i, i₀, hπ, U, u, g, hg, hgu⟩ := h δ j hj hk T x hx q
  obtain ⟨y, hy⟩ := SDLocS_point_of_factor hι (pullback.snd (specAlong T j) e) i i₀ hπ g hg u
  exact ⟨V, hV, e, he, hq, y, hy.trans hgu⟩

end AlgMag.SD

#print axioms AlgMag.SD.SDLocS_localFactor
#print axioms AlgMag.SD.SDLocS_chart
#print axioms AlgMag.SD.SDLocS_lift_action
#print axioms AlgMag.SD.SDLocS_factor
#print axioms AlgMag.SD.SDLocS_point_of_factor
