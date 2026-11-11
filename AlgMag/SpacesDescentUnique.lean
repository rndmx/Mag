/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesDescentScheme

/-!
# Uniqueness in Lemma D for an algebraic space

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Propositions 3.31 (ii), 3.32 (ii), via the descent
lemma `AlgMag.SD.DescentProp`. Uniqueness: the equalizer `E → Q`
of two points of `X` over `Q` is a scheme, as the diagonal of `X` is representable; `W → E` is invariant, so the
scheme case gives a section of `E → Q`; a monomorphism with a section is an isomorphism. No closedness, and no
reduction to a torsion-free grading, is needed.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.GenM

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- The equalizer argument: if every monomorphism `E → Q` through which `π : W → Q` factors has a section, two
points of `X` over `Q` which agree over `W` are equal. Only the representability of the diagonal is used. -/
theorem SDUnique_of_section {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : yoneda.relativelyRepresentable (CategoryTheory.Limits.diag X)) {W Q : BigFppfOver B S hS} (π : W ⟶ Q)
    (H : ∀ (E : BigFppfOver B S hS) (e : E ⟶ Q) [Mono e] (ρ : W ⟶ E), ρ ≫ e = π → ∃ s : Q ⟶ E, s ≫ e = 𝟙 Q)
    (x y : X.obj (op Q)) (hxy : X.map π.op x = X.map π.op y) : x = y := by
  let u : yoneda.obj Q ⟶ X := yonedaEquiv.symm x
  let v : yoneda.obj Q ⟶ X := yonedaEquiv.symm y
  obtain ⟨E, e, f, hp⟩ := hX (prod.lift u v)
  have hfu : f = yoneda.map e ≫ u := by
    have h := hp.w =≫ prod.fst
    simpa using h
  have hfv : f = yoneda.map e ≫ v := by
    have h := hp.w =≫ prod.snd
    simpa using h
  have hm : Mono (yoneda.map e) := by
    refine ⟨fun {Z} a b hab => hp.hom_ext ?_ hab⟩
    rw [← cancel_mono (CategoryTheory.Limits.diag X), Category.assoc, Category.assoc, hp.w,
      ← Category.assoc, ← Category.assoc, hab]
  have hme : Mono e := by
    refine ⟨fun {Z} a b hab => yoneda.map_injective ?_⟩
    rw [← cancel_mono (yoneda.map e), ← yoneda.map_comp, ← yoneda.map_comp, hab]
  have hwu : yoneda.map π ≫ u = yoneda.map π ≫ v := by
    have key : ∀ z : X.obj (op Q), yonedaEquiv (yoneda.map π ≫ yonedaEquiv.symm z) = X.map π.op z :=
      fun z => by simp [yonedaEquiv_apply, yonedaEquiv_symm_app_apply]
    apply yonedaEquiv.injective
    rw [key, key, hxy]
  let r : yoneda.obj W ⟶ yoneda.obj E := hp.lift (yoneda.map π ≫ u) (yoneda.map π) (by
    ext1
    · simp
    · simp [hwu])
  have hr : r ≫ yoneda.map e = yoneda.map π := hp.lift_snd _ _ _
  obtain ⟨s, hs⟩ := H E e (yoneda.preimage r) (yoneda.map_injective (by
    rw [yoneda.map_comp, yoneda.map_preimage, hr]))
  have huv : u = v := by
    have h1 : yoneda.map (s ≫ e) = 𝟙 _ := by rw [hs, yoneda.map_id]
    calc u = yoneda.map (s ≫ e) ≫ u := by rw [h1, Category.id_comp]
      _ = yoneda.map s ≫ f := by rw [yoneda.map_comp, Category.assoc, hfu]
      _ = yoneda.map (s ≫ e) ≫ v := by rw [yoneda.map_comp, Category.assoc, hfv]
      _ = v := by rw [h1, Category.id_comp]
  exact yonedaEquiv.symm.injective huv

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Lemma D, uniqueness**, for a sheaf with representable diagonal, in the form of `DescentProp.uniq`. -/
theorem SDUnique_uniq (hX : yoneda.relativelyRepresentable (CategoryTheory.Limits.diag X))
    {P P₀ Γ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    [AddCommGroup Γ] [AddGroup.FG Γ] (δ : P →+ Γ) (j : P₀ →+ P) (hj : Function.Injective j)
    (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
    (x y : X.obj (op (specObj P₀ T)))
    (hxy : X.map (specAlong T j).op x = X.map (specAlong T j).op y) : x = y := by
  refine SDUnique_of_section hX (specAlong T j) ?_ x y hxy
  intro E e _ ρ hρ
  have hinv : IsInvPt (yoneda.obj E) δ ρ := by
    intro T' t g c
    change specLift t (g.comp (AddMonoidHom.toMultiplicative δ) * c) ≫ ρ = specLift t c ≫ ρ
    rw [← cancel_mono e, Category.assoc, Category.assoc, hρ, ← specLift_along, ← specLift_along]
    have hc : APt.along j (g.comp (AddMonoidHom.toMultiplicative δ) * c) = APt.along j c := by
      refine MonoidHom.ext fun p => ?_
      have h0 : δ (j (Multiplicative.toAdd p)) = 0 := (hk _).2 ⟨_, rfl⟩
      change g (Multiplicative.ofAdd (δ (j (Multiplicative.toAdd p)))) * _ = _
      rw [h0, ofAdd_zero, map_one, one_mul]
      rfl
    rw [hc]
  obtain ⟨s, hs⟩ := (descentProp_scheme E).desc δ j hj hk T ρ hinv
  have hs' : specAlong T j ≫ s = ρ := hs
  refine ⟨s, (descentProp_scheme (specObj P₀ T)).uniq δ j hj hk T _ _ ?_⟩
  change specAlong T j ≫ s ≫ e = specAlong T j ≫ 𝟙 _
  rw [← Category.assoc, hs', hρ, Category.comp_id]

/-- **Lemma D, uniqueness**, for an algebraic space. -/
theorem SDUnique_uniq_of_isAlgebraicSpace (hX : IsAlgebraicSpace B S hS X)
    {P P₀ Γ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    [AddCommGroup Γ] [AddGroup.FG Γ] (δ : P →+ Γ) (j : P₀ →+ P) (hj : Function.Injective j)
    (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
    (x y : X.obj (op (specObj P₀ T)))
    (hxy : X.map (specAlong T j).op x = X.map (specAlong T j).op y) : x = y :=
  SDUnique_uniq hX.diagonal_representable δ j hj hk T x y hxy

/-- `DescentProp` for an algebraic space follows from its existence half alone. -/
theorem SDUnique_descentProp (hX : IsAlgebraicSpace B S hS X)
    (hdesc : ∀ {P P₀ Γ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
      [AddCommGroup Γ] [AddGroup.FG Γ] (δ : P →+ Γ) (j : P₀ →+ P), Function.Injective j →
      (∀ p, δ p = 0 ↔ p ∈ Set.range j) → ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
      (x : X.obj (op (specObj P T))), IsInvPt X δ x → ∃ x₀, X.map (specAlong T j).op x₀ = x) :
    DescentProp X where
  uniq := fun δ j hj hk T _ x y h => SDUnique_uniq_of_isAlgebraicSpace hX δ j hj hk T x y h
  desc := hdesc

/-- **Lemma D, uniqueness, for a graded ring** (Step 2 of the note, for the torsion-free gradings and the base
changes used in Steps 3 and 4): `W`, `Q` are identified with `Spec A`, `Spec A₀`, with `A₀` the invariants. -/
theorem SDUnique_uniq_coact (hX : yoneda.relativelyRepresentable (CategoryTheory.Limits.diag X))
    {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ] [UniqueSums Γ]
    {c : Coact A Γ} {ι : A₀ →+* A} (hι : c.IsInv ι) {W Q : BigFppfOver B S hS} (π : W ⟶ Q)
    (i : (SCH).obj W ≅ Spec (.of A)) (i₀ : (SCH).obj Q ≅ Spec (.of A₀))
    (hπ : (SCH).map π ≫ i₀.hom = i.hom ≫ sp ι)
    (x y : X.obj (op Q)) (hxy : X.map π.op x = X.map π.op y) : x = y := by
  refine SDUnique_of_section hX π ?_ x y hxy
  intro E e _ ρ hρ
  have hme : Mono ((SCH).map e) := inferInstance
  have hπ' : i.inv ≫ (SCH).map π = sp ι ≫ i₀.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hσ : c.σ.comp ι = (cC A Γ).comp ι := by
    refine RingHom.ext fun a => ?_
    exact (hι.range (ι a)).2 ⟨a, rfl⟩
  have hF : IsInvariantF c (i.inv ≫ (SCH).map ρ) := by
    change sp c.σ ≫ _ = sp (cC A Γ) ≫ _
    rw [← cancel_mono ((SCH).map e)]
    have hm : i.inv ≫ (SCH).map ρ ≫ (SCH).map e = sp ι ≫ i₀.inv := by
      rw [← CategoryTheory.Functor.map_comp, hρ, hπ']
    have hs2 : sp c.σ ≫ sp ι = sp (cC A Γ) ≫ sp ι := by rw [← sp_comp, ← sp_comp, hσ]
    simp only [Category.assoc]
    rw [hm, ← Category.assoc, hs2, Category.assoc]
  obtain ⟨f, hf⟩ := exists_desc_of_torsionFree hι hF
  have hsplit := hι.isSplit
  let f' : (SCH).obj Q ⟶ (SCH).obj E := i₀.hom ≫ f
  have hwf : (SCH).map π ≫ f' = (SCH).map ρ := by
    change (SCH).map π ≫ i₀.hom ≫ f = _
    rw [← Category.assoc, hπ, Category.assoc, hf, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hcancel : ∀ {Z : Scheme.{u}} (a b : (SCH).obj Q ⟶ Z), (SCH).map π ≫ a = (SCH).map π ≫ b → a = b := by
    intro Z a b hab
    have h1 : i₀.inv ≫ a = i₀.inv ≫ b := by
      refine desc_unique hsplit ?_
      rw [← Category.assoc, ← Category.assoc, ← hπ', Category.assoc, Category.assoc, hab]
    rwa [cancel_epi] at h1
  refine ⟨overHom f' (hcancel _ _ ?_), toScheme_map_injective ?_⟩
  · have e2 : (SCH).map ρ ≫ E.hom.hom = W.hom.hom := site_w ρ
    have e3 : (SCH).map π ≫ Q.hom.hom = W.hom.hom := site_w π
    rw [← Category.assoc, hwf, e2, e3]
  · refine hcancel _ _ ?_
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    change (SCH).map π ≫ f' ≫ _ = _
    rw [← Category.assoc, hwf, ← CategoryTheory.Functor.map_comp, hρ]

end AlgMag.SD

#print axioms AlgMag.SD.SDUnique_of_section
#print axioms AlgMag.SD.SDUnique_uniq_of_isAlgebraicSpace
#print axioms AlgMag.SD.SDUnique_descentProp
#print axioms AlgMag.SD.SDUnique_uniq_coact
