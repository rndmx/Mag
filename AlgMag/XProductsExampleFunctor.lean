/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsExampleClass

/-!
# Example 4.4: the printed identifications of functors, on all `T`

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, Example 4.4, on the category of all
schemes, with `pt = ⊤_ Scheme` (`= Spec ℤ = S`), `0 = exPt true`, `∞ = exPt false`. No connectedness.

## Main results

* `AlgMag.XP.ex44AttrEquiv`: `X^{εℕ} = 𝔸(N_ε) ⊔ pt`, with `X^{εℕ} → X` the map `exMb`, that is
  `(ℙ¹ ∖ {∞}) ⊔ {∞} → ℙ¹` for `ε = +`.
* `AlgMag.XP.ex44XNEquiv`: `X^𝒩 = G_m ⊔ {0} ⊔ {∞}`, with `X^𝒩 → X` the monomorphism `exM`.
* `AlgMag.XP.ex44ZeroEquiv`: `X^{⋂ N} = X^0 = {0, ∞}`.
* each with the map to `X` (`*_toPoint`) and base-change compatibility (`*_comp`).
* `AlgMag.XP.ex44XNEquiv_orbit`, `AlgMag.XP.ex44XNEquiv_const`: under the identification, the summands are
  the maps `z ↦ az` and the two constant maps.
* `AlgMag.XP.exThm41`: **Theorem 4.1** in this example, on all schemes, by Zariski gluing.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

noncomputable section

variable {T T' : Scheme.{0}}

section Generic

/-- The open cover of `T` by a family of opens. -/
abbrev opCov {T : Scheme.{0}} {I : Type} (U : I → T.Opens) (hsup : ⨆ i, U i = ⊤) : T.OpenCover :=
  T.openCoverOfIsOpenCover U hsup

/-- Morphisms agreeing on an open cover are equal. -/
lemma hom_ext_of_opens {P : Scheme.{0}} {I : Type} (U : I → T.Opens) (hU : ∀ z : T, ∃ i, z ∈ U i)
    {a a' : T ⟶ P} (h : ∀ i, (U i).ι ≫ a = (U i).ι ≫ a') : a = a' := by
  have hsup : ⨆ i, U i = ⊤ := top_le_iff.mp fun z _ => by
    obtain ⟨i, hi⟩ := hU z
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  exact (T.openCoverOfIsOpenCover U hsup).hom_ext _ _ h

/-- A morphism which locally factors through a monomorphism factors through it. -/
theorem exists_factor_of_local {Y P : Scheme.{0}} (m : Y ⟶ P) [Mono m] (x : T ⟶ P) {I : Type}
    (U : I → T.Opens) (hU : ∀ z : T, ∃ i, z ∈ U i) (a : ∀ i, (U i).toScheme ⟶ Y)
    (ha : ∀ i, a i ≫ m = (U i).ι ≫ x) : ∃ t : T ⟶ Y, t ≫ m = x := by
  have hsup : ⨆ i, U i = ⊤ := top_le_iff.mp fun z _ => by
    obtain ⟨i, hi⟩ := hU z
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hf : ∀ i j : (opCov U hsup).I₀, pullback.fst ((opCov U hsup).f i) ((opCov U hsup).f j) ≫ a i =
      pullback.snd ((opCov U hsup).f i) ((opCov U hsup).f j) ≫ a j := by
    intro i j
    have := pullback.condition (f := (opCov U hsup).f i) (g := (opCov U hsup).f j)
    refine (cancel_mono m).mp ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ha i)).trans
      (Eq.trans ?_ ((congrArg (_ ≫ ·) (ha j)).symm.trans (Category.assoc _ _ _).symm))))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) this).trans (Category.assoc _ _ _))
  refine ⟨(opCov U hsup).glueMorphisms a hf, (opCov U hsup).hom_ext _ _ fun i => ?_⟩
  have e := (opCov U hsup).ι_glueMorphisms a hf i
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [e]
  exact ha i

lemma mem_inl_or_inr {A B : Scheme.{0}} (z : ↑(A ⨿ B)) :
    z ∈ Set.range (coprod.inl : A ⟶ A ⨿ B) ∨ z ∈ Set.range (coprod.inr : B ⟶ A ⨿ B) := by
  have := (isCompl_range_inl_inr A B).sup_eq_top
  have hz : z ∈ (Set.range (coprod.inl : A ⟶ A ⨿ B) ⊔ Set.range (coprod.inr : B ⟶ A ⨿ B)) := by
    rw [this]; trivial
  exact hz

/-- The piece of `T` mapped to the left summand. -/
def inlOpen {A B : Scheme.{0}} (t : T ⟶ A ⨿ B) : T.Opens :=
  t ⁻¹ᵁ (coprod.inl : A ⟶ A ⨿ B).opensRange

/-- The piece of `T` mapped to the right summand. -/
def inrOpen {A B : Scheme.{0}} (t : T ⟶ A ⨿ B) : T.Opens :=
  t ⁻¹ᵁ (coprod.inr : B ⟶ A ⨿ B).opensRange

lemma inl_inr_cover {A B : Scheme.{0}} (t : T ⟶ A ⨿ B) (z : T) :
    ∃ d : Bool, z ∈ (if d then inlOpen t else inrOpen t) := by
  rcases mem_inl_or_inr (t z) with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

lemma exists_lift_of_range {A P : Scheme.{0}} (i : A ⟶ P) [IsOpenImmersion i] (W : T.Opens)
    (t : T ⟶ P) (h : ∀ z ∈ W, t z ∈ Set.range i) : ∃ l : W.toScheme ⟶ A, l ≫ i = W.ι ≫ t := by
  have hr : Set.range (W.ι ≫ t) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    exact h w.1 w.2
  exact ⟨IsOpenImmersion.lift i _ hr, IsOpenImmersion.lift_fac _ _ _⟩

/-- A coproduct of monomorphisms with disjoint images is a monomorphism. -/
theorem mono_coprod_desc {A B P : Scheme.{0}} (f : A ⟶ P) (g : B ⟶ P) [Mono f] [Mono g]
    (hd : ∀ p q, f p ≠ g q) : Mono (coprod.desc f g) := by
  have hl : ∀ p : A, (coprod.desc f g) ((coprod.inl : A ⟶ A ⨿ B) p) = f p := fun p =>
    congrArg (fun k : A ⟶ P => k p) (coprod.inl_desc f g)
  have hr : ∀ q : B, (coprod.desc f g) ((coprod.inr : B ⟶ A ⨿ B) q) = g q := fun q =>
    congrArg (fun k : B ⟶ P => k q) (coprod.inr_desc f g)
  constructor
  intro W a a' e
  have hpt : ∀ w : W, (coprod.desc f g) (a w) = (coprod.desc f g) (a' w) := fun w =>
    congrArg (fun k : W ⟶ P => k w) e
  refine hom_ext_of_opens (I := Bool) (fun d => if d then inlOpen a else inrOpen a)
    (inl_inr_cover a) fun d => ?_
  cases d
  · change (inrOpen a).ι ≫ a = (inrOpen a).ι ≫ a'
    have h' : ∀ z ∈ inrOpen a, a' z ∈ Set.range (coprod.inr : B ⟶ A ⨿ B) := by
      rintro z ⟨q, hq⟩
      rcases mem_inl_or_inr (a' z) with ⟨p, hp⟩ | h
      · refine (hd p q ?_).elim
        have hq' : (coprod.inr : B ⟶ A ⨿ B) q = a z := hq
        rw [← hl, ← hr, hp, hq']
        exact (hpt z).symm
      · exact h
    obtain ⟨l, hl1⟩ := exists_lift_of_range (coprod.inr : B ⟶ A ⨿ B) (inrOpen a) a fun z hz => hz
    obtain ⟨l', hl2⟩ := exists_lift_of_range (coprod.inr : B ⟶ A ⨿ B) (inrOpen a) a' h'
    rw [← hl1, ← hl2]
    congr 1
    rw [← cancel_mono g, ← coprod.inr_desc f g, ← Category.assoc, ← Category.assoc, hl1, hl2,
      Category.assoc, Category.assoc, e]
  · change (inlOpen a).ι ≫ a = (inlOpen a).ι ≫ a'
    have h' : ∀ z ∈ inlOpen a, a' z ∈ Set.range (coprod.inl : A ⟶ A ⨿ B) := by
      rintro z ⟨p, hp⟩
      rcases mem_inl_or_inr (a' z) with h | ⟨q, hq⟩
      · exact h
      · refine (hd p q ?_).elim
        have hp' : (coprod.inl : A ⟶ A ⨿ B) p = a z := hp
        rw [← hl, ← hr, hq, hp']
        exact hpt z
    obtain ⟨l, hl1⟩ := exists_lift_of_range (coprod.inl : A ⟶ A ⨿ B) (inlOpen a) a fun z hz => hz
    obtain ⟨l', hl2⟩ := exists_lift_of_range (coprod.inl : A ⟶ A ⨿ B) (inlOpen a) a' h'
    rw [← hl1, ← hl2]
    congr 1
    rw [← cancel_mono f, ← coprod.inl_desc f g, ← Category.assoc, ← Category.assoc, hl1, hl2,
      Category.assoc, Category.assoc, e]

/-- The identification of a functor with a subfunctor given by a monomorphism. -/
def liftEquiv {Y P : Scheme.{0}} (m : Y ⟶ P) [Mono m] {B : Type*} (tp : B → (T ⟶ P))
    (inj : Function.Injective tp) (hr : ∀ x : T ⟶ P, (∃ a, tp a = x) ↔ ∃ t : T ⟶ Y, t ≫ m = x) :
    (T ⟶ Y) ≃ B :=
  Equiv.ofBijective (fun t => ((hr (t ≫ m)).2 ⟨t, rfl⟩).choose)
    ⟨fun t t' h => by
        have h1 := ((hr (t ≫ m)).2 ⟨t, rfl⟩).choose_spec
        have h2 := ((hr (t' ≫ m)).2 ⟨t', rfl⟩).choose_spec
        have h' : ((hr (t ≫ m)).2 ⟨t, rfl⟩).choose = ((hr (t' ≫ m)).2 ⟨t', rfl⟩).choose := h
        rw [h'] at h1
        exact (cancel_mono m).mp (h1.symm.trans h2),
      fun a => by
        obtain ⟨t, ht⟩ := (hr (tp a)).1 ⟨a, rfl⟩
        refine ⟨t, inj ?_⟩
        have h1 := ((hr (t ≫ m)).2 ⟨t, rfl⟩).choose_spec
        exact h1.trans ht⟩

lemma liftEquiv_spec {Y P : Scheme.{0}} (m : Y ⟶ P) [Mono m] {B : Type*} (tp : B → (T ⟶ P))
    (inj : Function.Injective tp) (hr : ∀ x : T ⟶ P, (∃ a, tp a = x) ↔ ∃ t : T ⟶ Y, t ≫ m = x)
    (t : T ⟶ Y) : tp (liftEquiv m tp inj hr t) = t ≫ m :=
  ((hr (t ≫ m)).2 ⟨t, rfl⟩).choose_spec

end Generic

section Schemes

/-- The point `pt = Spec ℤ = S`. -/
abbrev exPtS : Scheme.{0} := ⊤_ Scheme.{0}

instance (d : Bool) : Mono (exPt d exPtS) := terminalIsTerminal.mono_from _

/-- The scheme `𝔸(N_ε) ⊔ pt`. -/
abbrev exYb (b : Bool) : Scheme.{0} := AZ (exFam.N b) ⨿ exPtS

/-- `𝔸(N_ε) ⊔ pt → ℙ¹`, the inclusion of the chart and the constant in the other chart. -/
def exMb (b : Bool) : exYb b ⟶ exFam.AN := coprod.desc (exFam.ι b) (exPt (!b) exPtS)

/-- The scheme `{0} ⊔ {∞}`. -/
abbrev exY0 : Scheme.{0} := exPtS ⨿ exPtS

/-- `{0} ⊔ {∞} → ℙ¹`. -/
def exM0 : exY0 ⟶ exFam.AN := coprod.desc (exPt true exPtS) (exPt false exPtS)

/-- The scheme `G_m ⊔ {0} ⊔ {∞}`. -/
abbrev exY : Scheme.{0} := exFam.D ⨿ exY0

/-- `G_m ⊔ {0} ⊔ {∞} → ℙ¹`. -/
def exM : exY ⟶ exFam.AN := coprod.desc exFam.ιD exM0

/-- A constant is not in the other chart. -/
lemma exPt_ne_ι {d b : Bool} (h : d = !b) (p : T) (q : AZ (exFam.N b)) : exPt d T p ≠ exFam.ι b q := by
  subst h
  intro e
  have := exPt_notMem_range (!b) p
  rw [Bool.not_not] at this
  exact this ⟨q, e.symm⟩

instance (b : Bool) : Mono (exMb b) :=
  mono_coprod_desc _ _ fun p q e => exPt_ne_ι rfl q p e.symm

instance : Mono exM0 :=
  mono_coprod_desc _ _ fun p q e => by
    have h := exPt_eq (T := exPtS) false
    apply exPt_ne_ι (d := true) (b := false) rfl p (mkPt false 0 q)
    refine e.trans ?_
    rw [h]
    rfl

instance : Mono exM :=
  mono_coprod_desc _ _ fun p q e => by
    have hD : ∀ b, exFam.ιD p = exFam.ι b (exFam.gpMap b p) := fun b =>
      (congrArg (fun k : exFam.D ⟶ exFam.AN => k p) (exFam.gpMap_ι b)).symm
    rcases mem_inl_or_inr q with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · have e' : exFam.ιD p = exPt true exPtS r := by
        refine e.trans ?_
        exact congrArg (fun k : exPtS ⟶ exFam.AN => k r) (coprod.inl_desc _ _)
      exact exPt_ne_ι (d := true) (b := false) rfl r _ (e'.symm.trans (hD false))
    · have e' : exFam.ιD p = exPt false exPtS r := by
        refine e.trans ?_
        exact congrArg (fun k : exPtS ⟶ exFam.AN => k r) (coprod.inr_desc _ _)
      exact exPt_ne_ι (d := false) (b := true) rfl r _ (e'.symm.trans (hD true))

lemma comp_inr_exMb {V : Scheme.{0}} (b : Bool) (l : V ⟶ exPtS) :
    (l ≫ coprod.inr) ≫ exMb b = exPt (!b) V := by
  rw [Category.assoc, exMb, coprod.inr_desc, comp_exPt]

lemma comp_inl_exMb {V : Scheme.{0}} (b : Bool) (l : V ⟶ AZ (exFam.N b)) :
    (l ≫ coprod.inl) ≫ exMb b = l ≫ exFam.ι b := by
  rw [Category.assoc, exMb, coprod.inl_desc]

end Schemes

section Local

/-- The clopen decomposition of a `G_m`-fixed point: over the preimage of the chart `d`, it is the constant
`0` or `∞`. -/
theorem fixed_local (y : T ⟶ exFam.AN)
    (hfix : ∀ {T' : Scheme.{0}} (s : T' ⟶ T) (k : APt Scheme.Γ ℤ (op T')),
      exFam.smulN k (s ≫ y) = s ≫ y) (d : Bool) :
    (y ⁻¹ᵁ (exFam.ι d).opensRange).ι ≫ y = exPt d _ := by
  obtain ⟨a, ha⟩ := exFam.exists_lift_preimage y d
  have h0 := eq_mkPt_zero_of_fixed a fun {T₁} s k => by
    rw [← ha, ← Category.assoc]
    exact hfix _ k
  rw [ha, h0, exPt_eq]

variable {b : Bool}

lemma y₀_baseChange (φ : AttractorPt exAct (exFam.N b) T) (s : T' ⟶ T) :
    y₀ (AttractorPt.baseChange s φ) = s ≫ y₀ φ := by
  rw [y₀_comp]
  change φ.app (𝟙 T' ≫ s) _ = φ.app s _
  rw [Category.id_comp]

/-- The open of `T` where the limit point of `φ` lies in the chart `d`. -/
def limOpen (φ : AttractorPt exAct (exFam.N b) T) (d : Bool) : T.Opens :=
  y₀ φ ⁻¹ᵁ (exFam.ι d).opensRange

lemma limOpen_cover (φ : AttractorPt exAct (exFam.N b) T) (z : T) : ∃ d, z ∈ limOpen φ d := by
  obtain ⟨d, hd⟩ := exFam.exists_mem_range (y₀ φ z)
  exact ⟨d, hd⟩

/-- Restricting to an open inside `limOpen φ d` the limit point is the constant `d`. -/
lemma y₀_restrict (φ : AttractorPt exAct (exFam.N b) T) (d : Bool) {V : Scheme.{0}} (s : V ⟶ T)
    (hs : ∀ v, s v ∈ limOpen φ d) : y₀ (AttractorPt.baseChange s φ) = exPt d V := by
  rw [y₀_baseChange]
  have hr : Set.range s ⊆ Set.range (limOpen φ d).ι := by
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨_, hs v⟩, rfl⟩
  have hl := IsOpenImmersion.lift_fac (limOpen φ d).ι s hr
  have h := fixed_local (y₀ φ) (fun r k => y₀_fixed φ r k) d
  rw [← hl, Category.assoc]
  have h' : (limOpen φ d).ι ≫ y₀ φ = exPt d _ := h
  rw [h', comp_exPt]

/-- Extensionality of points of `X^N` over a Zariski cover of `T`. -/
lemma attractor_ext_of_cover {φ φ' : AttractorPt exAct (exFam.N b) T} {I : Type} (W : I → T.Opens)
    (hW : ∀ z : T, ∃ i, z ∈ W i)
    (h : ∀ i, AttractorPt.baseChange (W i).ι φ = AttractorPt.baseChange (W i).ι φ') : φ = φ' := by
  refine AttractorPt.ext ?_
  funext T' t a
  refine hom_ext_of_opens (T := T') (fun i => t ⁻¹ᵁ W i) (fun z => hW (t z)) fun i => ?_
  have key : ∀ χ : AttractorPt exAct (exFam.N b) T, (t ⁻¹ᵁ W i).ι ≫ χ.app t a =
      (AttractorPt.baseChange (W i).ι χ).app (t ∣_ W i) (APt.res (t ⁻¹ᵁ W i).ι.op a) := by
    intro χ
    have e := χ.naturality (t ⁻¹ᵁ W i).ι t a
    refine e.symm.trans ?_
    change χ.app _ _ = χ.app ((t ∣_ W i) ≫ (W i).ι) _
    rw [morphismRestrict_ι]
  rw [key φ, key φ', h i]

lemma attractor_eq_of_Fv {ψ ψ' : AttractorPt exAct (exFam.N b) T}
    (h : ∀ {T' : Scheme.{0}} (t : T' ⟶ T) (r : Scheme.Γ.obj (op T')), Fv ψ t r = Fv ψ' t r) :
    ψ = ψ' := by
  refine AttractorPt.ext ?_
  funext T' t a
  have e : a = powHom b (a (exGen b)) := eq_powHom a
  rw [e]
  exact h t _

/-- `toPoint` of a point with limit in its own chart lies in the chart. -/
lemma toPoint_same {ψ : AttractorPt exAct (exFam.N b) T} (hy : y₀ ψ = exPt b T) :
    ∃ a : T ⟶ AZ (exFam.N b), ψ.toPoint = a ≫ exFam.ι b := by
  obtain ⟨g, hg⟩ := attractor_same ψ hy
  rw [toPoint_eq_Fv]
  exact ⟨_, hg (𝟙 T) 1⟩

lemma toPoint_other {ψ : AttractorPt exAct (exFam.N b) T} (hy : y₀ ψ = exPt (!b) T) :
    ψ.toPoint = exPt (!b) T := by
  rw [toPoint_eq_Fv]
  exact attractor_other ψ hy (𝟙 T) 1

lemma eq_of_same {ψ ψ' : AttractorPt exAct (exFam.N b) T} (hy : y₀ ψ = exPt b T)
    (hy' : y₀ ψ' = exPt b T) (h : ψ.toPoint = ψ'.toPoint) : ψ = ψ' := by
  obtain ⟨g, hg⟩ := attractor_same ψ hy
  obtain ⟨g', hg'⟩ := attractor_same ψ' hy'
  have e1 := hg (𝟙 T) 1
  have e2 := hg' (𝟙 T) 1
  rw [← toPoint_eq_Fv] at e1 e2
  have hunit : ∀ g₀ : Scheme.Γ.obj (op T), (Scheme.Γ.map (𝟙 T).op).hom g₀ * 1 = g₀ := by
    intro g₀
    rw [mul_one, op_id, Scheme.Γ.map_id]
    rfl
  rw [hunit] at e1 e2
  have e3 := (cancel_mono (exFam.ι b)).mp (e1.symm.trans (h.trans e2))
  have hgg : g = g' := (coordEquiv b T).symm.injective e3
  subst hgg
  exact attractor_eq_of_Fv fun t r => (hg t r).trans (hg' t r).symm

lemma eq_of_other {ψ ψ' : AttractorPt exAct (exFam.N b) T} (hy : y₀ ψ = exPt (!b) T)
    (hy' : y₀ ψ' = exPt (!b) T) : ψ = ψ' :=
  attractor_eq_of_Fv fun t r => (attractor_other ψ hy t r).trans (attractor_other ψ' hy' t r).symm

/-- **Example 4.4**, on all `T`: `X^{εℕ} → X` is injective on `T`-points. -/
theorem attr_toPoint_injective (T : Scheme.{0}) :
    Function.Injective (AttractorPt.toPoint : AttractorPt exAct (exFam.N b) T → (T ⟶ exFam.AN)) := by
  intro φ φ' h
  have h' : φ.toPoint = φ'.toPoint := h
  -- on `limOpen φ d ∩ limOpen φ' (!d)` there are no points
  have hmix : ∀ (z : T) (d : Bool), z ∈ limOpen φ d → z ∈ limOpen φ' (!d) → False := by
    intro z d hd hd'
    let W := limOpen φ d ⊓ limOpen φ' (!d)
    have hW : ∀ v : W.toScheme, W.ι v ∈ limOpen φ d := fun v => v.2.1
    have hW' : ∀ v : W.toScheme, W.ι v ∈ limOpen φ' (!d) := fun v => v.2.2
    have e1 := y₀_restrict φ d W.ι hW
    have e2 := y₀_restrict φ' (!d) W.ι hW'
    have ht : (AttractorPt.baseChange W.ι φ).toPoint = (AttractorPt.baseChange W.ι φ').toPoint := by
      rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, h']
    let v : W.toScheme := ⟨z, hd, hd'⟩
    cases hdb : (d == b) with
    | true =>
      have hdb' : d = b := by simpa using hdb
      subst hdb'
      obtain ⟨a, ha⟩ := toPoint_same e1
      have := toPoint_other e2
      exact exPt_ne_ι (d := !d) (b := d) rfl v (a v)
        (congrArg (fun k : W.toScheme ⟶ exFam.AN => k v) (this.symm.trans (ht.symm.trans ha)))
    | false =>
      have hdb' : d = !b := by
        cases d <;> cases b <;> first | rfl | simp at hdb
      subst hdb'
      rw [Bool.not_not] at e2
      obtain ⟨a, ha⟩ := toPoint_same e2
      have := toPoint_other e1
      exact exPt_ne_ι (d := !b) (b := b) rfl v (a v)
        (congrArg (fun k : W.toScheme ⟶ exFam.AN => k v) (this.symm.trans (ht.trans ha)))
  refine attractor_ext_of_cover (I := Bool) (fun d => limOpen φ d ⊓ limOpen φ' d) (fun z => ?_)
    fun d => ?_
  · obtain ⟨d, hd⟩ := limOpen_cover φ z
    obtain ⟨d', hd'⟩ := limOpen_cover φ' z
    by_cases e : d' = d
    · subst e
      exact ⟨d', hd, hd'⟩
    · have : d' = !d := by cases d <;> cases d' <;> first | rfl | exact (e rfl).elim
      subst this
      exact (hmix z d hd hd').elim
  · let W := limOpen φ d ⊓ limOpen φ' d
    have e1 := y₀_restrict φ d W.ι fun v => v.2.1
    have e2 := y₀_restrict φ' d W.ι fun v => v.2.2
    by_cases e : d = b
    · subst e
      exact eq_of_same e1 e2 (by
        rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, h'])
    · have : d = !b := by cases d <;> cases b <;> first | rfl | exact (e rfl).elim
      subst this
      exact eq_of_other e1 e2

end Local

section Attr

variable {b : Bool}

lemma toPoint_exLinear' (b : Bool) (g : Scheme.Γ.obj (op T)) :
    (exLinear b g).toPoint = mkPt b g ≫ exFam.ι b := by
  change mkPt b ((Scheme.Γ.map (𝟙 T).op).hom g *
    genVal (1 : APt (τO (𝟭 Scheme.{0})) (exFam.N b) (op T))) ≫ exFam.ι b = _
  have e1 : genVal (1 : APt (τO (𝟭 Scheme.{0})) (exFam.N b) (op T)) = 1 := rfl
  rw [e1, mul_one, op_id, Scheme.Γ.map_id]
  rfl

/-- A point of `X` lying in `X^N` on a Zariski cover lies in `X^N`. -/
theorem exists_attr_of_cover (x : T ⟶ exFam.AN) {I : Type} (U : I → T.Opens)
    (hU : ∀ z : T, ∃ i, z ∈ U i)
    (h : ∀ i, ∃ φ : AttractorPt exAct (exFam.N b) (U i).toScheme, φ.toPoint = (U i).ι ≫ x) :
    ∃ φ : AttractorPt exAct (exFam.N b) T, φ.toPoint = x := by
  have hF : Presieve.IsSheaf Scheme.zariskiTopology (selfX exFam (𝟭 Scheme.{0})) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj exFam.AN)
  have hsup : ⨆ i, U i = ⊤ := top_le_iff.mp fun z _ => by
    obtain ⟨i, hi⟩ := hU z
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let R : Sieve T := Sieve.generate (opCov U hsup).presieve₀
  have hR : R ∈ Scheme.zariskiTopology T := (opCov U hsup).mem_grothendieckTopology
  have hsh := isSheaf_attractor exAct (exFam.N b) _ hF
  have h' : ∀ {Y : Scheme.{0}} (g : Y ⟶ T), R g →
      ∃ φ : AttractorPt exAct (exFam.N b) Y, φ.toPoint = g ≫ x := by
    rintro Y g ⟨W, a, c, ⟨i⟩, rfl⟩
    obtain ⟨φ, hφ⟩ := h i
    refine ⟨AttractorPt.baseChange a φ, (AttractorPt.toPoint_baseChange a φ).trans ?_⟩
    refine (congrArg (a ≫ ·) hφ).trans ?_
    exact (Category.assoc _ _ _).symm
  let fam : Presieve.FamilyOfElements (attractor exAct (exFam.N b)) R.arrows :=
    fun Y g hg => (h' g hg).choose
  have hfam : ∀ {Y} (g : Y ⟶ T) (hg : R g),
      AttractorPt.toPoint (fam g hg : AttractorPt exAct (exFam.N b) Y) = g ≫ x :=
    fun g hg => (h' g hg).choose_spec
  have hc : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    apply attr_toPoint_injective Z
    change AttractorPt.toPoint (AttractorPt.baseChange g₁ (fam f₁ h₁)) =
      AttractorPt.toPoint (AttractorPt.baseChange g₂ (fam f₂ h₂))
    rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, hfam f₁ h₁, hfam f₂ h₂]
    change g₁ ≫ f₁ ≫ x = g₂ ≫ f₂ ≫ x
    rw [← Category.assoc, ← Category.assoc, e]
  obtain ⟨φ, hφ, -⟩ := hsh R hR fam hc
  refine ⟨φ, (hF R hR).isSeparatedFor.ext fun Y g hg => ?_⟩
  have := congrArg AttractorPt.toPoint (hφ g hg)
  rw [show (selfX exFam (𝟭 Scheme.{0})).map g.op x = g ≫ x from rfl, ← hfam g hg, ← this]
  exact (AttractorPt.toPoint_baseChange g φ).symm

/-- **Example 4.4**, on all `T`: a point of `ℙ¹` is in the image of `X^{εℕ}` exactly when it factors through
`𝔸(N_ε) ⊔ pt → ℙ¹`. Includes the lift of the constant in the chart and the lift of the other constant. -/
theorem attr_range (x : T ⟶ exFam.AN) :
    (∃ φ : AttractorPt exAct (exFam.N b) T, φ.toPoint = x) ↔ ∃ t : T ⟶ exYb b, t ≫ exMb b = x := by
  constructor
  · rintro ⟨φ, rfl⟩
    have hloc : ∀ d : Bool, ∃ a : (limOpen φ d).toScheme ⟶ exYb b,
        a ≫ exMb b = (limOpen φ d).ι ≫ φ.toPoint := by
      intro d
      have e1 := y₀_restrict φ d (limOpen φ d).ι fun v => v.2
      have htp : (AttractorPt.baseChange (limOpen φ d).ι φ).toPoint =
          (limOpen φ d).ι ≫ φ.toPoint := AttractorPt.toPoint_baseChange _ _
      by_cases e : d = b
      · subst e
        obtain ⟨a, ha⟩ := toPoint_same e1
        exact ⟨a ≫ coprod.inl, by rw [comp_inl_exMb, ← ha, htp]⟩
      · have : d = !b := by cases d <;> cases b <;> first | rfl | exact (e rfl).elim
        subst this
        exact ⟨terminal.from _ ≫ coprod.inr, by rw [comp_inr_exMb, ← htp, toPoint_other e1]⟩
    choose a ha using hloc
    exact exists_factor_of_local (exMb b) _ (fun d => limOpen φ d) (limOpen_cover φ) a ha
  · rintro ⟨t, rfl⟩
    refine exists_attr_of_cover _ (I := Bool) (fun d => if d then inlOpen t else inrOpen t)
      (inl_inr_cover t) fun d => ?_
    cases d
    · change ∃ φ : AttractorPt exAct (exFam.N b) (inrOpen t).toScheme, φ.toPoint = (inrOpen t).ι ≫ _
      obtain ⟨l, hl⟩ := exists_lift_of_range (coprod.inr : exPtS ⟶ exYb b) (inrOpen t) t fun z hz => hz
      refine ⟨exLinearConst b _, ?_⟩
      rw [← Category.assoc, ← hl, comp_inr_exMb]
      rfl
    · change ∃ φ : AttractorPt exAct (exFam.N b) (inlOpen t).toScheme, φ.toPoint = (inlOpen t).ι ≫ _
      obtain ⟨l, hl⟩ := exists_lift_of_range (coprod.inl : AZ (exFam.N b) ⟶ exYb b) (inlOpen t) t
        fun z hz => hz
      refine ⟨exLinear b (exCoord l), ?_⟩
      rw [← Category.assoc, ← hl, comp_inl_exMb, toPoint_exLinear', mkPt_exCoord]

/-- **Example 4.4**, on all `T`: `X^{εℕ} = 𝔸(N_ε) ⊔ pt`. -/
def ex44AttrEquiv (b : Bool) (T : Scheme.{0}) : (T ⟶ exYb b) ≃ AttractorPt exAct (exFam.N b) T :=
  liftEquiv (exMb b) AttractorPt.toPoint (attr_toPoint_injective T) attr_range

/-- **Example 4.4**: `X^{εℕ} → X` is `exMb`: `(ℙ¹ ∖ {∞}) ⊔ {∞} → ℙ¹`, resp. `(ℙ¹ ∖ {0}) ⊔ {0} → ℙ¹`. -/
theorem ex44AttrEquiv_toPoint (b : Bool) (t : T ⟶ exYb b) :
    (ex44AttrEquiv b T t).toPoint = t ≫ exMb b :=
  liftEquiv_spec _ _ _ _ t

/-- **Example 4.4**: compatibility with base change. -/
theorem ex44AttrEquiv_comp (b : Bool) (s : T' ⟶ T) (t : T ⟶ exYb b) :
    ex44AttrEquiv b T' (s ≫ t) = AttractorPt.baseChange s (ex44AttrEquiv b T t) := by
  apply attr_toPoint_injective
  change AttractorPt.toPoint _ = AttractorPt.toPoint _
  rw [ex44AttrEquiv_toPoint, AttractorPt.toPoint_baseChange, ex44AttrEquiv_toPoint]
  exact Category.assoc _ _ _

end Attr

section Thm41

/-- `X^Z → X` is injective for `Z = ℤ`, in Example 4.4: `X^Z = X`. -/
lemma gp_toPoint_injective (T : Scheme.{0}) : Function.Injective
    (AttractorPt.toPoint : AttractorPt exAct exFam.Z.toAddSubmonoid T → (T ⟶ exFam.AN)) := by
  intro φ ψ h
  refine AttractorPt.ext ?_
  funext T' t a
  let k : APt (τO (𝟭 Scheme.{0})) ℤ (op T') :=
    a.comp (AddMonoidHom.toMultiplicative
      { toFun := fun n => (⟨n, trivial⟩ : exFam.Z.toAddSubmonoid)
        map_zero' := rfl
        map_add' := fun _ _ => rfl })
  have ha : APt.toMagnet exFam.Z.toAddSubmonoid k = a := MonoidHom.ext fun n => rfl
  have hh : φ.toPoint = ψ.toPoint := h
  rw [← ha, AttractorPt.app_eq_smul_toPoint, AttractorPt.app_eq_smul_toPoint, hh]

/-- **Theorem 4.1** in Example 4.4, on all schemes. -/
def exThm41 (T : Scheme.{0}) :
    XNPt exFam (𝟭 Scheme.{0}) exAct T ≃ XProdPt exFam (𝟭 Scheme.{0}) exAct T :=
  thm41Equiv (τ := 𝟭 Scheme.{0}) (J := Scheme.zariskiTopology)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj exFam.AN))
    (fun y => exFam.coverSieve_mem_zariski y) gp_toPoint_injective T

end Thm41

section XN

/-- `X^𝒩 → X` is injective on `T`-points, on all `T`. -/
theorem xn_toPoint_injective (T : Scheme.{0}) :
    Function.Injective (XNPt.toPoint : XNPt exFam (𝟭 Scheme.{0}) exAct T → (T ⟶ exFam.AN)) :=
  toPoint_injective_of_equiv (exThm41 T).injective fun b => attr_toPoint_injective T

/-- The constant `d` in `𝔸(N_ε) ⊔ pt`. -/
def exCst (b d : Bool) : exPtS ⟶ exYb b :=
  if d = b then mkPt b 0 ≫ coprod.inl else coprod.inr

lemma exCst_exMb (b d : Bool) : exCst b d ≫ exMb b = exPt d exPtS := by
  unfold exCst
  split_ifs with h
  · subst h
    rw [comp_inl_exMb, exPt_eq]
  · have hd : d = !b := by cases d <;> cases b <;> first | rfl | exact (h rfl).elim
    subst hd
    rw [exMb, coprod.inr_desc]

/-- `G_m ⊔ {0} ⊔ {∞} → 𝔸(N_ε) ⊔ pt`. -/
def exJ (b : Bool) : exY ⟶ exYb b :=
  coprod.desc (exFam.gpMap b ≫ coprod.inl) (coprod.desc (exCst b true) (exCst b false))

lemma exJ_exMb (b : Bool) : exJ b ≫ exMb b = exM := by
  refine coprod.hom_ext ?_ (coprod.hom_ext ?_ ?_)
  · rw [exJ, coprod.inl_desc_assoc, comp_inl_exMb, exFam.gpMap_ι, exM, coprod.inl_desc]
  · rw [exJ, coprod.inr_desc_assoc, coprod.inl_desc_assoc, exCst_exMb, exM, coprod.inr_desc,
      exM0, coprod.inl_desc]
  · rw [exJ, coprod.inr_desc_assoc, coprod.inr_desc_assoc, exCst_exMb, exM, coprod.inr_desc,
      exM0, coprod.inr_desc]

/-- **Example 4.4**, on all `T`: "fiber products commute with disjoint unions and fiber products of
immersions are intersections": a point of `ℙ¹` factoring through both `𝔸(N_ε) ⊔ pt` factors through
`G_m ⊔ {0} ⊔ {∞}`. -/
theorem factor_exM_of_both (x : T ⟶ exFam.AN) (tp : T ⟶ exYb true) (tm : T ⟶ exYb false)
    (hp : tp ≫ exMb true = x) (hm : tm ≫ exMb false = x) : ∃ t : T ⟶ exY, t ≫ exM = x := by
  let U : Fin 3 → T.Opens := ![inlOpen tp ⊓ inlOpen tm, inrOpen tp, inrOpen tm]
  have hU : ∀ z : T, ∃ i, z ∈ U i := by
    intro z
    rcases mem_inl_or_inr (tp z) with h1 | h1
    · rcases mem_inl_or_inr (tm z) with h2 | h2
      · exact ⟨0, h1, h2⟩
      · exact ⟨2, h2⟩
    · exact ⟨1, h1⟩
  have hloc : ∀ i, ∃ a : (U i).toScheme ⟶ exY, a ≫ exM = (U i).ι ≫ x := by
    intro i
    fin_cases i
    · change ∃ a : (inlOpen tp ⊓ inlOpen tm).toScheme ⟶ exY, a ≫ exM = (inlOpen tp ⊓ inlOpen tm).ι ≫ x
      obtain ⟨l₁, hl₁⟩ := exists_lift_of_range (coprod.inl : AZ (exFam.N true) ⟶ exYb true)
        (inlOpen tp ⊓ inlOpen tm) tp fun z hz => hz.1
      obtain ⟨l₂, hl₂⟩ := exists_lift_of_range (coprod.inl : AZ (exFam.N false) ⟶ exYb false)
        (inlOpen tp ⊓ inlOpen tm) tm fun z hz => hz.2
      have e₁ : l₁ ≫ exFam.ι true = (inlOpen tp ⊓ inlOpen tm).ι ≫ x := by
        rw [← comp_inl_exMb, hl₁, Category.assoc, hp]
      have e₂ : l₂ ≫ exFam.ι false = (inlOpen tp ⊓ inlOpen tm).ι ≫ x := by
        rw [← comp_inl_exMb, hl₂, Category.assoc, hm]
      obtain ⟨u, hu, -⟩ := exFam.exists_factor_of_overlap (by decide) l₁ l₂ (e₁.trans e₂.symm)
      refine ⟨u ≫ coprod.inl, ?_⟩
      rw [Category.assoc, exM, coprod.inl_desc, ← exFam.gpMap_ι true, ← Category.assoc, hu, e₁]
    · change ∃ a : (inrOpen tp).toScheme ⟶ exY, a ≫ exM = (inrOpen tp).ι ≫ x
      obtain ⟨l, hl⟩ := exists_lift_of_range (coprod.inr : exPtS ⟶ exYb true) (inrOpen tp) tp
        fun z hz => hz
      refine ⟨l ≫ coprod.inr ≫ coprod.inr, ?_⟩
      rw [← hp, ← Category.assoc (inrOpen tp).ι, ← hl, comp_inr_exMb, Category.assoc, Category.assoc,
        exM, coprod.inr_desc, exM0, coprod.inr_desc, comp_exPt]
      rfl
    · change ∃ a : (inrOpen tm).toScheme ⟶ exY, a ≫ exM = (inrOpen tm).ι ≫ x
      obtain ⟨l, hl⟩ := exists_lift_of_range (coprod.inr : exPtS ⟶ exYb false) (inrOpen tm) tm
        fun z hz => hz
      refine ⟨l ≫ coprod.inl ≫ coprod.inr, ?_⟩
      rw [← hm, ← Category.assoc (inrOpen tm).ι, ← hl, comp_inr_exMb, Category.assoc, Category.assoc,
        exM, coprod.inr_desc, exM0, coprod.inl_desc, comp_exPt]
      rfl
  choose a ha using hloc
  exact exists_factor_of_local exM x U hU a ha

/-- **Example 4.4**, on all `T`: the image of `X^𝒩 → X` is the image of `G_m ⊔ {0} ⊔ {∞}`. -/
theorem xn_range (x : T ⟶ exFam.AN) :
    (∃ ψ : XNPt exFam (𝟭 Scheme.{0}) exAct T, ψ.toPoint = x) ↔ ∃ t : T ⟶ exY, t ≫ exM = x := by
  constructor
  · rintro ⟨ψ, rfl⟩
    obtain ⟨tp, hp⟩ := (attr_range _).1 ⟨ψ.toProd.1 true, XNPt.toPoint_toProd ψ true⟩
    obtain ⟨tm, hm⟩ := (attr_range _).1 ⟨ψ.toProd.1 false, XNPt.toPoint_toProd ψ false⟩
    exact factor_exM_of_both _ tp tm hp hm
  · rintro ⟨t, rfl⟩
    have hb : ∀ b, ∃ φ : AttractorPt exAct (exFam.N b) T, φ.toPoint = t ≫ exM := fun b =>
      (attr_range _).2 ⟨t ≫ exJ b, by rw [Category.assoc, exJ_exMb]⟩
    choose Φ hΦ using hb
    let P : XProdPt exFam (𝟭 Scheme.{0}) exAct T := ⟨Φ, fun α β => (hΦ α).trans (hΦ β).symm⟩
    refine ⟨(exThm41 T).symm P, ?_⟩
    have e : ((exThm41 T).symm P).toProd = P := (exThm41 T).apply_symm_apply P
    rw [← XNPt.toPoint_toProd _ true, e]
    exact hΦ true

/-- **Example 4.4**, on all `T`: `X^𝒩 = G_m ⊔ {0} ⊔ {∞}`. -/
def ex44XNEquiv (T : Scheme.{0}) : (T ⟶ exY) ≃ XNPt exFam (𝟭 Scheme.{0}) exAct T :=
  liftEquiv exM XNPt.toPoint (xn_toPoint_injective T) xn_range

/-- **Example 4.4**: `X^𝒩 → X` is the monomorphism `exM`. -/
theorem ex44XNEquiv_toPoint (t : T ⟶ exY) : (ex44XNEquiv T t).toPoint = t ≫ exM :=
  liftEquiv_spec _ _ _ _ t

/-- **Example 4.4**: compatibility with base change. -/
theorem ex44XNEquiv_comp (s : T' ⟶ T) (t : T ⟶ exY) :
    ex44XNEquiv T' (s ≫ t) = (ex44XNEquiv T t).baseChange s := by
  apply xn_toPoint_injective
  change XNPt.toPoint _ = XNPt.toPoint _
  rw [ex44XNEquiv_toPoint, XNPt.toPoint_baseChange, ex44XNEquiv_toPoint]
  exact Category.assoc _ _ _

/-- **Example 4.4**: the summand `G_m` is the family of maps `z ↦ az`, `a` a unit. -/
theorem ex44XNEquiv_orbit (a : Γ(T, ⊤)ˣ) :
    ex44XNEquiv T ((pts exFam.Z.toAddSubmonoid T).symm (APt.toMagnet _ (exChar a)) ≫ coprod.inl) =
      exOrbit a := by
  apply xn_toPoint_injective
  change XNPt.toPoint _ = XNPt.toPoint _
  rw [ex44XNEquiv_toPoint, toPoint_exOrbit, Category.assoc, exM, coprod.inl_desc]

/-- **Example 4.4**: the summands `{0}`, `{∞}` are the two constant maps. -/
theorem ex44XNEquiv_const (d : Bool) :
    ex44XNEquiv T (terminal.from T ≫ (if d then coprod.inl else coprod.inr) ≫ coprod.inr) =
      exConst d T := by
  apply xn_toPoint_injective
  change XNPt.toPoint _ = XNPt.toPoint _
  rw [ex44XNEquiv_toPoint]
  change _ = exPt d T
  rw [Category.assoc, Category.assoc, exM, coprod.inr_desc]
  cases d
  · change terminal.from T ≫ coprod.inr ≫ exM0 = _
    rw [exM0, coprod.inr_desc, comp_exPt]
  · change terminal.from T ≫ coprod.inl ≫ exM0 = _
    rw [exM0, coprod.inl_desc, comp_exPt]

end XN

section Zero

lemma iInf_fixed (χ : AttractorPt exAct (⨅ b, exFam.N b) T) {T₁ : Scheme.{0}} (s : T₁ ⟶ T)
    (k : APt Scheme.Γ ℤ (op T₁)) : exFam.smulN k (s ≫ χ.toPoint) = s ≫ χ.toPoint := by
  let χ' := AttractorPt.baseChange s χ
  have e : s ≫ χ.toPoint = χ'.toPoint := (AttractorPt.toPoint_baseChange s χ).symm
  rw [e]
  have hk : APt.toMagnet (⨅ b, exFam.N b) (k : APt (τO (𝟭 Scheme.{0})) ℤ (op T₁)) * 1 = 1 := by
    refine MonoidHom.ext fun n => ?_
    have hn : n = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      have h4 : (⨅ b, exFam.N b) ≤ ⊥ := ex44_iInf.le
      exact AddSubmonoid.mem_bot.mp (h4 (Multiplicative.toAdd n).2)
    rw [hn]
    exact (map_one _).trans (map_one _).symm
  have heq := χ'.equivariant (𝟙 _) k 1
  rw [hk] at heq
  exact heq.symm

lemma iInf_apt_eq_one {T₁ : Scheme.{0}} (a : APt (τO (𝟭 Scheme.{0})) (⨅ b, exFam.N b : AddSubmonoid ℤ) (op T₁)) :
    a = 1 := by
  refine MonoidHom.ext fun n => ?_
  have hn : n = 1 := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    have h4 : (⨅ b, exFam.N b) ≤ ⊥ := ex44_iInf.le
    exact AddSubmonoid.mem_bot.mp (h4 (Multiplicative.toAdd n).2)
  rw [hn]
  exact (map_one _).trans (map_one _).symm

lemma iInf_app (χ : AttractorPt exAct (⨅ b, exFam.N b) T) {T₁ : Scheme.{0}} (t : T₁ ⟶ T)
    (a : APt (τO (𝟭 Scheme.{0})) (⨅ b, exFam.N b : AddSubmonoid ℤ) (op T₁)) : χ.app t a = t ≫ χ.toPoint := by
  have e := χ.naturality t (𝟙 T) 1
  rw [Category.comp_id, iInf_apt_eq_one (APt.res _ _)] at e
  rw [iInf_apt_eq_one a]
  exact e

/-- `X^0 → X` is injective on `T`-points. -/
theorem zero_toPoint_injective (T : Scheme.{0}) : Function.Injective
    (AttractorPt.toPoint : AttractorPt exAct (⨅ b, exFam.N b) T → (T ⟶ exFam.AN)) := by
  intro χ χ' h
  have h' : χ.toPoint = χ'.toPoint := h
  refine AttractorPt.ext ?_
  funext T₁ t a
  rw [iInf_app, iInf_app, h']

/-- **Example 4.4**, on all `T`: the image of `X^{⋂ N} → X` is the image of `{0} ⊔ {∞}`. -/
theorem zero_range (x : T ⟶ exFam.AN) :
    (∃ χ : AttractorPt exAct (⨅ b, exFam.N b) T, χ.toPoint = x) ↔ ∃ t : T ⟶ exY0, t ≫ exM0 = x := by
  constructor
  · rintro ⟨χ, rfl⟩
    have hfix : ∀ {T₁ : Scheme.{0}} (s : T₁ ⟶ T) (k : APt Scheme.Γ ℤ (op T₁)),
        exFam.smulN k (s ≫ χ.toPoint) = s ≫ χ.toPoint := fun s k => iInf_fixed χ s k
    let V : Bool → T.Opens := fun d => χ.toPoint ⁻¹ᵁ (exFam.ι d).opensRange
    have hV : ∀ z : T, ∃ d, z ∈ V d := fun z => exFam.exists_mem_range _
    have hloc : ∀ d, ∃ a : (V d).toScheme ⟶ exY0, a ≫ exM0 = (V d).ι ≫ χ.toPoint := by
      intro d
      have e : (V d).ι ≫ χ.toPoint = exPt d _ := fixed_local _ hfix d
      rw [e]
      cases d
      · exact ⟨terminal.from _ ≫ coprod.inr, by
          rw [Category.assoc, exM0, coprod.inr_desc, comp_exPt]⟩
      · exact ⟨terminal.from _ ≫ coprod.inl, by
          rw [Category.assoc, exM0, coprod.inl_desc, comp_exPt]⟩
    choose a ha using hloc
    exact exists_factor_of_local exM0 _ V hV a ha
  · rintro ⟨t, rfl⟩
    have hfixed : ∀ {T₁ : Scheme.{0}} (s : T₁ ⟶ T) (k : APt Scheme.Γ ℤ (op T₁)),
        exFam.smulN k (s ≫ t ≫ exM0) = s ≫ t ≫ exM0 := by
      intro T₁ s k
      refine hom_ext_of_opens (I := Bool) (fun d => if d then inlOpen (s ≫ t) else inrOpen (s ≫ t))
        (inl_inr_cover (s ≫ t)) fun d => ?_
      have key : ∀ (W : T₁.Opens) (d' : Bool), W.ι ≫ s ≫ t ≫ exM0 = exPt d' W.toScheme →
          W.ι ≫ exFam.smulN k (s ≫ t ≫ exM0) = W.ι ≫ s ≫ t ≫ exM0 := by
        intro W d' h
        rw [exFam.comp_smulN, h, smulN_exPt]
      cases d
      · refine key (inrOpen (s ≫ t)) false ?_
        obtain ⟨l, hl⟩ := exists_lift_of_range (coprod.inr : exPtS ⟶ exY0) (inrOpen (s ≫ t)) (s ≫ t)
          fun z hz => hz
        have e : (inrOpen (s ≫ t)).ι ≫ s ≫ t ≫ exM0 = (l ≫ coprod.inr) ≫ exM0 := by
          rw [hl]; simp only [Category.assoc]
        rw [e, Category.assoc, exM0, coprod.inr_desc, comp_exPt]
      · refine key (inlOpen (s ≫ t)) true ?_
        obtain ⟨l, hl⟩ := exists_lift_of_range (coprod.inl : exPtS ⟶ exY0) (inlOpen (s ≫ t)) (s ≫ t)
          fun z hz => hz
        have e : (inlOpen (s ≫ t)).ι ≫ s ≫ t ≫ exM0 = (l ≫ coprod.inl) ≫ exM0 := by
          rw [hl]; simp only [Category.assoc]
        rw [e, Category.assoc, exM0, coprod.inl_desc, comp_exPt]
    refine ⟨{ app := fun {T₁} s _ => s ≫ t ≫ exM0
              naturality := fun r s a => Category.assoc _ _ _
              equivariant := fun {T₁} s k a => (hfixed s k).symm }, ?_⟩
    exact Category.id_comp _

/-- **Example 4.4**, on all `T`: `X^{⋂ N} = X^0 = {0, ∞}`. -/
def ex44ZeroEquiv (T : Scheme.{0}) : (T ⟶ exY0) ≃ AttractorPt exAct (⨅ b, exFam.N b) T :=
  liftEquiv exM0 AttractorPt.toPoint (zero_toPoint_injective T) zero_range

theorem ex44ZeroEquiv_toPoint (t : T ⟶ exY0) : (ex44ZeroEquiv T t).toPoint = t ≫ exM0 :=
  liftEquiv_spec _ _ _ _ t

/-- **Example 4.4**: compatibility with base change. -/
theorem ex44ZeroEquiv_comp (s : T' ⟶ T) (t : T ⟶ exY0) :
    ex44ZeroEquiv T' (s ≫ t) = AttractorPt.baseChange s (ex44ZeroEquiv T t) := by
  apply zero_toPoint_injective
  change AttractorPt.toPoint _ = AttractorPt.toPoint _
  rw [ex44ZeroEquiv_toPoint, AttractorPt.toPoint_baseChange, ex44ZeroEquiv_toPoint]
  exact Category.assoc _ _ _

end Zero

end

end AlgMag.XP

#print axioms AlgMag.XP.ex44AttrEquiv
#print axioms AlgMag.XP.ex44AttrEquiv_comp
#print axioms AlgMag.XP.ex44XNEquiv
#print axioms AlgMag.XP.ex44XNEquiv_comp
#print axioms AlgMag.XP.ex44XNEquiv_orbit
#print axioms AlgMag.XP.ex44XNEquiv_const
#print axioms AlgMag.XP.ex44ZeroEquiv
#print axioms AlgMag.XP.ex44ZeroEquiv_comp
