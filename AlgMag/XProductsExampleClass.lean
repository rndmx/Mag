/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsExampleCoord
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Example 4.4: the attractors of `ℙ¹`

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, Example 4.4.

## Main results

* `AlgMag.XP.fixed_dichotomy`: a `G_m`-fixed point of `ℙ¹` over a connected base is `0` or `∞`.
* `AlgMag.XP.attractor_lands`: a point of `X^{N_ε}` lands in one chart.
* `AlgMag.XP.ex44_attractor`: `X^{εN} → X` is `(ℙ¹ ∖ {∞}) ⊔ {∞} → ℙ¹`, over a connected base.
* `AlgMag.XP.ex44_zero`: `X^{⋂ N} = X^0 = {0, ∞}`, over a connected base.
* `AlgMag.XP.ex44_surjective`: **Example 4.4**: over a connected base `T`, `X^𝒩(T)` consists of the maps
  `z ↦ az` (`a` a unit) and the two constant maps. So `X^𝒩 = G_m ⊔ {0} ⊔ {∞}`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Polynomial LaurentPolynomial

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

noncomputable section

variable {T T' T'' : Scheme.{0}}

section Fixed

/-- A point `exPt b` does not lie in the other chart. -/
lemma exPt_notMem_range (b : Bool) (z : T) : exPt b T z ∉ Set.range (exFam.ι (!b)) := by
  intro hz
  let ξ := T.fromSpecResidueField z
  have hr : Set.range (ξ ≫ exPt b T) ⊆ Set.range (exFam.ι (!b)) := by
    rintro _ ⟨w, rfl⟩
    have hw : ξ w = z := by
      have : w = default := Subsingleton.elim _ _
      rw [this]
      exact T.fromSpecResidueField_apply z _
    change exPt b T (ξ w) ∈ _
    rw [hw]
    exact hz
  let a' := IsOpenImmersion.lift (exFam.ι (!b)) _ hr
  have ha' : a' ≫ exFam.ι (!b) = ξ ≫ exPt b T := IsOpenImmersion.lift_fac _ _ _
  rw [comp_exPt, exPt_eq] at ha'
  have h1 := coord_mul_of_overlap (b := b) _ _ ha'.symm
  rw [exCoord_mkPt, zero_mul] at h1
  exact not_isUnit_zero_of_nonempty (T := Spec (T.residueField z)) (h1 ▸ isUnit_one)

/-- **Example 4.4**: a `G_m`-fixed point of `ℙ¹` over a connected base is `0` or `∞`. -/
theorem fixed_dichotomy [ConnectedSpace T] (y : T ⟶ exFam.AN)
    (hfix : ∀ {T' : Scheme.{0}} (s : T' ⟶ T) (k : APt Scheme.Γ ℤ (op T')),
      exFam.smulN k (s ≫ y) = s ≫ y) :
    ∃ d, y = exPt d T := by
  let A : Bool → Set T := fun d => y ⁻¹' Set.range (exFam.ι d)
  have hAo : ∀ d, IsOpen (A d) := fun d =>
    (exFam.ι d).isOpenEmbedding.isOpen_range.preimage y.continuous
  have hcov : ∀ x, x ∈ A true ∨ x ∈ A false := by
    intro x
    obtain ⟨α, hα⟩ := exFam.exists_mem_range (y x)
    cases α
    · exact Or.inr hα
    · exact Or.inl hα
  have hlift : ∀ (T₂ : Scheme.{0}) (d : Bool) (a : T₂ ⟶ AZ (exFam.N d)) (s : T₂ ⟶ T),
      s ≫ y = a ≫ exFam.ι d → a = mkPt d 0 := by
    intro T₂ d a s e
    refine eq_mkPt_zero_of_fixed a fun {T₁} r k => ?_
    rw [← e, ← Category.assoc]
    exact hfix (r ≫ s) k
  have hdisj : ∀ x, x ∈ A true → x ∈ A false → False := by
    intro x h1 h2
    let ξ := T.fromSpecResidueField x
    have hw : ∀ w, ξ w = x := fun w => by
      have : w = default := Subsingleton.elim _ _
      rw [this]
      exact T.fromSpecResidueField_apply x _
    have hr : ∀ d, x ∈ A d → Set.range (ξ ≫ y) ⊆ Set.range (exFam.ι d) := by
      rintro d hd _ ⟨w, rfl⟩
      change y (ξ w) ∈ _
      rw [hw]
      exact hd
    have e1 : IsOpenImmersion.lift (exFam.ι true) _ (hr true h1) ≫ exFam.ι true = ξ ≫ y :=
      IsOpenImmersion.lift_fac _ _ _
    have e2 : IsOpenImmersion.lift (exFam.ι false) _ (hr false h2) ≫ exFam.ι false = ξ ≫ y :=
      IsOpenImmersion.lift_fac _ _ _
    have h3 := coord_mul_of_overlap (b := true) _ _ (e1.trans e2.symm)
    rw [hlift _ _ _ ξ e1.symm, exCoord_mkPt, zero_mul] at h3
    exact not_isUnit_zero_of_nonempty (T := Spec (T.residueField x)) (h3 ▸ isUnit_one)
  have hcl : IsClopen (A true) := by
    refine ⟨?_, hAo true⟩
    rw [← isOpen_compl_iff]
    convert hAo false using 1
    ext x
    exact ⟨fun h => (hcov x).resolve_left h, fun h h' => hdisj x h' h⟩
  have hland : ∀ d, A d = Set.univ → ∃ d', y = exPt d' T := by
    intro d hd
    have hr : Set.range y ⊆ Set.range (exFam.ι d) := by
      rintro _ ⟨w, rfl⟩
      have : w ∈ A d := by rw [hd]; trivial
      exact this
    have e : IsOpenImmersion.lift (exFam.ι d) y hr ≫ exFam.ι d = y := IsOpenImmersion.lift_fac _ _ _
    have e0 := hlift T d _ (𝟙 T) (by rw [Category.id_comp]; exact e.symm)
    exact ⟨d, by rw [exPt_eq, ← e0, e]⟩
  rcases isClopen_iff.mp hcl with h | h
  · refine hland false ?_
    ext x
    refine ⟨fun _ => trivial, fun _ => (hcov x).resolve_left fun hx => ?_⟩
    rw [h] at hx
    exact hx
  · exact hland true h

end Fixed

section Fv

variable {b : Bool} (φ : AttractorPt exAct (exFam.N b) T)

/-- The value `φ(r)` of a point of `X^{N_ε}` at the point of the chart with coordinate `r`. -/
def Fv {T' : Scheme.{0}} (t : T' ⟶ T) (r : Scheme.Γ.obj (op T')) : T' ⟶ exFam.AN :=
  φ.app t (powHom b r)

lemma powHom_res (s : T'' ⟶ T') (r : Scheme.Γ.obj (op T')) :
    APt.res s.op (powHom b r) = powHom b ((Scheme.Γ.map s.op).hom r) := by
  refine MonoidHom.ext fun n => ?_
  change (Scheme.Γ.map s.op).hom (r ^ exExp (Multiplicative.toAdd n)) =
    ((Scheme.Γ.map s.op).hom r) ^ exExp (Multiplicative.toAdd n)
  exact map_pow _ _ _

lemma Fv_comp (s : T'' ⟶ T') (t : T' ⟶ T) (r : Scheme.Γ.obj (op T')) :
    s ≫ Fv φ t r = Fv φ (s ≫ t) ((Scheme.Γ.map s.op).hom r) := by
  have h := φ.naturality s t (powHom b r)
  have e : APt.res (𝒪 := τO (𝟭 Scheme.{0})) s.op (powHom b r) =
      powHom b ((Scheme.Γ.map s.op).hom r) := powHom_res s r
  rw [e] at h
  exact h.symm

lemma Fv_smul (t : T' ⟶ T) (k : APt Scheme.Γ ℤ (op T')) (r : Scheme.Γ.obj (op T')) :
    Fv φ t (k (Multiplicative.ofAdd (exE b)) * r) = exFam.smulN k (Fv φ t r) := by
  have h := φ.equivariant t k (powHom b r)
  have e : (APt.toMagnet (exFam.N b) k * powHom b r : APt Scheme.Γ (exFam.N b) (op T')) =
      powHom b (k (Multiplicative.ofAdd (exE b)) * r) := by
    rw [eq_powHom (APt.toMagnet (exFam.N b) k * powHom b r)]
    congr 1
    change k (Multiplicative.ofAdd (exE b)) * (r ^ exExp (Multiplicative.toAdd (exGen b))) = _
    rw [exExp_gen, pow_one]
  have h' : φ.app t (APt.toMagnet (exFam.N b) k * powHom b r) = exFam.smulN k (φ.app t (powHom b r)) := h
  rw [show (APt.toMagnet (exFam.N b) k * powHom b r) =
    powHom b (k (Multiplicative.ofAdd (exE b)) * r) from e] at h'
  exact h'

/-- The value of `φ` at the point `0`: the limit point. -/
def y₀ : T ⟶ exFam.AN := Fv φ (𝟙 T) 0

lemma y₀_comp (s : T' ⟶ T) : s ≫ y₀ φ = Fv φ s 0 := by
  rw [y₀, Fv_comp, Category.comp_id]
  congr 1
  exact map_zero _

lemma y₀_fixed (s : T' ⟶ T) (k : APt Scheme.Γ ℤ (op T')) :
    exFam.smulN k (s ≫ y₀ φ) = s ≫ y₀ φ := by
  rw [y₀_comp, ← Fv_smul, mul_zero]

lemma powHom_one (T' : Scheme.{0}) : powHom b (1 : Scheme.Γ.obj (op T')) = 1 := by
  refine MonoidHom.ext fun n => ?_
  change (1 : Scheme.Γ.obj (op T')) ^ exExp (Multiplicative.toAdd n) = 1
  exact one_pow _

/-- `toPoint` is the value at the point `1`. -/
lemma toPoint_eq_Fv : φ.toPoint = Fv φ (𝟙 T) 1 := by
  change φ.app (𝟙 T) 1 = φ.app (𝟙 T) (powHom b 1)
  have : (powHom b (1 : Scheme.Γ.obj (op T)) : APt (τO (𝟭 Scheme.{0})) (exFam.N b) (op T)) = 1 :=
    powHom_one T
  rw [this]

end Fv

section Rings

variable {S S' : CommRingCat.{0}}

/-- `S → Γ(Spec S)`. -/
def invS (c : S) : Scheme.Γ.obj (op (Spec S)) := (Scheme.ΓSpecIso S).inv.hom c

lemma map_invS (θ : S ⟶ S') (c : S) :
    (Scheme.Γ.map (Spec.map θ).op).hom (invS c) = invS (θ.hom c) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality θ) c).symm

lemma invS_surj (r : Scheme.Γ.obj (op (Spec S))) : ∃ c : S, invS c = r :=
  ⟨(Scheme.ΓSpecIso S).hom.hom r, ConcreteCategory.congr_hom (Scheme.ΓSpecIso S).hom_inv_id r⟩

lemma invS_mul (c c' : S) : invS (c * c') = invS c * invS c' :=
  map_mul (Scheme.ΓSpecIso S).inv.hom c c'

lemma invS_zero : invS (0 : S) = 0 := map_zero (Scheme.ΓSpecIso S).inv.hom

lemma invS_one : invS (1 : S) = 1 := map_one (Scheme.ΓSpecIso S).inv.hom

/-- The character `n ↦ T^{nε}` of `R[T, T⁻¹]`. -/
def tCharB (R : CommRingCat.{0}) (b : Bool) :
    Multiplicative ℤ →* CommRingCat.of (AddMonoidAlgebra R ℤ) where
  toFun n := AddMonoidAlgebra.single (Multiplicative.toAdd n * exE b) 1
  map_one' := by
    change AddMonoidAlgebra.single ((0 : ℤ) * exE b) (1 : R) = 1
    rw [zero_mul]
    rfl
  map_mul' m n := by
    rw [AddMonoidAlgebra.single_mul_single, mul_one, toAdd_mul, add_mul]

/-- Coordinates of the action on the charts over `Spec S`. -/
lemma smulN_ptS {d : Bool} (κ : Multiplicative ℤ →* S) (g : S) :
    exFam.smulN (charS κ) (ptS d g ≫ exFam.ι d) =
      ptS d (κ (Multiplicative.ofAdd (exE d)) * g) ≫ exFam.ι d := by
  rw [exFam.smulN_comp_ι]
  congr 1
  apply coordS_inj
  rw [coordS_smulA, coordS_ptS, coordS_ptS]

lemma exCoord_ptS (d : Bool) (c : S) : exCoord (ptS d c) = invS c := exCoord_mkPt d _

lemma charS_apply (κ : Multiplicative ℤ →* S) (n : Multiplicative ℤ) :
    charS κ n = invS (κ n) := rfl

variable {b : Bool} (φ : AttractorPt exAct (exFam.N b) T)

lemma FvS_map (θ : S ⟶ S') (t₀ : Spec S ⟶ T) (c : S) :
    Spec.map θ ≫ Fv φ t₀ (invS c) = Fv φ (Spec.map θ ≫ t₀) (invS (θ.hom c)) := by
  rw [Fv_comp, map_invS]

lemma FvS_smul (κ : Multiplicative ℤ →* S) (t₀ : Spec S ⟶ T) (c : S) :
    Fv φ t₀ (invS (κ (Multiplicative.ofAdd (exE b)) * c)) =
      exFam.smulN (charS κ) (Fv φ t₀ (invS c)) := by
  rw [← Fv_smul, invS_mul, charS_apply]

end Rings

section Poly

variable {R : Type} [CommRing R]

/-- `R[X] → R[X][T, T⁻¹]`, `X ↦ T X`. -/
def rhoRing (R : Type) [CommRing R] : R[X] →+* AddMonoidAlgebra R[X] ℤ :=
  Polynomial.eval₂RingHom ((AddMonoidAlgebra.singleZeroRingHom).comp Polynomial.C)
    (AddMonoidAlgebra.single (1 : ℤ) (1 : R[X]) * AddMonoidAlgebra.single (0 : ℤ) Polynomial.X)

lemma rhoRing_monomial (m : ℕ) (g : R) :
    rhoRing R (Polynomial.monomial m g) =
      AddMonoidAlgebra.single (m : ℤ) (Polynomial.monomial m g) := by
  rw [rhoRing, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_pow]
  change AddMonoidAlgebra.single (0 : ℤ) (Polynomial.C g) * _ = _
  rw [AddMonoidAlgebra.single_mul_single, one_mul, Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  simp

lemma rhoRing_coeff (G : R[X]) (n : ℕ) :
    (rhoRing R G).coeff (n : ℤ) = Polynomial.monomial n (G.coeff n) := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, Polynomial.coeff_add, map_add]
  | monomial m g =>
    rw [rhoRing_monomial, AddMonoidAlgebra.coeff_single, Polynomial.coeff_monomial]
    by_cases h : m = n
    · subst h
      simp
    · have h' : (m : ℤ) ≠ n := by exact_mod_cast h
      rw [Finsupp.single_eq_of_ne' h', if_neg h, map_zero]

/-- The weight computation of Example 4.4: if `G(TX) = T^s G(X)`, then `G = g X` for `s = 1`, and
`G = 0` for `s = -1`. -/
lemma poly_weight_one {G : R[X]} (h : rhoRing R G = AddMonoidAlgebra.single (1 : ℤ) G) :
    G = Polynomial.monomial 1 (G.coeff 1) := by
  ext n
  by_cases hn : n = 1
  · subst hn
    simp
  · rw [Polynomial.coeff_monomial, if_neg (Ne.symm hn)]
    have h1 := rhoRing_coeff G n
    rw [h, AddMonoidAlgebra.coeff_single] at h1
    have hne : (1 : ℤ) ≠ n := by
      intro h'
      apply hn
      exact_mod_cast h'.symm
    rw [Finsupp.single_eq_of_ne' hne] at h1
    have h2 := congrArg (fun q : R[X] => q.coeff n) h1
    simpa using h2.symm

lemma poly_weight_neg {G : R[X]} (h : rhoRing R G = AddMonoidAlgebra.single (-1 : ℤ) G) : G = 0 := by
  ext n
  have h1 := rhoRing_coeff G n
  rw [h, AddMonoidAlgebra.coeff_single] at h1
  have hne : (-1 : ℤ) ≠ n := by omega
  rw [Finsupp.single_eq_of_ne' hne] at h1
  have h2 := congrArg (fun q : R[X] => q.coeff n) h1
  simpa using h2.symm

end Poly

section Lands

variable {b : Bool} (φ : AttractorPt exAct (exFam.N b) T)

/-- `Polynomial.C` as a morphism of `CommRingCat`. -/
def polyC (R : CommRingCat.{0}) : R ⟶ CommRingCat.of R[X] := CommRingCat.ofHom Polynomial.C

/-- Evaluation of polynomials at `c`. -/
def polyEv (R : CommRingCat.{0}) (c : R) : CommRingCat.of R[X] ⟶ R :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id R) c)

lemma polyC_polyEv (R : CommRingCat.{0}) (c : R) : polyC R ≫ polyEv R c = 𝟙 R := by
  ext x
  simp [polyC, polyEv]

lemma specMap_polyEv_polyC (R : CommRingCat.{0}) (c : R) :
    Spec.map (polyEv R c) ≫ Spec.map (polyC R) = 𝟙 _ := by
  rw [← Spec.map_comp, polyC_polyEv, Spec.map_id]

/-- `R[X] → R[T, T⁻¹]`. -/
def polyL (R : CommRingCat.{0}) : CommRingCat.of R[X] ⟶ CommRingCat.of (AddMonoidAlgebra R ℤ) :=
  CommRingCat.ofHom (Polynomial.toLaurent (R := R))

lemma polyC_polyL (R : CommRingCat.{0}) : polyC R ≫ polyL R = laurentC R := by
  exact CommRingCat.hom_ext (RingHom.ext fun x => Polynomial.toLaurent_C x)

lemma polyL_injective (R : CommRingCat.{0}) : Function.Injective (polyL R).hom :=
  Polynomial.toLaurent_injective

lemma spec_subsingleton (κ : CommRingCat.{0}) (hu : ∀ c : κ, c ≠ 0 → IsUnit c) : Subsingleton (Spec κ) := by
  have key : ∀ P : PrimeSpectrum κ, P.asIdeal = ⊥ := by
    intro P
    rw [eq_bot_iff]
    intro x hx
    by_contra h
    exact P.isPrime.ne_top ((Ideal.eq_top_of_isUnit_mem _ hx (hu x h)))
  exact ⟨fun P Q => PrimeSpectrum.ext ((key P).trans (key Q).symm)⟩

variable {d : Bool} (hy : y₀ φ = exPt d T)

include hy in
/-- The heart of Example 4.4: over a field, the value of `φ` lies in the chart of the limit point. The
line through `0` and `σ`, on which `φ` is equivariant, has its generic point in the open preimage of
that chart. -/
theorem lands_of_field (κ : CommRingCat.{0}) [IsDomain κ] (hu : ∀ c : κ, c ≠ 0 → IsUnit c)
    (τ₀ : Spec κ ⟶ T) (σ : κ) :
    Set.range (Fv φ τ₀ (invS σ)) ⊆ Set.range (exFam.ι d) := by
  by_contra hcon
  have hsub : Subsingleton (Spec κ) := spec_subsingleton κ hu
  let w₁ : Spec κ := (⊥ : PrimeSpectrum κ)
  let ξ := Fv φ τ₀ (invS σ)
  have hNo : ¬ Set.range ξ ⊆ Set.range (exFam.ι d) := hcon
  -- the point `ξ` is the constant `!d`
  have hξ : ξ = exPt (!d) (Spec κ) := by
    obtain ⟨_, ⟨w₀, rfl⟩, hw₀⟩ := Set.not_subset.mp hNo
    have hall : ∀ w, ξ w = ξ w₀ := fun w => congrArg ξ (Subsingleton.elim w w₀)
    obtain ⟨d', hd'⟩ := exFam.exists_mem_range (ξ w₀)
    have hd'' : d' = !d := by
      cases d' <;> cases d <;> first | rfl | exact (hw₀ hd').elim
    subst hd''
    have hr : Set.range ξ ⊆ Set.range (exFam.ι (!d)) := by
      rintro _ ⟨w, rfl⟩
      rw [hall]
      exact hd'
    let a := IsOpenImmersion.lift (exFam.ι (!d)) ξ hr
    have ha : a ≫ exFam.ι (!d) = ξ := IsOpenImmersion.lift_fac _ _ _
    by_cases hc : coordS a = 0
    · rw [exPt_eq, ← ha]
      congr 1
      apply (coordEquiv (!d) (Spec κ)).injective
      change exCoord a = exCoord (mkPt (!d) 0)
      rw [exCoord_mkPt]
      have := ConcreteCategory.congr_hom (Scheme.ΓSpecIso κ).hom_inv_id (exCoord a)
      refine this.symm.trans ?_
      have h0 : (Scheme.ΓSpecIso κ).hom.hom (exCoord a) = 0 := hc
      exact (congrArg (Scheme.ΓSpecIso κ).inv.hom h0).trans (map_zero _)
    · exfalso
      obtain ⟨u, hu'⟩ := hu _ hc
      have hmul : invS (coordS a) * invS (↑u⁻¹ : κ) = 1 := by
        rw [← invS_mul, ← hu', Units.mul_inv, invS_one]
      have e : exCoord a = invS (coordS a) :=
        (ConcreteCategory.congr_hom (Scheme.ΓSpecIso κ).hom_inv_id (exCoord a)).symm
      have hov := overlap_of_coord_mul (T := Spec κ) (b := !d) (invS (coordS a)) (invS (↑u⁻¹ : κ)) hmul
      rw [← e, mkPt_exCoord] at hov
      rw [ha] at hov
      apply hNo
      rw [hov]
      rintro _ ⟨w, rfl⟩
      rw [Bool.not_not]
      exact ⟨_, rfl⟩
  -- the line through `0` and `σ`
  let t₁ : Spec (CommRingCat.of κ[X]) ⟶ T := Spec.map (polyC κ) ≫ τ₀
  let Y' := Fv φ t₁ (invS (Polynomial.C σ * Polynomial.X : κ[X]))
  -- at the origin it is the limit point
  have horig : Spec.map (polyEv κ 0) ≫ Y' = exPt d (Spec κ) := by
    rw [FvS_map]
    have e1 : Spec.map (polyEv κ 0) ≫ t₁ = τ₀ := by
      change Spec.map (polyEv κ 0) ≫ Spec.map (polyC κ) ≫ τ₀ = τ₀
      rw [← Category.assoc, specMap_polyEv_polyC, Category.id_comp]
    have e2 : (polyEv κ 0).hom (Polynomial.C σ * Polynomial.X : κ[X]) = 0 := by
      simp [polyEv]
    rw [e1, e2, invS_zero, ← y₀_comp, hy, comp_exPt]
  -- on the punctured line it is the orbit of `ξ`
  have hpunct : Spec.map (polyL κ) ≫ Y' = exPt (!d) (Spec (.of (AddMonoidAlgebra κ ℤ))) := by
    rw [FvS_map]
    have e1 : Spec.map (polyL κ) ≫ t₁ = Spec.map (laurentC κ) ≫ τ₀ := by
      change Spec.map (polyL κ) ≫ Spec.map (polyC κ) ≫ τ₀ = _
      rw [← Category.assoc, ← Spec.map_comp, polyC_polyL]
    have e2 : (polyL κ).hom (Polynomial.C σ * Polynomial.X : κ[X]) =
        tCharB κ b (Multiplicative.ofAdd (exE b)) * (laurentC κ).hom σ := by
      change Polynomial.toLaurent (Polynomial.C σ * Polynomial.X) = AddMonoidAlgebra.single (exE b * exE b) (1 : κ) *
        AddMonoidAlgebra.single (0 : ℤ) σ
      rw [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X, exE_mul_self, mul_comm]
      rfl
    rw [e1, e2, FvS_smul, ← FvS_map]
    change exFam.smulN _ (Spec.map (laurentC κ) ≫ ξ) = _
    rw [hξ, comp_exPt, smulN_exPt]
  -- the generic point
  let o : Spec (CommRingCat.of κ[X]) := Spec.map (polyEv κ 0) w₁
  have hbot : (⊥ : PrimeSpectrum κ[X]) ⤳ (show PrimeSpectrum κ[X] from o) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  have hopen : IsOpen (Y' ⁻¹' Set.range (exFam.ι d)) :=
    (exFam.ι d).isOpenEmbedding.isOpen_range.preimage Y'.continuous
  have ho : o ∈ Y' ⁻¹' Set.range (exFam.ι d) := by
    change (Spec.map (polyEv κ 0) ≫ Y') w₁ ∈ Set.range (exFam.ι d)
    rw [horig, exPt_eq]
    exact ⟨_, rfl⟩
  have hη : (⊥ : PrimeSpectrum κ[X]) ∈ Y' ⁻¹' Set.range (exFam.ι d) := hbot.mem_open hopen ho
  have hcomap : (Spec.map (polyL κ)) (⊥ : PrimeSpectrum (AddMonoidAlgebra κ ℤ)) =
      (⊥ : PrimeSpectrum κ[X]) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (polyL κ).hom ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (polyL_injective κ)
  have hη' : (Spec.map (polyL κ) ≫ Y') (⊥ : PrimeSpectrum (AddMonoidAlgebra κ ℤ)) ∈
      Set.range (exFam.ι d) := by
    change Y' ((Spec.map (polyL κ)) (⊥ : PrimeSpectrum (AddMonoidAlgebra κ ℤ))) ∈ Set.range (exFam.ι d)
    rw [hcomap]
    exact hη
  rw [hpunct] at hη'
  have := exPt_notMem_range (T := Spec (.of (AddMonoidAlgebra κ ℤ))) (!d)
    (⊥ : PrimeSpectrum (AddMonoidAlgebra κ ℤ))
  rw [Bool.not_not] at this
  exact this hη'

include hy in
/-- The value of `φ` at the universal point lands in the chart of the limit point. -/
theorem lands_poly (R : CommRingCat.{0}) (t₀ : Spec R ⟶ T) :
    Set.range (Fv φ (Spec.map (polyC R) ≫ t₀) (invS (Polynomial.X : R[X]))) ⊆
      Set.range (exFam.ι d) := by
  rintro _ ⟨p, rfl⟩
  let W : Scheme.{0} := Spec (CommRingCat.of R[X])
  let Y : W ⟶ exFam.AN := Fv φ (Spec.map (polyC R) ≫ t₀) (invS (Polynomial.X : R[X]))
  let ξ := W.fromSpecResidueField p
  obtain ⟨σ, hσ⟩ := invS_surj ((Scheme.Γ.map ξ.op).hom (invS (Polynomial.X : R[X])))
  have e : ξ ≫ Y = Fv φ (ξ ≫ Spec.map (polyC R) ≫ t₀) (invS σ) := by
    rw [hσ]
    exact Fv_comp φ _ _ _
  have hl := lands_of_field φ hy (W.residueField p) (fun c hc => isUnit_iff_ne_zero.mpr hc)
    (ξ ≫ Spec.map (polyC R) ≫ t₀) σ
  let w : Spec (W.residueField p) := default
  have hw : ξ w = p := W.fromSpecResidueField_apply p _
  have : Y p = (ξ ≫ Y) w := by
    change Y p = Y (ξ w)
    rw [hw]
  change Y p ∈ Set.range (exFam.ι d)
  rw [this, e]
  exact hl ⟨w, rfl⟩

lemma comp_ptS {S S' : CommRingCat.{0}} {d' : Bool} (θ : S ⟶ S') (g : S) :
    Spec.map θ ≫ ptS d' g = ptS d' (θ.hom g) := by
  apply coordS_inj
  rw [coordS_comp, coordS_ptS, coordS_ptS]

include hy in
/-- The universal value of `φ` on `Spec R`: a polynomial `G` of weight `ε_d ε_b`, and `φ(c) = G(c)` in the
chart of the limit point. -/
theorem affine_formula (R : CommRingCat.{0}) (t₀ : Spec R ⟶ T) :
    ∃ G : R[X], rhoRing R G = AddMonoidAlgebra.single (exE d * exE b) G ∧
      ∀ c : R, Fv φ t₀ (invS c) = ptS d (Polynomial.eval₂ (RingHom.id R) c G) ≫ exFam.ι d := by
  let A : CommRingCat.{0} := CommRingCat.of R[X]
  let t₁ : Spec A ⟶ T := Spec.map (polyC R) ≫ t₀
  let Y : Spec A ⟶ exFam.AN := Fv φ t₁ (invS (Polynomial.X : R[X]))
  have hr := lands_poly φ hy R t₀
  let a : Spec A ⟶ AZ (exFam.N d) := IsOpenImmersion.lift (exFam.ι d) Y hr
  have ha : a ≫ exFam.ι d = Y := IsOpenImmersion.lift_fac _ _ _
  let G : R[X] := coordS a
  have hY : Y = ptS d G ≫ exFam.ι d := by rw [← ha, ptS_coordS a]
  refine ⟨G, ?_, fun c => ?_⟩
  · let ρ : A ⟶ CommRingCat.of (AddMonoidAlgebra A ℤ) := CommRingCat.ofHom (rhoRing R)
    let C' := laurentC A
    have hρC : polyC R ≫ ρ = polyC R ≫ C' := by
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      change rhoRing R (Polynomial.C x) = _
      rw [rhoRing, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    have hρX : ρ.hom (Polynomial.X : R[X]) =
        tCharB A b (Multiplicative.ofAdd (exE b)) * C'.hom (Polynomial.X : R[X]) := by
      change rhoRing R Polynomial.X = AddMonoidAlgebra.single (exE b * exE b) (1 : R[X]) *
        AddMonoidAlgebra.single (0 : ℤ) Polynomial.X
      rw [rhoRing, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, exE_mul_self]
    have h1 : Spec.map ρ ≫ Y = exFam.smulN (charS (tCharB A b)) (Spec.map C' ≫ Y) := by
      have e1 : Spec.map ρ ≫ t₁ = Spec.map C' ≫ t₁ := by
        change Spec.map ρ ≫ Spec.map (polyC R) ≫ t₀ = Spec.map C' ≫ Spec.map (polyC R) ≫ t₀
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hρC]
      change Spec.map ρ ≫ Fv φ t₁ (invS (Polynomial.X : R[X])) = exFam.smulN _ (Spec.map C' ≫ Fv φ t₁ _)
      rw [FvS_map, e1, hρX, FvS_smul, FvS_map]
    rw [hY, ← Category.assoc, ← Category.assoc, comp_ptS, comp_ptS, smulN_ptS] at h1
    have h2 := (cancel_mono (exFam.ι d)).mp h1
    have h3 := congrArg coordS h2
    rw [coordS_ptS, coordS_ptS] at h3
    have h4 : rhoRing R G = AddMonoidAlgebra.single (exE d * exE b) (1 : R[X]) *
        AddMonoidAlgebra.single (0 : ℤ) G := h3
    rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul] at h4
    exact h4
  · have h1 : Fv φ t₀ (invS c) = Spec.map (polyEv R c) ≫ Y := by
      change _ = Spec.map (polyEv R c) ≫ Fv φ t₁ (invS (Polynomial.X : R[X]))
      rw [FvS_map]
      have e1 : Spec.map (polyEv R c) ≫ t₁ = t₀ := by
        change Spec.map (polyEv R c) ≫ Spec.map (polyC R) ≫ t₀ = t₀
        rw [← Category.assoc, specMap_polyEv_polyC, Category.id_comp]
      have e2 : (polyEv R c).hom (Polynomial.X : R[X]) = c := by
        change Polynomial.eval₂RingHom (RingHom.id R) c Polynomial.X = c
        simp
      rw [e1, e2]
    rw [h1, hY, ← Category.assoc, comp_ptS]
    rfl

end Lands

section Global

variable {b : Bool} (φ : AttractorPt exAct (exFam.N b) T)

/-- Case of the limit point in the other chart: `φ` is the constant map. -/
theorem attractor_other (hy : y₀ φ = exPt (!b) T) {T' : Scheme.{0}} (t : T' ⟶ T)
    (r : Scheme.Γ.obj (op T')) : Fv φ t r = exPt (!b) T' := by
  refine T'.affineOpenCover.openCover.hom_ext _ _ fun j => ?_
  let R := T'.affineOpenCover.X j
  let f : Spec R ⟶ T' := T'.affineOpenCover.f j
  change f ≫ Fv φ t r = f ≫ exPt (!b) T'
  rw [Fv_comp, comp_exPt]
  obtain ⟨c, hc⟩ := invS_surj ((Scheme.Γ.map f.op).hom r)
  rw [← hc]
  obtain ⟨G, hG, hev⟩ := affine_formula φ hy R (f ≫ t)
  have hne : exE (!b) * exE b = -1 := by cases b <;> rfl
  rw [hne] at hG
  rw [hev, poly_weight_neg hG, Polynomial.eval₂_zero, exPt_eq]
  congr 1
  apply (coordEquiv _ _).injective
  change exCoord (ptS (!b) (0 : R)) = exCoord (mkPt (!b) 0)
  rw [exCoord_mkPt]
  exact (exCoord_ptS _ _).trans invS_zero

/-- Case of the limit point in the same chart: `φ(r) = g r`, with `g` the coordinate of `φ(1)`. -/
theorem attractor_same (hy : y₀ φ = exPt b T) :
    ∃ g : Scheme.Γ.obj (op T), ∀ {T' : Scheme.{0}} (t : T' ⟶ T) (r : Scheme.Γ.obj (op T')),
      Fv φ t r = mkPt b ((Scheme.Γ.map t.op).hom g * r) ≫ exFam.ι b := by
  have haff : ∀ (R : CommRingCat.{0}) (t₀ : Spec R ⟶ T), ∃ g : R, ∀ c : R,
      Fv φ t₀ (invS c) = ptS b (g * c) ≫ exFam.ι b := by
    intro R t₀
    obtain ⟨G, hG, hev⟩ := affine_formula φ hy R t₀
    rw [exE_mul_self] at hG
    refine ⟨G.coeff 1, fun c => ?_⟩
    rw [hev]
    congr 2
    conv_lhs => rw [poly_weight_one hG]
    simp
  let x : T ⟶ exFam.AN := Fv φ (𝟙 T) 1
  have hx : ∀ {T' : Scheme.{0}} (t : T' ⟶ T), t ≫ x = Fv φ t 1 := by
    intro T' t
    rw [Fv_comp, Category.comp_id]
    congr 1
    exact map_one _
  have hr : Set.range x ⊆ Set.range (exFam.ι b) := by
    rintro _ ⟨z, rfl⟩
    let 𝒰 := T.affineOpenCover.openCover
    obtain ⟨y, hy'⟩ := 𝒰.covers z
    obtain ⟨g, hg⟩ := haff _ (T.affineOpenCover.f (𝒰.idx z))
    have e : (T.affineOpenCover.f (𝒰.idx z)) ≫ x = _ := (hx _).trans
      ((congrArg _ invS_one.symm).trans (hg 1))
    have : x z = ((T.affineOpenCover.f (𝒰.idx z)) ≫ x) y := by
      change x z = x ((T.affineOpenCover.f (𝒰.idx z)) y)
      exact congrArg x hy'.symm
    rw [this, e]
    exact ⟨_, rfl⟩
  let a₁ : T ⟶ AZ (exFam.N b) := IsOpenImmersion.lift (exFam.ι b) x hr
  have ha₁ : a₁ ≫ exFam.ι b = x := IsOpenImmersion.lift_fac _ _ _
  refine ⟨exCoord a₁, fun {T'} t r => ?_⟩
  refine T'.affineOpenCover.openCover.hom_ext _ _ fun j => ?_
  let R := T'.affineOpenCover.X j
  let f : Spec R ⟶ T' := T'.affineOpenCover.f j
  change f ≫ Fv φ t r = f ≫ mkPt b _ ≫ exFam.ι b
  rw [Fv_comp]
  obtain ⟨c, hc⟩ := invS_surj ((Scheme.Γ.map f.op).hom r)
  rw [← hc]
  obtain ⟨g, hg⟩ := haff R (f ≫ t)
  rw [hg, ← Category.assoc]
  congr 1
  have hg1 : (f ≫ t) ≫ a₁ = ptS b g := by
    have e1 : (f ≫ t) ≫ a₁ ≫ exFam.ι b = ptS b g ≫ exFam.ι b := by
      rw [ha₁, hx]
      have := hg 1
      rw [mul_one, invS_one] at this
      exact this
    rw [← Category.assoc] at e1
    exact (cancel_mono (exFam.ι b)).mp e1
  have hg2 : (Scheme.Γ.map (f ≫ t).op).hom (exCoord a₁) = invS g := by
    rw [← exCoord_comp, hg1]
    exact exCoord_ptS _ _
  apply (coordEquiv _ _).injective
  change exCoord (ptS b (g * c)) = exCoord (f ≫ mkPt b _)
  rw [exCoord_comp, exCoord_mkPt]
  refine (exCoord_ptS _ _).trans ?_
  have e3 : (Scheme.Γ.map f.op).hom ((Scheme.Γ.map t.op).hom (exCoord a₁) * r) =
      (Scheme.Γ.map (f ≫ t).op).hom (exCoord a₁) * (Scheme.Γ.map f.op).hom r := by
    rw [map_mul, op_comp, Functor.map_comp]
    rfl
  refine Eq.trans ?_ e3.symm
  rw [hg2, ← hc]
  exact invS_mul g c

end Global

section Conclusion

variable [ConnectedSpace T]

/-- Every point of `X^{N_ε}`, for `b` and `T` connected, is in one chart or the constant in the other. -/
theorem attractor_cases {b : Bool} (φ : AttractorPt exAct (exFam.N b) T) :
    (∃ g : Scheme.Γ.obj (op T), ∀ {T' : Scheme.{0}} (t : T' ⟶ T) (r : Scheme.Γ.obj (op T')),
      Fv φ t r = mkPt b ((Scheme.Γ.map t.op).hom g * r) ≫ exFam.ι b) ∨
    (∀ {T' : Scheme.{0}} (t : T' ⟶ T) (r : Scheme.Γ.obj (op T')), Fv φ t r = exPt (!b) T') := by
  obtain ⟨d, hd⟩ := fixed_dichotomy (y₀ φ) (fun s k => y₀_fixed φ s k)
  by_cases h : d = b
  · subst h
    exact Or.inl (attractor_same φ hd)
  · have hd' : d = !b := by cases d <;> cases b <;> first | rfl | exact (h rfl).elim
    subst hd'
    exact Or.inr fun t r => attractor_other φ hd t r

/-- **Example 4.4**: `X^{εℕ} → X` is `(ℙ¹ ∖ {∞}) ⊔ {∞} → ℙ¹` over a connected base: the image consists of
the points of the chart `𝔸(N_ε)` and of the constant in the other chart. -/
theorem ex44_attractor {b : Bool} (φ : AttractorPt exAct (exFam.N b) T) :
    (∃ a : T ⟶ AZ (exFam.N b), φ.toPoint = a ≫ exFam.ι b) ∨ φ.toPoint = exPt (!b) T := by
  rw [toPoint_eq_Fv]
  rcases attractor_cases φ with ⟨g, hg⟩ | h
  · exact Or.inl ⟨_, hg (𝟙 T) 1⟩
  · exact Or.inr (h (𝟙 T) 1)

/-- The coordinate of a point of `𝔸(N_ε)`, on the site of all schemes. -/
def genVal {b : Bool} {T' : Scheme.{0}} (s : APt (τO (𝟭 Scheme.{0})) (exFam.N b) (op T')) :
    Scheme.Γ.obj (op T') := s (exGen b)

/-- **Example 4.4**, converse: every point of the chart `𝔸(N_ε)` underlies a point of `X^{εℕ}`. The point
with coordinate `g` is `r ↦ g r`. -/
def exLinear (b : Bool) (g : Scheme.Γ.obj (op T)) : AttractorPt exAct (exFam.N b) T where
  app {T'} t s := mkPt b ((Scheme.Γ.map t.op).hom g * genVal s) ≫ exFam.ι b
  naturality {T₁ T₂} u t s := by
    change mkPt b _ ≫ exFam.ι b = u ≫ mkPt b _ ≫ exFam.ι b
    rw [← Category.assoc]
    congr 1
    apply (coordEquiv b T₂).injective
    change exCoord (mkPt b _) = exCoord (u ≫ mkPt b _)
    rw [exCoord_comp, exCoord_mkPt, exCoord_mkPt, map_mul]
    congr 1
  equivariant {T₁} t k s := by
    change mkPt b _ ≫ exFam.ι b = exFam.smulN k (mkPt b _ ≫ exFam.ι b)
    rw [exFam.smulN_comp_ι]
    congr 1
    apply (coordEquiv b T₁).injective
    change exCoord (mkPt b _) = exCoord (smulA k (mkPt b _))
    rw [exCoord_smulA, exCoord_mkPt, exCoord_mkPt]
    exact mul_left_comm _ _ _

/-- **Example 4.4**, converse: the constant in the other chart underlies a point of `X^{εℕ}`. -/
def exLinearConst (b : Bool) (T : Scheme.{0}) : AttractorPt exAct (exFam.N b) T where
  app {T'} _ _ := exPt (!b) T'
  naturality u t s := (comp_exPt (!b) u).symm
  equivariant {T₁} t k s := (smulN_exPt (!b) (T := T₁) k).symm

lemma toPoint_exLinear (b : Bool) (g : Scheme.Γ.obj (op T)) :
    (exLinear b g).toPoint = mkPt b g ≫ exFam.ι b := by
  change mkPt b ((Scheme.Γ.map (𝟙 T).op).hom g *
    genVal (1 : APt (τO (𝟭 Scheme.{0})) (exFam.N b) (op T))) ≫ exFam.ι b = _
  have e1 : genVal (1 : APt (τO (𝟭 Scheme.{0})) (exFam.N b) (op T)) = 1 := rfl
  rw [e1, mul_one, op_id, Scheme.Γ.map_id]
  rfl

/-- **Example 4.4**, converse of `ex44_attractor`. -/
theorem ex44_attractor_converse (b : Bool) :
    (∀ a : T ⟶ AZ (exFam.N b), ∃ φ : AttractorPt exAct (exFam.N b) T, φ.toPoint = a ≫ exFam.ι b) ∧
      ∃ φ : AttractorPt exAct (exFam.N b) T, φ.toPoint = exPt (!b) T :=
  ⟨fun a => ⟨exLinear b (exCoord a), by rw [toPoint_exLinear, mkPt_exCoord]⟩,
    exLinearConst b T, rfl⟩

/-- A point of `X^𝒩` is determined by its restrictions to the `𝔸(N_α)`. -/
theorem ext_of_toProd (ψ ψ' : XNPt exFam (𝟭 Scheme.{0}) exAct T)
    (h : ∀ (b : Bool) {T' : Scheme.{0}} (t : T' ⟶ T) (r : Scheme.Γ.obj (op T')),
      (ψ.toProd.1 b).app t (powHom b r) = (ψ'.toProd.1 b).app t (powHom b r)) : ψ = ψ' := by
  refine XNPt.ext ?_
  funext T' t y
  have hF : Presieve.IsSheaf Scheme.zariskiTopology (yoneda.obj exFam.AN) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj exFam.AN)
  refine (hF _ (exFam.coverSieve_mem_zariski (W := T') y)).isSeparatedFor.ext fun V g hg => ?_
  obtain ⟨α, a, e⟩ := hg
  have key : ∀ χ : XNPt exFam (𝟭 Scheme.{0}) exAct T,
      g ≫ χ.app t y = (χ.toProd.1 α).app (g ≫ t) (powHom α (exCoord a)) := by
    intro χ
    have h1 := χ.naturality g t y
    have h2 : (𝟭 Scheme.{0}).map g ≫ y = a ≫ exFam.ι α := e
    rw [h2] at h1
    refine h1.symm.trans ?_
    change _ = χ.app (g ≫ t) ((ptsT (𝟭 Scheme.{0}) _ V).symm (powHom α (exCoord a)) ≫ exFam.ι α)
    congr 2
    have : ptsT (𝟭 Scheme.{0}) (exFam.N α) V a = powHom α (exCoord a) := eq_powHom _
    rw [← this, Equiv.symm_apply_apply]
  exact (key ψ).trans ((h α _ _).trans (key ψ').symm)

/-- The restriction of `z ↦ az` to the chart `𝔸(N_ε)`. -/
lemma exOrbit_toProd (a : Γ(T, ⊤)ˣ) (b : Bool) {T' : Scheme.{0}} (t : T' ⟶ T)
    (r : Scheme.Γ.obj (op T')) :
    ((exOrbit a).toProd.1 b).app t (powHom b r) =
      mkPt b ((Scheme.Γ.map t.op).hom (exChar a (Multiplicative.ofAdd (exE b))) * r) ≫ exFam.ι b := by
  change exFam.smulN (W := T') (APt.res (𝒪 := τO (𝟭 Scheme.{0})) t.op (exChar a))
    ((ptsT (𝟭 Scheme.{0}) _ T').symm (powHom b r) ≫ exFam.ι b) = _
  rw [exFam.smulN_comp_ι]
  congr 1
  apply (coordEquiv b T').injective
  change exCoord (smulA _ _) = exCoord (mkPt b _)
  rw [exCoord_smulA, exCoord_mkPt]
  congr 1
  exact exCoord_mkPt b r

/-- **Example 4.4**: over a connected base `T`, the `G_m`-equivariant maps `ℙ¹_T → ℙ¹_T` are the maps
`z ↦ az` (`a` a unit) and the two constant maps. Together with `ex44_injective`:
`X^𝒩(T) = Γ(T)ˣ ⊔ {0} ⊔ {∞}`, i.e. `X^𝒩 = G_m ⊔ {0} ⊔ {∞}`. -/
theorem ex44_surjective : Function.Surjective (exPoint T) := by
  intro ψ
  have : Nonempty T := ConnectedSpace.toNonempty
  have hT := ψ.toProd.2 true false
  rw [toPoint_eq_Fv, toPoint_eq_Fv] at hT
  have hunit : ∀ (b : Bool) (g : Scheme.Γ.obj (op T)),
      (Scheme.Γ.map (𝟙 T).op).hom g * 1 = g := by
    intro b g
    rw [mul_one, op_id, Scheme.Γ.map_id]
    rfl
  rcases attractor_cases (ψ.toProd.1 true) with ⟨g, hg⟩ | ht <;>
    rcases attractor_cases (ψ.toProd.1 false) with ⟨h, hh⟩ | hf
  · -- the case `z ↦ az`
    have e1 := hg (𝟙 T) 1
    have e2 := hh (𝟙 T) 1
    rw [hunit true g] at e1
    rw [hunit false h] at e2
    have hgh : g * h = 1 := by
      have := coord_mul_of_overlap (b := true) (mkPt true g) (mkPt false h)
        (e1.symm.trans (hT.trans e2))
      exact (congrArg₂ (· * ·) (exCoord_mkPt true g).symm (exCoord_mkPt false h).symm).trans this
    let a : Γ(T, ⊤)ˣ := ⟨g, h, hgh, (mul_comm h g).trans hgh⟩
    refine ⟨.inl a, ext_of_toProd _ _ fun b {T'} t r => ?_⟩
    refine (exOrbit_toProd a b t r).trans ?_
    cases b
    · refine Eq.trans ?_ (hh t r).symm
      congr 3
      congr 1
      change ((a ^ (-1 : ℤ) : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) = h
      rw [zpow_neg_one]
      rfl
    · refine Eq.trans ?_ (hg t r).symm
      congr 3
      congr 1
      change ((a ^ (1 : ℤ) : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) = g
      rw [zpow_one]
  · -- the constant `0`
    have e1 := hg (𝟙 T) 1
    have e2 := hf (𝟙 T) 1
    rw [hunit true g] at e1
    have hg0 : g = 0 := by
      have e3 : mkPt true g ≫ exFam.ι true = mkPt true 0 ≫ exFam.ι true := by
        rw [← e1, hT, e2]
        exact exPt_eq true
      have e4 := (cancel_mono (exFam.ι true)).mp e3
      exact (coordEquiv true T).symm.injective e4
    refine ⟨.inr true, ext_of_toProd _ _ fun b {T'} t r => ?_⟩
    change exPt true T' = _
    cases b
    · exact (hf t r).symm
    · refine Eq.trans ?_ (hg t r).symm
      rw [exPt_eq, hg0, map_zero, zero_mul]
  · -- the constant `∞`
    have e1 := ht (𝟙 T) 1
    have e2 := hh (𝟙 T) 1
    rw [hunit false h] at e2
    have hh0 : h = 0 := by
      have e3 : mkPt false h ≫ exFam.ι false = mkPt false 0 ≫ exFam.ι false := by
        rw [← e2, ← hT, e1]
        exact exPt_eq false
      have e4 := (cancel_mono (exFam.ι false)).mp e3
      exact (coordEquiv false T).symm.injective e4
    refine ⟨.inr false, ext_of_toProd _ _ fun b {T'} t r => ?_⟩
    change exPt false T' = _
    cases b
    · refine Eq.trans ?_ (hh t r).symm
      rw [exPt_eq, hh0, map_zero, zero_mul]
    · exact (ht t r).symm
  · -- the two constants would agree
    have e1 := ht (𝟙 T) 1
    have e2 := hf (𝟙 T) 1
    have e3 : exPt false T = exPt true T := e1.symm.trans (hT.trans e2)
    have := ex44_injective T (a₁ := .inr false) (a₂ := .inr true) e3
    simp at this

/-- **Example 4.4**: `X^{ε₁ℕ ∩ ε₂ℕ} = X^0 = {0, ∞}`, over a connected base: the image of a point of
`X^{⋂ N}` is `0` or `∞`. -/
theorem ex44_zero (χ : AttractorPt exAct (⨅ b, exFam.N b) T) : ∃ d, χ.toPoint = exPt d T := by
  let x : T ⟶ exFam.AN := χ.toPoint
  have hfix : ∀ {T' : Scheme.{0}} (s : T' ⟶ T) (k : APt Scheme.Γ ℤ (op T')),
      exFam.smulN k (s ≫ x) = s ≫ x := by
    intro T' s k
    let χ' := AttractorPt.baseChange s χ
    have e : s ≫ x = χ'.toPoint := (AttractorPt.toPoint_baseChange s χ).symm
    rw [e]
    have hk : APt.toMagnet (⨅ b, exFam.N b) (k : APt (τO (𝟭 Scheme.{0})) ℤ (op T')) * 1 = 1 := by
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
  exact fixed_dichotomy x hfix

end Conclusion

end

end AlgMag.XP

#print axioms AlgMag.XP.fixed_dichotomy
#print axioms AlgMag.XP.attractor_same
#print axioms AlgMag.XP.attractor_other
#print axioms AlgMag.XP.ex44_attractor
#print axioms AlgMag.XP.ex44_attractor_converse
#print axioms AlgMag.XP.ex44_surjective
#print axioms AlgMag.XP.ex44_zero
