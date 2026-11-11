/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDTorusRing
import AlgMag.SpacesDescentProps
import AlgMag.FinalMisc331

/-!
# Lemma D: the reduction to `Γ = ℤ^r`, and Propositions 3.31 (ii), 3.32 (ii) for algebraic spaces

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). Step 1 of the proof of Props. 3.31 (ii), 3.32 (ii).

For `q : ℤ^r → Γ` surjective, `Ã = O(T)[P ×_Γ ℤ^r]` is `ℤ^r`-graded by the second coordinate, with degree-zero part
`O(T)[P₀]`. The map `Spec O(T)[P × ℤ^r] → Spec Ã` is an fppf `D(Γ)`-torsor. Lemma D for `δ` follows from Lemma D for
`Ã`, that is from `UniqZr X` and `DescZr X`, the statements to be proved for `Γ = ℤ^r`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SDTorus

open AlgMag AlgMag.SQ AlgMag.SD

/-- `ℤ^r`, in the universe of the site. -/
abbrev Lat (r : ℕ) : Type u := ULift.{u} (Fin r → ℤ)

instance (r : ℕ) : AddGroup.FG (Lat.{u} r) := by
  have : AddGroup.FG (Fin r → ℤ) := Module.Finite.iff_addGroup_fg.1 inferInstance
  exact AddGroup.fg_of_surjective (f := (AddEquiv.ulift.{0, u} (α := Fin r → ℤ)).symm.toAddMonoidHom)
    (AddEquiv.ulift.symm.surjective)

/-- Every finitely generated group is a quotient of some `ℤ^r`. -/
theorem exists_surj (Γ : Type u) [AddCommGroup Γ] [AddGroup.FG Γ] :
    ∃ (r : ℕ) (q : Lat.{u} r →+ Γ), Function.Surjective q := by
  have : Module.Finite ℤ Γ := Module.Finite.iff_addGroup_fg.2 inferInstance
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' ℤ Γ
  exact ⟨r, f.toAddMonoidHom.comp (AddEquiv.ulift.{0, u} (α := Fin r → ℤ)).toAddMonoidHom,
    hf.comp AddEquiv.ulift.surjective⟩

section Monoid

variable {P Γ Λ : Type u} [AddCommMonoid P] [AddCommGroup Γ] [AddCommGroup Λ]

/-- Two points of `𝔸(P × Λ)` with the same image in `𝔸(P ×_Γ Λ)` differ by a point of `D(Γ)`. -/
theorem exists_torsor_elt (δ : P →+ Γ) {q : Λ →+ Γ} (hq : Function.Surjective q) {O : Type*} [CommMonoid O]
    (d₁ d₂ : Multiplicative (P × Λ) →* O)
    (h : ∀ x : Pt δ q, d₁ (Multiplicative.ofAdd (x : P × Λ)) = d₂ (Multiplicative.ofAdd (x : P × Λ))) :
    ∃ g : Multiplicative Γ →* O, ∀ p : P,
      d₂ (Multiplicative.ofAdd (p, 0)) = g (Multiplicative.ofAdd (δ p)) * d₁ (Multiplicative.ofAdd (p, 0)) := by
  have add : ∀ (d : Multiplicative (P × Λ) →* O) (a b : P × Λ),
      d (Multiplicative.ofAdd (a + b)) = d (Multiplicative.ofAdd a) * d (Multiplicative.ofAdd b) := by
    intro d a b
    rw [ofAdd_add, map_mul]
  let e : (Multiplicative (P × Λ) →* O) → Λ → O := fun d z => d (Multiplicative.ofAdd ((0 : P), z))
  have eadd : ∀ d (a b : Λ), e d (a + b) = e d a * e d b := by
    intro d a b
    change d _ = _
    rw [← add]
    congr 2
    exact Prod.ext (by simp) (by simp)
  have ezero : ∀ d, e d 0 = 1 := fun d => map_one d
  let u : Λ → O := fun z => e d₁ z * e d₂ (-z)
  have uadd : ∀ a b, u (a + b) = u a * u b := by
    intro a b
    simp only [u, neg_add, eadd]
    exact mul_mul_mul_comm _ _ _ _
  have hK : ∀ k, q k = 0 → e d₁ k = e d₂ k := by
    intro k hk
    exact h ⟨(0, k), mem_Pt.2 (by simp [hk])⟩
  have uwd : ∀ a b, q a = q b → u a = u b := by
    intro a b hab
    have hk : q (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have e1 : a = b + (a - b) := by abel
    have e2 : u (a - b) = 1 := by
      simp only [u]
      rw [hK _ hk, ← eadd, add_neg_cancel, ezero]
    rw [congrArg u e1, uadd, e2, mul_one]
  let σ := Function.surjInv hq
  have hσ : ∀ γ, q (σ γ) = γ := Function.surjInv_eq hq
  refine ⟨{ toFun := fun γ => u (σ (Multiplicative.toAdd γ))
            map_one' := ?_
            map_mul' := ?_ }, fun p => ?_⟩
  · have : u (σ 0) = u 0 := uwd _ _ (by rw [hσ, map_zero])
    refine this.trans ?_
    simp [u, ezero]
  · intro a b
    change u (σ (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [uwd _ (σ (Multiplicative.toAdd a) + σ (Multiplicative.toAdd b)) (by simp [hσ]), uadd]
  · change _ = u (σ (δ p)) * _
    have hz : d₁ (Multiplicative.ofAdd (p, σ (δ p))) = d₂ (Multiplicative.ofAdd (p, σ (δ p))) :=
      h ⟨(p, σ (δ p)), mem_Pt.2 (hσ _).symm⟩
    have s1 : ∀ d : Multiplicative (P × Λ) →* O, d (Multiplicative.ofAdd (p, σ (δ p))) =
        d (Multiplicative.ofAdd (p, 0)) * e d (σ (δ p)) := by
      intro d
      rw [← add]
      congr 2
      exact Prod.ext (by simp) (by simp)
    have s2 : e d₂ (σ (δ p)) * e d₂ (-σ (δ p)) = 1 := by
      rw [← eadd, add_neg_cancel, ezero]
    calc d₂ (Multiplicative.ofAdd (p, 0))
        = d₂ (Multiplicative.ofAdd (p, 0)) * (e d₂ (σ (δ p)) * e d₂ (-σ (δ p))) := by rw [s2, mul_one]
      _ = d₂ (Multiplicative.ofAdd (p, σ (δ p))) * e d₂ (-σ (δ p)) := by rw [s1, mul_assoc]
      _ = d₁ (Multiplicative.ofAdd (p, 0)) * e d₁ (σ (δ p)) * e d₂ (-σ (δ p)) := by rw [← hz, s1]
      _ = u (σ (δ p)) * d₁ (Multiplicative.ofAdd (p, 0)) := by
        simp only [u]
        rw [mul_assoc, mul_comm]

end Monoid

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- Uniqueness in **Lemma D** for `Γ = ℤ^r`. -/
def UniqZr (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (r : ℕ) {P P₀ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    (δ : P →+ Lat.{u} r) (j : P₀ →+ P), Function.Injective j →
    (∀ p, δ p = 0 ↔ p ∈ Set.range j) → ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
    (x y : X.obj (op (specObj P₀ T))),
    X.map (specAlong T j).op x = X.map (specAlong T j).op y → x = y

/-- Existence in **Lemma D** for `Γ = ℤ^r`. -/
def DescZr (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (r : ℕ) {P P₀ : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P₀] [Countable P₀]
    (δ : P →+ Lat.{u} r) (j : P₀ →+ P), Function.Injective j →
    (∀ p, δ p = 0 ↔ p ∈ Set.range j) → ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
    (x : X.obj (op (specObj P T))), IsInvPt X δ x → ∃ x₀, X.map (specAlong T j).op x₀ = x

section Along

variable {P P' P'' : Type u} [AddCommMonoid P] [Countable P] [AddCommMonoid P'] [Countable P']
  [AddCommMonoid P''] [Countable P''] (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

lemma specAlong_eq (g : P' →+ P) : specAlong T g = specLift (specPr P T) (APt.along g (specPt P T)) :=
  specLift_uniq _ _ _ (specAlong_pr T g) (res_specAlong T g)

lemma specAlong_comp (g : P' →+ P) (h : P'' →+ P') :
    specAlong T (g.comp h) = specAlong T g ≫ specAlong T h := by
  refine (specAlong_eq T _).trans (specLift_uniq _ _ _ ?_ ?_).symm
  · rw [Category.assoc, specAlong_pr, specAlong_pr]
  · rw [op_comp, APt.res_comp, res_specAlong]
    refine MonoidHom.ext fun p => ?_
    exact congrArg (fun a => a (AddMonoidHom.toMultiplicative h p)) (res_specAlong T g)

lemma specAlong_id : specAlong T (AddMonoidHom.id P) = 𝟙 _ := by
  refine (specAlong_eq T _).trans (specLift_uniq _ _ _ (Category.id_comp _) ?_).symm
  refine MonoidHom.ext fun p => ?_
  simp [APt.res, op_id]

end Along

section Reduction

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {P P₀ Γ Λ : Type u} [AddCommMonoid P] [Countable P]
  [AddCommMonoid P₀] [Countable P₀] [AddCommGroup Γ] [AddCommGroup Λ] [Countable Λ] [AddGroup.FG Λ]
  (δ : P →+ Γ) {q : Λ →+ Γ} (hq : Function.Surjective q) (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

include hq in
/-- `𝔸(P × Λ)_T → 𝔸(P ×_Γ Λ)_T` is an fppf cover. -/
theorem cover_Pt : Sieve.generate (Presieve.singleton (specAlong T (Pt δ q).subtype)) ∈
    BigFppfOver.topology B S hS (specObj (Pt δ q) T) := by
  have hfl : Flat (specAlong T (Pt δ q).subtype |> (BigFppfOver.toScheme B S hS).map) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (flat_of_isFreeAlong _ (isFreeAlong_Pt δ hq))
  have hlf : LocallyOfFinitePresentation (specAlong T (Pt δ q).subtype |> (BigFppfOver.toScheme B S hS).map) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr (fp_Pt δ hq _)
  have hsu : Surjective (specAlong T (Pt δ q).subtype |> (BigFppfOver.toScheme B S hS).map) :=
    ⟨comap_Pt_surjective δ hq _⟩
  exact Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS _ hsu hfl hlf

/-- Separatedness along the cover. -/
theorem ext_Pt (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) (hq : Function.Surjective q)
    {u v : X.obj (op (specObj (Pt δ q) T))}
    (h : X.map (specAlong T (Pt δ q).subtype).op u = X.map (specAlong T (Pt δ q).subtype).op v) : u = v := by
  have hsf := (Presieve.isSheafFor_iff_generate _).2 (hF _ (cover_Pt δ hq T))
  refine hsf.isSeparatedFor.ext ?_
  rintro W g ⟨⟩
  exact h

/-- Step 1: an invariant point descends along the torsor to `F̃` over `𝔸(P ×_Γ Λ)_T`. -/
theorem exists_tilde (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) (hq : Function.Surjective q)
    (x : X.obj (op (specObj P T))) (hx : IsInvPt X δ x) :
    ∃ y : X.obj (op (specObj (Pt δ q) T)),
      X.map (specAlong T (Pt δ q).subtype).op y = X.map (specAlong T (AddMonoidHom.inl P Λ)).op x := by
  have hsf := (Presieve.isSheafFor_iff_generate _).2 (hF _ (cover_Pt δ hq T))
  let x'' := X.map (specAlong T (AddMonoidHom.inl P Λ)).op x
  let fam : Presieve.FamilyOfElements X (Presieve.singleton (specAlong T (Pt δ q).subtype)) := fun _ f hf =>
    (Presieve.singleton.rec (motive := fun Y f _ => X.obj (op Y)) x'' hf)
  have hc : fam.Compatible := by
    rintro Y₁ Y₂ W g₁ g₂ f₁ f₂ ⟨⟩ ⟨⟩ comm
    change X.map g₁.op x'' = X.map g₂.op x''
    have ht : g₁ ≫ specPr (P × Λ) T = g₂ ≫ specPr (P × Λ) T := by
      rw [← specAlong_pr T (Pt δ q).subtype, ← Category.assoc, ← Category.assoc, comm]
    let d : (W ⟶ specObj (P × Λ) T) → APt (fppfO B S hS) (P × Λ) (op W) := fun g => APt.res g.op (specPt _ T)
    have hL : ∀ g : W ⟶ specObj (P × Λ) T, g ≫ specAlong T (AddMonoidHom.inl P Λ) =
        specLift (g ≫ specPr _ T) (APt.along (AddMonoidHom.inl P Λ) (d g)) := by
      intro g
      rw [specLift_along]
      exact congrArg (· ≫ specAlong T (AddMonoidHom.inl P Λ)) (specLift_uniq _ _ g rfl rfl)
    have hd : ∀ (g : W ⟶ specObj (P × Λ) T) (y : Pt δ q),
        d g (Multiplicative.ofAdd (y : P × Λ)) =
          APt.res (g ≫ specAlong T (Pt δ q).subtype).op (specPt (Pt δ q) T) (Multiplicative.ofAdd y) := by
      intro g y
      rw [op_comp, APt.res_comp, res_specAlong]
      rfl
    obtain ⟨γ, hγ⟩ := exists_torsor_elt δ hq (d g₁) (d g₂) (fun y => by rw [hd, hd, comm])
    have hA : APt.along (AddMonoidHom.inl P Λ) (d g₂) =
        γ.comp (AddMonoidHom.toMultiplicative δ) * APt.along (AddMonoidHom.inl P Λ) (d g₁) :=
      MonoidHom.ext fun p => hγ (Multiplicative.toAdd p)
    have h₀ := hx (g₁ ≫ specPr _ T) γ (APt.along (AddMonoidHom.inl P Λ) (d g₁))
    rw [← hA] at h₀
    change X.map g₁.op (X.map _ x) = X.map g₂.op (X.map _ x)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hL, hL, ← ht]
    exact h₀.symm
  obtain ⟨y, hy, -⟩ := hsf fam hc
  exact ⟨y, hy _ Presieve.singleton.mk⟩

/-- `P₀ → P ×_Γ Λ`, `k ↦ (j k, 0)`. -/
def jt (δ : P →+ Γ) (q : Λ →+ Γ) (j : P₀ →+ P) (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) : P₀ →+ Pt δ q :=
  ((AddMonoidHom.inl P Λ).comp j).codRestrict (Pt δ q) fun k => mem_Pt.2 (by
    simpa using (hk (j k)).2 ⟨k, rfl⟩)

/-- The `Λ`-grading of `P ×_Γ Λ`. -/
def dt (δ : P →+ Γ) (q : Λ →+ Γ) : Pt δ q →+ Λ := (AddMonoidHom.snd P Λ).comp (Pt δ q).subtype

lemma subtype_jt (q : Λ →+ Γ) (j : P₀ →+ P) (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) :
    (Pt δ q).subtype.comp (jt δ q j hk) = (AddMonoidHom.inl P Λ).comp j := rfl

lemma jt_inj (q : Λ →+ Γ) {j : P₀ →+ P} (hj : Function.Injective j) (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) :
    Function.Injective (jt δ q j hk) := fun a b h =>
  hj (congrArg (fun y : Pt δ q => (y : P × Λ).1) h)

lemma dt_eq_zero (q : Λ →+ Γ) (j : P₀ →+ P) (hk : ∀ p, δ p = 0 ↔ p ∈ Set.range j) (y : Pt δ q) :
    dt δ q y = 0 ↔ y ∈ Set.range (jt δ q j hk) := by
  constructor
  · intro h0
    have h0' : (y : P × Λ).2 = 0 := h0
    have hp : δ (y : P × Λ).1 = 0 := by rw [mem_Pt.1 y.2, h0', map_zero]
    obtain ⟨k, hk'⟩ := (hk _).1 hp
    exact ⟨k, Subtype.ext (Prod.ext hk' h0'.symm)⟩
  · rintro ⟨k, rfl⟩
    rfl

/-- `F̃` is invariant for the `ℤ^r`-grading: the statement `IsInvPt` needed by `DescZr`. -/
theorem isInvPt_tilde (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) (hq : Function.Surjective q)
    {x : X.obj (op (specObj P T))} {y : X.obj (op (specObj (Pt δ q) T))}
    (hy : X.map (specAlong T (Pt δ q).subtype).op y = X.map (specAlong T (AddMonoidHom.inl P Λ)).op x) :
    IsInvPt X (dt δ q) y := by
  intro T' t g c
  -- on the cover, `c` lifts to `𝔸(P × Λ)`
  have hcov := (BigFppfOver.topology B S hS).pullback_stable (specLift t c) (cover_Pt δ hq T)
  have hsep := (hF _ hcov).isSeparatedFor
  refine hsep.ext ?_
  rintro W s ⟨Z, w, f, ⟨⟩, hf⟩
  let d : APt (fppfO B S hS) (P × Λ) (op W) := APt.res w.op (specPt _ T)
  have hd : APt.along (Pt δ q).subtype d = APt.res s.op c := by
    have e : APt.along (Pt δ q).subtype d =
        APt.res (w ≫ specAlong T (Pt δ q).subtype).op (specPt (Pt δ q) T) := by
      rw [op_comp, APt.res_comp, res_specAlong]
      rfl
    rw [e, hf, op_comp, APt.res_comp, res_specLift]
  have main : ∀ (t' : W ⟶ T) (d' : APt (fppfO B S hS) (P × Λ) (op W)),
      X.map (specLift t' (APt.along (Pt δ q).subtype d')).op y =
        X.map (specLift t' (APt.along (AddMonoidHom.inl P Λ) d')).op x := by
    intro t' d'
    rw [specLift_along, specLift_along, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hy]
  let G : APt (fppfO B S hS) Λ (op W) := APt.res s.op g
  let d' : APt (fppfO B S hS) (P × Λ) (op W) := d * G.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd P Λ))
  have e1 : APt.along (Pt δ q).subtype d' = APt.res s.op (g.comp (AddMonoidHom.toMultiplicative (dt δ q)) * c) := by
    rw [APt.res_mul, ← hd]
    refine MonoidHom.ext fun p => mul_comm _ _
  have e2 : APt.along (AddMonoidHom.inl P Λ) d' = APt.along (AddMonoidHom.inl P Λ) d := by
    refine MonoidHom.ext fun p => ?_
    change d _ * G (Multiplicative.ofAdd 0) = d _
    have : G (Multiplicative.ofAdd (0 : Λ)) = 1 := map_one G
    rw [this, mul_one]
  change X.map s.op (X.map _ y) = X.map s.op (X.map _ y)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, ← specLift_comp, ← specLift_comp,
    ← e1, ← hd, main, main, e2]

/-- **Lemma D, Step 1**: Lemma D for `Γ` from Lemma D for `ℤ^r`. -/
theorem descentProp_of_zr (hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X) (hU : UniqZr X) (hE : DescZr X) :
    DescentProp X where
  uniq := by
    intro P P₀ Γ _ _ _ _ _ _ δ j hj hk T _ x y h
    obtain ⟨r, q, hq⟩ := exists_surj Γ
    refine hU r (dt δ q) (jt δ q j hk) (jt_inj δ q hj hk) (dt_eq_zero δ q j hk) T x y (ext_Pt δ T hX hq ?_)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← specAlong_comp, subtype_jt,
      specAlong_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h]
  desc := by
    intro P P₀ Γ _ _ _ _ _ _ δ j hj hk T _ x hx
    obtain ⟨r, q, hq⟩ := exists_surj Γ
    obtain ⟨y, hy⟩ := exists_tilde δ T hX hq x hx
    obtain ⟨x₀, h₀⟩ := hE r (dt δ q) (jt δ q j hk) (jt_inj δ q hj hk) (dt_eq_zero δ q j hk) T y
      (isInvPt_tilde δ T hX hq hy)
    refine ⟨x₀, ?_⟩
    -- restrict along `w ↦ (w, 1)`
    let s : P × Lat r →+ P := AddMonoidHom.fst P (Lat r)
    have e1 : j = (s.comp (Pt δ q).subtype).comp (jt δ q j hk) := rfl
    have e2 : X.map (specAlong T j).op x₀ = X.map (specAlong T (s.comp (Pt δ q).subtype)).op y := by
      rw [← h₀, ← Functor.map_comp_apply, ← op_comp, ← specAlong_comp, ← e1]
    rw [e2, specAlong_comp, op_comp, Functor.map_comp_apply, hy, ← Functor.map_comp_apply, ← op_comp,
      ← specAlong_comp]
    have e3 : s.comp (AddMonoidHom.inl P (Lat r)) = AddMonoidHom.id P := rfl
    rw [e3, specAlong_id]
    simp

end Reduction

section Final

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Lemma D** for an algebraic space, given the case `Γ = ℤ^r`. -/
theorem descentProp_space (hX : IsAlgebraicSpace B S hS X) (hU : UniqZr X) (hE : DescZr X) : DescentProp X :=
  descentProp_of_zr ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf) hU hE

/-- **Proposition 3.32 (ii)**: `X` an algebraic space, `M` a finitely generated abelian group, `N, L` submonoids:
`(X^N)^L = X^{N ∩ L}`. -/
theorem prop332 (hX : IsAlgebraicSpace B S hS X) (hU : UniqZr X) (hE : DescZr X) {M : Type u} [AddCommGroup M]
    [AddGroup.FG M] {aX : AAction (fppfO B S hS) M X} {N L : AddSubmonoid M} (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T) := by
  have : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  have : Countable M := countable_of_fg M
  exact prop332_of_descent ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf) (descentProp_space hX hU hE) T

/-- **Proposition 3.31 (ii)**: `X` an algebraic space, `M, Z` finitely generated abelian groups, `f : M → Z`, `Y` a
submonoid of `Z`: `X^{f⁻¹(Y) ⊂ M} = X^{Y ⊂ Z}`. -/
theorem prop331 (hX : IsAlgebraicSpace B S hS X) (hU : UniqZr X) (hE : DescZr X) {M Z : Type u} [AddCommGroup M]
    [AddCommGroup Z] [AddGroup.FG M] [AddGroup.FG Z] {f : M →+ Z} {Y : AddSubmonoid Z}
    {aX : AAction (fppfO B S hS) M X} (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong aX : AttractorPt aX (Y.comap f) T → AttractorPt (actAlong f aX) Y T) := by
  have : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  have : AddMonoid.FG Z := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  have : Countable M := countable_of_fg M
  have : Countable Z := countable_of_fg Z
  exact prop331_of_descent ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf) (descentProp_space hX hU hE) T

end Final

end AlgMag.SDTorus

#print axioms AlgMag.SDTorus.descentProp_of_zr
#print axioms AlgMag.SDTorus.prop332
#print axioms AlgMag.SDTorus.prop331
