/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Build
import AlgMag.ChartS5Spec

/-!
# Chart lemma, Artin approximation step: `φ̃` at a finite level

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

`exists_finite_level`: the data `(f, r, φ)` over `P̂₀` is defined over a finite type `P₀`-subalgebra
`R_t ⊆ P̂₀`, with `φ̃ : Spec(Q_{R_t}/(f̃)) → X` equivariant.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

open ChartAlg TensorProduct

section Grade

variable {M : Type u} [AddCommGroup M] [DecidableEq M] {ι : Type u} [Finite ι] {w : ι → M}
  {R : Type u} [CommRing R] [Algebra (P0 w ℤ) R]

/-- `Q_R/(F)`. -/
abbrev Dq {s₁ : ℕ} (F : Fin s₁ → QR w R) : Type u := QR w R ⧸ Ideal.span (Set.range F)

lemma span_homog {s₁ : ℕ} {F : Fin s₁ → QR w R} {deg : Fin s₁ → M}
    (hF : ∀ ℓ, F ℓ ∈ qGrade w R (deg ℓ)) :
    (Ideal.span (Set.range F)).IsHomogeneous (qGrade w R) := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro _ ⟨ℓ, rfl⟩
  exact ⟨deg ℓ, hF ℓ⟩

/-- The grading of `Q_R/(F)`. -/
noncomputable abbrev gq {s₁ : ℕ} (F : Fin s₁ → QR w R) (d : M) : AddSubgroup (Dq F) :=
  ChartGraded.quotGrade (qGrade w R) (Ideal.span (Set.range F)) d

/-- The graded ring `Q_R/(F)`. -/
noncomputable abbrev gqRing {s₁ : ℕ} {F : Fin s₁ → QR w R} {deg : Fin s₁ → M}
    (hF : ∀ ℓ, F ℓ ∈ qGrade w R (deg ℓ)) : GradedRing (gq F) :=
  ChartGraded.quotGradedRing (span_homog hF)

/-- `Q_R/(F) → Q_{R'}/(g F)`. -/
noncomputable def Dmap {R' : Type u} [CommRing R'] [Algebra (P0 w ℤ) R'] {s₁ : ℕ}
    (F : Fin s₁ → QR w R) (g : R →ₐ[P0 w ℤ] R') : Dq F →+* Dq (fun ℓ => QRmap w g (F ℓ)) :=
  Ideal.quotientMap _ (QRmap w g : QR w R →ₐ[_] QR w R').toRingHom (by
    rw [Ideal.span_le]
    rintro _ ⟨ℓ, rfl⟩
    exact Ideal.subset_span ⟨ℓ, rfl⟩)

@[simp] lemma Dmap_mk {R' : Type u} [CommRing R'] [Algebra (P0 w ℤ) R'] {s₁ : ℕ}
    (F : Fin s₁ → QR w R) (g : R →ₐ[P0 w ℤ] R') (q : QR w R) :
    Dmap F g (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk _ (QRmap w g q) := rfl

lemma Dmap_mem {R' : Type u} [CommRing R'] [Algebra (P0 w ℤ) R'] {s₁ : ℕ}
    (F : Fin s₁ → QR w R) (g : R →ₐ[P0 w ℤ] R') {d : M} {a : Dq F} (ha : a ∈ gq F d) :
    Dmap F g a ∈ gq (fun ℓ => QRmap w g (F ℓ)) d := by
  obtain ⟨q, hq, rfl⟩ := ha
  exact ⟨_, QRmap_mem w g hq, rfl⟩

end Grade

section Sys

variable {M : Type u} [AddCommGroup M] [DecidableEq M] {ι : Type u} [Finite ι] {w : ι → M}
  {Rh : Type u} [CommRing Rh] [Algebra (P0 w ℤ) Rh] {t₀ : Finset Rh} {s₁ : ℕ}
  (F₁ : Fin s₁ → QR w (Rs w t₀))

/-- The index set: `t ⊇ t₀`. -/
abbrev Jx (t₀ : Finset Rh) : Type u := {t : Finset Rh // t₀ ⊆ t}

/-- The ideal `(F₁)` at level `j`. -/
noncomputable abbrev Ij (j : Jx t₀) : Ideal (QR w (Rs w j.1)) :=
  Ideal.span (Set.range fun ℓ => QRmap w (RsLE w j.2) (F₁ ℓ))

/-- `Q_{R_j}/(F₁)`. -/
abbrev Drj (j : Jx t₀) : Type u := QR w (Rs w j.1) ⧸ Ij F₁ j

lemma Ij_le {j k : Jx t₀} (h : j ≤ k) :
    Ij F₁ j ≤ (Ij F₁ k).comap (QRmap w (RsLE w h) : _ →ₐ[_] _).toRingHom := by
  rw [Ideal.span_le]
  rintro _ ⟨ℓ, rfl⟩
  refine Ideal.subset_span ⟨ℓ, ?_⟩
  exact (QRmap_RsLE_RsLE w j.2 h (F₁ ℓ)).symm

/-- The transition maps. -/
noncomputable def πj {j k : Jx t₀} (h : j ≤ k) : Drj F₁ j →+* Drj F₁ k :=
  Ideal.quotientMap _ (QRmap w (RsLE w h) : _ →ₐ[_] _).toRingHom (Ij_le F₁ h)

@[simp] lemma πj_mk {j k : Jx t₀} (h : j ≤ k) (q : QR w (Rs w j.1)) :
    πj F₁ h (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk _ (QRmap w (RsLE w h) q) := rfl

lemma πj_id (j : Jx t₀) (h : j ≤ j) : πj F₁ h = RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun q => ?_)
  exact congrArg _ (QRmap_id w q)

lemma πj_comp {j k l : Jx t₀} (h : j ≤ k) (h' : k ≤ l) :
    (πj F₁ h').comp (πj F₁ h) = πj F₁ (h.trans h') := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun q => ?_)
  exact congrArg _ (QRmap_RsLE_RsLE w h h' q)

variable {deg : Fin s₁ → M} (hd : ∀ ℓ, F₁ ℓ ∈ qGrade w (Rs w t₀) (deg ℓ))

include hd in
lemma Fj_mem (j : Jx t₀) (ℓ : Fin s₁) : QRmap w (RsLE w j.2) (F₁ ℓ) ∈ qGrade w (Rs w j.1) (deg ℓ) :=
  QRmap_mem w _ (hd ℓ)

end Sys

section Main

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [hSa : IsAffine S]
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (actT : AAction (fppfO B S hS) M (yoneda.obj T)) [GradedRing (ChartMain.homog actT)]
  {m : Ideal (RT T)} {ι : Type u} [Finite ι] {w : ι → M} {x : ι → RT T}
  (hx : ∀ i, x i ∈ ChartMain.homog actT (w i)) (hC : CompletePair (ChartMain.homog actT) m)

/-- `Q_R/(F) → Γ(T)`. -/
noncomputable def psiD {t : Finset (P0hat w x m)} {s₁ : ℕ} (F₁ : Fin s₁ → QR w (Rs w t))
    (h : ∀ ℓ, varpi hx hC t (F₁ ℓ) = 0) : Dq F₁ →+* RT T :=
  Ideal.Quotient.lift _ (varpi hx hC t) (fun a ha => by
    have : Ideal.span (Set.range F₁) ≤ RingHom.ker (varpi hx hC t) := by
      rw [Ideal.span_le]; rintro _ ⟨ℓ, rfl⟩; exact h ℓ
    exact this ha)

/-- **Artin approximation step, functor `F` and spreading.** The data `(f, r, φ)` over `P̂₀` is defined over a finite type
`P₀`-subalgebra `R_t ⊆ P̂₀`: `φ̃ : Spec(Q_{R_t}/(f̃)) → X` is equivariant, and restricts to `φ`
along `T → Spec(Q_{R_t}/(f̃))`. -/
theorem exists_finite_level {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
    [Algebra.FiniteType ℤ (RT (siteTop (B := B) (S := S) (hS := hS)))]
    (hκ : ∀ a, ((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom a ∈ ChartMain.homog actT 0)
    (hsurj : Function.Surjective (Qmap hx hC))
    {s₁ t₁ : ℕ} (F : Fin s₁ → Qring w x m) (hF : Ideal.span (Set.range F) = RingHom.ker (Qmap hx hC))
    (deg : Fin s₁ → M) (hd : ∀ ℓ, qProj (deg ℓ) (F ℓ) = F ℓ)
    (r : Fin t₁ → Fin s₁ → Qring w x m) (hs : ∀ j, ∑ ℓ, r j ℓ * F ℓ = 0)
    (φ : yoneda.obj T ⟶ X) (hφ : IsEquivariant actT actX φ) :
    ∃ (t : Finset (P0hat w x m)) (F₁ : Fin s₁ → QR w (Rs w t)) (r₁ : Fin t₁ → Fin s₁ → QR w (Rs w t))
      (hFI : ∀ ℓ, QRmap w (RsI w t) (F₁ ℓ) = F ℓ) (_ : ∀ j ℓ, QRmap w (RsI w t) (r₁ j ℓ) = r j ℓ)
      (_ : ∀ j, ∑ ℓ, r₁ j ℓ * F₁ ℓ = 0) (hm : ∀ ℓ, F₁ ℓ ∈ qGrade w (Rs w t) (deg ℓ))
      (ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* Dq F₁)
      (hCt : B.Contains (Spec (.of (Dq F₁)))) (h0 : ∀ a, ρ a ∈ gq F₁ 0)
      (hv : ∀ ℓ, varpi hx hC t (F₁ ℓ) = 0)
      (hψ : (psiD actT hx hC F₁ hv).comp ρ = ((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom)
      (xt : yoneda.obj (rObj ρ hCt) ⟶ X),
      (letI := gqRing hm; IsEquivariant (rAct ρ hCt (gq F₁) h0) actX xt) ∧
      yoneda.map (spLift _ ρ hCt (toTop' T) (psiD actT hx hC F₁ hv) hψ) ≫ xt = φ := by
  classical
  obtain ⟨s, F₀, r₀, hF₀, hr₀, hs₀, hm₀⟩ := exists_spread F r hs deg hd
  obtain ⟨t, hst, ρ₀, hρ₀⟩ := exists_structure hx hC F hF
    (((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom) hκ hsurj F₀ hF₀
  let F₁ : Fin s₁ → QR w (Rs w t) := fun ℓ => QRmap w (RsLE w hst) (F₀ ℓ)
  have hF₁I : ∀ ℓ, QRmap w (RsI w t) (F₁ ℓ) = F ℓ := fun ℓ => by
    rw [QRmap_RsI_RsLE, hF₀]
  have hF₁m : ∀ ℓ, F₁ ℓ ∈ qGrade w (Rs w t) (deg ℓ) := fun ℓ => QRmap_mem w _ (hm₀ ℓ)
  have hFv : ∀ ℓ, Qmap hx hC (F ℓ) = 0 := fun ℓ => by
    have : F ℓ ∈ RingHom.ker (Qmap hx hC) := by rw [← hF]; exact Ideal.subset_span ⟨ℓ, rfl⟩
    exact this
  have hvj : ∀ (j : Jx t) ℓ, varpi hx hC j.1 (QRmap w (RsLE w j.2) (F₁ ℓ)) = 0 := fun j ℓ => by
    rw [varpi_LE]
    change Qmap hx hC (QRmap w (RsI w t) (F₁ ℓ)) = 0
    rw [hF₁I, hFv]
  let ψs : ∀ j : Jx t, Drj F₁ j →+* RT T := fun j =>
    psiD actT hx hC (fun ℓ => QRmap w (RsLE w j.2) (F₁ ℓ)) (hvj j)
  let base : ∀ j : Jx t, Dq F₁ →+* Drj F₁ j := fun j =>
    Ideal.quotientMap _ (QRmap w (RsLE w j.2) : _ →ₐ[_] _).toRingHom (by
      rw [Ideal.span_le]; rintro _ ⟨ℓ, rfl⟩; exact Ideal.subset_span ⟨ℓ, rfl⟩)
  let ρs : ∀ j : Jx t, RT (siteTop (B := B) (S := S) (hS := hS)) →+* Drj F₁ j :=
    fun j => (base j).comp ρ₀
  have hft : ∀ j : Jx t, Algebra.FiniteType (P0 w ℤ) (Rs w j.1) := fun j =>
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset _)
  have hCs : ∀ j : Jx t, B.Contains (Spec (.of (Drj F₁ j))) := fun j => by
    letI := (ρs j).toAlgebra
    haveI := hft j
    haveI : Algebra.FiniteType ℤ (QR w (Rs w j.1)) := finiteType_QR_int w _
    haveI : Algebra.FiniteType ℤ (Drj F₁ j) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ (Ij F₁ j)) Ideal.Quotient.mk_surjective
    haveI : Algebra.FiniteType (RT (siteTop (B := B) (S := S) (hS := hS))) (Drj F₁ j) :=
      Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
    exact contains_ft (RT (siteTop (B := B) (S := S) (hS := hS))) (Drj F₁ j) (contains_RT _)
  have hm_j : ∀ (j : Jx t) ℓ, QRmap w (RsLE w j.2) (F₁ ℓ) ∈ qGrade w (Rs w j.1) (deg ℓ) :=
    fun j ℓ => QRmap_mem w _ (hF₁m ℓ)
  let 𝒢 : ∀ j : Jx t, M → AddSubgroup (Drj F₁ j) := fun j =>
    gq (fun ℓ => QRmap w (RsLE w j.2) (F₁ ℓ))
  letI grj : ∀ j : Jx t, GradedRing (𝒢 j) := fun j => gqRing (hm_j j)
  have hρs : ∀ (j : Jx t) a, ∃ q ∈ qGrade w (Rs w t) 0, Ideal.Quotient.mk _ q = ρ₀ a ∧
      varpi hx hC t q = ((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom a := fun _ a => hρ₀ a
  have h0s : ∀ (j : Jx t) a, ρs j a ∈ 𝒢 j 0 := fun j a => by
    obtain ⟨q, hq, e, -⟩ := hρ₀ a
    refine ⟨QRmap w (RsLE w j.2) q, QRmap_mem w _ hq, ?_⟩
    change _ = base j (ρ₀ a)
    rw [← e]
    rfl
  have π_ρ : ∀ {j k : Jx t} (h : j ≤ k), (πj F₁ h).comp (ρs j) = ρs k := fun {j k} h => by
    refine RingHom.ext fun a => ?_
    obtain ⟨q, -, e, -⟩ := hρ₀ a
    change πj F₁ h (base j (ρ₀ a)) = base k (ρ₀ a)
    rw [← e]
    exact congrArg (Ideal.Quotient.mk _) (QRmap_RsLE_RsLE w j.2 h q)
  have hψ : ∀ j, (ψs j).comp (ρs j) = ((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom :=
    fun j => RingHom.ext fun a => by
      obtain ⟨q, -, e, e'⟩ := hρ₀ a
      change ψs j (base j (ρ₀ a)) = _
      rw [← e, ← e']
      exact varpi_LE hx hC j.2 q
  have ψ_π : ∀ {j k : Jx t} (h : j ≤ k), (ψs k).comp (πj F₁ h) = ψs j := fun {j k} h =>
    Ideal.Quotient.ringHom_ext (RingHom.ext fun q => varpi_LE hx hC h q)
  have ψm : ∀ j, ∀ d, ∀ a ∈ 𝒢 j d, ψs j a ∈ ChartMain.homog actT d := by
    rintro j d _ ⟨q, hq, rfl⟩
    exact varpi_mem hx hC hq
  have πm : ∀ {j k : Jx t} (h : j ≤ k), ∀ d, ∀ a ∈ 𝒢 j d, πj F₁ h a ∈ 𝒢 k d := by
    rintro j k h d _ ⟨q, hq, rfl⟩
    exact ⟨_, QRmap_mem w _ hq, rfl⟩
  have hsj : ∀ c, ∃ (j : Jx t) (y : Drj F₁ j), ψs j y = c := fun c => by
    obtain ⟨q, rfl⟩ := hsurj c
    obtain ⟨t', ht', q', e⟩ := exists_QR_lift_mono w t q
    exact ⟨⟨t', ht'⟩, Ideal.Quotient.mk _ q', congrArg (Qmap hx hC) e⟩
  have hij : ∀ (j : Jx t) (y : Drj F₁ j), ψs j y = 0 →
      ∃ (k : Jx t) (h : j ≤ k), πj F₁ h y = 0 := by
    intro j y hy
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨t', h', hmem⟩ := exists_mem_span hx hC F hF (fun ℓ => QRmap w (RsLE w j.2) (F₁ ℓ))
      (fun ℓ => by rw [QRmap_RsI_RsLE, hF₁I]) q hy
    refine ⟨⟨t', j.2.trans h'⟩, h', Ideal.Quotient.eq_zero_iff_mem.2 ?_⟩
    have e : (fun ℓ => QRmap w (RsLE w h') (QRmap w (RsLE w j.2) (F₁ ℓ))) =
        fun ℓ => QRmap w (RsLE w (j.2.trans h')) (F₁ ℓ) :=
      funext fun ℓ => QRmap_RsLE_RsLE w j.2 h' (F₁ ℓ)
    rw [e] at hmem
    exact hmem
  haveI : Nonempty (Jx t) := ⟨⟨t, Finset.Subset.refl _⟩⟩
  haveI : IsDirected (Jx t) (· ≤ ·) := ⟨fun a b => ⟨⟨a.1 ∪ b.1, a.2.trans Finset.subset_union_left⟩,
    Finset.subset_union_left, Finset.subset_union_right⟩⟩
  have hc := isColimit_lvl (B := B) (S := S) (hS := hS) (T := T) (Drj F₁) (fun {j k} => πj F₁)
    (πj_id F₁) (πj_comp F₁) ψs ψ_π hsj hij
  obtain ⟨j, xj, h1, h2⟩ := exists_level (Drj F₁) ρs hCs (fun {j k} => πj F₁) (πj_id F₁) (πj_comp F₁)
    π_ρ ψs hψ ψ_π 𝒢 h0s πm actX hl actT ψm hc φ hφ
  have hs_j : ∀ i, ∑ ℓ, QRmap w (RsLE w j.2) (QRmap w (RsLE w hst) (r₀ i ℓ)) *
      QRmap w (RsLE w j.2) (F₁ ℓ) = 0 := fun i => by
    have := congrArg (fun z => QRmap w (RsLE w j.2) (QRmap w (RsLE w hst) z)) (hs₀ i)
    simpa only [map_sum, map_mul, map_zero] using this
  exact ⟨j.1, fun ℓ => QRmap w (RsLE w j.2) (F₁ ℓ), fun i ℓ => QRmap w (RsLE w j.2) (QRmap w (RsLE w hst) (r₀ i ℓ)),
    fun ℓ => by rw [QRmap_RsI_RsLE, hF₁I],
    fun i ℓ => by rw [QRmap_RsI_RsLE, QRmap_RsI_RsLE, hr₀],
    hs_j, hm_j j, ρs j, hCs j, h0s j, hvj j, hψ j, xj, h1, h2⟩

end Main

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.exists_finite_level
