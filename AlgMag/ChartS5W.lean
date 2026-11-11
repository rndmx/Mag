/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Pt
import AlgMag.ChartS5Spec

/-!
# Chart lemma, Artin approximation step: maps out of `W`, killing the orbit ideal

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

`W = Spec G`, with `G` graded, `Λ : G → C/m` graded onto. The stabilizer clause of `Section5Output`
("`H ⊂ G_u` since `O ≅ G_k/H`"), from: `O = V(m) ⊂ T` maps monomorphically to `X`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

namespace AlgMag.ChartS5

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [hSa : IsAffine S]
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] {m : Ideal (RT T)}
  {G : Type u} [CommRing G] (ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* G)
  (hC : B.Contains (Spec (.of G)))
  (Λ : G →+* RT T ⧸ m) (hΛ : Function.Surjective Λ)
  (hρ : ∀ a, Λ (ρ a) = Ideal.Quotient.mk m (((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom a))

/-- A map to `Spec G` killing `ker Λ` factors through `T`, on rings: the map `Γ(T) → Γ(T')`. -/
noncomputable def descRing {T' : BigFppfOver B S hS} (τ : T' ⟶ rObj ρ hC)
    (hk : ∀ a, Λ a = 0 → ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (rSec ρ hC a) = 0) :
    RT T →+* Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) :=
  (RingHom.liftOfSurjective Λ hΛ
    ⟨(((BigFppfOver.toScheme B S hS).map τ).appTop.hom).comp (rSec ρ hC : G →+* _),
      fun a ha => RingHom.mem_ker.2 (hk a (RingHom.mem_ker.1 ha))⟩).comp
    (Ideal.Quotient.mk m)

lemma descRing_spec {T' : BigFppfOver B S hS} (τ : T' ⟶ rObj ρ hC)
    (hk : ∀ a, Λ a = 0 → ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (rSec ρ hC a) = 0)
    (c : RT T) (y : G) (hy : Λ y = Ideal.Quotient.mk m c) :
    descRing ρ hC Λ hΛ τ hk c = ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (rSec ρ hC y) := by
  unfold descRing
  rw [RingHom.comp_apply, ← hy]
  exact RingHom.liftOfRightInverse_comp_apply Λ (Function.surjInv hΛ) (Function.rightInverse_surjInv hΛ) _ y

include hρ in
/-- The map `T' → T` underlying `τ : T' → Spec G`, `τ` killing `ker Λ`. -/
theorem exists_desc {T' : BigFppfOver B S hS} (τ : T' ⟶ rObj ρ hC)
    (hk : ∀ a, Λ a = 0 → ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (rSec ρ hC a) = 0) :
    ∃ a : T' ⟶ T, ((BigFppfOver.toScheme B S hS).map a).appTop.hom = descRing ρ hC Λ hΛ τ hk := by
  haveI : IsAffine (B.obj hS).obj := hSa
  haveI : IsAffine (Over.left T).obj := ‹IsAffine ((BigFppfOver.toScheme B S hS).obj T)›
  have hw : ChartMain.toAffine (T := (BigFppfOver.toScheme B S hS).obj T')
      (U := (BigFppfOver.toScheme B S hS).obj T) (descRing ρ hC Λ hΛ τ hk) ≫ T.hom.hom = T'.hom.hom := by
    refine ChartMain.toAffine_comp T.hom.hom _ _ (RingHom.ext fun s => ?_)
    have e1 := descRing_spec ρ hC Λ hΛ τ hk (((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom s)
      (ρ s) (hρ s)
    have hT : ∀ Y : BigFppfOver B S hS, Y.hom.hom = (BigFppfOver.toScheme B S hS).map (toTop' Y) :=
      fun Y => (congrArg (fun z => z.hom) (Over.w (toTop' Y))).symm.trans (Category.comp_id _)
    rw [RingHom.comp_apply, hT T, hT T']
    refine e1.trans ?_
    have e2 := spToT_appTop (siteTop (B := B) (S := S) (hS := hS)) ρ hC s
    have e3 : τ ≫ spToT (siteTop (B := B) (S := S) (hS := hS)) ρ hC = toTop' T' :=
      Over.mkIdTerminal.hom_ext _ _
    have e4 := congrArg (fun z : T' ⟶ siteTop (B := B) (S := S) (hS := hS) => ((BigFppfOver.toScheme B S hS).map z).appTop.hom s) e3
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at e4
    refine Eq.trans ?_ e4
    exact congrArg _ e2.symm
  exact ⟨Over.homMk ⟨ChartMain.toAffine (T := (BigFppfOver.toScheme B S hS).obj T')
      (U := (BigFppfOver.toScheme B S hS).obj T) (descRing ρ hC Λ hΛ τ hk)⟩ (by
    apply InducedCategory.hom_ext
    exact hw), ChartMain.toAffine_appTop (T := (BigFppfOver.toScheme B S hS).obj T')
      (U := (BigFppfOver.toScheme B S hS).obj T) _⟩

variable (𝒜 : M → AddSubgroup G) [GradedRing 𝒜] (h0 : ∀ s, ρ s ∈ 𝒜 0)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)

include hρ hΛ in
/-- **Shrinking step**: "`H ⊂ G_u` since `O ≅ G_k/H`". If `V(m) ⊂ T` maps monomorphically to `X`, the stabilizer
in `Spec G` of a point of `V(ker Λ)` is that of its image in `X`. -/
theorem stab_of_mono (hhom : (RingHom.ker Λ).IsHomogeneous 𝒜) (f : yoneda.obj (rObj ρ hC) ⟶ X)
    (hf : IsEquivariant (rAct ρ hC 𝒜 h0) actX f) (φ : yoneda.obj T ⟶ X)
    (hfac : ∀ {T' : BigFppfOver B S hS} (τ : T' ⟶ rObj ρ hC) (a : T' ⟶ T)
      (_ : ∀ y c, Λ y = Ideal.Quotient.mk m c → ((BigFppfOver.toScheme B S hS).map a).appTop.hom c =
        ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (rSec ρ hC y)),
      f.app (op T') τ = φ.app (op T') a)
    (hMono : ∀ {T' : BigFppfOver B S hS} (a b : T' ⟶ T),
      (∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map a).appTop.hom c = 0) →
      (∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map b).appTop.hom c = 0) →
      φ.app (op T') a = φ.app (op T') b → a = b)
    {T' : BigFppfOver B S hS} (τ : T' ⟶ rObj ρ hC)
    (hk : ∀ a, Λ a = 0 → ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (rSec ρ hC a) = 0)
    (g : APt (fppfO B S hS) M (op T'))
    (hg : actX.smul g (f.app (op T') τ) = f.app (op T') τ) :
    (rAct ρ hC 𝒜 h0).smul (F := yoneda.obj (rObj ρ hC)) g τ = τ := by
  classical
  letI := tGradedRing (rSec ρ hC) 𝒜
  set τ₂ : T' ⟶ rObj ρ hC := (rAct ρ hC 𝒜 h0).smul (F := yoneda.obj (rObj ρ hC)) g τ with hτ₂
  have hk₂ : ∀ a, Λ a = 0 → ((BigFppfOver.toScheme B S hS).map τ₂).appTop.hom (rSec ρ hC a) = 0 := by
    intro a ha
    have e : ((BigFppfOver.toScheme B S hS).map τ₂).appTop.hom =
        ChartMain.twist (tGrade (rSec ρ hC) 𝒜) ((BigFppfOver.toScheme B S hS).map τ).appTop.hom g :=
      ChartMain.toAffine_appTop (T := (BigFppfOver.toScheme B S hS).obj T')
        (U := (BigFppfOver.toScheme B S hS).obj (rObj ρ hC)) _
    rw [e, ← DirectSum.sum_support_decompose 𝒜 a, map_sum, map_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    refine (ChartMain.twist_of_mem (tGrade (rSec ρ hC) 𝒜) _ g (mem_tGrade _ 𝒜 (SetLike.coe_mem _))).trans ?_
    exact mul_eq_zero_of_left (hk _ (hhom d ha)) _
  obtain ⟨a₁, h₁⟩ := exists_desc ρ hC Λ hΛ hρ τ hk
  obtain ⟨a₂, h₂⟩ := exists_desc ρ hC Λ hΛ hρ τ₂ hk₂
  have s₁ : ∀ y c, Λ y = Ideal.Quotient.mk m c → ((BigFppfOver.toScheme B S hS).map a₁).appTop.hom c =
      ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (rSec ρ hC y) := fun y c e => by
    rw [h₁]; exact descRing_spec ρ hC Λ hΛ τ hk c y e
  have s₂ : ∀ y c, Λ y = Ideal.Quotient.mk m c → ((BigFppfOver.toScheme B S hS).map a₂).appTop.hom c =
      ((BigFppfOver.toScheme B S hS).map τ₂).appTop.hom (rSec ρ hC y) := fun y c e => by
    rw [h₂]; exact descRing_spec ρ hC Λ hΛ τ₂ hk₂ c y e
  have killM : ∀ (a : T' ⟶ T) (τ' : T' ⟶ rObj ρ hC)
      (_ : ∀ y c, Λ y = Ideal.Quotient.mk m c → ((BigFppfOver.toScheme B S hS).map a).appTop.hom c =
        ((BigFppfOver.toScheme B S hS).map τ').appTop.hom (rSec ρ hC y))
      (_ : ∀ a, Λ a = 0 → ((BigFppfOver.toScheme B S hS).map τ').appTop.hom (rSec ρ hC a) = 0),
      ∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map a).appTop.hom c = 0 := by
    intro a τ' s k c hc
    have e0 : Ideal.Quotient.mk m c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
    rw [s 0 c (by rw [map_zero, e0]), map_zero, map_zero]
  have hEq : a₁ = a₂ := hMono a₁ a₂ (killM _ _ s₁ hk) (killM _ _ s₂ hk₂) (by
    rw [← hfac τ a₁ s₁, ← hfac τ₂ a₂ s₂, hτ₂, hf g τ, hg])
  subst hEq
  refine ChartMain.siteExt (ChartMain.toAffine_ext (RingHom.ext fun y₀ => ?_))
  obtain ⟨y, rfl⟩ := (rSec ρ hC).surjective y₀
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Λ y)
  exact (s₂ y c hc.symm).symm.trans (s₁ y c hc.symm)

omit [AddMonoid.FG M] [DecidableEq M] in
/-- Maps to `Spec G` are determined on elements of `G`. -/
lemma hom_ext_rObj {T' : BigFppfOver B S hS} {b c : T' ⟶ rObj ρ hC}
    (h : ∀ y, ((BigFppfOver.toScheme B S hS).map b).appTop.hom (rSec ρ hC y) =
      ((BigFppfOver.toScheme B S hS).map c).appTop.hom (rSec ρ hC y)) : b = c := by
  refine ChartMain.siteExt (ChartMain.toAffine_ext (RingHom.ext fun y₀ => ?_))
  obtain ⟨y, rfl⟩ := (rSec ρ hC).surjective y₀
  exact h y

/-- Composition with a map of `Spec`s, on elements. -/
lemma comp_spMap_sec {G' : Type u} [CommRing G'] {ρ' : RT (siteTop (B := B) (S := S) (hS := hS)) →+* G'}
    {hC' : B.Contains (Spec (.of G'))} (π : G →+* G') (hπ : π.comp ρ = ρ')
    {T' : BigFppfOver B S hS} (τ : T' ⟶ rObj ρ' hC') (y : G) :
    ((BigFppfOver.toScheme B S hS).map (τ ≫ spMap _ (hC := hC) (hC' := hC') π hπ)).appTop.hom (rSec ρ hC y) =
      ((BigFppfOver.toScheme B S hS).map τ).appTop.hom (rSec ρ' hC' (π y)) := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  exact congrArg _ (spMap_appTop _ _ _ y)

/-- Composition with `spLift`, on elements. -/
lemma comp_spLift_sec {T₁ T' : BigFppfOver B S hS} (ψ : G →+* Γ((BigFppfOver.toScheme B S hS).obj T₁, ⊤))
    (hψ : ψ.comp ρ = ((BigFppfOver.toScheme B S hS).map (toTop' T₁)).appTop.hom) (a : T' ⟶ T₁) (y : G) :
    ((BigFppfOver.toScheme B S hS).map (a ≫ spLift _ ρ hC (toTop' T₁) ψ hψ)).appTop.hom (rSec ρ hC y) =
      ((BigFppfOver.toScheme B S hS).map a).appTop.hom (ψ y) := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  exact congrArg _ (spLift_appTop _ _ _ _ _ _ y)

/-- A homogeneous ideal of `G` gives a homogeneous ideal of `Γ(Spec G)`. -/
theorem comap_homog (𝒜 : M → AddSubgroup G) [GradedRing 𝒜] (h0 : ∀ s, ρ s ∈ 𝒜 0) (I : Ideal G)
    (hI : I.IsHomogeneous 𝒜) :
    letI := ChartMain.gradedRingOfAction (rAct ρ hC 𝒜 h0)
    (I.comap ((rSec ρ hC).symm : Γ((BigFppfOver.toScheme B S hS).obj (rObj ρ hC), ⊤) →+* G)).IsHomogeneous
      (ChartMain.homog (rAct ρ hC 𝒜 h0)) := by
  letI := ChartMain.gradedRingOfAction (rAct ρ hC 𝒜 h0)
  intro d a ha
  obtain ⟨a₀, rfl⟩ := (rSec ρ hC).surjective a
  have h1 := ChartMain.decompose_map 𝒜 (ChartMain.homog (rAct ρ hC 𝒜 h0))
    (rSec ρ hC : G →+* Γ((BigFppfOver.toScheme B S hS).obj (rObj ρ hC), ⊤))
    (fun d a ha => (mem_homog_rAct ρ hC 𝒜 h0).2 ha) a₀ d
  have h2 : a₀ ∈ I := by
    have : (rSec ρ hC).symm (rSec ρ hC a₀) ∈ I := ha
    rwa [(rSec ρ hC).symm_apply_apply] at this
  change (rSec ρ hC).symm _ ∈ I
  have h1' : ((decompose (ChartMain.homog (rAct ρ hC 𝒜 h0)) (rSec ρ hC a₀) d :
      ChartMain.homog (rAct ρ hC 𝒜 h0) d) : Γ((BigFppfOver.toScheme B S hS).obj (rObj ρ hC), ⊤)) =
      rSec ρ hC ((decompose 𝒜 a₀ d : 𝒜 d) : G) := h1
  rw [h1', (rSec ρ hC).symm_apply_apply]
  exact hI d h2

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.stab_of_mono
