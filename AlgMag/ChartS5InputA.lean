/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5InputZ
import AlgMag.ChartS5InputAlg

/-!
# Chart lemma, Artin approximation step (formal étaleness): `eA`, and the lift `Spec C/𝔲² → V`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

`exists_eA_pkg`: from the thickening hypothesis (the ideal of `V(m^j) ×_X V` in `V` lies in `p^j`),
`Γ(V)/p^j ≃ Ξ/((f) + 𝔫^j)`, and a map `a₁ : V(𝔲²) → V` over `X` computing `eA 2`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [hSa : IsAffine S]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V T P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `𝔲 = ker (Γ(T) → Γ(P))`. -/
noncomputable abbrev kerI {P T : BigFppfOver B S hS} (u : P ⟶ T) : Ideal Γ((SCH).obj T, ⊤) :=
  RingHom.ker ((SCH).map u).appTop.hom

section Step

variable {e : yoneda.obj V ⟶ X} (he : EtP e) (φ : yoneda.obj T ⟶ X) {k : Type u} [Field k]
  (iso : (BigFppfOver.toScheme B S hS).obj P ≅ Spec (.of k))
  (u : P ⟶ T) (v : P ⟶ V) (hw : yoneda.map u ≫ φ = yoneda.map v ≫ e)
  (hus : Function.Surjective ((BigFppfOver.toScheme B S hS).map u).appTop.hom)
  (hvs : Function.Surjective ((BigFppfOver.toScheme B S hS).map v).appTop.hom)
  (I : Ideal (RT T)) (hI : ∀ c ∈ I, ((BigFppfOver.toScheme B S hS).map u).appTop.hom c = 0)
  (ho : ChartMain.ClosedP (yoneda.map (Zi T I) ≫ φ))

include hw in
lemma hw_z : yoneda.map (zLift I u hI) ≫ yoneda.map (Zi T I) ≫ φ = yoneda.map v ≫ e := by
  rw [← Category.assoc, ← Functor.map_comp, zLift_ι, hw]

/-- The point `P → V(I) ×_X V`. -/
noncomputable abbrev tauZ : P ⟶ ho.rep.pullback e :=
  ho.rep.lift' (zLift I u hI) v (hw_z φ u v hw I hI)

variable {φ I} in
/-- `Γ(V) → Γ(V(I) ×_X V)`. -/
noncomputable abbrev rV : Γ((SCH).obj V, ⊤) →+* Γ((SCH).obj (ho.rep.pullback e), ⊤) :=
  ((SCH).map (ho.rep.snd e)).appTop.hom

variable {φ I} in
/-- `Γ(V(I)) → Γ(V(I) ×_X V)`. -/
noncomputable abbrev cV : Γ((SCH).obj (Zc T I), ⊤) →+* Γ((SCH).obj (ho.rep.pullback e), ⊤) :=
  ((SCH).map (ho.rep.fst' e)).appTop.hom

/-- `𝔟`, the point of `V(I) ×_X V`. -/
noncomputable abbrev bI : Ideal Γ((SCH).obj (ho.rep.pullback e), ⊤) :=
  kerI (tauZ φ u v hw I hI ho)

lemma kappa_r (y) : ((SCH).map (tauZ φ u v hw I hI ho)).appTop.hom (rV ho y) =
    ((SCH).map v).appTop.hom y := by
  have h : tauZ φ u v hw I hI ho ≫ ho.rep.snd e = v := ho.rep.lift'_snd _ _ _
  conv_rhs => rw [← h, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

lemma kappa_c (y) : ((SCH).map (tauZ φ u v hw I hI ho)).appTop.hom (cV ho y) =
    ((SCH).map (zLift I u hI)).appTop.hom y := by
  have h : tauZ φ u v hw I hI ho ≫ ho.rep.fst' e = zLift I u hI := ho.rep.lift'_fst _ _ _
  conv_rhs => rw [← h, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

lemma kappa_c_rZ (c) : ((SCH).map (tauZ φ u v hw I hI ho)).appTop.hom (cV ho (rZ T I c)) =
    ((SCH).map u).appTop.hom c := by
  rw [kappa_c, zLift_appTop]

include iso hvs in
lemma bI_max : (bI φ u v hw I hI ho).IsMaximal := by
  letI := (isField_of_iso iso).toField
  refine RingHom.ker_isMaximal_of_surjective _ fun y => ?_
  obtain ⟨a, rfl⟩ := hvs y
  exact ⟨rV ho a, kappa_r φ u v hw I hI ho a⟩

include hus in
lemma bI_res : Function.Surjective ((Ideal.Quotient.mk (bI φ u v hw I hI ho)).comp (cV ho)) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := hus (((SCH).map (tauZ φ u v hw I hI ho)).appTop.hom y)
  refine ⟨rZ T I c, Ideal.Quotient.eq.2 ?_⟩
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, kappa_c_rZ]
  exact hc

lemma bI_comap_r : (bI φ u v hw I hI ho).comap (rV ho) = kerI v := by
  ext y
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, kappa_r]

lemma bI_comap_c : ((bI φ u v hw I hI ho).comap (cV ho)).comap (rZ T I) = kerI u := by
  ext y
  rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, kappa_c_rZ]

include he iso hus hvs in
/-- One truncation: `Γ(V)/p^j ≃ C/𝔲^j`. -/
theorem eA_step (j : ℕ) (hk : (ChartMain.idealOf ho e).ideal ⟨⊤, isAffineOpen_top _⟩ ≤ kerI v ^ j)
    (hIj : I ≤ kerI u ^ j) :
    ∃ E : (Γ((SCH).obj V, ⊤) ⧸ kerI v ^ j) ≃+* (RT T ⧸ kerI u ^ j),
      ∀ a c, rV ho a - cV ho (rZ T I c) ∈ bI φ u v hw I hI ho ^ j →
        E (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ c := by
  obtain ⟨hA, het, hsurj, hker, -⟩ := etale_base_change_ideal ho he
  haveI := bI_max φ iso u v hw hvs I hI ho
  refine ea_pkg (rV ho) hsurj (cV ho) het (bI φ u v hw I hI ho) (bI_res φ u v hw hus I hI ho)
    (rZ T I) (rZ_surjective T I) (kerI u) (bI_comap_c φ u v hw I hI ho) (kerI v)
    (bI_comap_r φ u v hw I hI ho) j (hker.trans_le hk) ?_
  intro c hc
  exact hIj ((rZ_eq_zero_iff T I c).1 hc)

/-- `V(J) → V(I)`, for `I ≤ J`. -/
noncomputable abbrev zIncl (J : Ideal (RT T)) (hIJ : I ≤ J) : Zc T J ⟶ Zc T I :=
  zLift I (Zi T J) fun c hc => (rZ_eq_zero_iff T J c).2 (hIJ hc)

lemma zIncl_rZ (J : Ideal (RT T)) (hIJ : I ≤ J) (c) :
    ((SCH).map (zIncl I J hIJ)).appTop.hom (rZ T I c) = rZ T J c :=
  zLift_appTop I _ _ c

include he iso hus hvs in
/-- **`a₁ : V(𝔲^j) → V`**, for `I ≤ 𝔲^j`. -/
theorem exists_a1 (j : ℕ) (hIj : I ≤ kerI u ^ j) (hj : 1 ≤ j) :
    ∃ a₁ : Zc T (kerI u ^ j) ⟶ V, yoneda.map a₁ ≫ e = yoneda.map (Zi T (kerI u ^ j)) ≫ φ ∧
      ∀ y c, rV ho y - cV ho (rZ T I c) ∈ bI φ u v hw I hI ho ^ j →
        ((SCH).map a₁).appTop.hom y = rZ T (kerI u ^ j) c := by
  obtain ⟨hA, het, hsurj, -, hsq⟩ := etale_base_change_ideal ho he
  haveI := hA
  haveI := bI_max φ iso u v hw hvs I hI ho
  have hres := bI_res φ u v hw hus I hI ho
  haveI : ((bI φ u v hw I hI ho).comap (cV ho)).IsMaximal := comap_isMaximal_of_surj _ _ hres
  let g₀ := ((SCH).map (zIncl I _ hIj)).appTop.hom
  have hg₀ : ∀ c, g₀ (rZ T I c) = rZ T (kerI u ^ j) c := zIncl_rZ I _ hIj
  obtain ⟨g', hg'c, hg'k⟩ := exists_trunc_lift (cV ho) het (bI φ u v hw I hI ho) hres j g₀ (by
    intro z hz
    obtain ⟨c, rfl⟩ := rZ_surjective T I z
    have h4 : (((bI φ u v hw I hI ho).comap (cV ho)) ^ j).comap (rZ T I) = kerI u ^ j :=
      comap_pow_of_surjective (rZ T I) (rZ_surjective T I) (kerI u) _ (bI_comap_c φ u v hw I hI ho) j
        (fun c hc => hIj ((rZ_eq_zero_iff T I c).1 hc))
    have h5 : c ∈ kerI u ^ j := h4 ▸ hz
    rw [hg₀]
    exact (rZ_eq_zero_iff T _ c).2 h5)
  have hgS : ∀ s, g' (((SCH).map (toTop' (ho.rep.pullback e))).appTop.hom s) =
      ((SCH).map (toTop' (Zc T (kerI u ^ j)))).appTop.hom s := fun s => by
    rw [← top_comp (ho.rep.fst' e) s]
    refine (hg'c _).trans (top_comp _ s)
  let b₁ : Zc T (kerI u ^ j) ⟶ ho.rep.pullback e := siteOfRing g' hgS
  have hb : ((SCH).map b₁).appTop.hom = g' := siteOfRing_appTop g' hgS
  have hb1 : b₁ ≫ ho.rep.fst' e = zIncl I _ hIj := by
    refine ChartMain.siteExt (ChartMain.toAffine_ext (RingHom.ext fun z => ?_))
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map b₁).appTop.hom (cV ho z) = _
    rw [hb]
    exact hg'c z
  refine ⟨b₁ ≫ ho.rep.snd e, ?_, fun y c h => ?_⟩
  · rw [Functor.map_comp, Category.assoc, ← hsq, ← Category.assoc, ← Functor.map_comp, hb1,
      ← Category.assoc, ← Functor.map_comp, zLift_ι]
  · rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map b₁).appTop.hom (rV ho y) = _
    rw [hb]
    have h1 : g' (rV ho y) - g' (cV ho (rZ T I c)) = 0 := by
      rw [← map_sub]; exact hg'k _ h
    rw [sub_eq_zero.1 h1, hg'c, hg₀]

end Step

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.eA_step
#print axioms AlgMag.ChartS5.exists_a1
