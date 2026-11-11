/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12PrintedAffine
import AlgMag.GeneralBaseThm320
import AlgMag.Sec11SchemesRep
import AlgMag.Sec12Topology

/-!
# Theorem 12.4 for `X` affine over `S`, along the printed proof

Mayeux, *Algebraic Magnetism*, Theorem 12.4, schemes only. `X → S` is affine and smooth; `U` is an
affine open of `S`, `A = Γ(X, p⁻¹U)`, `B = A/J_N`, `B₀ = A/J_{N^×}`.

The only use of §11 is the definition `AlgMag.Sec12Printed.smooth_faceZ`
(**marked: call of Cor 11.10 / Prop 11.7, to rewire**).
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

universe u

namespace AlgMag.Sec12Printed

open AlgMag.GB

attribute [local instance] gradedAlgebraOf

/-- The units `N^×` of a magnet. -/
def unitsOf {M : Type*} [AddCommGroup M] (N : AddSubmonoid M) : AddSubgroup M where
  carrier := {x | x ∈ N ∧ -x ∈ N}
  add_mem' := fun {a b} ha hb => ⟨N.add_mem ha.1 hb.1, by
    rw [neg_add]; exact N.add_mem ha.2 hb.2⟩
  zero_mem' := ⟨N.zero_mem, by simp [N.zero_mem]⟩
  neg_mem' := fun {a} ha => ⟨ha.2, by simpa using ha.1⟩

lemma isFace_unitsOf {M : Type*} [AddCommGroup M] (N : AddSubmonoid M) :
    IsFace (unitsOf N).toAddSubmonoid N := by
  refine ⟨fun x hx => hx.1, fun {x y} hx hy h => ?_⟩
  have hn : -(x + y) ∈ N := h.2
  refine ⟨⟨hx, ?_⟩, ⟨hy, ?_⟩⟩
  · have := N.add_mem hn hy
    simpa [neg_add, add_assoc, add_comm, add_left_comm] using this
  · have := N.add_mem hn hx
    simpa [neg_add, add_assoc, add_comm, add_left_comm] using this

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]
variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))
variable (N : AddSubmonoid M) {F : AddSubgroup M} (hF : IsFace F.toAddSubmonoid N)

section Face

/-- The morphism `X^N → X^F` of schemes representing the attractors. -/
def faceZ : Zatt act N ⟶ Zatt act F.toAddSubmonoid :=
  (attEquiv act F.toAddSubmonoid _).symm (AttractorPt.ofFace hF (attEquiv act N _ (𝟙 _)))

lemma faceZ_spec {T : Over S} (w : T ⟶ Zatt act N) :
    attEquiv act F.toAddSubmonoid T (w ≫ faceZ act N hF) =
      AttractorPt.ofFace hF (attEquiv act N T w) := by
  rw [attEquiv_comp, faceZ, Equiv.apply_symm_apply]
  have : attEquiv act N T w = (attEquiv act N _ (𝟙 _)).baseChange w := by
    rw [← attEquiv_comp, Category.comp_id]
  rw [this]
  refine AttractorPt.ext ?_
  funext T₁ t a
  rfl

/-- The step "By 11.2 ... smooth" in the proof of **Theorem 12.4** of Algebraic Magnetism, obtained
here from Corollary 11.10 (Proposition 11.7). -/
theorem smooth_faceZ [Smooth X.hom] : Smooth (faceZ act N hF).left :=
  SmoothSchemes.smooth_repFace N act hF (representsAttractor act N)
    (representsAttractor act F.toAddSubmonoid) (faceZ act N hF) (fun _ w => faceZ_spec act N hF w)

end Face


section Local

variable {U : S.Opens} (hU : IsAffineOpen U)

/-- Proposition 3.31 for `M → Z = M/F`: the `Z`-grading of `A`. -/
abbrev gZ : (M ⧸ F) → Submodule Γ(S, U) (Aalg X U) :=
  pushGrading (gradingOf hU act) (QuotientAddGroup.mk' F)

/-- `Y = N/F`. -/
abbrev Yq (F : AddSubgroup M) (N : AddSubmonoid M) : AddSubmonoid (M ⧸ F) :=
  N.map (QuotientAddGroup.mk' F)

include hF in
lemma comap_Yq : (Yq F N).comap (QuotientAddGroup.mk' F) = N := by
  ext x
  constructor
  · rintro ⟨n, hn, e⟩
    have hg : -n + x ∈ F := QuotientAddGroup.eq.1 e
    have := N.add_mem hn (hF.le hg)
    simpa using this
  · exact fun hx => ⟨x, hx, rfl⟩

lemma comap_bot : (⊥ : AddSubmonoid (M ⧸ F)).comap (QuotientAddGroup.mk' F) = F.toAddSubmonoid := by
  ext x
  change QuotientAddGroup.mk' F x = 0 ↔ x ∈ F
  exact QuotientAddGroup.eq_zero_iff x

include hF in
lemma hI₁' : magnetIdeal (gradingOf hU act) N = magnetIdeal (gZ act hU (F := F)) (Yq F N) := by
  rw [magnetIdeal_pushGrading, comap_Yq N hF]

lemma hI₀' : magnetIdeal (gradingOf hU act) F.toAddSubmonoid =
    magnetIdeal (gZ act hU (F := F)) (⊥ : AddSubmonoid (M ⧸ F)) := by
  rw [magnetIdeal_pushGrading, comap_bot]

include hF in
lemma sharp_Yq : ∀ y ∈ Yq F N, ∀ y' ∈ Yq F N, y + y' = 0 → y = 0 := by
  rintro _ ⟨n, hn, rfl⟩ _ ⟨n', hn', rfl⟩ e
  have : n + n' ∈ F := (QuotientAddGroup.eq_zero_iff _).1 e
  exact (QuotientAddGroup.eq_zero_iff _).2 (hF.mem_of_add_mem hn hn' this).1

/-- The morphism `A/J_F → A/J_N` of the printed proof. -/
abbrev rho0 : Qalg act F.toAddSubmonoid hU →ₐ[Γ(S, U)] Qalg act N hU :=
  rho (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU) (sharp_Yq N hF)

lemma pr0_gr {m : M} {a : Aalg X U} (ha : a ∈ gradingOf hU act m) :
    pr0 (gZ act hU (F := F)) a = if m ∈ F then a else 0 := by
  rw [pr0_of_mem _ (le_pushGrading (QuotientAddGroup.mk' F) m ha)]
  congr 1
  exact propext (QuotientAddGroup.eq_zero_iff m)

lemma rho0_mk {a : Aalg X U} :
    rho0 act N hF hU (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (pr0 (gZ act hU (F := F)) a) := rfl


/-- The value of `X^N → X^F` on functions of degree in `F`. -/
lemma eval_face {T : Over S} (hT : LiesOver T U) (φ : AttractorPt act N T) {m : M}
    {x : Aalg X U} (hx : x ∈ gradingOf hU act m) (hm : m ∈ F) :
    ptX X hU T hT (AttractorPt.ofFace hF φ).toPoint x = ptX X hU T hT φ.toPoint x := by
  obtain ⟨f, rfl⟩ : ∃ f, ptGr hU act N hT f = φ :=
    ⟨_, (localEquiv hU act N hT).left_inv φ⟩
  have hmN : m ∈ N := hF.le hm
  obtain ⟨c, hc⟩ := exists_single_of_mem_magnetGrading hmN (f.map_mem' hx)
  change ptX X hU T hT (grVal hU act N hT (𝟙 T) (APt.faceExt hF 1) f) x =
    ptX X hU T hT (grVal hU act N hT (𝟙 T) 1 f) x
  rw [grVal, grVal, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change evalAlg _ _ (f.toAlgHom x) = evalAlg _ _ (f.toAlgHom x)
  have hc' : f.toAlgHom x = AddMonoidAlgebra.single ⟨m, hmN⟩ c := hc
  rw [hc', evalAlg_single, evalAlg_single]
  congr 1
  exact APt.faceExt_pos hF 1 (n := Multiplicative.ofAdd ⟨m, hmN⟩) hm

/-- The ring form of `p_{N,F} : X^N → X^F`. -/
lemma localEquiv_ofFace {T : Over S} (hT : LiesOver T U) (φ : AttractorPt act N T) :
    localEquiv hU act F.toAddSubmonoid hT (AttractorPt.ofFace hF φ) =
      (localEquiv hU act N hT φ).comp (rho0 act N hF hU) := by
  refine AlgHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change ptX X hU T hT (AttractorPt.ofFace hF φ).toPoint a =
    localEquiv hU act N hT φ (rho0 act N hF hU (Ideal.Quotient.mk _ a))
  rw [rho0_mk]
  change _ = ptX X hU T hT φ.toPoint (pr0 (gZ act hU (F := F)) a)
  induction a using DirectSum.Decomposition.inductionOn (gradingOf hU act) with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | @homogeneous m a =>
    rw [pr0_gr act hU a.2]
    split_ifs with hm
    · exact eval_face act N hF hU hT φ a.2 hm
    · rw [map_zero]
      exact toPoint_kills hU act F.toAddSubmonoid hT _
        (mem_magnetIdeal_of_notMem (fun h => hm h) a.2)

lemma localEquiv_rho0_mk {T : Over S} (hT : LiesOver T U) (φ : AttractorPt act N T) (a : Aalg X U) :
    localEquiv hU act N hT φ (rho0 act N hF hU (Ideal.Quotient.mk _ a)) =
      ptX X hU T hT φ.toPoint (pr0 (gZ act hU (F := F)) a) := rfl

lemma ptX_comp_iotaX {T : Over S} (hT : LiesOver T U) (s : T ⟶ Phi hU (Aalg X U)) :
    ptX X hU T hT (s ≫ iotaX X hU) = homPhi hU T hT _ s := by
  change homPhi hU T hT _ (toChart X hU T hT ((toChart X hU T hT).symm s)) = _
  rw [Equiv.apply_symm_apply]

/-- `Z_U^N → Z^N → Z^F` is `Z_U^N → Z_U^F → Z^F`. -/
lemma chart_square (U : S.affineOpens) :
    iotaZ act N U ≫ faceZ act N hF =
      PhiMap U.2 (rho0 act N hF U.2) ≫ iotaZ act F.toAddSubmonoid U := by
  refine iAtt_cancel act F.toAddSubmonoid ?_
  have hT := liesOver_Zloc act N U.2
  apply (ptX X U.2 _ hT).injective
  have e₁ : iotaZ act N U ≫ faceZ act N hF ≫ iAtt act F.toAddSubmonoid =
      (AttractorPt.ofFace hF (attEquiv act N _ (iotaZ act N U))).toPoint := by
    rw [← faceZ_spec act N hF, toPoint_attEquiv, Category.assoc]
  have e₂ : (attEquiv act N _ (iotaZ act N U)).toPoint = PhiMap U.2 (qAlg act N U.2) ≫ iotaX X U.2 := by
    rw [toPoint_attEquiv, iotaZ_iAtt]
    rfl
  rw [Category.assoc, e₁, Category.assoc, iotaZ_iAtt]
  have e₃ := ptX_comp_iotaX (X := X) U.2 hT
    (PhiMap U.2 (rho0 act N hF U.2) ≫ PhiMap U.2 (qAlg act F.toAddSubmonoid U.2))
  refine Eq.trans ?_ (Eq.trans e₃.symm (congrArg _ (Category.assoc _ _ _)))
  refine Eq.trans ?_ (congrArg _ (PhiMap_comp U.2 (qAlg act F.toAddSubmonoid U.2) (rho0 act N hF U.2)))
  refine Eq.trans ?_ (homPhi_PhiMap U.2 _).symm
  refine AlgHom.ext fun a => ?_
  have h := DFunLike.congr_fun (localEquiv_ofFace act N hF U.2 hT (attEquiv act N _ (iotaZ act N U)))
    (Ideal.Quotient.mk _ a)
  refine Eq.trans h ?_
  refine (localEquiv_rho0_mk act N hF U.2 hT _ a).trans ?_
  rw [e₂]
  rw [ptX_comp_iotaX U.2 hT]
  rw [homPhi_PhiMap U.2]
  rfl

instance instOpenIotaZ (U : S.affineOpens) (N : AddSubmonoid M) : IsOpenImmersion (iotaZ act N U).left := by
  have := isOpen_iota (X := X) U
  exact MorphismProperty.of_isPullback (isPullback_chart act N U).flip this

/-- `B₀ → B` is smooth: restriction of `smooth_faceZ` to the chart. -/
theorem smooth_rho0 [Smooth X.hom] (U : S.affineOpens) : (rho0 act N hF U.2).toRingHom.Smooth := by
  have := smooth_faceZ act N hF
  have h : Smooth ((PhiMap U.2 (rho0 act N hF U.2)).left ≫ (iotaZ act F.toAddSubmonoid U).left) := by
    have e := congrArg (fun k => k.left) (chart_square act N hF U)
    simp only [Over.comp_left] at e
    rw [← e]
    infer_instance
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f hf => by
      have : IsIso f := hf
      change Smooth f
      infer_instance
  have : MorphismProperty.HasOfPostcompProperty (@Smooth : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict (@Smooth : MorphismProperty Scheme.{u}) (fun f U hf => by
      have : Smooth f := hf
      infer_instance)
  have h₂ : Smooth (PhiMap U.2 (rho0 act N hF U.2)).left :=
    MorphismProperty.of_postcomp @Smooth (W' := @IsOpenImmersion) _ _ (instOpenIotaZ act U _) h
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h₂

end Local

section Main

variable {U : S.Opens} (hU : IsAffineOpen U)

include hU in
lemma finiteType_Aalg [Smooth X.hom] : Algebra.FiniteType Γ(S, U) (Aalg X U) := by
  have h : (X.hom.appLE U (X.hom ⁻¹ᵁ U) le_rfl).hom.FinitePresentation :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) X.hom inferInstance
      ⟨U, hU⟩ ⟨X.hom ⁻¹ᵁ U, isAffineOpen_preimage X hU⟩ le_rfl
  letI := (X.hom.appLE U (X.hom ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have : Algebra.FinitePresentation Γ(S, U) Γ(X.left, X.hom ⁻¹ᵁ U) := h
  exact (inferInstance : Algebra.FiniteType Γ(S, U) Γ(X.left, X.hom ⁻¹ᵁ U))

/-- Comp of a product: if `m` is not in the submonoid `P`, then the component of degree `m` of a
product is a sum of `x_u y_v` with `u` or `v` outside `P`. -/
lemma comp_mul_mem {𝒜 : M → Submodule Γ(S, U) (Aalg X U)} [GradedAlgebra 𝒜] {P : AddSubmonoid M}
    {J : Ideal (Aalg X U)} {x y : Aalg X U}
    (hx : ∀ m, m ∉ P → (DirectSum.decompose 𝒜 x m : Aalg X U) ∈ J)
    (hy : ∀ m, m ∉ P → (DirectSum.decompose 𝒜 y m : Aalg X U) ∈ J) (m : M) (hm : m ∉ P) :
    (DirectSum.decompose 𝒜 (x * y) m : Aalg X U) ∈ J := by
  rw [← GradedRing.proj_apply 𝒜 m, ← DirectSum.sum_support_decompose 𝒜 x,
    ← DirectSum.sum_support_decompose 𝒜 y, Finset.sum_mul_sum, map_sum]
  refine J.sum_mem fun u _ => ?_
  rw [map_sum]
  refine J.sum_mem fun v _ => ?_
  rw [GradedRing.proj_apply]
  have hmem := SetLike.mul_mem_graded (SetLike.coe_mem (DirectSum.decompose 𝒜 x u))
    (SetLike.coe_mem (DirectSum.decompose 𝒜 y v))
  by_cases huv : u + v = m
  · subst huv
    rw [DirectSum.decompose_of_mem_same 𝒜 hmem]
    by_cases hu : u ∈ P
    · have hv : v ∉ P := fun hv => hm (P.add_mem hu hv)
      exact J.mul_mem_left _ (hy v hv)
    · exact J.mul_mem_right _ (hx u hu)
  · rw [DirectSum.decompose_of_mem_ne 𝒜 hmem huv]
    exact J.zero_mem

include hF hU in
/-- **Proposition 8.5, the affine step** (first half of its printed proof: "consider degrees of a
finite set of generators"): a finitely generated `N_c ⊆ N` containing `F`, such that every function
of degree outside `N_c` lies in `J_N`. -/
theorem exists_Nc [Smooth X.hom] (h : N.FG ∨ AddGroup.FG M) :
    ∃ Nc : AddSubmonoid M, Nc ≤ N ∧ F.toAddSubmonoid ≤ Nc ∧ Nc.FG ∧
      ∀ m, m ∉ Nc → ∀ a ∈ gradingOf hU act m, a ∈ magnetIdeal (gradingOf hU act) N := by
  rcases h with h | h
  · exact ⟨N, le_rfl, hF.le, h, fun m hm a ha => mem_magnetIdeal_of_notMem hm ha⟩
  have hft := finiteType_Aalg (X := X) hU
  obtain ⟨g, hg⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra Γ(S, U) (Aalg X U)).FG)
  let 𝒜 := gradingOf hU act
  let D : Finset M := g.biUnion fun x => (DirectSum.decompose 𝒜 x).support
  let Nc : AddSubmonoid M := F.toAddSubmonoid ⊔ AddSubmonoid.closure {m | m ∈ D ∧ m ∈ N}
  have hle : Nc ≤ N := sup_le hF.le (AddSubmonoid.closure_le.2 fun m hm => hm.2)
  have hFg : F.toAddSubmonoid.FG := by
    have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.2 h
    have hF₁ : (AddSubgroup.toIntSubmodule F).FG := IsNoetherian.noetherian _
    have hF₂ : F.FG := (Submodule.fg_iff_addSubgroup_fg _).1 hF₁
    exact (AddSubgroup.fg_iff_addSubmonoid_fg F).1 hF₂
  have hfin : (AddSubmonoid.closure {m | m ∈ D ∧ m ∈ N}).FG :=
    ⟨D.filter (· ∈ N), by
      congr 1
      ext m
      simp⟩
  refine ⟨Nc, hle, le_sup_left, hFg.sup hfin, ?_⟩
  have key : ∀ x : Aalg X U, ∀ m, m ∉ Nc →
      (DirectSum.decompose 𝒜 x m : Aalg X U) ∈ magnetIdeal 𝒜 N := by
    intro x
    have hx : x ∈ Algebra.adjoin Γ(S, U) (g : Set (Aalg X U)) := hg ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      intro m hm
      by_cases hd : (DirectSum.decompose 𝒜 x m : Aalg X U) = 0
      · rw [hd]
        exact Ideal.zero_mem _
      · have hmD : m ∈ D := Finset.mem_biUnion.2 ⟨x, hx, by
          rw [DFinsupp.mem_support_iff]
          exact fun e => hd (by rw [e]; rfl)⟩
        have hmN : m ∉ N := fun hN =>
          hm (AddSubmonoid.mem_sup_right (AddSubmonoid.subset_closure ⟨hmD, hN⟩))
        exact mem_magnetIdeal_of_notMem hmN (SetLike.coe_mem _)
    | algebraMap r =>
      intro m hm
      have hm0 : (0 : M) ≠ m := fun e => hm (e ▸ Nc.zero_mem)
      rw [DirectSum.decompose_of_mem_ne 𝒜 (SetLike.algebraMap_mem_graded 𝒜 r) hm0]
      exact Ideal.zero_mem _
    | add x y _ _ hx hy =>
      intro m hm
      rw [DirectSum.decompose_add]
      exact Ideal.add_mem _ (hx m hm) (hy m hm)
    | mul x y _ _ hx hy => exact comp_mul_mem hx hy
  intro m hm a ha
  have := key a m hm
  rwa [DirectSum.decompose_of_mem_same 𝒜 ha] at this

/-- **Theorem 12.4**, `X → S` affine and smooth, `N` finitely generated or `M` finitely generated:
over an affine open `U` of `S`, with `B₀ = O(X^F|_U) → B = O(X^N|_U)`, the module
`P = ker(B → B₀)/ker²` is finite projective and `B = Sym_{B₀}(P)`.
Here `F` is a face subgroup of `N`; see `thm124_affine` for `F = N^×`. -/
theorem printed_affine [Smooth X.hom] (h : N.FG ∨ AddGroup.FG M) :
    letI := (rho0 act N hF hU).toRingHom.toAlgebra
    Module.Finite (Qalg act F.toAddSubmonoid hU)
        (Conormal (piB (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU)
          (sharp_Yq N hF))) ∧
      Module.Projective (Qalg act F.toAddSubmonoid hU)
        (Conormal (piB (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU)
          (sharp_Yq N hF))) ∧
      Nonempty (SymmetricAlgebra (Qalg act F.toAddSubmonoid hU)
        (Conormal (piB (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU)
          (sharp_Yq N hF))) ≃ₐ[Qalg act F.toAddSubmonoid hU] Qalg act N hU) := by
  obtain ⟨Nc, hle, hFN, hfg, hsupp⟩ := exists_Nc act N hF hU h
  have hFc : IsFace F.toAddSubmonoid Nc :=
    ⟨hFN, fun {x y} hx hy e => hF.mem_of_add_mem (hle hx) (hle hy) e⟩
  obtain ⟨w, hw⟩ := exists_weight_of_isFace hFc hfg
  let f := QuotientAddGroup.mk' F
  -- `w` descends to `M/F`
  let wZ : M ⧸ F → ℕ := fun z =>
    if hz : ∃ n : Nc, f n = z then w hz.choose else 0
  have wZ_f : ∀ n : Nc, wZ (f n) = w n := by
    intro n
    have hz : ∃ n' : Nc, f n' = f n := ⟨n, rfl⟩
    have e : wZ (f n) = w hz.choose := dif_pos hz
    rw [e]
    obtain ⟨n', hn'⟩ : ∃ n' : Nc, n' = hz.choose := ⟨_, rfl⟩
    rw [← hn']
    have ef : f (n' : M) = f n := by rw [hn']; exact hz.choose_spec
    -- `n' = n + g` and `n = n' + g'` with `g, g' ∈ F`
    have hg₁ : -(n : M) + n' ∈ F := QuotientAddGroup.eq.1 ef.symm
    have hg₂ : -(n' : M) + n ∈ F := QuotientAddGroup.eq.1 ef
    let g₁ : Nc := ⟨_, hFN hg₁⟩
    let g₂ : Nc := ⟨_, hFN hg₂⟩
    have w₁ : w g₁ = 0 := (hw g₁).2 hg₁
    have w₂ : w g₂ = 0 := (hw g₂).2 hg₂
    have e₁ : n' = n + g₁ := Subtype.ext (by simp [g₁])
    rw [e₁, map_add, w₁, add_zero]
  have himg : ∀ z, ∀ a ∈ gZ act hU (F := F) z,
      Ideal.Quotient.mk (magnetIdeal (gradingOf hU act) N) a ≠ 0 → ∃ n : Nc, f n = z := by
    intro z a ha hne
    by_contra hz
    refine hne (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    refine pushGrading_induction (motive := fun a => a ∈ magnetIdeal (gradingOf hU act) N) ha
      (fun m hm b hb => hsupp m (fun hmc => hz ⟨⟨m, hmc⟩, hm⟩) b hb)
      (Ideal.zero_mem _) (fun a b h₁ h₂ => Ideal.add_mem _ h₁ h₂)
  have hsm : (rho0 act N hF hU).toRingHom.Smooth := smooth_rho0 act N hF ⟨U, hU⟩
  letI := (rho0 act N hF hU).toRingHom.toAlgebra
  have hS : Algebra.Smooth (Qalg act F.toAddSubmonoid hU) (Qalg act N hU) := hsm
  have : Algebra.FormallySmooth (Qalg act F.toAddSubmonoid hU) (Qalg act N hU) := inferInstance
  have : Algebra.FiniteType (Qalg act F.toAddSubmonoid hU) (Qalg act N hU) := inferInstance
  refine printed_graded (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU)
    (sharp_Yq N hF) wZ ?_ ?_
  · intro z a ha hne hz0
    obtain ⟨n, rfl⟩ := himg z a ha hne
    rw [wZ_f] at hz0
    exact (QuotientAddGroup.eq_zero_iff _).2 ((hw n).1 hz0)
  · intro u a ha hne v b hb hne'
    obtain ⟨n, rfl⟩ := himg u a ha hne
    obtain ⟨n', rfl⟩ := himg v b hb hne'
    have : f (n : M) + f (n' : M) = f ((n + n' : Nc) : M) := by
      rw [AddSubmonoid.coe_add, map_add]
    rw [this, wZ_f, wZ_f, wZ_f, map_add]

end Main

#print axioms AlgMag.Sec12Printed.printed_affine

end AlgMag.Sec12Printed
