/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalAtlasFree
import AlgMag.FinalNonQCRelQC
import AlgMag.ChartQSL11Pull

/-!
# Proposition 8.5 with `S` not necessarily separated

`X` separated and locally of finite presentation, `X → S` quasi-compact, `S` quasi-compact (not necessarily separated), no atlas in
the hypotheses. "The assertion is local over `S`": `S` is covered by finitely many affine opens `O`; over each, `prop85_free` applied to
the restriction of `X` gives a finitely generated `N_O`; `N_c` is the supremum of the `N_O` and of `N^×`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hZ : B.Contains (⊤_ Scheme.{u}))

local notation "SCH" => BigFppfOver.toScheme B S hS

include hZ in
/-- **Proposition 8.5**, `S` quasi-compact, not necessarily separated, `X → S` quasi-compact, no atlas in the hypotheses. -/
theorem prop85_general [CompactSpace S] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompact B S hS (toT1 X)) (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    ∃ (Nc : AddSubmonoid M) (hc : Nc ≤ N), Nc.FG ∧ unitsSub Nc = unitsSub N ∧
      ∀ T : BigFppfOver B S hS, Function.Bijective (AttractorPt.ofLE (act := act) (T := T) hc) := by
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hsep' := isSeparatedOver_iff_space.1 hsep
  have hlfp := (lfp_toT1_iff hX).2 hfp
  obtain ⟨t, A, hA, hcovS⟩ := AlgMag.ChartQSL11.exists_finite_affine_cover S
  -- the local statement over each affine open of the cover
  have hloc : ∀ i : t, ∃ (Ni : AddSubmonoid M) (hi : Ni ≤ N), Ni.FG ∧
      ∀ W : BigFppfOver B (openBase (B := B) (hS := hS) (A i)).left.1
          (openBase (B := B) (hS := hS) (A i)).left.2,
        Function.Surjective (AttractorPt.ofLE (act := resAct (T₀ := openBase (B := B) (hS := hS) (A i)) act)
          (T := W) hi) := by
    intro i
    let T₀ := openBase (B := B) (hS := hS) (A i)
    have : IsAffine T₀.left.1 := isAffine_openBase (B := B) (hS := hS) (hA i)
    have : T₀.left.1.IsSeparated := inferInstance
    have : CompactSpace T₀.left.1 := inferInstance
    have hR := res_alg T₀ hX
    have hsR := res_sep T₀ hX hsep
    have hlR := res_lfp T₀ hX hlfp
    obtain ⟨Ni, hi, hfg, -, hb⟩ := prop85_free hZ hM hR (isSeparatedOver_iff_space.1 hsR) hsR hlR
      ((lfp_toT1_iff hR).1 hlR) (res_qc T₀ hX hq) (resAct act) N
    exact ⟨Ni, hi, hfg, fun W => (hb W).2⟩
  choose Ni hi hfg hsurj using hloc
  let U : AddSubmonoid M := (unitsSub N).toAddSubmonoid
  have hU : U ≤ N := fun x hx => by
    simp only [U, unitsSub] at hx ⊢
    exact hx.1
  let Nc : AddSubmonoid M := U ⊔ ⨆ i, Ni i
  have hc : Nc ≤ N := sup_le hU (iSup_le hi)
  have hle : ∀ i, Ni i ≤ Nc := fun i => le_sup_of_le_right (le_iSup Ni i)
  refine ⟨Nc, hc, ?_, ?_, fun T => ⟨?_, ?_⟩⟩
  · refine (fg_unitsSub N).sup ?_
    classical
    choose s hs using fun i => hfg i
    refine ⟨Finset.univ.biUnion s, ?_⟩
    rw [Finset.coe_biUnion]
    simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true]
    rw [AddSubmonoid.closure_iUnion]
    simp only [hs]
  · ext x
    simp only [unitsSub]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hc h1, hc h2⟩
    · rintro hx
      exact ⟨le_sup_left (a := U) (show x ∈ U from hx),
        le_sup_left (a := U) (show -x ∈ U from by
          simp only [U, AddSubgroup.mem_toAddSubmonoid]; exact (unitsSub N).neg_mem hx)⟩
  · intro χ χ' h
    apply attractor_toPoint_injective_sep hX hsep'
    rw [← AttractorPt.toPoint_ofLE hc χ, ← AttractorPt.toPoint_ofLE hc χ', h]
  intro ψ
  suffices hχ : ∃ χ : AttractorPt act Nc T, χ.toPoint = ψ.toPoint by
    obtain ⟨χ, hχ⟩ := hχ
    exact ⟨χ, attractor_toPoint_injective_sep hX hsep' _ _ ((AttractorPt.toPoint_ofLE hc χ).trans hχ)⟩
  have hinjN := fun T => attractor_toPoint_injective_sep (aX := act) hX hsep' Nc T
  let I : Type u := { W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens //
    ∃ i : t, ∀ τ ∈ W.1, structMap T τ ∈ A i }
  have hC : ∀ i : I, B.Contains (i.1.1 : Scheme.{u}) := fun i =>
    Scheme.size_lt_of_isOpenImmersion i.1.1.ι T.left.property
  let V : I → BigFppfOver B S hS := fun i => siteObject B S hS (hC i) (i.1.1.ι ≫ T.hom.hom)
  let π : ∀ i, V i ⟶ T := fun i => siteHom i.1.1.ι rfl
  have hcov : Sieve.ofArrows V π ∈ BigFppfOver.topology B S hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS π
      (fun i => inferInstanceAs (IsOpenImmersion i.1.1.ι)) fun τ => ?_
    obtain ⟨j, hj⟩ := hcovS (structMap T τ)
    have hopen : IsOpen (structMap T ⁻¹' (A j : Set S)) :=
      (A j).isOpen.preimage (Scheme.Hom.continuous _)
    obtain ⟨_, ⟨W, hW, rfl⟩, hτ, hsub⟩ :=
      ((BigFppfOver.toScheme B S hS).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (show τ ∈ structMap T ⁻¹' (A j : Set S) from hj) hopen
    refine ⟨⟨⟨W, hW⟩, j, fun τ' h' => hsub h'⟩, ⟨τ, hτ⟩, ?_⟩
    rfl
  refine exists_toPoint_of_sieve hsX hinjN ψ.toPoint _ hcov ?_
  rintro Wt g ⟨Wt', a, b, ⟨i⟩, rfl⟩
  obtain ⟨W, j, hsub⟩ := i
  let i' : I := ⟨W, j, hsub⟩
  obtain ⟨l, -⟩ := exists_lift_openBase (O := A j) (V i') (fun τ => by
    have : structMap (V i') τ = structMap T (W.1.ι τ) := rfl
    rw [this]
    exact hsub (τ : W.1.toScheme).1 (τ : W.1.toScheme).2)
  let T₀ := openBase (B := B) (hS := hS) (A j)
  have hψ : l.left ≫ T₀.hom = (V i').hom := Over.w l
  let e := overMapMkIso T₀.hom hψ
  let ψ₀ : AttractorPt (resAct (T₀ := T₀) act) N (Over.mk l.left) :=
    attrDown (AttractorPt.baseChange e.inv (AttractorPt.baseChange (π i') ψ))
  obtain ⟨φ₀, hφ₀⟩ := hsurj j (Over.mk l.left) ψ₀
  let φ : AttractorPt act Nc ((Over.map T₀.hom).obj (Over.mk l.left)) := attrUp (AttractorPt.ofLE (hle j) φ₀)
  have hφ : φ.toPoint = (AttractorPt.baseChange e.inv (AttractorPt.baseChange (π i') ψ)).toPoint := by
    rw [attrUp_toPoint, AttractorPt.toPoint_ofLE, ← AttractorPt.toPoint_ofLE (hi j) φ₀, hφ₀]
    exact attrDown_toPoint _
  refine ⟨AttractorPt.baseChange a (AttractorPt.baseChange e.hom φ), ?_⟩
  rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, hφ, AttractorPt.toPoint_baseChange,
    AttractorPt.toPoint_baseChange, map_overMapMkIso_hom_inv T₀.hom X hψ, ← Functor.map_comp_apply, ← op_comp]

end AlgMag.Final

#print axioms AlgMag.Final.prop85_general
