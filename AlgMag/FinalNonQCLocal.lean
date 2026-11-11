/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCBase

/-!
# Fact 3.34 (ii), Theorem 15.3 with `S` arbitrary

"The assertion is local over `S`": a point over an affine `T` lands, Zariski locally on `T`, in an affine open `O` of `S`, and there the
statement is `fact334_nonqc` on the site of `O`, where the base is separated.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- The statement over an object `T₀` of the site whose underlying scheme is separated. -/
theorem fact334_step (T₀ : BigFppfOver B S hS) [T₀.left.1.IsSeparated]
    (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) {s : Set (AddSubmonoid M)} (y) (hne : s.Nonempty)
    (hy : ∀ N ∈ s, attractorImage act N = y) (W : BigFppfOver B T₀.left.1 T₀.left.2)
    (x : X.obj (op ((Over.map T₀.hom).obj W))) (hx : x ∈ y ((Over.map T₀.hom).obj W)) :
    ∃ φ : AttractorPt act (sInf s) ((Over.map T₀.hom).obj W), φ.toPoint = x := by
  let y₀ : ∀ W : BigFppfOver B T₀.left.1 T₀.left.2, Set ((Res X T₀).obj (op W)) :=
    fun W r => r.1 ∈ y ((Over.map T₀.hom).obj W)
  have hy₀ : ∀ N ∈ s, attractorImage (resAct (T₀ := T₀) act) N = y₀ := by
    intro N hN
    funext W'
    ext r
    constructor
    · rintro ⟨φ, rfl⟩
      change φ.toPoint.1 ∈ y _
      rw [← hy N hN, ← attrUp_toPoint]
      exact ⟨_, rfl⟩
    · intro hr
      have hr' : r.1 ∈ y ((Over.map T₀.hom).obj W') := hr
      rw [← hy N hN] at hr'
      obtain ⟨φ, hφ⟩ := hr'
      exact ⟨attrDown φ, Subtype.ext ((attrDown_toPoint φ).trans hφ)⟩
  have hR := res_alg T₀ hX
  have hfp' := (lfp_toT1_iff hR).1 (res_lfp T₀ hX ((lfp_toT1_iff hX).2 hfp))
  have key := fact334_nonqc hZ hM hR (res_sep T₀ hX hsep) hfp' (resAct (T₀ := T₀) act) y₀ hne hy₀
  have hmem : (resMk (T₀ := T₀) x : (Res X T₀).obj (op W)) ∈ y₀ W := hx
  rw [← key] at hmem
  obtain ⟨φ₀, hφ₀⟩ := hmem
  exact ⟨attrUp φ₀, (attrUp_toPoint φ₀).trans (congrArg Subtype.val hφ₀)⟩

include hZ in
/-- **Fact 3.34 (ii)**, arbitrary family, `X` separated, locally of finite presentation, not necessarily quasi-compact, `S` arbitrary,
no atlas in the hypotheses. -/
theorem fact334_general (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) {s : Set (AddSubmonoid M)} (y) (hne : s.Nonempty)
    (hy : ∀ N ∈ s, attractorImage act N = y) : attractorImage act (sInf s) = y := by
  obtain ⟨N₀, hN₀⟩ := id hne
  refine le_antisymm ((attractorImage_monotone act (sInf_le hN₀)).trans_eq (hy N₀ hN₀)) ?_
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hsep' := isSeparatedOver_iff_space.1 hsep
  have hinj := fun (P : AddSubmonoid M) T => attractor_toPoint_injective_sep (aX := act) hX hsep' P T
  intro T t ht
  let I : Type u := { W : ((SCH).obj T).affineOpens //
    ∃ O : S.affineOpens, ∀ τ ∈ W.1, structMap T τ ∈ O.1 }
  have hC : ∀ i : I, B.Contains (i.1.1 : Scheme.{u}) := fun i =>
    Scheme.size_lt_of_isOpenImmersion i.1.1.ι T.left.property
  let V : I → BigFppfOver B S hS := fun i => siteObject B S hS (hC i) (i.1.1.ι ≫ T.hom.hom)
  let π : ∀ i, V i ⟶ T := fun i => siteHom i.1.1.ι rfl
  have hcov : Sieve.ofArrows V π ∈ BigFppfOver.topology B S hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS π
      (fun i => inferInstanceAs (IsOpenImmersion i.1.1.ι)) fun τ => ?_
    obtain ⟨_, ⟨O, hO, rfl⟩, hs, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (structMap T τ)) isOpen_univ
    have hopen : IsOpen (structMap T ⁻¹' O) :=
      O.isOpen.preimage (Scheme.Hom.continuous _)
    obtain ⟨_, ⟨W, hW, rfl⟩, hτ, hsub⟩ := ((SCH).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (show τ ∈ structMap T ⁻¹' O from hs) hopen
    refine ⟨⟨⟨W, hW⟩, ⟨O, hO⟩, fun τ' h' => hsub h'⟩, ⟨τ, hτ⟩, ?_⟩
    rfl
  refine exists_toPoint_of_sieve hsX (hinj _) t _ hcov ?_
  rintro Y g ⟨Y', a, b, ⟨i⟩, rfl⟩
  obtain ⟨W, ⟨O, hO⟩, hsub⟩ := i
  let i' : I := ⟨W, ⟨O, hO⟩, hsub⟩
  obtain ⟨l, -⟩ := exists_lift_openBase (O := O) (V i') (fun τ => by
    have : structMap (V i') τ = structMap T (W.1.ι τ) := rfl
    rw [this]
    exact hsub (τ : W.1.toScheme).1 (τ : W.1.toScheme).2)
  let T₀ := openBase (B := B) (hS := hS) O
  have hAff : IsAffine ((SCH).obj T₀) := isAffine_openBase hO
  haveI : T₀.left.1.IsSeparated := by
    have : IsAffine T₀.left.1 := hAff
    infer_instance
  have hψ : l.left ≫ T₀.hom = (V i').hom := Over.w l
  let e := overMapMkIso T₀.hom hψ
  have hrest : X.map e.inv.op (X.map (π i').op t) ∈ y ((Over.map T₀.hom).obj (Over.mk l.left)) := by
    rw [← hy N₀ hN₀] at ht ⊢
    obtain ⟨χ, rfl⟩ := ht
    refine ⟨AttractorPt.baseChange e.inv (AttractorPt.baseChange (π i') χ), ?_⟩
    rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange]
  obtain ⟨φ, hφ⟩ := fact334_step hZ T₀ hM hX hsep hfp act y hne hy (Over.mk l.left) _ hrest
  refine ⟨AttractorPt.baseChange a (AttractorPt.baseChange e.hom φ), ?_⟩
  rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, hφ,
    map_overMapMkIso_hom_inv T₀.hom X hψ, ← Functor.map_comp_apply, ← op_comp]

include hZ in
/-- **Theorem 15.3**, `X` separated, locally of finite presentation, `S` arbitrary. -/
noncomputable def thm153_general (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) :
    pureMagnets (attractorImage act) ≃ Set.range (attractorImage act) :=
  pureEquivRange
    { monotone := attractorImage_monotone act
      sInf_of_const := fun _ y hne hy => fact334_general hZ hM hX hsep hfp act y hne hy }

end AlgMag.Final

#print axioms AlgMag.Final.fact334_general
#print axioms AlgMag.Final.thm153_general
