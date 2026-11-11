/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartTower
import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# The tower of thickenings of the orbit without separatedness (chart-lemma proof, §2)

The relation of the chart of `X_n` is affine for any algebraic space `X`
(no quasi-separatedness needed): the relation
`R_n = V_n ×_{X_n} V_n` is a thickening of `R_0 = V_0 ×_O V_0`, which is affine since `O` is, and a
thickening of an affine scheme is affine (Stacks 06AD).

* `isAffine_relation_of_nilpotent`: generalizes `ChartMain.isAffine_relation`.
* `exists_affine_thickening_qs`: `ChartMain.exists_affine_thickening`, no hypothesis on `X`.
* `exists_affineTower_qs`: `ChartMain.exists_affineTower`, no hypothesis on `X`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQSAsm

open ChartMain PrimeSpectrum

/-- A closed immersion of affine schemes with nilpotent kernel on global sections is surjective. -/
lemma surjective_of_ker_pow {Z V : Scheme.{u}} [IsAffine Z] [IsAffine V] (i : Z ⟶ V)
    [IsClosedImmersion i] {n : ℕ} (hn : RingHom.ker i.appTop.hom ^ n = ⊥) : Surjective i := by
  have hs : Function.Surjective i.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hS : Surjective (Spec.map i.appTop) := by
    refine ⟨fun x => ?_⟩
    have hxp : (x : PrimeSpectrum Γ(V, ⊤)).asIdeal.IsPrime := PrimeSpectrum.isPrime _
    have hk : RingHom.ker i.appTop.hom ≤ (x : PrimeSpectrum Γ(V, ⊤)).asIdeal := by
      intro a ha
      have h1 : a ^ n ∈ RingHom.ker i.appTop.hom ^ n := Ideal.pow_mem_pow ha n
      rw [hn] at h1
      have h2 : a ^ n ∈ (x : PrimeSpectrum Γ(V, ⊤)).asIdeal := by
        rw [(Ideal.mem_bot.1 h1)]
        exact Ideal.zero_mem _
      exact hxp.mem_of_pow_mem n h2
    let y : PrimeSpectrum Γ(Z, ⊤) :=
      ⟨Ideal.map i.appTop.hom (x : PrimeSpectrum Γ(V, ⊤)).asIdeal, Ideal.map_isPrime_of_surjective hs hk⟩
    refine ⟨y, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap i.appTop.hom (Ideal.map i.appTop.hom (x : PrimeSpectrum Γ(V, ⊤)).asIdeal) = _
    rw [Ideal.comap_map_of_surjective _ hs]
    exact sup_eq_left.2 hk
  have e : i = Z.isoSpec.hom ≫ Spec.map i.appTop ≫ V.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  infer_instance

section Relation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {V O : BigFppfOver B S hS} {φ : yoneda.obj V ⟶ W} {j : yoneda.obj O ⟶ W}
  (ho : ClosedP j)

include ho in
/-- **§2 (1)**, any algebraic space: the relation of an affine chart of `W`, on which an affine closed
`O ⊂ W` has nilpotent ideal, is affine. It is a thickening of `V_0 ×_O V_0` (Stacks 06AD). -/
theorem isAffine_relation_of_nilpotent
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    [IsAffine ((SCH).obj V)] [IsAffine ((SCH).obj O)] {n : ℕ}
    (hn : RingHom.ker ((SCH).map (ho.rep.snd φ)).appTop.hom ^ n = ⊥) :
    IsAffine ((SCH).obj (Space.atlasRelation B S hS hs)) := by
  let G := SCH
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  let tgt := Space.atlasRelationTarget B S hS hs
  let src := Space.atlasRelationSource B S hS hs
  let i := ho.rep.snd φ
  have hi : IsClosedImmersion (G.map i) := ho.property_snd φ
  have hV0 : IsAffine (G.obj (ho.rep.pullback φ)) := isAffine_of_isAffineHom (G.map i)
  let tR := yoneda.map src ≫ φ
  let i' := ho.rep.snd tR
  have hi' : IsClosedImmersion (G.map i') := ho.property_snd tR
  obtain ⟨q, hq, hq'⟩ := isPullback_snd_comp ho src φ tR rfl
  obtain ⟨p, hp, hp'⟩ := isPullback_snd_comp ho tgt φ tR (rel_w hs).symm
  obtain ⟨f, hf⟩ := yoneda.map_surjective (ho.rep.fst φ)
  have sq0 : IsPullback (yoneda.map i) (yoneda.map f) φ j := by
    rw [hf]; exact (ho.rep.isPullback φ).flip
  have hR : IsPullback (yoneda.map tgt) (yoneda.map src) φ φ := by
    have := hs.rep.isPullback φ
    simpa [tgt, src] using this
  have big := ((hq.map yoneda).flip.paste_horiz hR)
  have hcomm : yoneda.map p ≫ yoneda.map i = yoneda.map i' ≫ yoneda.map tgt := by
    rw [← Functor.map_comp, ← Functor.map_comp, hp.w]
  have big' : IsPullback (yoneda.map p ≫ yoneda.map i) (yoneda.map q) φ (yoneda.map f ≫ j) := by
    rw [hcomm, ← sq0.w]; exact big
  have hpqf : yoneda.map p ≫ yoneda.map f = yoneda.map q ≫ yoneda.map f := by
    rw [hf, hp', hq']
  have sqY : IsPullback (yoneda.map p) (yoneda.map q) (yoneda.map f) (yoneda.map f) :=
    IsPullback.of_right big' hpqf sq0
  have sqS : IsPullback (G.map p) (G.map q) (G.map f) (G.map f) :=
    (IsPullback.of_map yoneda (yoneda.map_injective (by simpa [Functor.map_comp] using hpqf)) sqY).map G
  -- `R_0` is affine
  have hR0 : IsAffine (G.obj (ho.rep.pullback tR)) := by
    have h1 : IsAffineHom (G.map f) := isAffineHom_of_isAffine _
    have h2 : IsAffineHom (G.map p) := MorphismProperty.of_isPullback (P := @IsAffineHom) sqS.flip h1
    exact isAffine_of_isAffineHom (G.map p)
  -- `R_0 → R` is a thickening
  have hsi : Surjective (G.map i) := surjective_of_ker_pow (G.map i) hn
  have hsi' : Surjective (G.map i') :=
    MorphismProperty.of_isPullback (P := @Surjective) (hq.map G) hsi
  exact Stacks.Thickenings.isAffine_of_isThickening (i := G.map i') ⟨hi', hsi'.surj⟩

end Relation

section Thick

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {O : BigFppfOver B S hS} {j : yoneda.obj O ⟶ X} (ho : ClosedP j)
  {U V : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
  {ψ : yoneda.obj V ⟶ X}
  (heψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) ψ)
  (hcov : ∀ w : (BigFppfOver.toScheme B S hS).obj O,
    ∃ q : (BigFppfOver.toScheme B S hS).obj (ho.rep.pullback ψ),
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (ho.rep.fst ψ))) q = w)

include heψ hcov in
/-- **§2**: `X_n` is affine (Stacks 05ZR), `X` any algebraic space. -/
theorem exists_affine_thickening_qs [IsAffine S] [IsAffine ((SCH).obj O)] [IsAffine ((SCH).obj V)]
    (hX : IsAlgebraicSpace B S hS X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ) (n : ℕ) :
    ∃ (T : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj T)),
      Nonempty (yoneda.obj T ≅ (thickening ho φ n).toFunctor) := by
  let G := SCH
  have hA := (isClosedSubspace_thickening ho hX hs he n).1
  obtain ⟨k, sq⟩ := exists_isPullback_thickening ho hs he ψ n
  have hke := thick_etale ho heψ sq
  have hks := thick_surjective ho hs he hcov sq hke
  have hcl := thickChartι_closed ho ψ n
  have hVa : IsAffine (G.obj (thickChart ho ψ n)) :=
    isAffine_of_isAffineHom (G.map (thickChartι ho ψ n))
  let jn : yoneda.obj O ⟶ (thickening ho φ n).toFunctor :=
    Subfunctor.lift j (range_le_thickening ho hs he n)
  have hjn : jn ≫ (thickening ho φ n).ι = j := Subfunctor.lift_ι _ _
  have hon : ClosedP jn := closedP_of_comp_mono ho _ hjn
  have hP : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hs1 := hon.rep.isPullback k
  have hs2 : IsPullback (hon.rep.fst k) (yoneda.map (hon.rep.snd k)) j
      (yoneda.map (thickChartι ho ψ n) ≫ ψ) := by
    have e : yoneda.map (thickChartι ho ψ n) ≫ ψ = k ≫ (thickening ho φ n).ι := sq.w.symm
    have h := (isPullback_comp_mono_iff (thickening ho φ n).ι).2 hs1
    rw [hjn] at h
    rw [e]
    exact h
  have hc' : hon.rep.fst k ≫ j = yoneda.map (hon.rep.snd k ≫ thickChartι ho ψ n) ≫ ψ := by
    rw [hs2.w, Functor.map_comp, Category.assoc]
  let m : hon.rep.pullback k ⟶ ho.rep.pullback ψ :=
    ho.rep.lift (hon.rep.fst k) (hon.rep.snd k ≫ thickChartι ho ψ n) hc'
  have hm : m ≫ ho.rep.snd ψ = hon.rep.snd k ≫ thickChartι ho ψ n := ho.rep.lift_snd _ _ _
  have hm' : yoneda.map m ≫ ho.rep.fst ψ = hon.rep.fst k := ho.rep.lift_fst _ _ _
  have sq3 : IsPullback (yoneda.map m) (yoneda.map (hon.rep.snd k)) (yoneda.map (ho.rep.snd ψ))
      (yoneda.map (thickChartι ho ψ n)) := by
    refine IsPullback.of_right (h₁₂ := ho.rep.fst ψ) (v₁₃ := j) (h₂₂ := ψ) ?_ ?_
      (ho.rep.isPullback ψ)
    · rw [hm']; exact hs2
    · rw [← Functor.map_comp, ← Functor.map_comp, hm]
  have sq4 : IsPullback m (hon.rep.snd k) (ho.rep.snd ψ) (thickChartι ho ψ n) :=
    IsPullback.of_map yoneda (by rw [hm]) sq3
  have hc1 : IsClosedImmersion (G.map (ho.rep.snd ψ)) := snd_closed ho ψ
  have hc2 : IsClosedImmersion (G.map (hon.rep.snd k)) := snd_closed hon k
  have hkm := ker_map_of_isPullback ((sq4.map G).flip)
  have hnil : RingHom.ker (G.map (hon.rep.snd k)).appTop.hom ^ (n + 1) = ⊥ := by
    rw [hkm, ← Ideal.map_pow, ← ker_thickChartι_appTop ho ψ n]
    exact (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl
  haveI := isAffine_relation_of_nilpotent (ho := hon) hks hnil
  exact exists_affine_of_nilpotent_chart (ho := hon) hA hks hke hnil

end Thick

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable [AddMonoid.FG M] {actX : AAction (fppfO B S hS) M X} (D : OrbitInput actX)

/-- **§2**: the tower of affine thickenings of `O` in `X`, `X` any algebraic space. As
`ChartMain.exists_affineTower`. -/
theorem exists_affineTower_qs [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (hN : IsLocallyNoetherian ((SCH).obj U)) :
    ∃ (Y : AffineTower B S hS M) (c : ∀ n, yoneda.obj (Y.U n) ⟶ X),
      (∀ n, Mono (c n)) ∧ (∀ n, Subfunctor.range (c n) = thickening D.closed φ n) ∧
      (∀ n, IsEquivariant (Y.act n) actX (c n)) ∧
      (∀ n, yoneda.map (Y.j n) ≫ c (n + 1) = c n) := by
  let G := SCH
  have hP : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have := D.aff
  let ho := D.closed
  obtain ⟨V, hVa, r, hr, hcov⟩ := exists_affine_chart_over_orbit ho hs he
  let ψ : yoneda.obj V ⟶ X := yoneda.map r ≫ φ
  have heψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) ψ := by
    have h1 : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map r) :=
      Space.presheaf_yoneda_map_of_inverseImage B S hS inferInstance _ hr
    have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (SCH)).IsStableUnderComposition := ⟨fun f g hf hg => by
      change Etale _
      rw [Functor.map_comp]
      have : Etale ((SCH).map f) := hf
      have : Etale ((SCH).map g) := hg
      infer_instance⟩
    exact MorphismProperty.comp_mem _ _ _ h1 he
  -- the affine objects
  have hT := fun n => exists_affine_thickening_qs ho heψ hcov hX hs he n
  choose T hTa he' using hT
  let e := fun n => (he' n).some
  let c : ∀ n, yoneda.obj (T n) ⟶ X := fun n => (e n).hom ≫ (thickening ho φ n).ι
  have hcm : ∀ n, Mono (c n) := fun n => mono_comp _ _
  have hrange : ∀ n, Subfunctor.range (c n) = thickening ho φ n := fun n => by
    refine le_antisymm ?_ ?_
    · rintro A _ ⟨x, rfl⟩
      exact ((e n).hom.app A x).2
    · rintro A x hx
      exact ⟨(e n).inv.app A ⟨x, hx⟩, by
        change (thickening ho φ n).ι.app A ((e n).hom.app A ((e n).inv.app A ⟨x, hx⟩)) = x
        have e3 := congrFun (congrArg (fun z => (z.app A : _ → _)) (e n).inv_hom_id) ⟨x, hx⟩
        rw [show (e n).hom.app A ((e n).inv.app A ⟨x, hx⟩) = ⟨x, hx⟩ from e3]
        rfl⟩
  -- the transition maps
  have hfac : ∀ {m n}, m ≤ n → ∃ t : T m ⟶ T n, yoneda.map t ≫ c n = c m := fun {m n} h => by
    have hle := thickening_mono ho hs he h
    have hm : ∀ A (x : (yoneda.obj (T m)).obj A), (c m).app A x ∈ Set.range ((c n).app A) := by
      intro A x
      have h1 : (c m).app A x ∈ (thickening ho φ m).obj A := ((e m).hom.app A x).2
      have h2 := hle A h1
      rw [← hrange n] at h2
      exact h2
    let x0 := yonedaEquiv (c m)
    obtain ⟨t, ht⟩ := hm (op (T m)) (𝟙 _)
    refine ⟨t, ?_⟩
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact ht
  -- the charts
  have hch : ∀ n, ∃ π : thickChart ho ψ n ⟶ T n,
      IsPullback (yoneda.map (thickChartι ho ψ n)) (yoneda.map π) ψ (c n) ∧
        Surjective (G.map π) ∧ Etale (G.map π) := fun n => by
    obtain ⟨k, sq⟩ := exists_isPullback_thickening ho hs he ψ n
    have hke := thick_etale ho heψ sq
    have hks := thick_surjective ho hs he hcov sq hke
    obtain ⟨π, hπ⟩ := yoneda.map_surjective (k ≫ (e n).inv)
    have hπ' : yoneda.map π ≫ (e n).hom = k := by rw [hπ]; simp
    have sq1 : IsPullback (𝟙 _) (yoneda.map π) k (e n).hom :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hπ']⟩
    refine ⟨π, ?_, hks.property _ _ _ sq1, hke.property _ _ _ sq1⟩
    simpa only [Category.id_comp] using sq1.paste_horiz sq.flip
  choose π hπ hπs hπe using hch
  have hVn : ∀ n, IsAffine (G.obj (thickChart ho ψ n)) := fun n => by
    have := thickChartι_closed ho ψ n
    exact isAffine_of_isAffineHom (G.map (thickChartι ho ψ n))
  have hff : ∀ n, (G.map (π n)).appTop.hom.FaithfullyFlat := fun n => by
    have := hπs n
    have := hπe n
    exact faithfullyFlat_appTop (G.map (π n))
  let K := chartIdeal ho ψ
  let Kn : ∀ n, Ideal Γ(G.obj (thickChart ho ψ n), ⊤) := fun n =>
    K.map (G.map (thickChartι ho ψ n)).appTop.hom
  have hsurj : ∀ n, Function.Surjective (G.map (thickChartι ho ψ n)).appTop.hom := fun n => by
    have := thickChartι_closed ho ψ n
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (G.map (thickChartι ho ψ n))).2
  have hKn : ∀ n, Kn n ^ (n + 1) = ⊥ := fun n => by
    change K.map _ ^ (n + 1) = ⊥
    rw [← Ideal.map_pow, ← ker_thickChartι_appTop ho ψ n]
    exact (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl
  -- the key computation
  have key : ∀ {m n : ℕ} (t : T m ⟶ T n), yoneda.map t ≫ c n = c m →
      IsClosedImmersion (G.map t) ∧
        (RingHom.ker (G.map t).appTop.hom).map (G.map (π n)).appTop.hom = Kn n ^ (m + 1) := by
    intro m n t ht
    have hcomm : yoneda.map (thickChartι ho ψ m) ≫ ψ = (yoneda.map (π m) ≫ yoneda.map t) ≫ c n := by
      rw [Category.assoc, ht, (hπ m).w]
    let l0 := (hπ n).lift _ _ hcomm
    obtain ⟨r', hr'⟩ := yoneda.map_surjective l0
    have h1 : yoneda.map r' ≫ yoneda.map (thickChartι ho ψ n) = yoneda.map (thickChartι ho ψ m) := by
      rw [hr']; exact (hπ n).lift_fst _ _ _
    have h2 : yoneda.map r' ≫ yoneda.map (π n) = yoneda.map (π m) ≫ yoneda.map t := by
      rw [hr']; exact (hπ n).lift_snd _ _ _
    have h1' : r' ≫ thickChartι ho ψ n = thickChartι ho ψ m :=
      yoneda.map_injective (by rw [Functor.map_comp, h1])
    have sq : IsPullback (yoneda.map r') (yoneda.map (π m)) (yoneda.map (π n)) (yoneda.map t) := by
      refine IsPullback.of_right ?_ h2 (hπ n)
      rw [h1, ht]
      exact hπ m
    have sq' : IsPullback r' (π m) (π n) t :=
      IsPullback.of_map yoneda (yoneda.map_injective (by simpa only [Functor.map_comp] using h2)) sq
    have sqG := sq'.map G
    have hcm' := thickChartι_closed ho ψ m
    have hcn' := thickChartι_closed ho ψ n
    have hr'c : IsClosedImmersion (G.map r') := by
      have : IsClosedImmersion (G.map r' ≫ G.map (thickChartι ho ψ n)) := by
        rw [← Functor.map_comp, h1']; exact hcm'
      exact IsClosedImmersion.of_comp _ (G.map (thickChartι ho ψ n))
    have hl : MorphismProperty.IsLocalAtTarget
        (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage := by
      have := Stacks.Descent.isClosedImmersion_isLocalAtTarget_fpqc
      exact MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
    have hts : Surjective (G.map (π n)) := hπs n
    have hte : Etale (G.map (π n)) := hπe n
    have htc : IsClosedImmersion (G.map t) := by
      refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
        (Scheme.Hom.singleton_mem_fppfPrecoverage (G.map (π n))) ?_
      intro Y' g' _ hg'
      cases hg'
      rw [← sqG.flip.isoPullback_inv_snd]
      have hRI : MorphismProperty.RespectsIso (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 hr'c
    refine ⟨htc, ?_⟩
    rw [← ker_map_of_isPullback sqG]
    have hcomp : (G.map r').appTop.hom.comp (G.map (thickChartι ho ψ n)).appTop.hom =
        (G.map (thickChartι ho ψ m)).appTop.hom := by
      rw [← h1', Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
    rw [ker_eq_map_of_comp (hsurj n) hcomp, ker_thickChartι_appTop ho ψ m, Ideal.map_pow]
  have hfac' : ∀ m n, m ≤ n → ∃ t : T m ⟶ T n, yoneda.map t ≫ c n = c m := fun _ _ h => hfac h
  let tw : ∀ m n, m ≤ n → (T m ⟶ T n) := fun m n h => (hfac' m n h).choose
  have htw : ∀ m n (h : m ≤ n), yoneda.map (tw m n h) ≫ c n = c m :=
    fun m n h => (hfac' m n h).choose_spec
  have hinj : ∀ n A, Function.Injective ((c n).app A) := fun n A =>
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 (hcm n) A)
  have hst : ∀ n {A : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M A)
      (x : (yoneda.obj (T n)).obj A), ∃ y, (c n).app A y = actX.smul h ((c n).app A x) := by
    intro n A h x
    have h1 : (c n).app A x ∈ (thickening ho φ n).obj A := ((e n).hom.app A x).2
    have h2 := smul_mem_thickening ho hs he D.equivariant n h h1
    rw [← hrange n] at h2
    exact h2
  have hN' : IsNoetherianRing Γ(G.obj V, ⊤) := by
    have : IsLocallyNoetherian (G.obj U) := hN
    have : LocallyOfFiniteType (G.map r) := by
      have : Etale (G.map r) := hr
      infer_instance
    have := LocallyOfFiniteType.isLocallyNoetherian (G.map r)
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let act := fun n => actOfMono actX (c n) (fun {_} h x => hst n h x)
  have hact : ∀ n {A : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M A)
      (x : (yoneda.obj (T n)).obj A), (c n).app A ((act n).smul h x) = actX.smul h ((c n).app A x) :=
    fun n _ h x => actOfMono_spec actX (c n) _ h x
  have hjc : ∀ n A x, (c (n + 1)).app A ((yoneda.map (tw n (n + 1) (Nat.le_succ n))).app A x) =
      (c n).app A x := fun n A x => by
    have := congrArg (fun z => z.app A x) (htw n (n + 1) (Nat.le_succ n))
    exact this
  refine ⟨{
    U := T
    aff := hTa
    act := act
    j := fun n => tw n (n + 1) (Nat.le_succ n)
    closed := fun n => (key _ (htw n (n + 1) (Nat.le_succ n))).1
    equivariant := fun n {A} h x => hinj (n + 1) A (by
      rw [hjc, hact, hact, hjc])
    incl := fun n => tw 0 n (Nat.zero_le n)
    incl_zero := yoneda.map_injective ((cancel_mono (c 0)).1 (by
      rw [CategoryTheory.Functor.map_id, Category.id_comp]; exact htw 0 0 (Nat.zero_le 0)))
    incl_succ := fun n => yoneda.map_injective ((cancel_mono (c (n + 1))).1 (by
      rw [Functor.map_comp, Category.assoc, htw n (n + 1) (Nat.le_succ n), htw 0 n (Nat.zero_le n),
        htw 0 (n + 1) (Nat.zero_le _)]))
    nil := fun n => ideal_eq_of_map_eq (hff n) (by
      rw [Ideal.map_pow, (key _ (htw 0 n (Nat.zero_le n))).2, zero_add, pow_one, hKn, Ideal.map_bot])
    ker_j := fun n => ideal_eq_of_map_eq (hff (n + 1)) (by
      rw [Ideal.map_pow, (key _ (htw 0 (n + 1) (Nat.zero_le _))).2, (key _ (htw n (n + 1) (Nat.le_succ n))).2, zero_add, pow_one])
    I_fg := ideal_fg_of_map_fg (hff 1) (by
      rw [(key _ (htw 0 1 (Nat.zero_le _))).2, zero_add, pow_one]
      exact Ideal.FG.map (IsNoetherian.noetherian K) _) }, c, hcm, hrange, ?_, ?_⟩
  · exact fun n {A} h x => hact n h x
  · exact fun n => htw n (n + 1) (Nat.le_succ n)

end Tower

end AlgMag.ChartQSAsm

#print axioms AlgMag.ChartQSAsm.isAffine_relation_of_nilpotent
#print axioms AlgMag.ChartQSAsm.exists_affine_thickening_qs
#print axioms AlgMag.ChartQSAsm.exists_affineTower_qs
