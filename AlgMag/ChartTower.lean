/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartTowerChart
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# The tower of thickenings of the orbit

Input: `AlgMag.ChartMain.OrbitInput`, an affine closed `D(M)`-stable `O ⊂ X`.

* `AlgMag.ChartMain.exists_affineTower`: the `AffineTower` of `X_n`, `X` separated over an affine `S`,
  with an atlas of `X` locally noetherian.
* `AlgMag.ChartMain.exists_thickeningSystem`: the resulting `ThickeningSystem`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartMain

section Rings

/-- Faithfully flat maps are injective on ideals. -/
lemma ideal_eq_of_map_eq {A C : Type*} [CommRing A] [CommRing C] {c : A →+* C}
    (hc : c.FaithfullyFlat) {a b : Ideal A} (h : a.map c = b.map c) : a = b := by
  let _ := c.toAlgebra
  have : Module.FaithfullyFlat A C := RingHom.faithfullyFlat_algebraMap_iff.1 hc
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) a,
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) b]
  exact congrArg _ h

/-- Finite generation descends along a faithfully flat map. -/
lemma ideal_fg_of_map_fg {A C : Type*} [CommRing A] [CommRing C] {c : A →+* C}
    (hc : c.FaithfullyFlat) {a : Ideal A} (h : (a.map c).FG) : a.FG := by
  classical
  have h' : (Submodule.span C (c '' (a : Set A))).FG := h
  obtain ⟨s, hs, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 h'
  obtain ⟨t, ht, rfl⟩ := Finset.subset_set_image_iff.1 hs
  refine ⟨t, ideal_eq_of_map_eq hc ?_⟩
  refine le_antisymm (Ideal.map_le_of_le_comap ?_) ?_
  · rw [Ideal.span_le]
    intro x hx
    exact Ideal.mem_comap.2 (Ideal.mem_map_of_mem _ (ht hx))
  · change Submodule.span C (c '' (a : Set A)) ≤ _
    rw [hsp, Ideal.map_span]
    simp

/-- The kernel of `ρ`, for `ρ ∘ π = π'` and `π` surjective. -/
lemma ker_eq_map_of_comp {R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] {π : R →+* B}
    {π' : R →+* B'} {ρ : B →+* B'} (hπ : Function.Surjective π) (h : ρ.comp π = π') :
    RingHom.ker ρ = (RingHom.ker π').map π := by
  rw [← h, ← RingHom.comap_ker, Ideal.map_comap_of_surjective _ hπ]

end Rings

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- An action restricted along a monomorphism whose image is stable. -/
noncomputable def actOfMono {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)
    (c : F ⟶ X) [Mono c]
    (hst : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (x : F.obj T),
      ∃ y, c.app T y = actX.smul h (c.app T x)) : AAction (fppfO B S hS) M F :=
  have hinj : ∀ T, Function.Injective (c.app T) := fun T =>
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance T)
  have hc : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (x : F.obj T),
      c.app T (hst h x).choose = actX.smul h (c.app T x) := fun h x => (hst h x).choose_spec
  { smul := fun h x => (hst h x).choose
    one_smul := fun {T} x => hinj T (by rw [hc, actX.one_smul])
    mul_smul := fun {T} g h x => hinj T (by rw [hc, hc, hc, actX.mul_smul])
    map_smul := fun {U V} f h x => hinj V (by
      rw [hc, NatTrans.naturality_apply c f, hc, actX.map_smul, NatTrans.naturality_apply c f]) }

lemma actOfMono_spec {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)
    (c : F ⟶ X) [Mono c]
    (hst : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (x : F.obj T),
      ∃ y, c.app T y = actX.smul h (c.app T x))
    {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (x : F.obj T) :
    c.app T ((actOfMono actX c hst).smul h x) = actX.smul h (c.app T x) :=
  (hst h x).choose_spec

/-- **Input of §2** (output of §1): an affine closed `D(M)`-stable `O ⊂ X`. -/
structure OrbitInput (actX : AAction (fppfO B S hS) M X) where
  /-- the orbit -/
  O : BigFppfOver B S hS
  aff : IsAffine ((BigFppfOver.toScheme B S hS).obj O)
  /-- the action on `O` -/
  actO : AAction (fppfO B S hS) M (yoneda.obj O)
  /-- `O → X` -/
  j : yoneda.obj O ⟶ X
  closed : ClosedP j
  equivariant : IsEquivariant actO actX j

variable [AddMonoid.FG M] {actX : AAction (fppfO B S hS) M X} (D : OrbitInput actX)

/-- **§2**: the tower of affine thickenings of `O` in `X`, with its maps to `X`: each `X_n → X` is an
equivariant monomorphism with image the `n`-th thickening, for the atlas `φ`. -/
theorem exists_affineTower [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
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
  have hT := fun n => exists_affine_thickening ho heψ hcov hX hsep hs he n
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

include D in
/-- **§2**: the `ThickeningSystem` of `X` and `O`. -/
theorem exists_thickeningSystem [DecidableEq M] [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (hN : IsLocallyNoetherian ((SCH).obj U)) :
    Nonempty (ChartGraded.ThickeningSystem.{u, u} M) := by
  obtain ⟨Y, -⟩ := exists_affineTower D hX hsep hs he hN
  exact ⟨Y.toThickeningSystem⟩

/-- An étale chart of a space of finite type over a locally noetherian `S` is locally noetherian. -/
lemma isLocallyNoetherian_chart (hSft : LocallyOfFiniteType (terminal.from S))
    (hft : Space.IsFiniteType B S hS (terminal.from X)) {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ) :
    IsLocallyNoetherian ((SCH).obj U) := by
  let T1 : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let hT : IsTerminal T1 := Over.mkIdTerminal
  let hY : IsTerminal (yoneda.obj T1) := Limits.IsTerminal.isTerminalObj yoneda T1 hT
  let b : yoneda.obj T1 ≅ ⊤_ _ := hY.uniqueUpToIso terminalIsTerminal
  have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (SCH)).presheaf b.hom := Space.presheaf_etale_of_iso B S hS b
  have hl : LocallyOfFiniteType ((SCH).map (hT.from U)) :=
    hft.1 U T1 φ b.hom (hT.from U) he hb (Subsingleton.elim _ _ |>.trans rfl)
  have hter : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
    have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
    have : IsNoetherianRing (CommRingCat.of (ULift.{u} ℤ)) := ‹IsNoetherianRing (ULift.{u} ℤ)›
    have e := terminalIsoIsTerminal specULiftZIsTerminal
    exact isLocallyNoetherian_of_isOpenImmersion e.hom
  have hSn : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (terminal.from S)
  have hSn' : IsLocallyNoetherian ((SCH).obj T1) := hSn
  exact LocallyOfFiniteType.isLocallyNoetherian ((SCH).map (hT.from U))

include D in
/-- **§2**, under the hypotheses of the chart lemma: `S` affine of finite type over `ℤ`, `X` separated
of finite type over `S`, and `O` from §1. -/
theorem exists_thickeningSystem_of_finiteType [DecidableEq M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hft : Space.IsFiniteType B S hS (terminal.from X)) :
    Nonempty (ChartGraded.ThickeningSystem.{u, u} M) := by
  obtain ⟨U, φ, hs, he⟩ := hX.exists_atlas
  exact exists_thickeningSystem D hX hsep hs he (isLocallyNoetherian_chart hSft hft he)

end Tower

end AlgMag.ChartMain

#print axioms AlgMag.ChartMain.exists_affineTower
#print axioms AlgMag.ChartMain.exists_thickeningSystem
#print axioms AlgMag.ChartMain.exists_thickeningSystem_of_finiteType
