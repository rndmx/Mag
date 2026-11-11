/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.StronglyFPR
import AlgMag.AppendixA
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Existence of strongly-FPR atlases: Lemma 2.1 (1)

Mayeux, *Existence of strongly-FPR atlases*, Lemma 2.1 (1), by the printed proof: `K = K^t × F`, the torus part acts
trivially on `E = U ×_X X^Z` (here by `AlgMag.isFPR_of_etale`, Theorem A.1 for irreducible fibres), so `E^K = E^F`, and for
`F` the equalizer of the action and the projection is open and closed in `F × E`, the image of its complement under the
finite locally free projection is open and closed, and the complement of that image represents `E^F`.

`lem21_1` is the statement that `U^Z → U ×_X X^Z` is an open and closed immersion: for each `T`-point `t` of
`U ×_X X^Z`, the locus where `t` lies in `U^Z` is an open and closed subset of `T`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.StronglyFPRNote

open AlgMag.StronglyFPR

noncomputable section

/-- `L = C × F`, `C` torsion-free, `F` finite. -/
theorem exists_split (L : Type u) [AddCommGroup L] [AddGroup.FG L] :
    ∃ (C F : Type u) (_ : AddCommGroup C) (_ : AddCommGroup F) (_ : AddGroup.FG C)
      (_ : IsAddTorsionFree C) (_ : Finite F), Nonempty (L ≃+ C × F) := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod L
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let g : L ≃+ ULift.{u} (Fin n →₀ ℤ) × ULift.{u} (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    f.trans (AddEquiv.prodCongr AddEquiv.ulift.symm AddEquiv.ulift.symm)
  have hfg : AddGroup.FG (ULift.{u} (Fin n →₀ ℤ)) :=
    AddGroup.fg_of_surjective (f := (AddMonoidHom.fst _ _).comp g.toAddMonoidHom)
      (fun c => ⟨g.symm (c, 0), by simp⟩)
  have htf : IsAddTorsionFree (ULift.{u} (Fin n →₀ ℤ)) :=
    Function.Injective.isAddTorsionFree (AddEquiv.ulift (α := Fin n →₀ ℤ)).toAddMonoidHom
      (AddEquiv.ulift (α := Fin n →₀ ℤ)).injective
  have hfin : Finite (ULift.{u} (DirectSum ι fun i => ZMod (p i ^ e i))) := by
    classical
    haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
      Finite.of_equiv _ (DirectSum.addEquivProd (fun i => ZMod (p i ^ e i))).symm.toEquiv
    infer_instance
  exact ⟨_, _, inferInstance, inferInstance, hfg, htf, hfin, ⟨g⟩⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `F` finite: `D(F)_T → T` is open and closed. -/
lemma specPr_open_closed (F : Type u) [AddCommGroup F] [Finite F] (T : BigFppfOver B S hS)
    [IsAffine ((SCH).obj T)] :
    IsOpenMap ((SCH).map (specPr F T)) ∧ IsClosedMap ((SCH).map (specPr F T)) := by
  let A := Γ((SCH).obj T, ⊤)
  have hfin : Module.Finite A (AddMonoidAlgebra A F) := inferInstance
  have hfree : Module.Free A (AddMonoidAlgebra A F) := inferInstance
  have hint : (algebraMap A (AddMonoidAlgebra A F)).IsIntegral :=
    fun x => Algebra.IsIntegral.isIntegral (R := A) x
  have hfp : Algebra.FinitePresentation A (AddMonoidAlgebra A F) := by
    haveI : AddMonoid.FG F := AddMonoid.fg_of_finite
    exact AlgMag.finitePresentation A F
  have hop : IsOpenMap (PrimeSpectrum.comap (algebraMap A (AddMonoidAlgebra A F))) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  have hcl : IsClosedMap (PrimeSpectrum.comap (algebraMap A (AddMonoidAlgebra A F))) :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hint
  have e : ⇑((SCH).map (specPr F T)) =
      ((SCH).obj T).isoSpec.inv ∘ (PrimeSpectrum.comap (algebraMap A (AddMonoidAlgebra A F))) := rfl
  rw [e]
  exact ⟨((SCH).obj T).isoSpec.inv.homeomorph.isOpenMap.comp hop,
    ((SCH).obj T).isoSpec.inv.homeomorph.isClosedMap.comp hcl⟩

section Main

variable {L : Type u} [AddCommGroup L] [AddGroup.FG L] {U : BigFppfOver B S hS}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actU : AAction (fppfO B S hS) L (yoneda.obj U)}
  {actX : AAction (fppfO B S hS) L X} {f : yoneda.obj U ⟶ X}

omit [AddGroup.FG L] in
lemma fixed_iff {T : BigFppfOver B S hS} (x : T ⟶ U) :
    (show (yoneda.obj U).obj (op T) from x) ∈ (fixedPoints actU).obj (op T) ↔
      ∀ {T'' : BigFppfOver B S hS} (r : T'' ⟶ T) (h : APt (fppfO B S hS) L (op T'')),
        (actU.smul h (r ≫ x) : T'' ⟶ U) = r ≫ x :=
  ⟨fun hx {_} r h => hx r.op h, fun hx {T'} s h => hx s.unop h⟩

omit [AddGroup.FG L] in
lemma fixed_comp {T T' : BigFppfOver B S hS} {x : T ⟶ U} (r : T' ⟶ T)
    (hx : (show (yoneda.obj U).obj (op T) from x) ∈ (fixedPoints actU).obj (op T)) :
    (show (yoneda.obj U).obj (op T') from r ≫ x) ∈ (fixedPoints actU).obj (op T') :=
  (fixedPoints actU).map r.op hx

omit [AddGroup.FG L] in
lemma map_fixed {T T' : BigFppfOver B S hS} {x : T ⟶ U} (r : T' ⟶ T)
    (hx : f.app (op T) x ∈ (fixedPoints actX).obj (op T)) :
    f.app (op T') (r ≫ x) ∈ (fixedPoints actX).obj (op T') := by
  have e : f.app (op T') (r ≫ x) = X.map r.op (f.app (op T) x) :=
    (NatTrans.naturality_apply f r.op x)
  rw [e]
  intro T2 s2 h
  have := hx (r.op ≫ s2) h
  rwa [Functor.map_comp_apply] at this

variable (hf : IsEquivariant actU actX f)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)

include hf he in
omit [AddGroup.FG L] in
/-- Lemma 2.1 (1), proof: "The torus `K^t` acts trivially on `E`". -/
theorem torus_fixed {C : Type u} [AddCommGroup C] [AddGroup.FG C] [IsAddTorsionFree C] (pC : L →+ C)
    {T : BigFppfOver B S hS} (x : T ⟶ U) (hx : f.app (op T) x ∈ (fixedPoints actX).obj (op T)) :
    (show (yoneda.obj U).obj (op T) from x) ∈ (fixedPoints (actU.comap pC)).obj (op T) := by
  have : Countable C := countable_of_fg C
  intro T3 s3 h3
  exact (isFPR_iff (hf.comap pC)).mp (isFPR_of_etale (contains_zmon_of_countable hS C)
    (irreducibleFibres_of_torsionFree C S) (hf.comap pC) he) (op T) x
    (fun s h => hx s (h.comp (AddMonoidHom.toMultiplicative pC))) s3 h3

variable [IsSeparated (terminal.from ((BigFppfOver.toScheme B S hS).obj U))]

include hf he in
/-- Lemma 2.1 (1) for `T` affine. -/
theorem exists_clopen_affine {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] (t : T ⟶ U)
    (hfix : f.app (op T) t ∈ (fixedPoints actX).obj (op T)) :
    ∃ Ω : ((SCH).obj T).Opens, IsClosed (Ω : Set ((SCH).obj T)) ∧
      ∀ {T' : BigFppfOver B S hS} (s : T' ⟶ T),
        (show (yoneda.obj U).obj (op T') from s ≫ t) ∈ (fixedPoints actU).obj (op T') ↔
          Set.range ((SCH).map s) ⊆ Ω := by
  obtain ⟨C, F, _, _, _, _, _, ⟨e⟩⟩ := exists_split L
  let pC : L →+ C := (AddMonoidHom.fst C F).comp e.toAddMonoidHom
  let pF : L →+ F := (AddMonoidHom.snd C F).comp e.toAddMonoidHom
  let iC : C →+ L := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl C F)
  let iF : F →+ L := e.symm.toAddMonoidHom.comp (AddMonoidHom.inr C F)
  have hsplit : ∀ n : L, iC (pC n) + iF (pF n) = n := fun n => by
    apply e.injective
    simp [iC, iF, pC, pF]
  let G := specObj F T
  let b : G ⟶ U := specPr F T ≫ t
  let a : G ⟶ U := (actU.comap pF).smul (specPt F T) (show (yoneda.obj U).obj (op G) from b)
  have hab : f.app (op G) a = f.app (op G) b := by
    have h1 : f.app (op G) a = (actX.comap pF).smul (specPt F T) (f.app (op G) b) :=
      (hf.comap pF) _ _
    rw [h1]
    have h2 : actX.smul ((specPt F T).comp (AddMonoidHom.toMultiplicative pF))
        (X.map (𝟙 (op G)) (f.app (op G) b)) = X.map (𝟙 (op G)) (f.app (op G) b) :=
      map_fixed (X := X) (actX := actX) (f := f) (specPr F T) hfix (𝟙 _) _
    simp only [CategoryTheory.Functor.map_id] at h2
    exact h2
  obtain ⟨O, hO, hι⟩ := exists_eqOpen he a b hab
  have hclosed : IsClosed (O : Set ((SCH).obj G)) := by
    refine isClosed_of_eqOpen ((SCH).map a) ((SCH).map b) O hι ?_
    intro Z c hc hcc
    let Zo := AlgMag.Chart.immObj G c
    let zι : Zo ⟶ G := AlgMag.Chart.immι G c
    have hz : (SCH).map zι = c := rfl
    have := (hO zι).mp (toScheme_map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hz]; exact hcc))
    rwa [hz] at this
  obtain ⟨hop, hcl⟩ := specPr_open_closed (B := B) (hS := hS) F T
  let π := (SCH).map (specPr F T)
  have hπ1 : IsClosed (π '' (O : Set ((SCH).obj G))ᶜ) := hcl _ O.isOpen.isClosed_compl
  have hπ2 : IsOpen (π '' (O : Set ((SCH).obj G))ᶜ) := hop _ hclosed.isOpen_compl
  refine ⟨⟨(π '' (O : Set ((SCH).obj G))ᶜ)ᶜ, hπ1.isOpen_compl⟩, hπ2.isClosed_compl, fun {T'} s => ?_⟩
  have hk : ∀ {Y : BigFppfOver B S hS} (k : Y ⟶ G), k ≫ a =
      (actU.comap pF).smul (APt.res k.op (specPt F T)) (show (yoneda.obj U).obj (op Y) from k ≫ b) :=
    fun k => (actU.comap pF).map_smul k.op _ _
  constructor
  · rintro hfx _ ⟨τ', rfl⟩ ⟨w, hw, hπw⟩
    obtain ⟨Q, a', b', τ, hab', h1, h2⟩ := exists_pt_pullback (specPr F T) s w τ' hπw
    have hbb : a' ≫ b = b' ≫ s ≫ t := by
      change a' ≫ specPr F T ≫ t = _
      rw [← Category.assoc, hab', Category.assoc]
    have h3 := (fixed_iff (actU := actU) _).mp hfx b'
      ((APt.res a'.op (specPt F T)).comp (AddMonoidHom.toMultiplicative pF))
    have h4 : a' ≫ a = a' ≫ b := by
      rw [hk, hbb]
      exact h3
    have := (hO a').mp h4 ⟨τ, rfl⟩
    rw [h1] at this
    exact hw this
  · intro hr
    refine (fixed_iff (actU := actU) _).mpr fun {T''} r h => ?_
    let x : T'' ⟶ U := r ≫ s ≫ t
    have hfx : f.app (op T'') x ∈ (fixedPoints actX).obj (op T'') := by
      have e0 : x = (r ≫ s) ≫ t := by simp [x]
      rw [e0]
      intro T2 s2 h2
      exact map_fixed (r ≫ s) hfix s2 h2
    let hC : APt (fppfO B S hS) C (op T'') := h.comp (AddMonoidHom.toMultiplicative iC)
    let hF : APt (fppfO B S hS) F (op T'') := h.comp (AddMonoidHom.toMultiplicative iF)
    have hd : h = hC.comp (AddMonoidHom.toMultiplicative pC) * hF.comp (AddMonoidHom.toMultiplicative pF) := by
      refine MonoidHom.ext fun n => ?_
      change h n = h (Multiplicative.ofAdd (iC (pC (Multiplicative.toAdd n)))) *
        h (Multiplicative.ofAdd (iF (pF (Multiplicative.toAdd n))))
      rw [← map_mul, ← ofAdd_add, hsplit]
      rfl
    let ℓ : T'' ⟶ G := specLift (r ≫ s) hF
    have hℓO : Set.range ((SCH).map ℓ) ⊆ O := by
      rintro _ ⟨y, rfl⟩
      by_contra hy
      refine hr ⟨(SCH).map r y, rfl⟩ ⟨_, hy, ?_⟩
      change ((SCH).map ℓ ≫ (SCH).map (specPr F T)) y = _
      rw [← Functor.map_comp, specLift_pr, Functor.map_comp]
      rfl
    have hℓ := (hO ℓ).mpr hℓO
    have hℓb : ℓ ≫ b = x := by
      change ℓ ≫ specPr F T ≫ t = _
      rw [← Category.assoc, specLift_pr, Category.assoc]
    have hFx : (actU.smul (hF.comp (AddMonoidHom.toMultiplicative pF)) x : T'' ⟶ U) = x := by
      have h5 := hk ℓ
      rw [hℓ, hℓb, res_specLift] at h5
      exact h5.symm
    have hCx := (fixed_iff (actU := actU.comap pC) x).mp (torus_fixed hf he pC x hfx) (𝟙 _) hC
    rw [Category.id_comp] at hCx
    change (actU.smul h x : T'' ⟶ U) = x
    rw [hd, actU.mul_smul, hFx]
    exact hCx

include hf he in
/-- **Lemma 2.1 (1)**, for an action of `L`; `L = M/Z` in `lem21_1`. -/
theorem lem21_1_L {T : BigFppfOver B S hS} (t : T ⟶ U)
    (hfix : f.app (op T) t ∈ (fixedPoints actX).obj (op T)) :
    ∃ Ω : ((SCH).obj T).Opens, IsClosed (Ω : Set ((SCH).obj T)) ∧
      ∀ {T' : BigFppfOver B S hS} (s : T' ⟶ T),
        (show (yoneda.obj U).obj (op T') from s ≫ t) ∈ (fixedPoints actU).obj (op T') ↔
          Set.range ((SCH).map s) ⊆ Ω := by
  let Fx : ∀ {Y : BigFppfOver B S hS}, (Y ⟶ U) → Prop := fun {Y} x =>
    (show (yoneda.obj U).obj (op Y) from x) ∈ (fixedPoints actU).obj (op Y)
  have hopen : ∀ A : ((SCH).obj T).Opens, IsOpenImmersion ((SCH).map (openJ A)) := fun A =>
    inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι A))
  -- the local pieces
  have hloc : ∀ A : ((SCH).obj T).affineOpens, ∃ Ω : ((SCH).obj (openObj A.1)).Opens,
      IsClosed (Ω : Set ((SCH).obj (openObj A.1))) ∧ ∀ {T' : BigFppfOver B S hS} (s : T' ⟶ openObj A.1),
        Fx (s ≫ openJ A.1 ≫ t) ↔ Set.range ((SCH).map s) ⊆ Ω := fun A => by
    haveI : IsAffine ((SCH).obj (openObj A.1)) := A.2
    exact exists_clopen_affine hf he (openJ A.1 ≫ t) (map_fixed _ hfix)
  choose Ωl hΩc hΩu using hloc
  let Ωg : ((SCH).obj T).Opens := ⨆ A : {A : ((SCH).obj T).Opens // Fx (openJ A ≫ t)}, A.1
  have memg : ∀ τ, τ ∈ Ωg ↔ ∃ G : ((SCH).obj T).Opens, Fx (openJ G ≫ t) ∧ τ ∈ G := fun τ => by
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨fun ⟨G, h⟩ => ⟨G.1, G.2, h⟩, fun ⟨G, h1, h2⟩ => ⟨⟨G, h1⟩, h2⟩⟩
  have rangeJ : ∀ A : ((SCH).obj T).Opens, Set.range ((SCH).map (openJ A)) = A := fun A =>
    StronglyFPR.range_openJ
  have injJ : ∀ A : ((SCH).obj T).Opens, Function.Injective ((SCH).map (openJ A)) := fun A =>
    (Scheme.Opens.ι A).isOpenEmbedding.injective
  -- `Ωg` restricted to an affine open is `Ωl`
  have key : ∀ (A : ((SCH).obj T).affineOpens) (a : (SCH).obj (openObj A.1)),
      (SCH).map (openJ A.1) a ∈ Ωg ↔ a ∈ Ωl A := by
    intro A a
    haveI := hopen A.1
    constructor
    · intro h
      obtain ⟨G, hG, hτ⟩ := (memg _).1 h
      let D : ((SCH).obj T).Opens := G ⊓ A.1
      haveI := hopen D
      haveI := hopen G
      obtain ⟨c, hc⟩ := exists_factor_open (openJ A.1) (openJ D) (by
        rw [rangeJ, rangeJ]; exact fun x hx => hx.2)
      obtain ⟨c2, hc2⟩ := exists_factor_open (openJ G) (openJ D) (by
        rw [rangeJ, rangeJ]; exact fun x hx => hx.1)
      have hfD : Fx (c ≫ openJ A.1 ≫ t) := by
        have e1 : c ≫ openJ A.1 ≫ t = c2 ≫ openJ G ≫ t := by
          rw [← Category.assoc, hc, ← Category.assoc, hc2]
        change (show (yoneda.obj U).obj (op _) from c ≫ openJ A.1 ≫ t) ∈ _
        rw [show (show (yoneda.obj U).obj (op _) from c ≫ openJ A.1 ≫ t) = c2 ≫ openJ G ≫ t from e1]
        exact fixed_comp c2 hG
      have hr := (hΩu A c).1 hfD
      have hτD : (SCH).map (openJ A.1) a ∈ D := ⟨hτ, by
        have : (SCH).map (openJ A.1) a ∈ Set.range ((SCH).map (openJ A.1)) := ⟨a, rfl⟩
        rwa [rangeJ] at this⟩
      obtain ⟨d, hd⟩ : (SCH).map (openJ A.1) a ∈ Set.range ((SCH).map (openJ D)) := by
        rw [rangeJ]; exact hτD
      have e2 : (SCH).map c d = a := injJ A.1 (by
        rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hc, hd])
      exact e2 ▸ hr ⟨d, rfl⟩
    · intro ha
      let E : ((SCH).obj T).Opens := ((SCH).map (openJ A.1)).opensFunctor.obj (Ωl A)
      haveI := hopen E
      refine (memg _).2 ⟨E, ?_, ⟨a, ha, rfl⟩⟩
      have hEr : Set.range ((SCH).map (openJ E)) ⊆ Set.range ((SCH).map (openJ A.1)) := by
        rw [rangeJ E]
        rintro _ ⟨y, -, rfl⟩
        exact ⟨y, rfl⟩
      obtain ⟨c, hc⟩ := exists_factor_open (openJ A.1) (openJ E) hEr
      have hr : Set.range ((SCH).map c) ⊆ Ωl A := by
        rintro _ ⟨y, rfl⟩
        have hy : (SCH).map (openJ E) y ∈ (E : Set _) := by
          rw [← rangeJ E]; exact ⟨y, rfl⟩
        obtain ⟨z, hz, hzy⟩ := hy
        have e3 : z = (SCH).map c y := injJ A.1 (by
          exact hzy.trans (by rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hc]))
        exact e3 ▸ hz
      have h8 : Fx (c ≫ openJ A.1 ≫ t) := (hΩu A c).2 hr
      rw [← Category.assoc, hc] at h8
      intro T3 s3 h3
      exact h8 s3 h3
  have exA : ∀ τ : (SCH).obj T, ∃ (A : ((SCH).obj T).affineOpens) (a : (SCH).obj (openObj A.1)),
      (SCH).map (openJ A.1) a = τ := fun τ => by
    obtain ⟨A, hA, hτ, -⟩ := exists_isAffineOpen_mem_and_subset (x := τ) (U := ⊤) trivial
    have : τ ∈ Set.range ((SCH).map (openJ A)) := by rw [rangeJ]; exact hτ
    obtain ⟨a, ha⟩ := this
    exact ⟨⟨A, hA⟩, a, ha⟩
  refine ⟨Ωg, ?_, fun {T'} s => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro τ hτ
    obtain ⟨A, a, rfl⟩ := exA τ
    have ha : a ∉ Ωl A := fun h => hτ ((key A a).2 h)
    have hom : IsOpenMap ((SCH).map (openJ A.1)) := (Scheme.Opens.ι A.1).isOpenEmbedding.isOpenMap
    refine ⟨(SCH).map (openJ A.1) '' (Ωl A : Set _)ᶜ, ?_, hom _ (hΩc A).isOpen_compl, ⟨a, ha, rfl⟩⟩
    rintro _ ⟨y, hy, rfl⟩ hg
    exact hy ((key A y).1 hg)
  · rintro _ ⟨τ', rfl⟩
    obtain ⟨A, a, ha⟩ := exA ((SCH).map s τ')
    haveI := hopen A.1
    let P : ((SCH).obj T').Opens := (SCH).map s ⁻¹ᵁ A.1
    have hPa : Set.range ((SCH).map (openJ P ≫ s)) ⊆ Set.range ((SCH).map (openJ A.1)) := by
      rw [rangeJ]
      rintro _ ⟨y, rfl⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact y.2
    obtain ⟨c, hc⟩ := exists_factor_open (openJ A.1) (openJ P ≫ s) hPa
    have hfP : Fx (c ≫ openJ A.1 ≫ t) := by
      rw [← Category.assoc, hc, Category.assoc]
      exact fixed_comp (openJ P) h
    have hr := (hΩu A c).1 hfP
    have hτP : (SCH).map s τ' ∈ A.1 := by
      rw [← ha]
      have : (SCH).map (openJ A.1) a ∈ Set.range ((SCH).map (openJ A.1)) := ⟨a, rfl⟩
      rwa [rangeJ] at this
    let y : (SCH).obj (openObj P) := ⟨τ', hτP⟩
    have hy : (SCH).map (openJ A.1) ((SCH).map c y) = (SCH).map s τ' := by
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hc]
      rfl
    rw [← hy]
    exact (key A _).2 (hr ⟨y, rfl⟩)
  · refine (fixed_iff (actU := actU) _).mpr fun {T''} r k => ?_
    refine toScheme_map_injective (Scheme.hom_ext_of_forall _ _ fun y => ?_)
    obtain ⟨G, hG, hτ⟩ := (memg _).1 (h ⟨(SCH).map r y, rfl⟩)
    let V : ((SCH).obj T'').Opens := (SCH).map (r ≫ s) ⁻¹ᵁ G
    haveI := hopen G
    haveI : IsOpenImmersion ((SCH).map (openJ V)) := inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι V))
    have hy : y ∈ V := by
      change (SCH).map (r ≫ s) y ∈ G
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact hτ
    obtain ⟨g, hg⟩ := exists_factor_open (openJ G) (openJ V ≫ r ≫ s) (by
      rw [rangeJ]
      rintro _ ⟨z, rfl⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact z.2)
    refine ⟨V, hy, ?_⟩
    have e1 : openJ V ≫ r ≫ s ≫ t = g ≫ openJ G ≫ t := by
      rw [← Category.assoc g, hg]
      simp
    have h1 := (fixed_iff (actU := actU) _).mp hG g (APt.res (openJ V).op k)
    have h2 : openJ V ≫ (actU.smul k (r ≫ s ≫ t) : T'' ⟶ U) =
        actU.smul (APt.res (openJ V).op k) (show (yoneda.obj U).obj (op _) from openJ V ≫ r ≫ s ≫ t) :=
      actU.map_smul (openJ V).op k _
    have h3 : openJ V ≫ (actU.smul k (r ≫ s ≫ t) : T'' ⟶ U) = openJ V ≫ r ≫ s ≫ t := by
      rw [h2, e1]
      exact h1
    have h4 := congrArg (fun z => (SCH).map z) h3
    simp only [Functor.map_comp] at h4
    exact h4

end Main

/-- **Lemma 2.1 (1)**: `f : U → X` equivariant étale, `U` a separated scheme, `M` finitely generated:
`U^Z → U ×_X X^Z` is an open and closed immersion. A `T`-point of `U ×_X X^Z` is a `t : T ⟶ U` with `f(t) ∈ X^Z(T)`. -/
theorem lem21_1 {M : Type u} [AddCommGroup M] [AddGroup.FG M] {U : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
    {actX : AAction (fppfO B S hS) M X} {f : yoneda.obj U ⟶ X} (hf : IsEquivariant actU actX f)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    [IsSeparated (terminal.from ((SCH).obj U))] (Z : AddSubgroup M)
    {T : BigFppfOver B S hS} (t : T ⟶ U)
    (hfix : f.app (op T) t ∈ (fixedPoints (quotientAction actX Z)).obj (op T)) :
    ∃ Ω : ((SCH).obj T).Opens, IsClosed (Ω : Set ((SCH).obj T)) ∧
      ∀ {T' : BigFppfOver B S hS} (s : T' ⟶ T),
        (show (yoneda.obj U).obj (op T') from s ≫ t) ∈ (fixedPoints (quotientAction actU Z)).obj (op T') ↔
          Set.range ((SCH).map s) ⊆ Ω :=
  have : AddGroup.FG (M ⧸ Z) := QuotientAddGroup.fg Z
  lem21_1_L (hf.comap (QuotientAddGroup.mk' Z)) he t (fun s h => hfix s h)

end

end AlgMag.StronglyFPRNote

#print axioms AlgMag.StronglyFPRNote.lem21_1
