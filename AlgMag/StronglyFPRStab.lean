/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStatement
import AlgMag.ChartEffective
import AlgMag.Sec12Topology
import AlgMag.Sec8Representability
import AlgMag.StronglyFPRRing

/-!
# Stabilizers on an affine chart: the good locus of Lemma 2.3

Mayeux, *Existence of strongly-FPR atlases*, §§2.1, 2.3.

Let `f : U → X` be equivariant étale, `U` affine, `X` separated. `E ⊆ D(M)_U` is the closed subscheme
of the `(g, u)` with `g • f(u) = f(u)`, and `O ⊆ E` is the open and closed part where `g • u = u`
(`AlgMag.StronglyFPR.StabData`). `AlgMag.StronglyFPR.StabData.bad` is the image in `U` of `E ∖ O`, so
that its complement is the set `Ω` of Lemma 2.3.

* `AlgMag.StronglyFPR.StabData.smul_eq`: on `Ω`, `g • f(t) = f(t)` implies `g • t = t`, for all
  `T`-points. This is Lemma 2.1 (2), (3) in the direction used.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.StronglyFPR

/-- Two maps to a formally unramified morphism agree on an open. -/
theorem exists_eqOpen_of_unramified {T W Y : Scheme.{u}} (g : W ⟶ Y) [FormallyUnramified g]
    [LocallyOfFiniteType g] (p q : T ⟶ W) (hpq : p ≫ g = q ≫ g) :
    ∃ O : T.Opens, ∀ {T' : Scheme.{u}} (k : T' ⟶ T), k ≫ p = k ≫ q ↔ Set.range k ⊆ O := by
  let l : T ⟶ pullback g g := pullback.lift p q hpq
  let Δ := pullback.diagonal g
  refine ⟨l ⁻¹ᵁ Δ.opensRange, fun {T'} k => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rintro _ ⟨y, rfl⟩
    have e : k ≫ l = (k ≫ p) ≫ Δ := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, show l ≫ pullback.fst g g = p from pullback.lift_fst _ _ _,
          show Δ ≫ pullback.fst g g = 𝟙 _ from pullback.diagonal_fst g, Category.comp_id]
      · rw [Category.assoc, Category.assoc, show l ≫ pullback.snd g g = q from pullback.lift_snd _ _ _,
          show Δ ≫ pullback.snd g g = 𝟙 _ from pullback.diagonal_snd g, Category.comp_id, h]
    change l (k y) ∈ Set.range Δ
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · have hr : Set.range (k ≫ l) ⊆ Set.range Δ := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact h ⟨y, rfl⟩
    have fac := IsOpenImmersion.lift_fac Δ (k ≫ l) hr
    have h1 := congrArg (· ≫ pullback.fst g g) fac
    have h2 := congrArg (· ≫ pullback.snd g g) fac
    simp only [Category.assoc, l, Δ, pullback.lift_fst, pullback.lift_snd,
      pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h1 h2
    exact h1.symm.trans h2

/-- For maps to a separated scheme, a locus of agreement which is open is closed. -/
theorem isClosed_of_eqOpen {T W : Scheme.{u}} [IsSeparated (terminal.from W)] (p q : T ⟶ W)
    (O : T.Opens) (h1 : O.ι ≫ p = O.ι ≫ q)
    (h2 : ∀ {Z : Scheme.{u}} (c : Z ⟶ T) [IsClosedImmersion c], c ≫ p = c ≫ q → Set.range c ⊆ O) :
    IsClosed (O : Set T) := by
  let g := terminal.from W
  let l : T ⟶ pullback g g := pullback.lift p q (terminal.hom_ext _ _)
  let Δ := pullback.diagonal g
  let c := pullback.fst l Δ
  have hc : IsClosedImmersion c := by
    have : IsClosedImmersion Δ := inferInstance
    exact inferInstanceAs (IsClosedImmersion (pullback.fst l Δ))
  have hrange : (O : Set T) = Set.range c := by
    apply Set.Subset.antisymm
    · intro x hx
      let m : (O : Scheme.{u}) ⟶ pullback l Δ := pullback.lift O.ι (O.ι ≫ p) (by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, show l ≫ pullback.fst g g = p from pullback.lift_fst _ _ _,
            show Δ ≫ pullback.fst g g = 𝟙 _ from pullback.diagonal_fst g, Category.comp_id]
        · rw [Category.assoc, Category.assoc, show l ≫ pullback.snd g g = q from pullback.lift_snd _ _ _,
            show Δ ≫ pullback.snd g g = 𝟙 _ from pullback.diagonal_snd g, Category.comp_id, h1])
      refine ⟨m ⟨x, hx⟩, ?_⟩
      change (m ≫ c) _ = _
      rw [pullback.lift_fst]
      rfl
    · refine h2 c ?_
      have e := pullback.condition (f := l) (g := Δ)
      have e1 := congrArg (· ≫ pullback.fst g g) e
      have e2 := congrArg (· ≫ pullback.snd g g) e
      simp only [Category.assoc] at e1 e2
      rw [show l ≫ pullback.fst g g = p from pullback.lift_fst _ _ _,
        show Δ ≫ pullback.fst g g = 𝟙 _ from pullback.diagonal_fst g, Category.comp_id] at e1
      rw [show l ≫ pullback.snd g g = q from pullback.lift_snd _ _ _,
        show Δ ≫ pullback.snd g g = 𝟙 _ from pullback.diagonal_snd g, Category.comp_id] at e2
      exact e1.trans e2.symm
  rw [hrange]
  exact c.isClosedEmbedding.isClosed_range

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {actX : AAction (fppfO B S hS) M X} {f : yoneda.obj U ⟶ X}

/-- Étale `f`: two points of `U` with the same image in `X` agree on an open. -/
theorem exists_eqOpen (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    {T : BigFppfOver B S hS} (t t' : T ⟶ U) (hw : f.app (op T) t = f.app (op T) t') :
    ∃ O : ((SCH).obj T).Opens,
      (∀ {T' : BigFppfOver B S hS} (k : T' ⟶ T), k ≫ t = k ≫ t' ↔ Set.range ((SCH).map k) ⊆ O) ∧
      O.ι ≫ (SCH).map t = O.ι ≫ (SCH).map t' := by
  let W := he.rep.pullback f
  let sn := he.rep.snd f
  let fs := he.rep.fst' f
  have hsq : ∀ (s : T ⟶ U), f.app (op T) s = f.app (op T) t' →
      yoneda.map s ≫ f = yoneda.map t' ≫ f := by
    intro s hs
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
    exact hs
  let l : T ⟶ W := he.rep.lift' t t' (hsq t hw)
  let l' : T ⟶ W := he.rep.lift' t' t' (hsq t' rfl)
  have hsn : Etale ((SCH).map sn) := he.property_snd f
  have hl1 : l ≫ fs = t := he.rep.lift'_fst _ _ _
  have hl2 : l' ≫ fs = t' := he.rep.lift'_fst _ _ _
  have hl3 : l ≫ sn = t' := he.rep.lift'_snd _ _ _
  have hl4 : l' ≫ sn = t' := he.rep.lift'_snd _ _ _
  obtain ⟨O, hO⟩ := exists_eqOpen_of_unramified ((SCH).map sn) ((SCH).map l) ((SCH).map l') (by
    rw [← Functor.map_comp, ← Functor.map_comp, hl3, hl4])
  have hmap : ∀ {Z : Scheme.{u}} (k : Z ⟶ (SCH).obj T), k ≫ (SCH).map l = k ≫ (SCH).map l' →
      k ≫ (SCH).map t = k ≫ (SCH).map t' := by
    intro Z k h
    have := congrArg (· ≫ (SCH).map fs) h
    simp only [Category.assoc, ← Functor.map_comp, hl1, hl2] at this
    exact this
  refine ⟨O, fun {T'} k => ⟨fun h => ?_, fun h => ?_⟩, hmap _ ((hO O.ι).mpr (by simp))⟩
  · refine (hO ((SCH).map k)).mp ?_
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    refine he.rep.hom_ext' ?_ ?_
    · rw [Category.assoc, Category.assoc, hl1, hl2, h]
    · rw [Category.assoc, Category.assoc, hl3, hl4]
  · have := hmap _ ((hO ((SCH).map k)).mpr h)
    rw [← Functor.map_comp, ← Functor.map_comp] at this
    exact toScheme_map_injective this

/-- A point of a fibre product in the site. -/
lemma exists_pt_pullback {A₁ A₂ A₃ : BigFppfOver B S hS} (g : A₁ ⟶ A₃) (g' : A₂ ⟶ A₃)
    (w : (SCH).obj A₁) (w' : (SCH).obj A₂) (h : (SCH).map g w = (SCH).map g' w') :
    ∃ (Q : BigFppfOver B S hS) (a : Q ⟶ A₁) (b : Q ⟶ A₂) (τ : (SCH).obj Q),
      a ≫ g = b ≫ g' ∧ (SCH).map a τ = w ∧ (SCH).map b τ = w' := by
  have : PreservesLimitsOfShape WalkingCospan (SCH) := inferInstance
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback w w' h
  let c := inv (pullbackComparison (SCH) g g')
  refine ⟨pullback g g', pullback.fst g g', pullback.snd g g', c z, pullback.condition, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply]
    have e : c ≫ (SCH).map (pullback.fst g g') = pullback.fst _ _ := by
      rw [IsIso.inv_comp_eq, pullbackComparison_comp_fst]
    rw [e, hz1]
  · rw [← Scheme.Hom.comp_apply]
    have e : c ≫ (SCH).map (pullback.snd g g') = pullback.snd _ _ := by
      rw [IsIso.inv_comp_eq, pullbackComparison_comp_snd]
    rw [e, hz2]

omit [Countable M] in
/-- Acting by a point of `D(M)` is injective on points. -/
lemma smul_injective {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) M F)
    {T : (BigFppfOver B S hS)ᵒᵖ} (g : APt (fppfO B S hS) M T) {x y : F.obj T}
    (h : act.smul g x = act.smul g y) : x = y := by
  let g' : APt (fppfO B S hS) M T := g.comp invMonoidHom
  have hg : g' * g = 1 := by
    refine MonoidHom.ext fun n => ?_
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, ← map_mul, invMonoidHom_apply, inv_mul_cancel,
      map_one, MonoidHom.one_apply]
  have := congrArg (act.smul g') h
  rwa [← act.mul_smul, ← act.mul_smul, hg, act.one_smul, act.one_smul] at this

section Chart

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The action morphism `D(M)_U → U`. -/
noncomputable def actMap (actU : AAction (fppfO B S hS) M (yoneda.obj U)) : specObj M U ⟶ U :=
  actU.smul (U := op (specObj M U)) (specPt M U) (specPr M U)

lemma specLift_actMap {T : BigFppfOver B S hS} (t : T ⟶ U) (k : APt (fppfO B S hS) M (op T)) :
    specLift t k ≫ actMap actU = actU.smul k t := by
  have h := actU.map_smul (specLift t k).op (specPt M U) (specPr M U)
  rw [res_specLift] at h
  have h2 : (yoneda.obj U).map (specLift t k).op (specPr M U) = t := specLift_pr t k
  rw [h2] at h
  exact h

/-- The stabilizers on `U`: `E ⊆ D(M)_U` is the closed subscheme of the `(g, u)` such that
`g • f(u) = f(u)`, and `O ⊆ E` the open and closed part of those with `g • u = u`. -/
structure StabData (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (actX : AAction (fppfO B S hS) M X) (f : yoneda.obj U ⟶ X) where
  /-- The stabilizer of the image in `X`. -/
  E : BigFppfOver B S hS
  /-- The inclusion. -/
  i : E ⟶ specObj M U
  closed : IsClosedImmersion ((SCH).map i)
  univ : ∀ {T : BigFppfOver B S hS} (t : T ⟶ U) (k : APt (fppfO B S hS) M (op T)),
    actX.smul k (f.app (op T) t) = f.app (op T) t ↔ ∃ w : T ⟶ E, w ≫ i = specLift t k
  /-- The stabilizer of `U`. -/
  O : ((SCH).obj E).Opens
  hO : ∀ {T' : BigFppfOver B S hS} (k : T' ⟶ E),
    k ≫ i ≫ actMap actU = k ≫ i ≫ specPr M U ↔ Set.range ((SCH).map k) ⊆ O
  closedO : IsClosed (O : Set ((SCH).obj E))

theorem nonempty_stabData (hf : IsEquivariant actU actX f)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    (hsep : Space.IsSeparatedOver B S hS X) : Nonempty (StabData actU actX f) := by
  obtain ⟨E, i, hi, hE⟩ := AlgMag.Chart.exists_eqLocus hsep (specObj M U)
    (f.app _ (actMap actU)) (f.app _ (specPr M U))
  have hnat : ∀ {T T' : BigFppfOver B S hS} (s : T' ⟶ T) (x : T ⟶ U),
      X.map s.op (f.app (op T) x) = f.app (op T') (s ≫ x) := fun s x =>
    (NatTrans.naturality_apply f s.op x).symm
  have hw : (f.app (op E) (i ≫ actMap actU)) = f.app (op E) (i ≫ specPr M U) := by
    rw [← hnat, ← hnat]
    exact (hE E i).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨O, hO, hι⟩ := exists_eqOpen he _ _ hw
  have hclosed : IsClosed (O : Set ((SCH).obj E)) := by
    refine isClosed_of_eqOpen ((SCH).map (i ≫ actMap actU)) ((SCH).map (i ≫ specPr M U)) O hι ?_
    intro Z c hc hcc
    let Zo := AlgMag.Chart.immObj E c
    let zι : Zo ⟶ E := AlgMag.Chart.immι E c
    have hz : (SCH).map zι = c := rfl
    have := (hO zι).mp (toScheme_map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hz]; exact hcc))
    rwa [hz] at this
  refine ⟨⟨E, i, hi, fun {T} t k => ⟨fun h => ?_, ?_⟩, O, fun {T'} k => ?_, hclosed⟩⟩
  · have := (hE T (specLift t k)).mp ?_
    · exact this
    · rw [hnat, hnat, specLift_actMap, specLift_pr, hf]
      exact h
  · rintro ⟨w, hw⟩
    have h1 := (hE T (specLift t k)).mpr ⟨w, hw⟩
    rw [hnat, hnat, specLift_actMap, specLift_pr, hf] at h1
    exact h1
  · rw [← hO k]

variable (D : StabData actU actX f)

/-- The complement of `Ω` in Lemma 2.3: the image in `U` of `E ∖ O`. -/
def StabData.bad : Set ((SCH).obj U) :=
  (SCH).map (D.i ≫ specPr M U) '' (D.O : Set ((SCH).obj D.E))ᶜ

/-- On `Ω`, a point of `D(M)` fixing `f(t)` fixes `t`. -/
theorem StabData.smul_eq {T : BigFppfOver B S hS} (t : T ⟶ U) (k : APt (fppfO B S hS) M (op T))
    (hfix : actX.smul k (f.app (op T) t) = f.app (op T) t)
    (hgood : ∀ τ, (SCH).map t τ ∉ D.bad) : actU.smul k t = t := by
  obtain ⟨w, hw⟩ := (D.univ t k).mp hfix
  have hr : Set.range ((SCH).map w) ⊆ D.O := by
    rintro _ ⟨τ, rfl⟩
    by_contra hτ
    apply hgood τ
    refine ⟨_, hτ, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Category.assoc, hw, specLift_pr]
  have := (D.hO w).mpr hr
  rw [← Category.assoc, ← Category.assoc, hw, specLift_actMap, specLift_pr] at this
  exact this

/-- A stabilizer-preserving point is not bad. -/
theorem StabData.notMem_bad {P : BigFppfOver B S hS} (u : P ⟶ U)
    (hst : ∀ {T : BigFppfOver B S hS} (s : T ⟶ P) (k : APt (fppfO B S hS) M (op T)),
      actX.smul k (f.app (op T) (s ≫ u)) = f.app (op T) (s ≫ u) → actU.smul k (s ≫ u) = s ≫ u)
    (x : (SCH).obj P) : (SCH).map u x ∉ D.bad := by
  rintro ⟨w', hw', e⟩
  obtain ⟨Q, a, b, τ, hab, h1, h2⟩ := exists_pt_pullback (D.i ≫ specPr M U) u w' x e
  let k : APt (fppfO B S hS) M (op Q) := APt.res (a ≫ D.i).op (specPt M U)
  have hl : a ≫ D.i = specLift (b ≫ u) k := by
    refine specLift_uniq _ _ _ ?_ rfl
    rw [Category.assoc, hab]
  have hfix := (D.univ (b ≫ u) k).mpr ⟨a, hl⟩
  have hs := hst b k hfix
  have : Set.range ((SCH).map a) ⊆ D.O := by
    refine (D.hO a).mp ?_
    rw [← Category.assoc, ← Category.assoc, hl, specLift_actMap, specLift_pr, hs]
  exact hw' (h1 ▸ this ⟨τ, rfl⟩)

/-- `Ω` is stable under `D(M)`. -/
theorem StabData.act_mem_bad (hf : IsEquivariant actU actX f) (w : (SCH).obj (specObj M U))
    (hw : (SCH).map (specPr M U) w ∈ D.bad) : (SCH).map (actMap actU) w ∈ D.bad := by
  obtain ⟨w', hw', e⟩ := hw
  obtain ⟨Q, a, b, τ, hab, h1, h2⟩ := exists_pt_pullback (D.i ≫ specPr M U) (specPr M U) w' w e
  let t : Q ⟶ U := b ≫ specPr M U
  let kk : APt (fppfO B S hS) M (op Q) := APt.res (a ≫ D.i).op (specPt M U)
  let gg : APt (fppfO B S hS) M (op Q) := APt.res b.op (specPt M U)
  have hl : a ≫ D.i = specLift t kk := by
    refine specLift_uniq _ _ _ ?_ rfl
    rw [Category.assoc, hab]
  have hb : b = specLift t gg := specLift_uniq _ _ _ rfl rfl
  have hfix := (D.univ t kk).mpr ⟨a, hl⟩
  let t2 : Q ⟶ U := actU.smul gg t
  have hb2 : b ≫ actMap actU = t2 := by
    rw [hb]; exact specLift_actMap t gg
  have hfix2 : actX.smul kk (f.app (op Q) t2) = f.app (op Q) t2 := by
    change actX.smul kk (f.app (op Q) (actU.smul gg t)) = f.app (op Q) (actU.smul gg t)
    rw [hf, ← actX.mul_smul, mul_comm, actX.mul_smul, hfix]
  obtain ⟨w2, hw2⟩ := (D.univ t2 kk).mp hfix2
  have hnot : (SCH).map w2 τ ∉ (D.O : Set _) := by
    intro hτ
    let V' : ((SCH).obj Q).Opens := (SCH).map w2 ⁻¹ᵁ D.O
    let j : openObj V' ⟶ Q := openJ V'
    have hrj : Set.range ((SCH).map (j ≫ w2)) ⊆ D.O := by
      rintro _ ⟨y, rfl⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact y.2
    have h3 := (D.hO (j ≫ w2)).mpr hrj
    have eA : w2 ≫ D.i ≫ actMap actU = actU.smul kk t2 := by
      rw [← Category.assoc, hw2, specLift_actMap]
    have eB : w2 ≫ D.i ≫ specPr M U = t2 := by
      rw [← Category.assoc, hw2, specLift_pr]
    rw [Category.assoc, Category.assoc, eA, eB] at h3
    -- `h3 : j ≫ kk • t2 = j ≫ t2`
    have hm : ∀ (g : APt (fppfO B S hS) M (op Q)) (x : Q ⟶ U),
        j ≫ (actU.smul g x : Q ⟶ U) = actU.smul (APt.res j.op g) (j ≫ x) :=
      fun g x => actU.map_smul j.op g x
    have h4 : (actU.smul (APt.res j.op kk) (j ≫ t) : openObj V' ⟶ U) = j ≫ t := by
      apply smul_injective actU (APt.res j.op gg)
      have e1 : j ≫ t2 = actU.smul (APt.res j.op gg) (j ≫ t) := hm gg t
      rw [hm, e1] at h3
      refine (actU.mul_smul _ _ _).symm.trans ((congrArg
        (fun z => actU.smul z (show (yoneda.obj U).obj (op (openObj V')) from j ≫ t))
        (mul_comm _ _)).trans ((actU.mul_smul _ _ _).trans h3))
    have h5 : Set.range ((SCH).map (j ≫ a)) ⊆ D.O := by
      refine (D.hO (j ≫ a)).mp ?_
      have eA : a ≫ D.i ≫ actMap actU = actU.smul kk t := by
        rw [← Category.assoc, hl, specLift_actMap]
      have eB : a ≫ D.i ≫ specPr M U = t := by
        rw [← Category.assoc, hl, specLift_pr]
      rw [Category.assoc, Category.assoc, eA, eB, hm]
      exact h4
    have hτ' : τ ∈ V' := hτ
    let y : (SCH).obj (openObj V') := ⟨τ, hτ'⟩
    have hy : (SCH).map j y = τ := rfl
    have h6 := h5 ⟨y, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hy, h1] at h6
    exact hw' h6
  refine ⟨_, hnot, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Category.assoc, hw2, specLift_pr, ← hb2,
    Functor.map_comp, Scheme.Hom.comp_apply, h2]

/-- Evaluation of `Γ(U)[M]` along a morphism to `D(M)_U`. -/
noncomputable def evalAt {T : BigFppfOver B S hS} (s : T ⟶ specObj M U) :
    gRing M U →+* Γ((SCH).obj T, ⊤) :=
  ((SCH).map s).appTop.hom.comp (Scheme.ΓSpecIso (.of (gRing M U))).inv.hom

lemma evalAt_specLift {T : BigFppfOver B S hS} (t : T ⟶ U) (k : APt (fppfO B S hS) M (op T)) :
    evalAt (specLift t k) = specRing t k := by
  refine RingHom.ext fun x => ?_
  exact appTop_toSpec_comp (specRing t k) x

lemma hom_inv_apply (x : Γ(Spec (.of (gRing M U)), ⊤)) :
    (Scheme.ΓSpecIso (.of (gRing M U))).inv.hom ((Scheme.ΓSpecIso (.of (gRing M U))).hom.hom x) = x := by
  simpa using congrArg (fun k => k.hom x) (Scheme.ΓSpecIso (.of (gRing M U))).hom_inv_id

lemma inv_injective_Γ {x y : gRing M U}
    (h : (Scheme.ΓSpecIso (.of (gRing M U))).inv.hom x = (Scheme.ΓSpecIso (.of (gRing M U))).inv.hom y) :
    x = y := by
  have e := congrArg (Scheme.ΓSpecIso (.of (gRing M U))).hom.hom h
  simpa using e

/-- The coaction `ρ : Γ(U) → Γ(U)[M]`. -/
noncomputable def rhoMap (actU : AAction (fppfO B S hS) M (yoneda.obj U)) :
    Γ((SCH).obj U, ⊤) →+* gRing M U :=
  (Scheme.ΓSpecIso (.of (gRing M U))).hom.hom.comp ((SCH).map (actMap actU)).appTop.hom

lemma appTop_smul {T : BigFppfOver B S hS} (t : T ⟶ U) (k : APt (fppfO B S hS) M (op T))
    (x : Γ((SCH).obj U, ⊤)) :
    ((SCH).map (actU.smul k t : T ⟶ U)).appTop.hom x = specRing t k (rhoMap actU x) := by
  rw [← specLift_actMap, Functor.map_comp, Scheme.Hom.comp_appTop, ← evalAt_specLift]
  change ((SCH).map (specLift t k)).appTop.hom (((SCH).map (actMap actU)).appTop.hom x) =
    ((SCH).map (specLift t k)).appTop.hom ((Scheme.ΓSpecIso (.of (gRing M U))).inv.hom
      ((Scheme.ΓSpecIso (.of (gRing M U))).hom.hom (((SCH).map (actMap actU)).appTop.hom x)))
  exact congrArg (fun z => ((SCH).map (specLift t k)).appTop.hom z)
    (hom_inv_apply (M := M) (U := U) (((SCH).map (actMap actU)).appTop.hom x)).symm

/-- The point of `Spec Γ(U)` below `Φ(p)`, for `Φ : D(M)_U → U`. -/
lemma isoSpec_apply (Φ : Spec (.of (gRing M U)) ⟶ (SCH).obj U) (p : Spec (.of (gRing M U))) :
    ((SCH).obj U).isoSpec.hom (Φ p) = PrimeSpectrum.comap
      ((Scheme.ΓSpecIso (.of (gRing M U))).hom.hom.comp Φ.appTop.hom)
        (show PrimeSpectrum (gRing M U) from p) := by
  have h : Φ ≫ ((SCH).obj U).isoSpec.hom =
      Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of (gRing M U))).hom.hom.comp Φ.appTop.hom)) := by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality, ← Scheme.isoSpec_hom, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp]
    rfl
  rw [← Scheme.Hom.comp_apply, h]
  rfl

lemma isoSpec_specPr (p : Spec (.of (gRing M U))) :
    ((SCH).obj U).isoSpec.hom (specPrS M U p) =
      PrimeSpectrum.comap (algebraMap _ (gRing M U)) (show PrimeSpectrum (gRing M U) from p) := by
  have h : specPrS M U ≫ ((SCH).obj U).isoSpec.hom =
      Spec.map (CommRingCat.ofHom (algebraMap _ (gRing M U))) := by
    simp [specPrS]
  rw [← Scheme.Hom.comp_apply, h]
  rfl

lemma map_specPr_apply (p : (SCH).obj (specObj M U)) :
    ((SCH).obj U).isoSpec.hom ((SCH).map (specPr M U) p) =
      PrimeSpectrum.comap (algebraMap _ (gRing M U)) (show PrimeSpectrum (gRing M U) from p) :=
  isoSpec_specPr p

lemma map_actMap_apply (p : (SCH).obj (specObj M U)) :
    ((SCH).obj U).isoSpec.hom ((SCH).map (actMap actU) p) =
      PrimeSpectrum.comap (rhoMap actU) (show PrimeSpectrum (gRing M U) from p) :=
  isoSpec_apply _ p

/-- `V(I)` and `D(e)` for the stabilizer data. -/
theorem StabData.exists_ideal (D : StabData actU actX f) :
    ∃ (I : Ideal (gRing M U)) (e : gRing M U), e * e - e ∈ I ∧
      (∀ x ∈ I, ∀ n, powMap _ n x ∈ I) ∧
      ((SCH).obj U).isoSpec.hom '' D.bad = badImage I e := by
  have hic := D.closed
  have hAff : IsAffine ((SCH).obj (specObj M U)) := inferInstance
  obtain ⟨hA, hS'⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map D.i)
  let κ : gRing M U →+* Γ((SCH).obj D.E, ⊤) := evalAt D.i
  have hκs : Function.Surjective κ := by
    intro y
    obtain ⟨z, hz⟩ := hS' y
    refine ⟨(Scheme.ΓSpecIso (.of (gRing M U))).hom.hom z, ?_⟩
    exact (congrArg (fun z' => ((SCH).map D.i).appTop.hom z') (hom_inv_apply (M := M) (U := U) z)).trans hz
  have hmap : (SCH).map D.i = ((SCH).obj D.E).toSpecΓ ≫ Spec.map (CommRingCat.ofHom κ) := by
    refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun y => ?_))
    have hy := hom_inv_apply (M := M) (U := U) y
    rw [← hy]
    exact (appTop_toSpec_comp κ _).symm
  have hpt : ∀ w : (SCH).obj D.E, ((SCH).map D.i w : PrimeSpectrum (gRing M U)) =
      PrimeSpectrum.comap κ (((SCH).obj D.E).isoSpec.hom w) := by
    intro w
    exact congrArg (fun m : (SCH).obj D.E ⟶ Spec (.of (gRing M U)) => m w) hmap
  let hme := Scheme.homeoOfIso ((SCH).obj D.E).isoSpec
  have hclopen : IsClopen (hme '' (D.O : Set ((SCH).obj D.E))ᶜ) :=
    ⟨hme.isClosed_image.mpr D.O.isOpen.isClosed_compl, hme.isOpen_image.mpr D.closedO.isOpen_compl⟩
  obtain ⟨ε, hε, hs⟩ := PrimeSpectrum.isClopen_iff.mp hclopen
  obtain ⟨e₀, he₀⟩ := hκs ε
  have key : ∀ w : (SCH).obj D.E, e₀ ∉ ((SCH).map D.i w : PrimeSpectrum (gRing M U)).asIdeal ↔
      w ∉ (D.O : Set _) := by
    intro w
    rw [hpt]
    change κ e₀ ∉ (hme w).asIdeal ↔ _
    rw [he₀]
    have h1 : ε ∉ (hme w).asIdeal ↔ hme w ∈ hme '' (D.O : Set ((SCH).obj D.E))ᶜ := by
      rw [hs]; rfl
    rw [h1, hme.injective.mem_set_image]
    rfl
  have hmem : ∀ p : PrimeSpectrum (gRing M U), RingHom.ker κ ≤ p.asIdeal ↔
      ∃ w : (SCH).obj D.E, ((SCH).map D.i w : PrimeSpectrum (gRing M U)) = p := by
    intro p
    constructor
    · intro hp
      have : p ∈ Set.range (PrimeSpectrum.comap κ) := by
        rw [range_comap_of_surjective _ _ hκs]
        exact hp
      obtain ⟨q, rfl⟩ := this
      refine ⟨hme.symm q, ?_⟩
      rw [hpt]
      congr 1
      exact hme.apply_symm_apply q
    · rintro ⟨w, rfl⟩ x hx
      rw [hpt]
      have h0 : κ x = 0 := RingHom.mem_ker.mp hx
      exact Ideal.mem_comap.mpr (by rw [h0]; exact Ideal.zero_mem _)
  refine ⟨RingHom.ker κ, e₀, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, map_sub, map_mul, he₀, hε.eq, sub_self]
  · intro x hx n
    let t₁ : D.E ⟶ U := D.i ≫ specPr M U
    let k₁ : APt (fppfO B S hS) M (op D.E) := APt.res D.i.op (specPt M U)
    have hi : D.i = specLift t₁ k₁ := specLift_uniq _ _ _ rfl rfl
    have hκ : κ = specRing t₁ k₁ := by
      change evalAt D.i = _
      rw [← evalAt_specLift, ← hi]
    have hfix₁ : actX.smul k₁ (f.app (op D.E) t₁) = f.app (op D.E) t₁ :=
      (D.univ t₁ k₁).mpr ⟨𝟙 _, by rw [Category.id_comp]; exact hi⟩
    have hfixn : ∀ n : ℕ, actX.smul (k₁ ^ n) (f.app (op D.E) t₁) = f.app (op D.E) t₁ := by
      intro n
      induction n with
      | zero => rw [pow_zero, actX.one_smul]
      | succ n ih => rw [pow_succ, actX.mul_smul, hfix₁, ih]
    obtain ⟨w, hw⟩ := (D.univ t₁ (k₁ ^ n)).mp (hfixn n)
    have hring : κ.comp (powMap _ n) = specRing t₁ (k₁ ^ n) := by
      rw [hκ]
      refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
      · have e : powMap Γ((SCH).obj U, ⊤) n (AddMonoidAlgebra.single (0 : M) r) =
            AddMonoidAlgebra.single 0 r := by simp [powMap]
        change specRing t₁ k₁ (powMap _ n (AddMonoidAlgebra.single 0 r)) = _
        rw [e, specRing_single, specRing_single]
        have h1 : (show Γ((SCH).obj D.E, ⊤) from k₁ (Multiplicative.ofAdd (0 : M))) = 1 := map_one k₁
        have h2 : (show Γ((SCH).obj D.E, ⊤) from (k₁ ^ n) (Multiplicative.ofAdd (0 : M))) = 1 :=
          map_one (k₁ ^ n)
        rw [h1, h2]
      · have e : powMap Γ((SCH).obj U, ⊤) n (AddMonoidAlgebra.single m 1) =
            AddMonoidAlgebra.single (n • m) 1 := by simp [powMap]
        change specRing t₁ k₁ (powMap _ n (AddMonoidAlgebra.single m 1)) = _
        rw [e, specRing_single, specRing_single]
        congr 1
        change k₁ (Multiplicative.ofAdd (n • m)) = (k₁ ^ n) (Multiplicative.ofAdd m)
        rw [ofAdd_nsmul, map_pow, MonoidHom.pow_apply]
    rw [RingHom.mem_ker]
    have h3 : κ (powMap _ n x) = specRing t₁ (k₁ ^ n) x := congrArg (fun φ => φ x) hring
    rw [h3, ← evalAt_specLift, ← hw]
    change ((SCH).map (w ≫ D.i)).appTop.hom _ = 0
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map w).appTop.hom (κ x) = 0
    rw [RingHom.mem_ker.mp hx, map_zero]
  · ext q
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨(SCH).map D.i w, (hmem _).mpr ⟨w, rfl⟩, (key w).mpr hw, ?_⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact (map_specPr_apply _).symm
    · rintro ⟨p, h1, h2, rfl⟩
      obtain ⟨w, rfl⟩ := (hmem p).mp h1
      refine ⟨(SCH).map (specPr M U) ((SCH).map D.i w), ⟨w, (key w).mp h2, ?_⟩,
        map_specPr_apply _⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply]

/-- **Lemma 2.3**, closedness of the complement of `Ω`. -/
theorem StabData.isClosed_bad (D : StabData actU actX f) [IsNoetherianRing Γ((SCH).obj U, ⊤)]
    [AddMonoid.FG M] : IsClosed D.bad := by
  obtain ⟨I, e, he, hI, hbad⟩ := D.exists_ideal
  have h := isClosed_badImage he hI
  rw [← hbad] at h
  let hme := Scheme.homeoOfIso ((SCH).obj U).isoSpec
  exact hme.isClosed_image.mp h

/-- The augmentation: `ρ` followed by `χ_m ↦ 1` is the identity (`1` acts trivially). -/
lemma rhoMap_aug (x : Γ((SCH).obj U, ⊤)) : (rhoMap actU x).coeff.sum (fun _ r => r) = x := by
  have h := appTop_smul (actU := actU) (𝟙 U) 1 x
  rw [actU.one_smul] at h
  have h1 : ((SCH).map (𝟙 U)).appTop.hom x = x := by simp
  have h2 : ∀ y : gRing M U, specRing (𝟙 U) (1 : APt (fppfO B S hS) M (op U)) y = y.coeff.sum (fun _ r => r) := by
    intro y
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single y]
    rw [Finsupp.sum, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [specRing_single]
    simp
    exact mul_one _
  rw [h2] at h
  exact h.symm.trans h1

/-- **The graded structure of `ρ`**, from the associativity of the action: the coefficient
`a_m` of `ρ a` is homogeneous of degree `m`. -/
theorem rhoMap_coeff (a : Γ((SCH).obj U, ⊤)) (m : M) :
    rhoMap actU ((rhoMap actU a).coeff m) = AddMonoidAlgebra.single m ((rhoMap actU a).coeff m) := by
  classical
  let V₀ := specObj M U
  let T := specObj M V₀
  let pr₂ : T ⟶ V₀ := specPr M V₀
  let t : T ⟶ U := pr₂ ≫ specPr M U
  let k : APt (fppfO B S hS) M (op T) := specPt M V₀
  let k' : APt (fppfO B S hS) M (op T) := APt.res pr₂.op (specPt M U)
  have hmul := actU.mul_smul k k' t
  have ht2 : (actU.smul k' t : T ⟶ U) = pr₂ ≫ actMap actU :=
    (actU.map_smul pr₂.op (specPt M U) (specPr M U)).symm
  set y := rhoMap actU a with hy
  have hz : specRing t (k * k') y = specRing (pr₂ ≫ actMap actU) k y := by
    have hL := appTop_smul (actU := actU) t (k * k') a
    have hR := appTop_smul (actU := actU) (pr₂ ≫ actMap actU) k a
    have hmul' : (actU.smul (k * k') t : T ⟶ U) = actU.smul k (pr₂ ≫ actMap actU) :=
      hmul.trans (congrArg (actU.smul k) ht2)
    exact hL.symm.trans ((congrArg (fun z : T ⟶ U => ((SCH).map z).appTop.hom a) hmul').trans hR)
  let invP : gRing M V₀ →+* Γ((SCH).obj T, ⊤) := (Scheme.ΓSpecIso (.of (gRing M V₀))).inv.hom
  let prs : Γ((SCH).obj U, ⊤) →+* Γ((SCH).obj V₀, ⊤) := ((SCH).map (specPr M U)).appTop.hom
  let acts : Γ((SCH).obj U, ⊤) →+* Γ((SCH).obj V₀, ⊤) := ((SCH).map (actMap actU)).appTop.hom
  let hn : M → Γ((SCH).obj V₀, ⊤) := fun n => specPt M U (Multiplicative.ofAdd n)
  have hkn : ∀ n : M, (show Γ((SCH).obj T, ⊤) from k (Multiplicative.ofAdd n)) =
      invP (AddMonoidAlgebra.single n 1) := fun n => rfl
  have hpr₂ : ∀ r : Γ((SCH).obj V₀, ⊤), ((SCH).map pr₂).appTop.hom r =
      invP (AddMonoidAlgebra.single 0 r) := fun r => specPrS_appTop V₀ r
  have hsingle : ∀ (n : M) (c : Γ((SCH).obj V₀, ⊤)),
      ((SCH).map pr₂).appTop.hom c * invP (AddMonoidAlgebra.single n 1) =
        invP (AddMonoidAlgebra.single n c) := by
    intro n c
    rw [hpr₂, ← map_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  have hL : ∀ (n : M) (r : Γ((SCH).obj U, ⊤)), specRing t (k * k') (AddMonoidAlgebra.single n r) =
      invP (AddMonoidAlgebra.single n (prs r * hn n)) := by
    intro n r
    rw [specRing_single, ← hsingle, map_mul]
    have e1 : ((SCH).map t).appTop.hom r = ((SCH).map pr₂).appTop.hom (prs r) := by
      simp [t, prs]
      rfl
    have e2 : (show Γ((SCH).obj T, ⊤) from (k * k') (Multiplicative.ofAdd n)) =
        invP (AddMonoidAlgebra.single n 1) * ((SCH).map pr₂).appTop.hom (hn n) := rfl
    rw [e1, e2]
    ring
  have hR : ∀ (n : M) (r : Γ((SCH).obj U, ⊤)),
      specRing (pr₂ ≫ actMap actU) k (AddMonoidAlgebra.single n r) =
        invP (AddMonoidAlgebra.single n (acts r)) := by
    intro n r
    rw [specRing_single, ← hsingle]
    have e1 : ((SCH).map (pr₂ ≫ actMap actU)).appTop.hom r = ((SCH).map pr₂).appTop.hom (acts r) := by
      simp [acts]
      rfl
    rw [e1]
    rfl
  have hyS : y = ∑ n ∈ y.coeff.support, AddMonoidAlgebra.single n (y.coeff n) :=
    (AddMonoidAlgebra.sum_coeff_single y).symm
  have hsum : (∑ n ∈ y.coeff.support, AddMonoidAlgebra.single n (prs (y.coeff n) * hn n) : gRing M V₀) =
      ∑ n ∈ y.coeff.support, AddMonoidAlgebra.single n (acts (y.coeff n)) := by
    have hzL : specRing t (k * k') y =
        ∑ n ∈ y.coeff.support, invP (AddMonoidAlgebra.single n (prs (y.coeff n) * hn n)) := by
      conv_lhs => rw [hyS]
      rw [map_sum]
      exact Finset.sum_congr rfl fun n _ => hL n _
    have hzR : specRing (pr₂ ≫ actMap actU) k y =
        ∑ n ∈ y.coeff.support, invP (AddMonoidAlgebra.single n (acts (y.coeff n))) := by
      conv_lhs => rw [hyS]
      rw [map_sum]
      exact Finset.sum_congr rfl fun n _ => hR n _
    apply inv_injective_Γ (U := V₀)
    have e : invP (∑ n ∈ y.coeff.support, AddMonoidAlgebra.single n (prs (y.coeff n) * hn n)) =
        invP (∑ n ∈ y.coeff.support, AddMonoidAlgebra.single n (acts (y.coeff n))) := by
      rw [map_sum, map_sum]
      exact hzL.symm.trans (hz.trans hzR)
    exact e
  by_cases hm : m ∈ y.coeff.support
  · have hc := congrArg (fun z : gRing M V₀ => z.coeff m) hsum
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finset.sum_ite_eq', hm, ite_true] at hc
    have hinv : ∀ z : gRing M U, (Scheme.ΓSpecIso (.of (gRing M U))).hom.hom
        ((Scheme.ΓSpecIso (.of (gRing M U))).inv.hom z) = z := fun z => by
      simpa using congrArg (fun q => q.hom z) (Scheme.ΓSpecIso (.of (gRing M U))).inv_hom_id
    let homU : Γ((SCH).obj V₀, ⊤) →+* gRing M U := (Scheme.ΓSpecIso (.of (gRing M U))).hom.hom
    have e1 : homU (prs (y.coeff m)) = AddMonoidAlgebra.single 0 (y.coeff m) := by
      have := specPrS_appTop (P := M) U (y.coeff m)
      exact (congrArg homU this).trans (hinv _)
    have e2 : homU (hn m) = AddMonoidAlgebra.single m 1 := hinv _
    have e3 : rhoMap actU (y.coeff m) = homU (acts (y.coeff m)) := rfl
    rw [e3, ← hc, map_mul, e1, e2, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  · rw [Finsupp.notMem_support_iff.mp hm]
    simp

/-- Homogeneous elements give stable opens. -/
theorem isStableOpen_basicOpen {b : Γ((SCH).obj U, ⊤)} {m : M}
    (hb : rhoMap actU b = AddMonoidAlgebra.single m b) :
    IsStableOpen actU (((SCH).obj U).basicOpen b) := by
  intro T t k ht
  let c : Γ((SCH).obj T, ⊤) := k (Multiplicative.ofAdd m)
  have hunit : IsUnit c := by
    have h1 : k (Multiplicative.ofAdd m * Multiplicative.ofAdd (-m)) = 1 := by
      rw [← ofAdd_add, add_neg_cancel, ofAdd_zero]
      exact map_one k
    exact IsUnit.of_mul_eq_one (k (Multiplicative.ofAdd (-m))) ((map_mul k _ _).symm.trans h1)
  have hform : ((SCH).map (actU.smul k t : T ⟶ U)).appTop.hom b = ((SCH).map t).appTop.hom b * c := by
    rw [appTop_smul, hb, specRing_single]
  have hs : (SCH).map (actU.smul k t : T ⟶ U) ⁻¹ᵁ ((SCH).obj U).basicOpen b =
      (SCH).map t ⁻¹ᵁ ((SCH).obj U).basicOpen b := by
    rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top]
    refine (congrArg _ hform).trans ?_
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hunit, inf_top_eq]
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ (SCH).map t ⁻¹ᵁ ((SCH).obj U).basicOpen b := ht ⟨y, rfl⟩
  rw [← hs] at hy
  exact hy

end Chart

end AlgMag.StronglyFPR
