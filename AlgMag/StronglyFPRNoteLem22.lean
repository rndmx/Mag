/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.StronglyFPRNoteLem21
import AlgMag.StronglyFPRNoteLem22Ring

/-!
# Existence of strongly-FPR atlases: Lemma 2.2

`x ∈ X(V)`, `V` affine noetherian: the stabilizer group `𝔊_V ⊆ D(M)_V` is `V(I)`. `lem22` gives `I`, with its universal
property, the fact that it is a subgroup, and the finiteness of the `Y_v = {m | χ^m = 1 on 𝔊_v}`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.StronglyFPRNote

open AlgMag.StronglyFPR SubgroupIdeal

noncomputable section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable (act : AAction (fppfO B S hS) M X) {V : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- The stabilizer locus. -/
structure StabIdeal (x : X.obj (op V)) where
  E : BigFppfOver B S hS
  i : E ⟶ specObj M V
  closed : IsClosedImmersion ((SCH).map i)
  univ : ∀ {T : BigFppfOver B S hS} (t : T ⟶ V) (k : APt (fppfO B S hS) M (op T)),
    act.smul k (X.map t.op x) = X.map t.op x ↔ ∃ w : T ⟶ E, w ≫ i = specLift t k

lemma nonempty_stabIdeal (hsep : Space.IsSeparatedOver B S hS X) (x : X.obj (op V)) :
    Nonempty (StabIdeal act x) := by
  let G := specObj M V
  obtain ⟨E, i, hi, hE⟩ := AlgMag.Chart.exists_eqLocus hsep G
    (act.smul (specPt M V) (X.map (specPr M V).op x)) (X.map (specPr M V).op x)
  refine ⟨⟨E, i, hi, fun {T} t k => ?_⟩⟩
  have h := hE T (specLift t k)
  have e0 : X.map (specLift t k).op (X.map (specPr M V).op x) = X.map t.op x := by
    rw [← Functor.map_comp_apply, ← op_comp, specLift_pr]
  rw [act.map_smul, res_specLift, e0] at h
  exact h

variable {act} {x : X.obj (op V)} (D : StabIdeal act x)

lemma evalAt_comp' {P : Type u} [AddCommGroup P] [Countable P] {T E' : BigFppfOver B S hS} (w : T ⟶ E') (i : E' ⟶ specObj P V) :
    evalAt (w ≫ i) = ((SCH).map w).appTop.hom.comp (evalAt i) := by
  refine RingHom.ext fun y => ?_
  simp only [evalAt, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- The ideal of the stabilizer. -/
def StabIdeal.I : Ideal (gRing M V) := RingHom.ker (evalAt D.i)

include D in
/-- A stabilizing `k` kills `I`. -/
lemma StabIdeal.kills {T : BigFppfOver B S hS} (t : T ⟶ V) (k : APt (fppfO B S hS) M (op T))
    (h : act.smul k (X.map t.op x) = X.map t.op x) {y : gRing M V} (hy : y ∈ D.I) :
    specRing t k y = 0 := by
  obtain ⟨w, hw⟩ := (D.univ t k).1 h
  have e := evalAt_specLift t k
  rw [← e, ← hw, evalAt_comp']
  have h0 : evalAt D.i y = 0 := hy
  simp [h0]

/-- `k` killing `I` stabilizes: `𝔊_V = V(I)`. -/
lemma StabIdeal.fix_of_kills {T : BigFppfOver B S hS} (t : T ⟶ V) (k : APt (fppfO B S hS) M (op T))
    (hk : ∀ y ∈ D.I, specRing t k y = 0) : act.smul k (X.map t.op x) = X.map t.op x := by
  have hic := D.closed
  have hAff : IsAffine ((SCH).obj (specObj M V)) := inferInstance
  obtain ⟨hA, hS'⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map D.i)
  let κ : gRing M V →+* Γ((SCH).obj D.E, ⊤) := evalAt D.i
  have hκs : Function.Surjective κ := by
    intro y
    obtain ⟨z, hz⟩ := hS' y
    refine ⟨(Scheme.ΓSpecIso (.of (gRing M V))).hom.hom z, ?_⟩
    exact (congrArg (fun z' => ((SCH).map D.i).appTop.hom z') (hom_inv_apply (M := M) (U := V) z)).trans hz
  have hmap : (SCH).map D.i = ((SCH).obj D.E).toSpecΓ ≫ Spec.map (CommRingCat.ofHom κ) := by
    refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun y => ?_))
    have hy := hom_inv_apply (M := M) (U := V) y
    rw [← hy]
    exact (appTop_toSpec_comp κ _).symm
  let ρ := specRing t k
  have hker : RingHom.ker κ ≤ RingHom.ker ρ := fun y hy => hk y hy
  let ρ' : Γ((SCH).obj D.E, ⊤) →+* Γ((SCH).obj T, ⊤) := RingHom.liftOfSurjective κ hκs ⟨ρ, hker⟩
  have hρ : ρ'.comp κ = ρ := RingHom.liftOfRightInverse_comp _ _ _ _
  let wS : (SCH).obj T ⟶ (SCH).obj D.E :=
    ((SCH).obj T).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ') ≫ ((SCH).obj D.E).isoSpec.inv
  have hinv : ((SCH).obj D.E).isoSpec.inv ≫ ((SCH).obj D.E).toSpecΓ = 𝟙 _ := by
    rw [← Scheme.isoSpec_hom]; exact Iso.inv_hom_id _
  have h0 : wS ≫ ((SCH).obj D.E).toSpecΓ = ((SCH).obj T).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ') := by
    simp only [wS, Category.assoc]
    rw [hinv]
    exact congrArg (fun z => ((SCH).obj T).toSpecΓ ≫ z) (Category.comp_id _)
  have hthis : CommRingCat.ofHom κ ≫ CommRingCat.ofHom ρ' = CommRingCat.ofHom ρ := by
    rw [← CommRingCat.ofHom_comp, hρ]
  have hw2 : wS ≫ ((SCH).obj D.E).toSpecΓ ≫ Spec.map (CommRingCat.ofHom κ) = specLiftS t k := by
    rw [← Category.assoc, h0, Category.assoc, ← Spec.map_comp, hthis]
    rfl
  have hw1 : wS ≫ (SCH).map D.i = specLiftS t k := (congrArg (fun z => wS ≫ z) hmap).trans hw2
  have hiw : (SCH).map D.i ≫ (specObj M V).hom.hom = D.E.hom.hom := congrArg (fun k => k.hom) (Over.w D.i)
  let w : T ⟶ D.E := overHom wS (by
    rw [← hiw, ← Category.assoc, hw1]
    exact congrArg (fun k => k.hom) (Over.w (specLift t k)))
  exact (D.univ t k).2 ⟨w, toScheme_map_injective (by rw [Functor.map_comp]; exact hw1)⟩

include D in
lemma StabIdeal.counit : ∀ y ∈ D.I, aug _ M y = 0 := by
  intro y hy
  have h := D.kills (𝟙 V) 1 (by rw [act.one_smul]) hy
  have e : specRing (𝟙 V) (1 : APt (fppfO B S hS) M (op V)) = aug _ M := by
    refine SubgroupIdeal.hom_ext' (fun r => ?_) (fun m => ?_)
    · rw [specRing_single]; simp [aug, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]; exact mul_one _
    · rw [specRing_single]; simp [aug, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]; exact mul_one _
  rwa [e] at h

section Sub

variable (J : Ideal (gRing (M × M) V))

/-- `Spec R[M × M]/J → D(M × M)_V`. -/
def jC : Spec (.of (gRing (M × M) V ⧸ J)) ⟶ (SCH).obj (specObj (M × M) V) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

instance : IsClosedImmersion (jC J) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- `V(J) ⊆ D(M × M)_V`. -/
def jObj : BigFppfOver B S hS := AlgMag.Chart.immObj (specObj (M × M) V) (jC J)

/-- The inclusion of `V(J)`. -/
def jι : jObj J ⟶ specObj (M × M) V := AlgMag.Chart.immι (specObj (M × M) V) (jC J)

lemma evalAt_jι_eq_zero {y : gRing (M × M) V} : evalAt (jι J) y = 0 ↔ y ∈ J := by
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have e : evalAt (jι J) y = (Scheme.ΓSpecIso (.of (gRing (M × M) V ⧸ J))).inv.hom (Ideal.Quotient.mk J y) :=
    (congrArg (fun k => k.hom y) hn).symm
  rw [e, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    have h0 := congrArg (Scheme.ΓSpecIso (.of (gRing (M × M) V ⧸ J))).hom.hom h
    have h1 := h0.trans (map_zero (Scheme.ΓSpecIso (.of (gRing (M × M) V ⧸ J))).hom.hom)
    simpa using h1
  · intro h
    rw [h]
    exact map_zero _

lemma specRing_jι (φ : M →+ M × M) :
    specRing (jι J ≫ specPr (M × M) V)
        ((APt.res (jι J).op (specPt (M × M) V)).comp (AddMonoidHom.toMultiplicative φ)) =
      (evalAt (jι J)).comp (AddMonoidAlgebra.mapDomainRingHom _ φ) := by
  refine SubgroupIdeal.hom_ext' (fun r => ?_) (fun m => ?_)
  · rw [specRing_single]
    have h1 : ((APt.res (jι J).op (specPt (M × M) V)).comp (AddMonoidHom.toMultiplicative φ))
        (Multiplicative.ofAdd (0 : M)) = 1 := map_one _
    refine Eq.trans (congrArg (fun z => ((SCH).map (jι J ≫ specPr (M × M) V)).appTop.hom r * z) h1)
      ((mul_one (_ : Γ((SCH).obj (jObj J), ⊤))).trans ?_)
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    simp only [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, map_zero]
    change ((SCH).map (jι J)).appTop.hom ((specPrS (M × M) V).appTop.hom r) = _
    rw [specPrS_appTop]
    rfl
  · rw [specRing_single, map_one, one_mul]
    simp only [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
    rfl

end Sub

include D in
/-- `V(I)` is a subgroup: it contains the unit section, and is stable under the product. -/
theorem StabIdeal.isSubgroupIdeal : IsSubgroupIdeal D.I := by
  refine ⟨D.counit, fun y hy => ?_⟩
  let J : Ideal (gRing (M × M) V) := D.I.map (inl' _ M) ⊔ D.I.map (inr' _ M)
  let t : jObj J ⟶ V := jι J ≫ specPr (M × M) V
  let pt := APt.res (jι J).op (specPt (M × M) V)
  let k1 : APt (fppfO B S hS) M (op (jObj J)) := pt.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M M))
  let k2 : APt (fppfO B S hS) M (op (jObj J)) := pt.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M M))
  let kd : APt (fppfO B S hS) M (op (jObj J)) := pt.comp (AddMonoidHom.toMultiplicative
    (AddMonoidHom.prod (AddMonoidHom.id M) (AddMonoidHom.id M)))
  have h1 := D.fix_of_kills t k1 (fun z hz => by
    have := congrArg (fun f => f z) (specRing_jι J (AddMonoidHom.inl M M))
    refine this.trans ((evalAt_jι_eq_zero J).2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hz))))
  have h2 := D.fix_of_kills t k2 (fun z hz => by
    have := congrArg (fun f => f z) (specRing_jι J (AddMonoidHom.inr M M))
    refine this.trans ((evalAt_jι_eq_zero J).2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hz))))
  have hd : kd = k1 * k2 := by
    refine MonoidHom.ext fun n => ?_
    change pt (Multiplicative.ofAdd (Multiplicative.toAdd n, Multiplicative.toAdd n)) =
      pt (Multiplicative.ofAdd (Multiplicative.toAdd n, 0)) * pt (Multiplicative.ofAdd (0, Multiplicative.toAdd n))
    rw [← map_mul, ← ofAdd_add]
    simp
  have h3 : act.smul kd (X.map t.op x) = X.map t.op x := by
    rw [hd, act.mul_smul, h2, h1]
  have h4 := D.kills t kd h3 hy
  have h5 := congrArg (fun f => f y) (specRing_jι J (AddMonoidHom.prod (AddMonoidHom.id M) (AddMonoidHom.id M)))
  exact (evalAt_jι_eq_zero J).1 (h5.symm.trans h4)

/-- **Lemma 2.2.** `V` affine noetherian, `x ∈ X(V)`, `X` separated over `S`: the stabilizer group `𝔊_V ⊆ D(M)_V` is `V(I)`
(first clause), and the `Y_v = charAt I v`, the `m` with `χ^m = 1` on the fibre `𝔊_v`, take finitely many values. -/
theorem lem22 [AddGroup.FG M] [IsNoetherianRing Γ((SCH).obj V, ⊤)] (act : AAction (fppfO B S hS) M X)
    (hsep : Space.IsSeparatedOver B S hS X) (x : X.obj (op V)) :
    ∃ I : Ideal (gRing M V),
      (∀ {T : BigFppfOver B S hS} (t : T ⟶ V) (k : APt (fppfO B S hS) M (op T)),
        act.smul k (X.map t.op x) = X.map t.op x ↔ ∀ y ∈ I, specRing t k y = 0) ∧
      IsSubgroupIdeal I ∧ (Set.range (charAt I)).Finite := by
  obtain ⟨D⟩ := nonempty_stabIdeal act hsep x
  exact ⟨D.I, fun t k => ⟨fun h y hy => D.kills t k h hy, D.fix_of_kills t k⟩, D.isSubgroupIdeal,
    finite_range _ D.isSubgroupIdeal⟩

end

end AlgMag.StronglyFPRNote

#print axioms AlgMag.StronglyFPRNote.lem22
