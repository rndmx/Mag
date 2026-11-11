/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.StronglyFPRStab
import AlgMag.ChartStratumRing
import AlgMag.ChartEffectiveMain

/-!
# The generic stabilizer on a chart

`AlgMag.ChartStratum.exists_generic_stabilizer`: for a point `p` of a separated `X` with `D(M)`-action
over an affine integral noetherian `V`, there are `s ≠ 0` and `Z ≤ M` such that over `D(s)` a point of
`D(M)` fixes `p` exactly when it is trivial on `Z`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- The ideal of the stabilizer locus, with its description on points. -/
theorem exists_stabIdeal (act : AAction (fppfO B S hS) M X)
    (hsep : Space.IsSeparatedOver B S hS X) (p : X.obj (op V)) :
    ∃ I : Ideal (gRing M V), ∀ (T : BigFppfOver B S hS) (t : T ⟶ V)
      (h : APt (fppfO B S hS) M (op T)),
      act.smul h (X.map t.op p) = X.map t.op p ↔ ∀ f ∈ I, specRing t h f = 0 := by
  obtain ⟨E, i, hi, hE⟩ := AlgMag.Chart.exists_eqLocus hsep (specObj M V)
    (act.smul (U := op (specObj M V)) (specPt (B := B) (S := S) (hS := hS) M V) (X.map (specPr M V).op p))
    (X.map (specPr M V).op p)
  have hA : IsAffine ((SCH).obj (specObj M V)) := inferInstance
  obtain ⟨hEa, hS'⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map i)
  let κ : gRing M V →+* Γ((SCH).obj E, ⊤) := AlgMag.StronglyFPR.evalAt (U := V) i
  have hκs : Function.Surjective κ := by
    intro y
    obtain ⟨z, hz⟩ := hS' y
    refine ⟨(Scheme.ΓSpecIso (.of (gRing M V))).hom.hom z, ?_⟩
    exact (congrArg (fun z' => ((SCH).map i).appTop.hom z') (hom_inv_apply (M := M) (U := V) z)).trans hz
  have hmap : (SCH).map i = ((SCH).obj E).toSpecΓ ≫ Spec.map (CommRingCat.ofHom κ) := by
    refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun y => ?_))
    have hy := hom_inv_apply (M := M) (U := V) y
    rw [← hy]
    exact (appTop_toSpec_comp κ _).symm
  have hpt : ∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T)),
      (act.smul h (X.map t.op p) = X.map t.op p ↔ ∃ u : T ⟶ E, u ≫ i = specLift t h) := by
    intro T t h
    rw [← hE T (specLift t h)]
    have e1 : X.map (specLift t h).op (X.map (specPr M V).op p) = X.map t.op p := by
      rw [← Functor.map_comp_apply, ← op_comp, specLift_pr]
    rw [act.map_smul, res_specLift, e1]
  refine ⟨RingHom.ker κ, fun T t h => ?_⟩
  rw [hpt]
  constructor
  · rintro ⟨u, hu⟩ f hf
    rw [← evalAt_specLift, ← hu]
    change ((SCH).map (u ≫ i)).appTop.hom _ = 0
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map u).appTop.hom (κ f) = 0
    rw [RingHom.mem_ker.mp hf, map_zero]
  · intro hk
    let φ : Γ((SCH).obj E, ⊤) →+* Γ((SCH).obj T, ⊤) :=
      (RingHom.liftOfRightInverse κ (Function.surjInv hκs) (Function.rightInverse_surjInv hκs))
        ⟨specRing t h, fun f hf => hk f hf⟩
    have hφ : φ.comp κ = specRing t h :=
      RingHom.liftOfRightInverse_comp _ _ _ _
    haveI : IsIso ((SCH).obj E).toSpecΓ := by
      exact inferInstance
    let u₀ : (SCH).obj T ⟶ (SCH).obj E :=
      ((SCH).obj T).toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ inv ((SCH).obj E).toSpecΓ
    have hu₀ : u₀ ≫ (SCH).map i = (SCH).map (specLift t h) := by
      have e2 : Spec.map (CommRingCat.ofHom φ) ≫ inv ((SCH).obj E).toSpecΓ ≫ ((SCH).obj E).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom κ) = Spec.map (CommRingCat.ofHom (specRing t h)) := by
        rw [IsIso.inv_hom_id_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
      have e3 : (SCH).map (specLift t h) =
          ((SCH).obj T).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (specRing t h)) := rfl
      rw [hmap, e3, ← e2]
      exact (Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))
    have hw : u₀ ≫ E.hom.hom = T.hom.hom := by
      have e1 : E.hom.hom = (SCH).map i ≫ (specObj M V).hom.hom :=
        (congrArg (fun k => k.hom) (Over.w i)).symm
      have e2 : (SCH).map (specLift t h) ≫ (specObj M V).hom.hom = T.hom.hom :=
        congrArg (fun k => k.hom) (Over.w (specLift t h))
      rw [e1, ← Category.assoc, hu₀, e2]
    exact ⟨overHom u₀ hw, toScheme_map_injective (by rw [Functor.map_comp, map_overHom, hu₀])⟩

/-- `specRing` along a further map. -/
lemma appTop_specRing {T T' : BigFppfOver B S hS} (j : T' ⟶ T) (a : T ⟶ V)
    (c : APt (fppfO B S hS) M (op T)) (f : gRing M V) :
    ((SCH).map j).appTop.hom (specRing a c f) = specRing (j ≫ a) (APt.res j.op c) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single n r =>
    rw [specRing_single, specRing_single, map_mul, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl

/-- Characters killing the stabilizer ideal are closed under products, for all algebras. -/
theorem hmul_of_stabIdeal (act : AAction (fppfO B S hS) M X) (p : X.obj (op V))
    (I : Ideal (gRing M V))
    (hI : ∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T)),
      act.smul h (X.map t.op p) = X.map t.op p ↔ ∀ f ∈ I, specRing t h f = 0)
    (A : Type u) [CommRing A] [Algebra Γ((SCH).obj V, ⊤) A] (g h : Multiplicative M →* A)
    (hg : ∀ f ∈ I, AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) A M g f = 0)
    (hh : ∀ f ∈ I, AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) A M h f = 0) :
    ∀ f ∈ I, AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) A M (g * h) f = 0 := by
  classical
  let W1 := specObj (B := B) (S := S) (hS := hS) M V
  let W := specObj (B := B) (S := S) (hS := hS) M W1
  let a : W ⟶ V := specPr M W1 ≫ specPr M V
  let g0 : APt (fppfO B S hS) M (op W) := APt.res (specPr M W1).op (specPt M V)
  let h0 : APt (fppfO B S hS) M (op W) := specPt M W1
  let L : Ideal Γ((SCH).obj W, ⊤) :=
    Ideal.span ((specRing a g0 '' (I : Set _)) ∪ (specRing a h0 '' (I : Set _)))
  let T := Chart.immObj W (Chart.closedι ((SCH).obj W) L)
  let j : T ⟶ W := Chart.immι W (Chart.closedι ((SCH).obj W) L)
  have hj : ∀ x ∈ L, ((SCH).map j).appTop.hom x = 0 := fun x hx =>
    AlgMag.ChartMain.closedι_appTop_of_mem L hx
  have stab : ∀ c : APt (fppfO B S hS) M (op W), (∀ f ∈ I, specRing a c f ∈ L) →
      act.smul (APt.res j.op c) (X.map (j ≫ a).op p) = X.map (j ≫ a).op p := by
    intro c hc
    refine (hI T (j ≫ a) _).mpr fun f hf => ?_
    rw [← appTop_specRing]
    exact hj _ (hc f hf)
  have hL : ∀ f ∈ I, specRing a (g0 * h0) f ∈ L := by
    intro f hf
    have e1 := stab g0 fun f hf => Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩)
    have e2 := stab h0 fun f hf => Ideal.subset_span (Or.inr ⟨f, hf, rfl⟩)
    have e3 : act.smul (APt.res j.op (g0 * h0)) (X.map (j ≫ a).op p) = X.map (j ≫ a).op p := by
      rw [APt.res_mul, act.mul_smul, e2, e1]
    have e4 := (hI T (j ≫ a) _).mp e3 f hf
    rw [← appTop_specRing] at e4
    exact Chart.closedι_appTop_eq_zero L _ e4
  let x0 : Γ((SCH).obj W1, ⊤) →+* A :=
    (AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) A M g).toRingHom.comp
      (Scheme.ΓSpecIso (.of (gRing M V))).hom.hom
  let Ξ0 : gRing M W1 →+* A := AddMonoidAlgebra.liftNCRingHom x0 h (fun _ _ => mul_comm _ _)
  let Ξ : Γ((SCH).obj W, ⊤) →+* A := Ξ0.comp (Scheme.ΓSpecIso (.of (gRing M W1))).hom.hom
  have iso1 : ∀ x : gRing M W1, Ξ ((Scheme.ΓSpecIso (.of (gRing M W1))).inv.hom x) = Ξ0 x := by
    intro x
    change Ξ0 ((Scheme.ΓSpecIso (.of (gRing M W1))).hom.hom
      ((Scheme.ΓSpecIso (.of (gRing M W1))).inv.hom x)) = _
    congr 1
    simpa using congrArg (fun k => k.hom x) (Scheme.ΓSpecIso (.of (gRing M W1))).inv_hom_id
  have iso0 : ∀ x : gRing M V, x0 ((Scheme.ΓSpecIso (.of (gRing M V))).inv.hom x) =
      AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) A M g x := by
    intro x
    change AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) A M g ((Scheme.ΓSpecIso (.of (gRing M V))).hom.hom
      ((Scheme.ΓSpecIso (.of (gRing M V))).inv.hom x)) = _
    congr 1
    simpa using congrArg (fun k => k.hom x) (Scheme.ΓSpecIso (.of (gRing M V))).inv_hom_id
  have Ξ0single : ∀ (n : M) (r : Γ((SCH).obj W1, ⊤)),
      Ξ0 (AddMonoidAlgebra.single n r) = x0 r * h (Multiplicative.ofAdd n) := by
    intro n r
    simp [Ξ0, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]
  have F0 : ∀ r : Γ((SCH).obj W1, ⊤), Ξ (((SCH).map (specPr M W1)).appTop.hom r) = x0 r := by
    intro r
    have := specPrS_appTop (B := B) (S := S) (hS := hS) (P := M) W1 r
    change Ξ ((specPrS M W1).appTop.hom r) = _
    rw [this, iso1, Ξ0single, ofAdd_zero, map_one, mul_one]
  have F1 : ∀ r : Γ((SCH).obj V, ⊤), Ξ (((SCH).map a).appTop.hom r) = algebraMap _ A r := by
    intro r
    have e : ((SCH).map a).appTop.hom r =
        ((SCH).map (specPr M W1)).appTop.hom (((SCH).map (specPr M V)).appTop.hom r) := by
      simp only [a, Functor.map_comp, Scheme.Hom.comp_appTop]
      rfl
    rw [e, F0]
    have e2 := specPrS_appTop (B := B) (S := S) (hS := hS) (P := M) V r
    change x0 ((specPrS M V).appTop.hom r) = _
    rw [e2, iso0, AddMonoidAlgebra.lift_single, ofAdd_zero, map_one, Algebra.smul_def, mul_one]
  have F2 : ∀ n, Ξ (g0 n) = g n := by
    intro n
    refine (F0 (show Γ((SCH).obj W1, ⊤) from specPt M V n)).trans ?_
    change x0 ((Scheme.ΓSpecIso (.of (gRing M V))).inv.hom _) = _
    rw [iso0, AddMonoidAlgebra.lift_single, one_smul]
    rfl
  have F3 : ∀ n, Ξ (h0 n) = h n := by
    intro n
    change Ξ ((Scheme.ΓSpecIso (.of (gRing M W1))).inv.hom _) = _
    rw [iso1, Ξ0single, map_one, one_mul]
    rfl
  have key : ∀ (c : APt (fppfO B S hS) M (op W)) (c' : Multiplicative M →* A),
      (∀ n, Ξ (c n) = c' n) → ∀ f, Ξ (specRing a c f) =
        AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) A M c' f := by
    intro c c' hc f
    induction f using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single n r =>
      rw [specRing_single, map_mul, F1, AddMonoidAlgebra.lift_single, Algebra.smul_def]
      congr 1
      exact hc _
  have hΞL : ∀ x ∈ L, Ξ x = 0 := by
    have : L ≤ RingHom.ker Ξ := by
      refine Ideal.span_le.mpr ?_
      rintro _ (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩)
      · exact (key g0 g F2 f).trans (hg f hf)
      · exact (key h0 h F3 f).trans (hh f hf)
    exact fun x hx => this hx
  intro f hf
  rw [← key (g0 * h0) (g * h) (fun n => by
    exact (map_mul Ξ (g0 n) (h0 n)).trans (congrArg₂ (· * ·) (F2 n) (F3 n)))]
  exact hΞL _ (hL f hf)

set_option synthInstance.maxHeartbeats 400000 in
/-- **Lemma 4.2, the generic stabilizer.** -/
theorem exists_generic_stabilizer [AddMonoid.FG M] [IsDomain Γ((SCH).obj V, ⊤)]
    [IsNoetherianRing Γ((SCH).obj V, ⊤)] (act : AAction (fppfO B S hS) M X)
    (hsep : Space.IsSeparatedOver B S hS X) (p : X.obj (op V)) :
    ∃ (s : Γ((SCH).obj V, ⊤)) (_ : s ≠ 0) (Z : AddSubgroup M),
      ∀ (T : BigFppfOver B S hS) (t : T ⟶ V), IsUnit (((SCH).map t).appTop.hom s) →
        ∀ h : APt (fppfO B S hS) M (op T),
          act.smul h (X.map t.op p) = X.map t.op p ↔
            ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := by
  obtain ⟨I, hI⟩ := exists_stabIdeal act hsep p
  have h1V : ∀ f ∈ I, specRing (𝟙 V) (1 : APt (fppfO B S hS) M (op V)) f = 0 := by
    refine (hI V (𝟙 V) 1).mp ?_
    exact act.one_smul _
  have h1 : ∀ f ∈ I, AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) (FractionRing Γ((SCH).obj V, ⊤)) M 1 f = 0 := by
    intro f hf
    have e : ∀ x : gRing M V, AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) (FractionRing Γ((SCH).obj V, ⊤)) M 1 x =
        algebraMap _ _ (specRing (𝟙 V) (1 : APt (fppfO B S hS) M (op V)) x) := by
      intro x
      induction x using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | single n r =>
        have e' : specRing (𝟙 V) (1 : APt (fppfO B S hS) M (op V)) (AddMonoidAlgebra.single n r) = r := by
          rw [specRing_single]
          change ((SCH).map (𝟙 V)).appTop.hom r * 1 = r
          simp
        rw [e', AddMonoidAlgebra.lift_single, Algebra.smul_def, MonoidHom.one_apply, mul_one]
    rw [e, h1V f hf, map_zero]
  obtain ⟨s, hs, Z, hZ⟩ := exists_stab_subgroup I h1
    (fun A _ _ g h hg hh => hmul_of_stabIdeal act p I hI A g h hg hh)
  refine ⟨s, hs, Z, fun T t hu h => ?_⟩
  letI : Algebra Γ((SCH).obj V, ⊤) Γ((SCH).obj T, ⊤) := ((SCH).map t).appTop.hom.toAlgebra
  have e : ∀ x : gRing M V, specRing t h x = AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) Γ((SCH).obj T, ⊤) M h x := by
    intro x
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single n r =>
      refine Eq.trans ?_ (AddMonoidAlgebra.lift_single _ _ _).symm
      rw [specRing_single, Algebra.smul_def]
      rfl
  rw [hI T t h]
  simp only [e]
  exact hZ _ hu h

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.exists_generic_stabilizer
