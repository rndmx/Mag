/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorelRouteReal
import AlgMag.Reductive.TorusImage

/-!
# L1b: `B ∩ Z(l)` is a Borel of `Z(l)`

For a Borel `B ⊆ P(l)` (with `U(l)` a smooth connected normal solvable subgroup of `P(l)`,
the named `UCand l` of `BorelRouteReal`):

* the limit map `ρ : H → H/B`, `ρ = lim (generic point of B)`, is a Hopf map whose kernel is
  `B ⊔ Z(l)`; hence `B ∩ Z(l)` is the image of `B` under `P(l) → Z(l)`: smooth, connected,
  solvable (Tau Ceti image lemmas);
* maximality: for a Borel candidate `J ⊇ Z(l)` contained in `B ∩ Z`, the normal product
  `U(l) · J` (in `P(l)`) is a Borel candidate containing `B` (since `b = (b ρ(b)⁻¹) ρ(b)`).
-/

open Magnetism TauCeti TauCeti.Cocharacter CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgMag.Reductive.L1bProof

open AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorelRouteReal

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The generic point of `V(I)`. -/
noncomputable def gen (I : HopfIdeal k H) : WithConv (H →ₐ[k] H ⧸ I.toIdeal) :=
  WithConv.toConv (Ideal.Quotient.mkₐ k I.toIdeal)

/-- A point kills `J` when `J ≤ I`. -/
theorem gen_mem {I J : HopfIdeal k H} (h : J ≤ I) :
    gen I ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
      (CommAlgCat.of k (H ⧸ I.toIdeal)) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro x hx
  change Ideal.Quotient.mk _ x = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (h hx)

/-- Points of `H` with values in `H/I` killing `J`. -/
noncomputable abbrev QS (I J : HopfIdeal k H) :=
  CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
    (CommAlgCat.of k (H ⧸ I.toIdeal))

theorem mem_QS {I J : HopfIdeal k H} {g : WithConv (H →ₐ[k] H ⧸ I.toIdeal)} :
    g ∈ QS I J ↔ ∀ x ∈ J, g.ofConv x = 0 :=
  CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _

variable (l : H →ₐc[k] LaurentPolynomial k) {B : HopfIdeal k H}

theorem gen_mem_parabolic (hPB : P l ≤ B) : gen B ∈ parabolic (H ⧸ B.toIdeal) l := by
  have h : gen B ∈ QS B (P l) := gen_mem hPB
  rwa [QS, quotientPointsSubgroup_parabolicDefiningHopfIdeal] at h

/-- The limit `ρ = lim_{t→0} l(t) b l(t)⁻¹` of the generic point `b` of `B`. -/
noncomputable def rho (hPB : P l ≤ B) : WithConv (H →ₐ[k] H ⧸ B.toIdeal) :=
  limit _ l ⟨gen B, gen_mem_parabolic l hPB⟩

theorem rho_mem_QS_Z (hPB : P l ≤ B) : rho l hPB ∈ QS B (Z l) := by
  rw [QS, quotientPointsSubgroup_leviDefiningHopfIdeal]
  exact limit_mem_levi _

theorem rho_mem_QS_B (hPB : P l ≤ B) (hBU : B ≤ U l) : rho l hPB ∈ QS B B := by
  have hu := mul_limit_inv_mem_unipotent (gen_mem_parabolic l hPB)
  have hu' : gen B * (rho l hPB)⁻¹ ∈ QS B (U l) := by
    rw [QS, BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal]
    exact hu
  have hu'' : gen B * (rho l hPB)⁻¹ ∈ QS B B :=
    mem_QS.2 fun x hx => mem_QS.1 hu' x (hBU hx)
  have : rho l hPB = (gen B * (rho l hPB)⁻¹)⁻¹ * gen B := by group
  rw [this]
  exact mul_mem (inv_mem hu'') (gen_mem le_rfl)

theorem rho_mem_QS_sup (hPB : P l ≤ B) (hBU : B ≤ U l) : rho l hPB ∈ QS B (B ⊔ Z l) := by
  rw [QS, CommHopfAlgCat.quotientPointsSubgroup_sup]
  exact ⟨rho_mem_QS_B l hPB hBU, rho_mem_QS_Z l hPB⟩

theorem le_sup_toIdeal : B.toIdeal ≤ (B ⊔ Z l).toIdeal :=
  HopfIdeal.toIdeal_le_toIdeal.2 le_sup_left

/-- `π ∘ ρ = mk_{B ⊔ Z}`: the limit of a Levi point is itself. -/
theorem factor_rho (hPB : P l ≤ B) :
    AlgHom.mapValue (Ideal.Quotient.factorₐ k (le_sup_toIdeal l (B := B))) (rho l hPB) =
      gen (B ⊔ Z l) := by
  have hz : gen (B ⊔ Z l) ∈ levi (H ⧸ (B ⊔ Z l).toIdeal) l := by
    have h : gen (B ⊔ Z l) ∈ QS (B ⊔ Z l) (Z l) := gen_mem le_sup_right
    rwa [QS, quotientPointsSubgroup_leviDefiningHopfIdeal] at h
  rw [rho, mapValue_limit]
  convert limit_of_mem_levi hz using 3
  exact Subtype.ext (by ext; rfl)

theorem ker_rho (hPB : P l ≤ B) (hBU : B ≤ U l) :
    RingHom.ker (rho l hPB).ofConv = (B ⊔ Z l).toIdeal := by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    have h := congrArg (fun g : WithConv (H →ₐ[k] H ⧸ (B ⊔ Z l).toIdeal) => g.ofConv x)
      (factor_rho l hPB)
    simp only [AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply, gen] at h
    rw [hx, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h.symm
  · intro hx
    exact mem_QS.1 (rho_mem_QS_sup l hPB hBU) x hx

theorem counit_comp_rho (hPB : P l ≤ B) :
    (Bialgebra.counitAlgHom k (H ⧸ B.toIdeal)).comp (rho l hPB).ofConv =
      Bialgebra.counitAlgHom k H := by
  have h1 : AlgHom.mapValue (Bialgebra.counitAlgHom k (H ⧸ B.toIdeal)) (gen B) = 1 := by
    rw [AlgHom.mapValue_apply, AlgHom.convOne_def]
    congr 1
  have h := mapValue_limit (Bialgebra.counitAlgHom k (H ⧸ B.toIdeal))
    ⟨gen B, gen_mem_parabolic l hPB⟩
  have key : ∀ p : parabolic k l, (p : WithConv (H →ₐ[k] k)) = 1 → limit k l p = 1 := by
    intro p hp1
    rw [show p = 1 from Subtype.ext hp1, map_one]
  rw [key _ h1, AlgHom.mapValue_apply, AlgHom.convOne_def] at h
  exact congrArg WithConv.ofConv h

theorem comul_comp_rho (hPB : P l ≤ B) :
    (Algebra.TensorProduct.map (rho l hPB).ofConv (rho l hPB).ofConv).comp
        (Bialgebra.comulAlgHom k H) =
      (Bialgebra.comulAlgHom k (H ⧸ B.toIdeal)).comp (rho l hPB).ofConv := by
  let Q := H ⧸ B.toIdeal
  let iL : Q →ₐ[k] Q ⊗[k] Q := Algebra.TensorProduct.includeLeft
  let iR : Q →ₐ[k] Q ⊗[k] Q := Algebra.TensorProduct.includeRight
  have hp := gen_mem_parabolic l hPB
  have hgen : AlgHom.mapValue (Bialgebra.comulAlgHom k Q) (gen B) =
      AlgHom.mapValue iL (gen B) * AlgHom.mapValue iR (gen B) := by
    rw [AlgHom.mapValue_apply, AlgHom.mapValue_apply, AlgHom.mapValue_apply, gen,
      WithConv.ofConv_toConv, AlgMag.Reductive.convMul_include]
    congr 1
  have hΔ := mapValue_limit (Bialgebra.comulAlgHom k Q) ⟨gen B, hp⟩
  have hL := mapValue_limit iL ⟨gen B, hp⟩
  have hR := mapValue_limit iR ⟨gen B, hp⟩
  have hmul : AlgHom.mapValue (Bialgebra.comulAlgHom k Q) (rho l hPB) =
      AlgHom.mapValue iL (rho l hPB) * AlgHom.mapValue iR (rho l hPB) := by
    rw [rho, hΔ, hL, hR, ← map_mul]
    congr 1
    exact Subtype.ext hgen
  have h3 := AlgMag.Reductive.convMul_include (k := k) (rho l hPB).ofConv (rho l hPB).ofConv
  rw [AlgHom.mapValue_apply, AlgHom.mapValue_apply, AlgHom.mapValue_apply] at hmul
  exact (congrArg WithConv.ofConv (h3.symm.trans hmul.symm))

/-- `ρ` as a bialgebra map: the coordinate map of `B → B ∩ Z(l)`, `b ↦ lim l(t) b l(t)⁻¹`. -/
noncomputable def rhoBialg (hPB : P l ≤ B) : H →ₐc[k] H ⧸ B.toIdeal :=
  BialgHom.ofAlgHom (rho l hPB).ofConv (counit_comp_rho l hPB) (comul_comp_rho l hPB)

variable [Algebra.FiniteType k H]

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-- `ρ` as a morphism of commutative Hopf algebras `H ⟶ H/B`. -/
noncomputable def rhoHom (hPB : P l ≤ B) :
    (Hf).obj ⟶ (FiniteTypeCommHopfAlgCat.quotient Hf B).obj :=
  _root_.CommHopfAlgCat.ofHom (rhoBialg l hPB)

theorem ker_rhoHom (hPB : P l ≤ B) (hBU : B ≤ U l) :
    HopfIdeal.ker (rhoHom l hPB).hom = B ⊔ Z l := by
  refine HopfIdeal.ext fun x => ?_
  rw [← HopfIdeal.mem_toIdeal, HopfIdeal.ker_toIdeal, ← HopfIdeal.mem_toIdeal, ← ker_rho l hPB hBU]
  rfl

/-- **(A)** `B ∩ Z(l)` is smooth, connected and solvable: it is the image of `B` under `ρ`. -/
theorem isBorelCandidate_sup (hB : HopfIdeal.IsBorelCandidate k Hf B) (hPB : P l ≤ B)
    (hBU : B ≤ U l) : HopfIdeal.IsBorelCandidate k Hf (B ⊔ Z l) := by
  have hker := ker_rhoHom l hPB hBU
  have hs := hB.smooth
  have hc := hB.geometricallyConnected
  have hsol := hB.geometricallySolvable
  rw [HopfIdeal.isBorelCandidate_iff, ← hker]
  refine ⟨smoothCommHopfAlgProperty.image (rhoHom l hPB) hs,
    geometricallyConnectedCommHopfAlgProperty.image (rhoHom l hPB) hc, ?_⟩
  exact geometricallySolvablePointsCommHopfAlgProperty.of_injective_of_smooth
    (CommHopfAlgCat.imageι (rhoHom l hPB)) (CommHopfAlgCat.imageι_injective _)
    ((smoothCommHopfAlgProperty_iff _).1 hs) hsol

/-- **Key containment** `B ⊆ U(l) · J` (inside `P(l)`), for `J ⊇ Z(l)` cutting out a subgroup
containing `B ∩ Z(l)`: the generic point of `B` is `(b ρ(b)⁻¹) · ρ(b)`. -/
theorem ker_product_le (hPB : P l ≤ B) (hBU : B ≤ U l) (hU : UCand l) {J : HopfIdeal k H}
    (hJ : J ≤ B ⊔ Z l) :
    HopfIdeal.ker (CommHopfAlgCat.productMapOfNormal
      (FiniteTypeCommHopfAlgCat.quotient Hf (P l)).obj ((U l).map (mk (P l)))
      (J.map (mk (P l))) hU.isNormal).hom ≤ B.map (mk (P l)) := by
  let Hc := (Hf).obj
  let Q := (FiniteTypeCommHopfAlgCat.quotient Hf (P l)).obj
  let A := CommAlgCat.of k (H ⧸ B.toIdeal)
  let Uq := (U l).map (mk (P l))
  let Jq := J.map (mk (P l))
  have hρQS : rho l hPB ∈ QS B (B ⊔ Z l) := rho_mem_QS_sup l hPB hBU
  have hρP : ∀ x ∈ P l, (rho l hPB).ofConv x = 0 := by
    have h : rho l hPB ∈ QS B (P l) := by
      rw [QS, quotientPointsSubgroup_parabolicDefiningHopfIdeal]
      exact levi_le_parabolic (limit_mem_levi _)
    exact mem_QS.1 h
  have huU : gen B * (rho l hPB)⁻¹ ∈ QS B (U l) := by
    rw [QS, BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal]
    exact mul_limit_inv_mem_unipotent (gen_mem_parabolic l hPB)
  have huP : ∀ x ∈ P l, (gen B * (rho l hPB)⁻¹).ofConv x = 0 := fun x hx =>
    mem_QS.1 huU x (BialgHom.parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal l hx)
  have hgP : ∀ x ∈ P l, (gen B).ofConv x = 0 := mem_QS.1 (gen_mem hPB)
  let g0 := CommHopfAlgCat.liftQuotientPoint Hc (P l) A (gen B) hgP
  let r0 := CommHopfAlgCat.liftQuotientPoint Hc (P l) A (rho l hPB) hρP
  let u0 := CommHopfAlgCat.liftQuotientPoint Hc (P l) A (gen B * (rho l hPB)⁻¹) huP
  have hprod : u0 * r0 = g0 := by
    apply CommHopfAlgCat.quotientPointsHom_injective Hc (P l) A
    have e : ∀ x, CommHopfAlgCat.quotientPointsHom Hc (P l) A x =
        (CommHopfAlgCat.quotientPointsHom Hc (P l) A).hom x := fun _ => rfl
    have h1 := CommHopfAlgCat.quotientPointsHom_liftQuotientPoint Hc (P l) A _ huP
    have h2 := CommHopfAlgCat.quotientPointsHom_liftQuotientPoint Hc (P l) A _ hρP
    have h3 := CommHopfAlgCat.quotientPointsHom_liftQuotientPoint Hc (P l) A _ hgP
    rw [e, map_mul, ← e, ← e]
    change CommHopfAlgCat.quotientPointsHom Hc (P l) A
        (CommHopfAlgCat.liftQuotientPoint Hc (P l) A (gen B * (rho l hPB)⁻¹) huP) *
      CommHopfAlgCat.quotientPointsHom Hc (P l) A
        (CommHopfAlgCat.liftQuotientPoint Hc (P l) A (rho l hPB) hρP) =
      CommHopfAlgCat.quotientPointsHom Hc (P l) A
        (CommHopfAlgCat.liftQuotientPoint Hc (P l) A (gen B) hgP)
    rw [h1, h2, h3, inv_mul_cancel_right]
  have hu0 : ∀ x ∈ Uq, u0.ofConv x = 0 := by
    have : u0 ∈ CommHopfAlgCat.quotientPointsSubgroup Q Uq A := by
      refine (CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff
        (CommHopfAlgCat.mkQuotient Hc (P l)) (U l) A u0).2 ?_
      change CommHopfAlgCat.quotientPointsHom Hc (P l) A u0 ∈ _
      rw [CommHopfAlgCat.quotientPointsHom_liftQuotientPoint]
      exact huU
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1 this
  have hr0 : ∀ x ∈ Jq, r0.ofConv x = 0 := by
    have : r0 ∈ CommHopfAlgCat.quotientPointsSubgroup Q Jq A := by
      refine (CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff
        (CommHopfAlgCat.mkQuotient Hc (P l)) J A r0).2 ?_
      change CommHopfAlgCat.quotientPointsHom Hc (P l) A r0 ∈ _
      rw [CommHopfAlgCat.quotientPointsHom_liftQuotientPoint]
      exact mem_QS.2 fun x hx => mem_QS.1 hρQS x (hJ hx)
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1 this
  let a := CommHopfAlgCat.liftQuotientPoint Q Uq A u0 hu0
  let b := CommHopfAlgCat.liftQuotientPoint Q Jq A r0 hr0
  have : IsMonHom.Normal (CommHopfAlgCat.quotientGrpObjInclusion Q Uq) :=
    (CommHopfAlgCat.quotientGrpObjInclusion_normal_iff Q Uq).2 hU.isNormal
  let q := CartesianMonoidalCategory.lift
    ((CommHopfAlgCat.grpObjPointsMulEquiv (CommHopfAlgCat.quotient Q Uq) (Opposite.op A)).symm a)
    ((CommHopfAlgCat.grpObjPointsMulEquiv (CommHopfAlgCat.quotient Q Jq) (Opposite.op A)).symm b)
  have hq := CommHopfAlgCat.mapPointsFunctor_app_grpObjPointsMulEquiv_normalSemidirect Q Uq Jq
    hU.isNormal A (CommHopfAlgCat.normalSemidirectMultiplicationCoordinateMap Q Uq Jq hU.isNormal)
    (CommHopfAlgCat.grpObjMap_normalSemidirectMultiplicationCoordinateMap Q Uq Jq hU.isNormal) q
  simp only [q, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd,
    MulEquiv.apply_symm_apply, a, b] at hq
  have e1 : (ConcreteCategory.hom (CommHopfAlgCat.quotientPointsHom Q Uq A))
      (CommHopfAlgCat.liftQuotientPoint Q Uq A u0 hu0) = u0 :=
    CommHopfAlgCat.quotientPointsHom_liftQuotientPoint Q Uq A u0 hu0
  have e2 : (ConcreteCategory.hom (CommHopfAlgCat.quotientPointsHom Q Jq A))
      (CommHopfAlgCat.liftQuotientPoint Q Jq A r0 hr0) = r0 :=
    CommHopfAlgCat.quotientPointsHom_liftQuotientPoint Q Jq A r0 hr0
  rw [e1, e2, hprod] at hq
  intro x hx
  have hx0 : (CommHopfAlgCat.productMapOfNormal Q Uq Jq hU.isNormal).hom x = 0 := by
    rw [← HopfIdeal.mem_toIdeal, HopfIdeal.ker_toIdeal] at hx
    exact hx
  have hφ : (CommHopfAlgCat.normalSemidirectMultiplicationCoordinateMap Q Uq Jq
      hU.isNormal).hom x = 0 := by
    rw [← CommHopfAlgCat.productMapOfNormal_comp_normalSemidirectProductIso_hom,
      _root_.CommHopfAlgCat.hom_comp]
    simp [hx0]
  have hg : g0.ofConv x = 0 := by
    rw [← hq, CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply, hφ, map_zero]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y ∈ B := by
    rw [CommHopfAlgCat.liftQuotientPoint_mk] at hg
    exact HopfIdeal.mem_toIdeal.1 (Ideal.Quotient.eq_zero_iff_mem.1 hg)
  exact HopfIdeal.mem_map_of_mem _ hy

/-- Borel candidates of `H/S` are the Borel candidates of `H` pulled back. -/
theorem cand_quot_iff (S : HopfIdeal k H) (I : HopfIdeal k (H ⧸ S.toIdeal)) :
    HopfIdeal.IsBorelCandidate k (FiniteTypeCommHopfAlgCat.quotient Hf S) I ↔
      HopfIdeal.IsBorelCandidate k Hf
        (I.comapOfSurjective (mk S) (Bialgebra.Quotient.mkBialgHom_surjective _)) :=
  (HopfIdeal.isBorelCandidate_comapOfSurjective_iff (FiniteTypeCommHopfAlgCat.mkQuotient Hf S)
    (CommHopfAlgCat.mkQuotient_surjective _ _) I).symm

omit [Algebra.FiniteType k H] in
theorem le_comap (S : HopfIdeal k H) (I : HopfIdeal k (H ⧸ S.toIdeal)) :
    S ≤ I.comapOfSurjective (mk S) (Bialgebra.Quotient.mkBialgHom_surjective _) := by
  have h := HopfIdeal.comapOfSurjective_mono (mk S)
    (Bialgebra.Quotient.mkBialgHom_surjective S.toIdeal) (bot_le : ⊥ ≤ I)
  rwa [HopfIdeal.comapOfSurjective_bot, HopfIdeal.kerOfSurjective_mkBialgHom] at h

omit [Algebra.FiniteType k H] in
theorem P_le_Z : P l ≤ Z l := by
  rw [Z_eq]
  exact le_sup_left

/-- **(B) Maximality.** A Borel candidate `J ⊇ Z(μ)` of `G` with `V(J) ⊇ B ∩ Z(μ)` contains `B`. -/
theorem le_of_candidate (hB : HopfIdeal.IsBorelOverAlgClosed k Hf B) (hPB : P l ≤ B)
    (hBU : B ≤ U l) (hU : UCand l) {J : HopfIdeal k H} (hJc : HopfIdeal.IsBorelCandidate k Hf J)
    (hZJ : Z l ≤ J) (hJ : J ≤ B ⊔ Z l) : B ≤ J := by
  have hPJ : P l ≤ J := (P_le_Z l).trans hZJ
  have hsurj := Bialgebra.Quotient.mkBialgHom_surjective (R := k) (H := H) (P l).toIdeal
  have hJq : HopfIdeal.IsBorelCandidate k (FiniteTypeCommHopfAlgCat.quotient Hf (P l))
      (J.map (mk (P l))) := by
    rw [cand_quot_iff, HopfIdeal.comapOfSurjective_map_mkBialgHom hPJ]
    exact hJc
  have hK := hJq.productOfNormal hU
  have hBq := hB.map_of_le hPB
  have h1 : B.map (mk (P l)) ≤ J.map (mk (P l)) :=
    (hBq.2.2 hK (ker_product_le l hPB hBU hU hJ)).trans
      (CommHopfAlgCat.ker_productMapOfNormal_le_right _ _ _ hU.isNormal)
  have h2 := HopfIdeal.comapOfSurjective_mono (mk (P l)) hsurj h1
  rwa [HopfIdeal.comapOfSurjective_map_mkBialgHom hPB,
    HopfIdeal.comapOfSurjective_map_mkBialgHom hPJ] at h2

/-- **L1b**, given the named `UCand` (also an input of `realBridge`). -/
theorem l1b (hU : ∀ l : H →ₐc[k] LaurentPolynomial k, UCand l) : L1b (k := k) (H := H) := by
  intro B l hB hPB
  have hBor := hB.2.1 rfl
  have hBU := U_le_of_borel_le_parabolic l hBor hPB (hU l)
  have hsurj := Bialgebra.Quotient.mkBialgHom_surjective (R := k) (H := H) (Z l).toIdeal
  have hcomap : ((B ⊔ Z l).map (mk (Z l))).comapOfSurjective (mk (Z l)) hsurj = B ⊔ Z l :=
    HopfIdeal.comapOfSurjective_map_mkBialgHom le_sup_right
  refine ⟨le_sup_right, fun hZ => ?_, hBor.1, ?_, ?_⟩
  · rw [hZ, sup_bot_eq]
    exact hBor
  · rw [cand_quot_iff, hcomap]
    exact isBorelCandidate_sup l hBor.2.1 hPB hBU
  · intro I hI hIle
    have hJc := (cand_quot_iff (Z l) I).1 hI
    have hJle := HopfIdeal.comapOfSurjective_mono (mk (Z l)) hsurj hIle
    rw [hcomap] at hJle
    have hBJ := le_of_candidate l hBor hPB hBU (hU l) hJc (le_comap (Z l) I) hJle
    exact (HopfIdeal.map_le_iff_le_comapOfSurjective hsurj).2 (sup_le hBJ (le_comap (Z l) I))

/-- The real bridge with `L1b` discharged: only `UCand` remains named. -/
noncomputable def realBridge' (hU : ∀ l : H →ₐc[k] LaurentPolynomial k, UCand l) :
    BorelBridge k H :=
  realBridge hU (l1b hU)

end AlgMag.Reductive.L1bProof
