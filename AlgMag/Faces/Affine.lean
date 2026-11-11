/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalMiscThm124Face
import AlgMag.Faces.Regrade

/-!
# Białynicki-Birula for faces, affine part (faces-bb.md, Theorem A (ii), Step 2)

`A` is `M`-graded, `N` a magnet, `F` a face of `N` (an `AddSubmonoid`). `B = A/J_N = O(X^N)`,
`B₀ = A/J_F = O(X^F)`. The printed proof of Theorem 12.4 (p.180) is run for the **coarsened grading** of
`B` by `N̄ = q(N) ⊆ M/F^gp`: `B₀` sits in `N̄`-degree `0`, and `N̄` is sharp. The section `B₀ → B` of
`B → B₀` is `a ↦ a₀`, the `N̄`-degree `0` part. This is why one must coarsen: in the `M`-grading `B₀`
is not in degree `0`.

To cover `N` not finitely generated (with `M` finitely generated), the finiteness reduction of the
note is used: `N_c ⊆ N` finitely generated carrying the support of `B` (`Sec12Printed.exists_Nc`),
`F_c = F ∩ N_c` a face of `N_c` (`Faces.isFace_inf`), and the coarsening is by `G = F_c^gp`.
Everything the printed proof needs is packaged in `Faces.FaceData`.

## Main results

* `AlgMag.Faces.face_sym_ring`: the ring statement, `I/I²` finite projective over `B₀` and
  `Sym_{B₀}(I/I²) ≅ B` (as `B₀`-algebras; the isomorphism is `N̄`-graded by construction of the
  printed proof, not recorded in the statement, as in `Sec12SpacesThm.SymOver`).
* `AlgMag.Faces.FaceChart`, `AlgMag.Faces.faceChart_printed`: over an affine open `V` of `S`, the
  square `X^N|_V → X^N`, `X^F|_V → X^F` is cartesian along `p_{N,F}`, and `p_{N,F}|_V` is the bundle
  projection `Spec Sym_{B₀}(I/I²) → Spec B₀`, with zero section `i_{F,N}`.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism DirectSum

open scoped Classical

universe u

namespace AlgMag.Faces

open AlgMag.GB AlgMag.Sec12Printed

section Ring

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {M : Type u} [AddCommGroup M]
  (𝒜 : M → Submodule R A) [GradedAlgebra 𝒜] (N F : AddSubmonoid M) (G : AddSubgroup M)

/-- The coarsened grading `A_z = ⨁_{q(m) = z} A_m`, `q : M → M/G` (Proposition 3.31). -/
abbrev gq : (M ⧸ G) → Submodule R A := pushGrading 𝒜 (QuotientAddGroup.mk' G)

/-- The data used by the printed proof of Theorem 12.4 for a face `F` of `N`, coarsened by `G`:
`J_N ⊆ J_F`; functions of degree in `G ∖ F` vanish on `X^N`; functions of degree off `G` vanish on
`X^F`; a product of functions of degrees `m ∉ G`, `m'` with `m + m' ∈ G` vanishes on `X^N`. -/
structure FaceData : Prop where
  le : F ≤ N
  hG : ∀ m, m ∈ G → m ∉ F → ∀ a ∈ 𝒜 m, a ∈ magnetIdeal 𝒜 N
  hnG : ∀ m, m ∉ G → ∀ a ∈ 𝒜 m, a ∈ magnetIdeal 𝒜 F
  hmul : ∀ m m', m + m' ∈ G → m ∉ G → ∀ a ∈ 𝒜 m, ∀ b ∈ 𝒜 m', a * b ∈ magnetIdeal 𝒜 N

/-- `F ∩ N_c` as coarsening group: the `FaceData` holds when the functions of degree off `N_c` vanish
on `X^N`. This uses only `N_c ∩ (F ∩ N_c)^gp = F ∩ N_c` (`Faces.mem_face_of_mem_closure`). -/
theorem faceData_of_Nc {Nc : AddSubmonoid M} (hF : IsFace F N) (hle : Nc ≤ N)
    (hsupp : ∀ m, m ∉ Nc → ∀ a ∈ 𝒜 m, a ∈ magnetIdeal 𝒜 N) :
    FaceData 𝒜 N F (Fgp (F ⊓ Nc)) where
  le := hF.le
  hG := fun m hmG hmF a ha => by
    by_cases hm : m ∈ Nc
    · exact absurd (AddSubmonoid.mem_inf.1
        (mem_face_of_mem_closure (isFace_inf hF hle) hm hmG)).1 hmF
    · exact hsupp m hm a ha
  hnG := fun m hmG a ha => by
    by_cases hmF : m ∈ F
    · by_cases hm : m ∈ Nc
      · exact absurd (AddSubgroup.subset_closure (AddSubmonoid.mem_inf.2 ⟨hmF, hm⟩)) hmG
      · exact magnetIdeal_anti 𝒜 hF.le (hsupp m hm a ha)
    · exact mem_magnetIdeal_of_notMem hmF ha
  hmul := fun m m' hG hmG a ha b hb => by
    by_cases hm : m ∈ Nc
    · by_cases hm' : m' ∈ Nc
      · have h1 := mem_face_of_mem_closure (isFace_inf hF hle) (Nc.add_mem hm hm') hG
        have h2 := ((isFace_inf hF hle).mem_of_add_mem hm hm' h1).1
        exact absurd (AddSubgroup.subset_closure h2) hmG
      · exact Ideal.mul_mem_left _ _ (hsupp m' hm' b hb)
    · exact Ideal.mul_mem_right _ _ (hsupp m hm a ha)

/-- The `N̄`-degree `0` part of a homogeneous element of `M`-degree `m`. -/
lemma pr0_hom {m : M} {a : A} (ha : a ∈ 𝒜 m) :
    pr0 (gq 𝒜 G) a = if m ∈ G then a else 0 := by
  rw [pr0_of_mem _ (le_pushGrading (𝒜 := 𝒜) (QuotientAddGroup.mk' G) m ha)]
  congr 1
  exact propext (QuotientAddGroup.eq_zero_iff m)

variable {𝒜 N F G} (H : FaceData 𝒜 N F G)

include H in
lemma pr0_mul_face (a b : A) :
    Ideal.Quotient.mk (magnetIdeal 𝒜 N) (pr0 (gq 𝒜 G) (a * b)) =
      Ideal.Quotient.mk (magnetIdeal 𝒜 N) (pr0 (gq 𝒜 G) a) *
        Ideal.Quotient.mk (magnetIdeal 𝒜 N) (pr0 (gq 𝒜 G) b) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' h h' => simp only [add_mul, map_add, h, h']
  | @homogeneous u a =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add b b' h h' => simp only [mul_add, map_add, h, h']
    | @homogeneous v b =>
      have hab := SetLike.mul_mem_graded a.2 b.2
      rw [pr0_hom 𝒜 G hab, pr0_hom 𝒜 G a.2, pr0_hom 𝒜 G b.2]
      by_cases huv : u + v ∈ G
      · rw [if_pos huv]
        by_cases hu : u ∈ G
        · have hv : v ∈ G := by simpa using G.sub_mem huv hu
          rw [if_pos hu, if_pos hv, map_mul]
        · rw [if_neg hu, map_zero, zero_mul, Ideal.Quotient.eq_zero_iff_mem]
          exact H.hmul u v huv hu _ a.2 _ b.2
      · rw [if_neg huv, map_zero]
        by_cases hu : u ∈ G
        · have hv : v ∉ G := fun hv => huv (G.add_mem hu hv)
          rw [if_neg hv, map_zero, mul_zero]
        · rw [if_neg hu, map_zero, zero_mul]

/-- `a ↦ a₀ mod J_N`, a morphism of algebras. -/
noncomputable def rhoTF : A →ₐ[R] A ⧸ magnetIdeal 𝒜 N :=
  { toFun := fun a => Ideal.Quotient.mk (magnetIdeal 𝒜 N) (pr0 (gq 𝒜 G) a)
    map_one' := by
      rw [pr0_hom 𝒜 G (SetLike.GradedOne.one_mem : (1 : A) ∈ 𝒜 0), if_pos G.zero_mem, map_one]
    map_mul' := pr0_mul_face H
    map_zero' := by simp
    map_add' := fun a b => by simp
    commutes' := fun r => by
      rw [pr0_hom 𝒜 G (SetLike.algebraMap_mem_graded 𝒜 r), if_pos G.zero_mem]
      rfl }

/-- The zero section `i_{F,N}` on rings: `B₀ = A/J_F → B = A/J_N`, `[a] ↦ [a₀]`. -/
noncomputable def rhoF : (A ⧸ magnetIdeal 𝒜 F) →ₐ[R] (A ⧸ magnetIdeal 𝒜 N) :=
  Ideal.Quotient.liftₐ (magnetIdeal 𝒜 F) (rhoTF H) (by
    intro a ha
    rw [magnetIdeal] at ha
    have hle : Ideal.span (⋃ (m : M) (_ : m ∉ F), (𝒜 m : Set A)) ≤
        RingHom.ker (rhoTF H).toRingHom := by
      refine Ideal.span_le.2 ?_
      simp only [Set.iUnion_subset_iff]
      intro m hm x hx
      change Ideal.Quotient.mk (magnetIdeal 𝒜 N) (pr0 (gq 𝒜 G) x) = 0
      rw [pr0_hom 𝒜 G hx]
      split_ifs with hmG
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (H.hG m hmG hm x hx)
      · exact map_zero _
    exact hle ha)

lemma rhoF_mk (a : A) : rhoF H (Ideal.Quotient.mk _ a) =
    Ideal.Quotient.mk (magnetIdeal 𝒜 N) (pr0 (gq 𝒜 G) a) := rfl

/-- `p_{N,F}` on rings: `B → B₀` (Corollary 3.22). -/
noncomputable abbrev piF : (A ⧸ magnetIdeal 𝒜 N) →ₐ[R] (A ⧸ magnetIdeal 𝒜 F) :=
  magnetQuotMap 𝒜 H.le

include H in
lemma mk0_pr0F (a : A) :
    Ideal.Quotient.mk (magnetIdeal 𝒜 F) (pr0 (gq 𝒜 G) a) = Ideal.Quotient.mk (magnetIdeal 𝒜 F) a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' h h' => simp only [map_add, h, h']
  | @homogeneous u a =>
    rw [pr0_hom 𝒜 G a.2]
    split_ifs with hu
    · rfl
    · rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact H.hnG u hu _ a.2

/-- `p_{N,F} ∘ i_{F,N} = Id`. -/
lemma piF_rhoF (x : A ⧸ magnetIdeal 𝒜 F) : piF H (rhoF H x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [rhoF_mk]
  exact mk0_pr0F H a

include H in
lemma homogF : IsHomogeneousIdeal (gq 𝒜 G) (magnetIdeal 𝒜 N) := by
  refine isHomogeneous_span (gq 𝒜 G) fun a ha => ?_
  simp only [Set.mem_iUnion, SetLike.mem_coe] at ha
  obtain ⟨m, -, h⟩ := ha
  exact ⟨_, le_pushGrading (QuotientAddGroup.mk' G) m h⟩

/-- The `N̄`-grading of `B` (more precisely by `M/G`), as `B₀`-submodules. -/
noncomputable def gradBF (z : M ⧸ G) :
    letI := (rhoF H).toRingHom.toAlgebra
    Submodule (A ⧸ magnetIdeal 𝒜 F) (A ⧸ magnetIdeal 𝒜 N) :=
  letI := (rhoF H).toRingHom.toAlgebra
  { carrier := quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N) z
    add_mem' := fun ha hb => (quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N) z).add_mem ha hb
    zero_mem' := (quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N) z).zero_mem
    smul_mem' := by
      rintro c _ ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [Algebra.smul_def]
      change rhoF H (Ideal.Quotient.mk _ a) * _ ∈ quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N) z
      rw [rhoF_mk]
      refine ⟨pr0 (gq 𝒜 G) a * x, ?_, rfl⟩
      have h0 : pr0 (gq 𝒜 G) a ∈ gq 𝒜 G 0 := by
        rw [GradedRing.proj_apply]
        exact SetLike.coe_mem _
      have := SetLike.mul_mem_graded h0 hx
      rwa [zero_add] at this }

/-- The grading of `B` over `B₀` (copy of `Sec12Printed.gradedB`). -/
noncomputable def gradedBF :
    letI := (rhoF H).toRingHom.toAlgebra
    GradedAlgebra (gradBF H) := by
  letI := (rhoF H).toRingHom.toAlgebra
  letI Gr : GradedAlgebra (quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N)) := quotGradedAlgebra (homogF H)
  let ι : ∀ z, quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N) z →+ gradBF H z := fun z =>
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let dec : (A ⧸ magnetIdeal 𝒜 N) →+ DirectSum (M ⧸ G) fun z => gradBF H z :=
    (DirectSum.toAddMonoid fun z =>
      (DirectSum.of (fun z => gradBF H z) z).comp (ι z)).comp
      (DirectSum.decomposeAddEquiv (quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N))).toAddMonoidHom
  have hdec : ∀ (z : M ⧸ G) (x : A ⧸ magnetIdeal 𝒜 N)
      (hx : x ∈ quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N) z),
      dec x = DirectSum.of (fun z => gradBF H z) z ⟨x, hx⟩ := by
    intro z x hx
    change DirectSum.toAddMonoid _ (DirectSum.decompose (quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N)) x) = _
    rw [DirectSum.decompose_of_mem _ hx, DirectSum.toAddMonoid_of]
    rfl
  exact
    { one_mem := (Gr.one_mem : (1 : A ⧸ magnetIdeal 𝒜 N) ∈ quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N) 0)
      mul_mem := fun i j x y hx hy =>
        (Gr.mul_mem hx hy : x * y ∈ quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N) (i + j))
      toDecomposition := DirectSum.Decomposition.ofAddHom _ dec
        (by
          refine AddMonoidHom.ext fun x => ?_
          induction x using DirectSum.Decomposition.inductionOn
            (quotGrading (gq 𝒜 G) (magnetIdeal 𝒜 N)) with
          | zero => simp
          | @homogeneous z x =>
            change DirectSum.coeAddMonoidHom _ (dec x) = _
            rw [hdec z x x.2, DirectSum.coeAddMonoidHom_of]
            rfl
          | add a b ha hb =>
            simp only [map_add, AddMonoidHom.add_apply] at ha hb ⊢
            rw [ha, hb])
        (by
          refine DirectSum.addHom_ext fun z x => ?_
          change dec (DirectSum.coeAddMonoidHom _ (DirectSum.of _ z x)) = _
          rw [DirectSum.coeAddMonoidHom_of]
          exact hdec z x.1 x.2) }

/-- `p_{N,F}`, `B₀`-linear. -/
noncomputable def piBF :
    letI := (rhoF H).toRingHom.toAlgebra
    (A ⧸ magnetIdeal 𝒜 N) →ₐ[A ⧸ magnetIdeal 𝒜 F] (A ⧸ magnetIdeal 𝒜 F) :=
  letI := (rhoF H).toRingHom.toAlgebra
  { (piF H).toRingHom with
    commutes' := fun r => piF_rhoF H r }

/-- The augmentation data of the printed proof, for the coarsened grading. -/
theorem isAug_face (w : (M ⧸ G) → ℕ)
    (hw : ∀ z, ∀ a ∈ gq 𝒜 G z, Ideal.Quotient.mk (magnetIdeal 𝒜 N) a ≠ 0 → w z = 0 → z = 0)
    (hadd : ∀ u, ∀ a ∈ gq 𝒜 G u, Ideal.Quotient.mk (magnetIdeal 𝒜 N) a ≠ 0 → ∀ v, ∀ b ∈ gq 𝒜 G v,
      Ideal.Quotient.mk (magnetIdeal 𝒜 N) b ≠ 0 → w (u + v) = w u + w v) :
    letI := (rhoF H).toRingHom.toAlgebra
    letI := gradedBF H
    IsAug (gradBF H) (piBF H) w := by
  letI := (rhoF H).toRingHom.toAlgebra
  letI := gradedBF H
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro y _ ⟨a, ha, rfl⟩ hb e
    exact hw y a ha hb e
  · rintro u _ ⟨a, ha, rfl⟩ hb v _ ⟨d, hd, rfl⟩ hd'
    exact hadd u a ha hb v d hd hd'
  · rintro y hy _ ⟨a, ha, rfl⟩
    change Ideal.Quotient.mk (magnetIdeal 𝒜 F) a = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine pushGrading_induction (motive := fun a => a ∈ magnetIdeal 𝒜 F) ha
      (fun m hm b hb => ?_) (Ideal.zero_mem _) (fun a b h₁ h₂ => Ideal.add_mem _ h₁ h₂)
    have hmG : m ∉ G := fun h => hy (by rw [← hm]; exact (QuotientAddGroup.eq_zero_iff m).2 h)
    exact H.hnG m hmG b hb
  · rintro _ ⟨a, ha, rfl⟩
    change rhoF H (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a
    rw [rhoF_mk, pr0_of_mem _ ha, if_pos rfl]

end Ring

section RingMain

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {M : Type u} [AddCommGroup M]
  (𝒜 : M → Submodule R A) [GradedAlgebra 𝒜] (N F : AddSubmonoid M)

/-- A nonzero function of `M/G`-degree `z` on `X^N` has `z = q(n)` with `n ∈ N_c`. -/
theorem exists_mem_Nc {G : AddSubgroup M} {Nc : AddSubmonoid M} (hsupp : ∀ m, m ∉ Nc → ∀ a ∈ 𝒜 m, a ∈ magnetIdeal 𝒜 N)
    {z : M ⧸ G} {a : A} (ha : a ∈ gq 𝒜 G z) (hne : Ideal.Quotient.mk (magnetIdeal 𝒜 N) a ≠ 0) :
    ∃ n ∈ Nc, QuotientAddGroup.mk' G n = z := by
  by_contra hz
  refine hne (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
  exact pushGrading_induction (motive := fun a => a ∈ magnetIdeal 𝒜 N) ha
    (fun m hm b hb => hsupp m (fun hmc => hz ⟨m, hmc, hm⟩) b hb)
    (Ideal.zero_mem _) (fun a b h₁ h₂ => Ideal.add_mem _ h₁ h₂)

/-- **Theorem A (ii), ring form.** `B = A/J_N`, `B₀ = A/J_F` smooth over `R`, `N_c ⊆ N` finitely
generated carrying the support of `B`. Then `I/I²` is finite projective over `B₀` and
`Sym_{B₀}(I/I²) ≅ B`. The printed proof of Theorem 12.4 (`printed_ring_smooth`: Tags 067U, 063M,
062Z) run for the grading by `M/(F ∩ N_c)^gp`. -/
theorem face_sym_ring (hF : IsFace F N) {Nc : AddSubmonoid M} (hle : Nc ≤ N) (hfg : Nc.FG)
    (hsupp : ∀ m, m ∉ Nc → ∀ a ∈ 𝒜 m, a ∈ magnetIdeal 𝒜 N)
    (s₁ : Algebra.Smooth R (A ⧸ magnetIdeal 𝒜 N)) (s₀ : Algebra.Smooth R (A ⧸ magnetIdeal 𝒜 F)) :
    letI := (rhoF (faceData_of_Nc 𝒜 N F hF hle hsupp)).toRingHom.toAlgebra
    Module.Finite (A ⧸ magnetIdeal 𝒜 F) (Conormal (piBF (faceData_of_Nc 𝒜 N F hF hle hsupp))) ∧
      Module.Projective (A ⧸ magnetIdeal 𝒜 F) (Conormal (piBF (faceData_of_Nc 𝒜 N F hF hle hsupp))) ∧
      Nonempty (SymmetricAlgebra (A ⧸ magnetIdeal 𝒜 F)
        (Conormal (piBF (faceData_of_Nc 𝒜 N F hF hle hsupp))) ≃ₐ[A ⧸ magnetIdeal 𝒜 F]
          (A ⧸ magnetIdeal 𝒜 N)) := by
  set H := faceData_of_Nc 𝒜 N F hF hle hsupp with hH
  letI := (rhoF H).toRingHom.toAlgebra
  letI := gradedBF H
  haveI := s₁
  haveI := s₀
  obtain ⟨wZ, hw0, hwadd, -⟩ := exists_weight_nbar (isFace_inf hF hle) hfg
  have hzero : ∀ n ∈ Nc, n ∈ F ⊓ Nc → QuotientAddGroup.mk' (Fgp (F ⊓ Nc)) n = 0 :=
    fun n _ h => (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.subset_closure h)
  have hIs := isAug_face H wZ ?_ ?_
  · have hfin := Sec12SpacesThm.finite_conormal_of_smooth (R := R) (piBF H)
      (magnetQuotMap 𝒜 hF.le) (fun _ => rfl)
    have hrest := printed_ring_smooth (R := R) (magnetQuotMap 𝒜 hF.le) (fun _ => rfl) hIs
    exact ⟨hfin, hrest⟩
  · intro z a ha hne h0
    obtain ⟨n, hn, rfl⟩ := exists_mem_Nc 𝒜 N hsupp ha hne
    exact hzero n hn ((hw0 n hn).1 h0)
  · intro u a ha hne v b hb hne'
    obtain ⟨n, hn, rfl⟩ := exists_mem_Nc 𝒜 N hsupp ha hne
    obtain ⟨n', hn', rfl⟩ := exists_mem_Nc 𝒜 N hsupp hb hne'
    rw [← map_add]
    exact hwadd n hn n' hn'

end RingMain

section Chart

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]
variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))
variable (N : AddSubmonoid M) {F : AddSubmonoid M} (hF : IsFace F N)

attribute [local instance] gradedAlgebraOf

/-- `p_{N,F} : X^N → X^F` of schemes, `F` any face (copy of `Sec12Printed.faceZ`). -/
def faceZF : Zatt act N ⟶ Zatt act F :=
  (attEquiv act F _).symm (AttractorPt.ofFace hF (attEquiv act N _ (𝟙 _)))

lemma faceZF_spec {T : Over S} (w : T ⟶ Zatt act N) :
    attEquiv act F T (w ≫ faceZF act N hF) = AttractorPt.ofFace hF (attEquiv act N T w) := by
  rw [attEquiv_comp, faceZF, Equiv.apply_symm_apply]
  have : attEquiv act N T w = (attEquiv act N _ (𝟙 _)).baseChange w := by
    rw [← attEquiv_comp, Category.comp_id]
  rw [this]
  refine AttractorPt.ext ?_
  funext T₁ t a
  rfl

variable {U : S.Opens} (hU : IsAffineOpen U)

/-- The ring map `O(X^F|_U) → O(X^N|_U)` of the zero section, for given `FaceData`. -/
abbrev rhoQ (G : AddSubgroup M) (H : FaceData (gradingOf hU act) N F G) :
    Qalg act F hU →ₐ[Γ(S, U)] Qalg act N hU :=
  rhoF H

/-- The value of `X^N → X^F` on functions of degree in `F` (copy of `Sec12Printed.eval_face`). -/
lemma eval_faceF {T : Over S} (hT : LiesOver T U) (φ : AttractorPt act N T) {m : M}
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

/-- The ring form of `p_{N,F}` (copy of `Sec12Printed.localEquiv_ofFace`). -/
lemma localEquiv_ofFaceF (G : AddSubgroup M) (H : FaceData (gradingOf hU act) N F G)
    {T : Over S} (hT : LiesOver T U) (φ : AttractorPt act N T) :
    localEquiv hU act F hT (AttractorPt.ofFace hF φ) =
      (localEquiv hU act N hT φ).comp (rhoQ act N hU G H) := by
  refine AlgHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change ptX X hU T hT (AttractorPt.ofFace hF φ).toPoint a =
    localEquiv hU act N hT φ (rhoQ act N hU G H (Ideal.Quotient.mk _ a))
  change _ = ptX X hU T hT φ.toPoint (pr0 (gq (gradingOf hU act) G) a)
  induction a using DirectSum.Decomposition.inductionOn (gradingOf hU act) with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | @homogeneous m a =>
    rw [pr0_hom (gradingOf hU act) G a.2]
    split_ifs with hm
    · by_cases hmF : m ∈ F
      · exact eval_faceF act N hF hU hT φ a.2 hmF
      · rw [toPoint_kills hU act F hT _ (mem_magnetIdeal_of_notMem hmF a.2),
          toPoint_kills hU act N hT φ (H.hG m hm hmF _ a.2)]
    · rw [map_zero]
      exact toPoint_kills hU act F hT _ (H.hnG m hm _ a.2)

lemma localEquiv_rhoQ_mk (G : AddSubgroup M) (H : FaceData (gradingOf hU act) N F G)
    {T : Over S} (hT : LiesOver T U) (φ : AttractorPt act N T) (a : Aalg X U) :
    localEquiv hU act N hT φ (rhoQ act N hU G H (Ideal.Quotient.mk _ a)) =
      ptX X hU T hT φ.toPoint (pr0 (gq (gradingOf hU act) G) a) := rfl

/-- `Z_U^N → Z^N → Z^F` is `Z_U^N → Z_U^F → Z^F` (copy of `Sec12Printed.chart_square`). -/
lemma chart_squareF (V : S.affineOpens) (G : AddSubgroup M) (H : FaceData (gradingOf V.2 act) N F G) :
    iotaZ act N V ≫ faceZF act N hF = PhiMap V.2 (rhoQ act N V.2 G H) ≫ iotaZ act F V := by
  refine iAtt_cancel act F ?_
  have hT := liesOver_Zloc act N V.2
  apply (ptX X V.2 _ hT).injective
  have e₁ : iotaZ act N V ≫ faceZF act N hF ≫ iAtt act F =
      (AttractorPt.ofFace hF (attEquiv act N _ (iotaZ act N V))).toPoint := by
    rw [← faceZF_spec act N hF, toPoint_attEquiv, Category.assoc]
  have e₂ : (attEquiv act N _ (iotaZ act N V)).toPoint = PhiMap V.2 (qAlg act N V.2) ≫ iotaX X V.2 := by
    rw [toPoint_attEquiv, iotaZ_iAtt]
    rfl
  rw [Category.assoc, e₁, Category.assoc, iotaZ_iAtt]
  have e₃ := ptX_comp_iotaX (X := X) V.2 hT
    (PhiMap V.2 (rhoQ act N V.2 G H) ≫ PhiMap V.2 (qAlg act F V.2))
  refine Eq.trans ?_ (Eq.trans e₃.symm (congrArg _ (Category.assoc _ _ _)))
  refine Eq.trans ?_ (congrArg _ (PhiMap_comp V.2 (qAlg act F V.2) (rhoQ act N V.2 G H)))
  refine Eq.trans ?_ (homPhi_PhiMap V.2 _).symm
  refine AlgHom.ext fun a => ?_
  have h := DFunLike.congr_fun (localEquiv_ofFaceF act N hF V.2 G H hT (attEquiv act N _ (iotaZ act N V)))
    (Ideal.Quotient.mk _ a)
  refine Eq.trans h ?_
  refine (localEquiv_rhoQ_mk act N V.2 G H hT _ a).trans ?_
  rw [e₂]
  rw [ptX_comp_iotaX V.2 hT]
  rw [homPhi_PhiMap V.2]
  rfl

/-- The chart square is a pullback (copy of `Sec12Printed.isPullback_chart_square`). -/
theorem isPullback_chart_squareF (V : S.affineOpens) (G : AddSubgroup M)
    (H : FaceData (gradingOf V.2 act) N F G) :
    IsPullback (iotaZ act N V).left (PhiMap V.2 (rhoQ act N V.2 G H)).left (faceZF act N hF).left
      (iotaZ act F V).left := by
  have mono₁ : ∀ {T : Over S} {l l' : T ⟶ Zloc act F V.2},
      l ≫ iotaZ act F V = l' ≫ iotaZ act F V → l = l' := by
    intro T l l' h
    refine Over.OverMorphism.ext ((cancel_mono (iotaZ act F V).left).1 ?_)
    exact congrArg (fun k => k.left) h
  refine isPullback_of_over _ _ _ _ (chart_squareF act N hF V G H) (fun t u h => ?_)
    (fun l l' h _ => ?_)
  · have hT : LiesOver _ V.1 := LiesOver.of_hom u (liesOver_Zloc act F V.2)
    obtain ⟨m, hm⟩ := exists_lift_iotaZ act N V hT t
    refine ⟨m, hm, mono₁ ?_⟩
    rw [Category.assoc, ← chart_squareF act N hF V G H, ← Category.assoc, hm, h]
  · refine Over.OverMorphism.ext ((cancel_mono (iotaZ act N V).left).1 ?_)
    exact congrArg (fun k => k.left) h

/-- **Theorem A (ii)**, chart form. Over the affine open `V` of `S`: there is the zero section
`ρ : B₀ = O(X^F|_V) → B = O(X^N|_V)` such that

* the square `X^N|_V → X^N`, `X^F|_V → X^F` along `Spec ρ` and `p_{N,F}` is cartesian;
* `π : B → B₀` (restriction of functions, `p_{N,F}`) is a `B₀`-algebra retraction of `ρ`;
* `I/I² = ker π / ker π²` is finite projective over `B₀` and `Sym_{B₀}(I/I²) ≅ B` as `B₀`-algebras.

So `p_{N,F}|_V` is the bundle projection `Spec Sym_{B₀}(I/I²) → Spec B₀` and `i_{F,N}` its zero section. -/
def FaceChart {V : S.Opens} (hV : IsAffineOpen V) : Prop :=
  ∃ ρ : Qalg act F hV →ₐ[Γ(S, V)] Qalg act N hV,
    IsPullback (iotaZ act N ⟨V, hV⟩).left (PhiMap hV ρ).left (faceZF act N hF).left
      (iotaZ act F ⟨V, hV⟩).left ∧
    (letI := ρ.toRingHom.toAlgebra
     ∃ π : Qalg act N hV →ₐ[Qalg act F hV] Qalg act F hV,
      (∀ x, π (ρ x) = x) ∧
      (∀ a : Aalg X V, π (qAlg act N hV a) = qAlg act F hV a) ∧
      Module.Finite (Qalg act F hV) (Conormal π) ∧
      Module.Projective (Qalg act F hV) (Conormal π) ∧
      Nonempty (SymmetricAlgebra (Qalg act F hV) (Conormal π) ≃ₐ[Qalg act F hV] Qalg act N hV))

/-- **Theorem A (ii)** for `X` affine and smooth over `S`, `N` finitely generated or `M` finitely
generated, `F` any face of `N`. Printed route: Cor 11.2 (`smooth_Qalg`), then Tags 067U, 063M, 062Z. -/
theorem faceChart_printed [Smooth X.hom] {V : S.Opens} (hV : IsAffineOpen V)
    (h : N.FG ∨ AddGroup.FG M) : FaceChart act N hF hV := by
  obtain ⟨Nc, hle, -, hfg, hsupp⟩ := exists_Nc act N (isFace_unitsOf N) hV h
  have s₁ := smooth_Qalg act ⟨V, hV⟩ N
  have s₀ := smooth_Qalg act ⟨V, hV⟩ F
  have hr := face_sym_ring (gradingOf hV act) N F hF hle hfg hsupp s₁ s₀
  refine ⟨rhoQ act N hV _ (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp),
    isPullback_chart_squareF act N hF ⟨V, hV⟩ _ (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp), ?_⟩
  letI := (rhoQ act N hV _ (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp)).toRingHom.toAlgebra
  exact ⟨piBF (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp), piF_rhoF (faceData_of_Nc (gradingOf hV act) N F hF hle hsupp),
    fun _ => rfl, hr.1, hr.2.1, hr.2.2⟩

end Chart

end AlgMag.Faces
