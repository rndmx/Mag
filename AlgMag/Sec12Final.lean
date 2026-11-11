/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12PrintedThm
import AlgMag.Sec8Theorem83
import AlgMag.Sec14Remaining
import AlgMag.Sec15General
import Mathlib.AlgebraicGeometry.AffineSpace
import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Algebraic Magnetism, §12 and Remark 14.2: printed forms

Mayeux, *Algebraic Magnetism*.

* `AlgMag.Sec12Printed.thm124_general`, `AlgMag.Sec12Printed.thm124_affineSpace`: **Theorem 12.4** for
  `N` not finitely generated, and its local form `𝔸ⁿ`. The step "a stable open containing the vertex
  contains `𝔸(N)_T`" is `AlgMag.Sec12Printed.exists_att_of_vertex_general`.
* `AlgMag.prop121_printed`: **Proposition 12.1** with the topology of `|X|`.
* `AlgMag.prop122_ii_printed`: **Proposition 12.2 (ii)** with its hypotheses.
* `AlgMag.exists_indHom_term`, `AlgMag.indHom_ext`, `AlgMag.exists_indHom_of_compatible`,
  `AlgMag.isIndAlgebraicSpace_fibreProduct`: **Remark 14.2**.
-/

section PartP1

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

universe u

namespace AlgMag.Sec12Printed

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

section GenericPoint

variable {K : Type u} [Field K] {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

/-- `X^n ↦ X^n` for `a₀(n) ≠ 0`, `X^n ↦ 0` otherwise. -/
def suppHom (a₀ : Multiplicative N →* K) : AddMonoidAlgebra K N →ₐ[K] AddMonoidAlgebra K M :=
  AddMonoidAlgebra.lift K (AddMonoidAlgebra K M) N
    { toFun := fun n => if a₀ n = 0 then 0 else AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M) 1
      map_one' := by
        rw [if_neg (by simp)]
        rfl
      map_mul' := fun a b => by
        by_cases ha : a₀ a = 0
        · simp [ha]
        by_cases hb : a₀ b = 0
        · simp [hb]
        rw [if_neg ha, if_neg hb, if_neg (by simpa [map_mul] using ⟨ha, hb⟩),
          AddMonoidAlgebra.single_mul_single]
        simp }

lemma suppHom_single (a₀ : Multiplicative N →* K) (n : N) (c : K) :
    suppHom N a₀ (AddMonoidAlgebra.single n c) =
      if a₀ (Multiplicative.ofAdd n) = 0 then 0 else AddMonoidAlgebra.single (n : M) c := by
  rw [suppHom, AddMonoidAlgebra.lift_single]
  by_cases h : a₀ (Multiplicative.ofAdd n) = 0
  · simp [h]
  · simp [h, AddMonoidAlgebra.smul_single]

/-- **The field-valued point of `𝔸(N)` with the support of `a₀`**, generizing the vertex. This
replaces the weight `w : N → ℕ` of Ogus, which exists only for `N` finitely generated. `e` is any
`K`-point of `𝔸(N)` killing the `n` with `a₀(n) = 0`. There are an algebraically closed `L ⊇ K`, and
a point `ξ` of `𝔸(N)_L` with the same support as `a₀`, a specialization of which is `e`, such that `a₀`
is the translate of `ξ` by a point `χ` of `D(M)(L)`. -/
theorem exists_generic_point (a₀ : Multiplicative N →* K) (e : AddMonoidAlgebra K N →ₐ[K] K)
    (he : ∀ n : N, a₀ (Multiplicative.ofAdd n) = 0 → e (AddMonoidAlgebra.single n 1) = 0) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L)
      (ξ : AddMonoidAlgebra K N →+* L) (χ : Multiplicative M →* Lˣ),
      (∀ c, ξ (algebraMap K _ c) = ι c) ∧ (∀ t, ξ t = 0 → e t = 0) ∧
      ∀ n : N, ι (a₀ (Multiplicative.ofAdd n)) =
        (χ (Multiplicative.ofAdd (n : M)) : L) * ξ (AddMonoidAlgebra.single n 1) := by
  let B := AddMonoidAlgebra K M
  let r := suppHom N a₀
  -- a linear form on `K[M]` through which `e` factors
  let g : M → K := fun m => if h : m ∈ N then e (AddMonoidAlgebra.single ⟨m, h⟩ 1) else 0
  let e' : B →ₗ[K] K := (Finsupp.linearCombination K g).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap
  have he' : ∀ t, e' (r t) = e t := by
    intro t
    induction t using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single n c =>
      change e' (suppHom N a₀ _) = _
      rw [suppHom_single]
      have hs : AddMonoidAlgebra.single n c = c • AddMonoidAlgebra.single n (1 : K) := by
        simp [AddMonoidAlgebra.smul_single]
      by_cases h : a₀ (Multiplicative.ofAdd n) = 0
      · rw [if_pos h, map_zero, hs, map_smul, he n h, smul_zero]
      · rw [if_neg h, hs, map_smul]
        change Finsupp.linearCombination K g ((AddMonoidAlgebra.single (n : M) c).coeff) =
          c • e (AddMonoidAlgebra.single n 1)
        rw [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
        simp [g]
  let P : Ideal (AddMonoidAlgebra K N) := RingHom.ker e.toRingHom
  have hP : P.IsPrime := RingHom.ker_isPrime _
  let Tm : Submonoid B := P.primeCompl.map (r : AddMonoidAlgebra K N →* B)
  have hdisj : Disjoint ((⊥ : Ideal B) : Set B) (Tm : Set B) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨t, ht, rfl⟩
    have h0 : r t = 0 := hx
    exact ht (show e t = 0 by rw [← he', h0, map_zero])
  obtain ⟨q, hq, -, hqd⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  let F := FractionRing (B ⧸ q)
  let L : Type u := AlgebraicClosure F
  let π : B →+* L := (algebraMap F L).comp ((algebraMap (B ⧸ q) F).comp (Ideal.Quotient.mk q))
  have hπ : ∀ b, π b = 0 → b ∈ q := by
    intro b hb
    have h1 : algebraMap (B ⧸ q) F (Ideal.Quotient.mk q b) = 0 :=
      (map_eq_zero_iff _ (algebraMap F L).injective).1 hb
    have h2 : Ideal.Quotient.mk q b = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  have hunit : ∀ m : M, π (AddMonoidAlgebra.single m 1) ≠ 0 := by
    intro m h0
    have : π (AddMonoidAlgebra.single m 1) * π (AddMonoidAlgebra.single (-m) 1) = 1 := by
      rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
      exact map_one π
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  let ι : K →+* L := π.comp (algebraMap K B)
  let ξ : AddMonoidAlgebra K N →+* L := π.comp (r : AddMonoidAlgebra K N →+* B)
  have hξ : ∀ n : N, a₀ (Multiplicative.ofAdd n) ≠ 0 →
      ξ (AddMonoidAlgebra.single n 1) = π (AddMonoidAlgebra.single (n : M) 1) := by
    intro n hn
    change π (suppHom N a₀ _) = _
    rw [suppHom_single, if_neg hn]
  let G : AddSubmonoid M :=
    { carrier := {m | ∃ h : m ∈ N, a₀ (Multiplicative.ofAdd ⟨m, h⟩) ≠ 0}
      zero_mem' := ⟨N.zero_mem, by
        have : a₀ 1 = 1 := map_one a₀
        exact fun h => one_ne_zero (this.symm.trans h)⟩
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨N.add_mem ha hb, ?_⟩
        have : a₀ (Multiplicative.ofAdd ⟨a + b, N.add_mem ha hb⟩) =
            a₀ (Multiplicative.ofAdd ⟨a, ha⟩) * a₀ (Multiplicative.ofAdd ⟨b, hb⟩) := by
          rw [← map_mul]
          rfl
        rw [this]
        exact mul_ne_zero ha' hb' }
  have hιne : ∀ c : K, c ≠ 0 → ι c ≠ 0 := fun c hc => (map_ne_zero ι).2 hc
  let ξu : Multiplicative G →* Lˣ :=
    { toFun := fun g =>
        Units.mk0 (ι (a₀ (Multiplicative.ofAdd ⟨_, (Multiplicative.toAdd g).2.choose⟩)) /
          π (AddMonoidAlgebra.single ((Multiplicative.toAdd g : G) : M) 1))
          (div_ne_zero (hιne _ (Multiplicative.toAdd g).2.choose_spec) (hunit _))
      map_one' := by
        refine Units.ext ?_
        have e1 : a₀ (Multiplicative.ofAdd ⟨((Multiplicative.toAdd (1 : Multiplicative G) : G) : M),
            (Multiplicative.toAdd (1 : Multiplicative G)).2.choose⟩) = 1 := map_one a₀
        have e2 : π (AddMonoidAlgebra.single ((Multiplicative.toAdd (1 : Multiplicative G) : G) : M) 1) = 1 :=
          map_one π
        simp only [Units.val_mk0, Units.val_one]
        rw [e1, e2, map_one, div_one]
      map_mul' := fun a b => by
        refine Units.ext ?_
        simp only [Units.val_mk0, Units.val_mul]
        have e1 : a₀ (Multiplicative.ofAdd ⟨((Multiplicative.toAdd (a * b) : G) : M),
            (Multiplicative.toAdd (a * b)).2.choose⟩) =
            a₀ (Multiplicative.ofAdd ⟨_, (Multiplicative.toAdd a).2.choose⟩) *
            a₀ (Multiplicative.ofAdd ⟨_, (Multiplicative.toAdd b).2.choose⟩) := by
          rw [← map_mul]
          rfl
        have e2 : π (AddMonoidAlgebra.single ((Multiplicative.toAdd (a * b) : G) : M) 1) =
            π (AddMonoidAlgebra.single ((Multiplicative.toAdd a : G) : M) 1) *
            π (AddMonoidAlgebra.single ((Multiplicative.toAdd b : G) : M) 1) := by
          rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [e1, e2, map_mul, mul_div_mul_comm] }
  have hdiv : ∀ (u : Lˣ) (n : ℕ), n ≠ 0 → ∃ v : Lˣ, v ^ n = u := by
    intro u n hn
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  obtain ⟨χ, hχ⟩ := exists_ext_units hdiv G ξu
  refine ⟨L, inferInstance, inferInstance, ι, ξ, χ, ?_, ?_, ?_⟩
  · intro c
    change π (r (algebraMap K _ c)) = π (algebraMap K B c)
    rw [AlgHom.commutes]
  · intro t ht
    by_contra hne
    have hm : r t ∈ (Tm : Set B) := ⟨t, hne, rfl⟩
    exact Set.disjoint_left.1 hqd (hπ _ ht) hm
  · intro n
    by_cases h : a₀ (Multiplicative.ofAdd n) = 0
    · have : ξ (AddMonoidAlgebra.single n 1) = 0 := by
        change π (suppHom N a₀ _) = _
        rw [suppHom_single, if_pos h, map_zero]
      rw [h, this, map_zero, mul_zero]
    · let g : G := ⟨n, n.2, h⟩
      have e1 := hχ g
      rw [hξ n h]
      have e2 : ((χ (Multiplicative.ofAdd (n : M))) : L) =
          ι (a₀ (Multiplicative.ofAdd ⟨_, g.2.choose⟩)) / π (AddMonoidAlgebra.single (n : M) 1) :=
        congrArg Units.val e1
      rw [e2, div_mul_cancel₀ _ (hunit _)]

end GenericPoint

end AlgMag.Sec12Printed

end PartP1

section PartP2

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

universe u

namespace AlgMag.Sec12Printed

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

attribute [local instance] gradedAlgebraOf

section VertexGeneral

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] {X W : Over S}
  {aX : AAction (overO S) M (yoneda.obj X)} {aW : AAction (overO S) M (yoneda.obj W)} (j : W ⟶ X)
  [IsOpenImmersion j.left]
  (hj : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ W), sm aW h x ≫ j = sm aX h (x ≫ j))
  {N : AddSubmonoid M} {F : AddSubgroup M} (hF : IsFace F.toAddSubmonoid N)

include hj in
/-- **The step "a stable open containing the vertex contains `𝔸(N)_T`" of the proof of Theorem 12.4**,
for `N` not finitely generated, over an algebraically
closed field: a stable open containing the vertex of `𝔸(N)_K → X` contains the whole image. No weight
`N → ℕ` is needed: every point of `𝔸(N)_K` is a translate of a generization of the vertex
(`exists_generic_point`). -/
theorem mem_range_field_general {T : Over S} (φ : AttractorPt aX N T) (u : T ⟶ W)
    (hu : (AttractorPt.ofFace hF φ).toPoint = u ≫ j) (K : Type u) [Field K] [IsAlgClosed K]
    (tk : Spec (CommRingCat.of K) ⟶ T.left) (a₀ : APt (overO S) N (op (spO (T := T) tk)))
    (x : Spec (CommRingCat.of K)) :
    (φ.app (T' := spO (T := T) tk) (Over.homMk tk rfl) a₀).left x ∈ Set.range j.left := by
  classical
  let Pk : CommRingCat.{u} := CommRingCat.of K
  let Tk : Over S := spO (T := T) tk
  let eK : Γ(Tk.left, ⊤) ≃+* K := (Scheme.ΓSpecIso Pk).commRingCatIsoToRingEquiv
  let a₁ : Multiplicative N →* K := (eK : Γ(Tk.left, ⊤) →* K).comp a₀
  have hne : ∀ n : N, (n : M) ∈ F → a₁ (Multiplicative.ofAdd n) ≠ 0 := by
    intro n hn h0
    let n' : N := ⟨-(n : M), hF.le (F.neg_mem hn)⟩
    have : a₁ (Multiplicative.ofAdd n) * a₁ (Multiplicative.ofAdd n') = 1 := by
      rw [← map_mul, ← map_one a₁]
      congr 1
      apply Multiplicative.toAdd.injective
      exact Subtype.ext (add_neg_cancel _)
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hfm : ∀ a b : N, ((a + b : N) : M) ∈ F ↔ ((a : M) ∈ F ∧ (b : M) ∈ F) := fun a b =>
    ⟨fun h => hF.mem_of_add_mem a.2 b.2 h, fun h => F.add_mem h.1 h.2⟩
  let ch : Multiplicative N →* K :=
    { toFun := fun n => if ((Multiplicative.toAdd n : N) : M) ∈ F then 1 else 0
      map_one' := if_pos F.zero_mem
      map_mul' := fun a b => by
        have := hfm (Multiplicative.toAdd a) (Multiplicative.toAdd b)
        change ite (((Multiplicative.toAdd a + Multiplicative.toAdd b : N) : M) ∈ F) _ _ = _
        rw [if_congr this rfl rfl]
        change _ = ite _ _ _ * ite _ _ _
        by_cases ha : ((Multiplicative.toAdd a : N) : M) ∈ F <;>
          by_cases hb : ((Multiplicative.toAdd b : N) : M) ∈ F <;> simp [ha, hb] }
  let e : AddMonoidAlgebra K N →ₐ[K] K := AddMonoidAlgebra.lift K K N ch
  have he1 : ∀ n : N, e (AddMonoidAlgebra.single n 1) = if (n : M) ∈ F then 1 else 0 := by
    intro n
    rw [AddMonoidAlgebra.lift_single, one_smul]
    rfl
  obtain ⟨L, _, _, ι, ξ, χ, hξC, hξe, hχ⟩ := exists_generic_point N a₁ e (fun n h0 => by
    rw [he1, if_neg]
    exact fun hn => hne n hn h0)
  let R : CommRingCat.{u} := CommRingCat.of (AddMonoidAlgebra K N)
  let PL : CommRingCat.{u} := CommRingCat.of L
  let fC : Pk ⟶ R := CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K N))
  let fe : R ⟶ Pk := CommRingCat.ofHom e.toRingHom
  let fξ : R ⟶ PL := CommRingCat.ofHom ξ
  have hfe : fC ≫ fe = 𝟙 _ :=
    CommRingCat.hom_ext (RingHom.ext fun c => e.commutes c)
  let tP : Spec R ⟶ T.left := Spec.map fC ≫ tk
  let TP : Over S := spO (T := T) tP
  let p : TP ⟶ Tk := spM (T := T) fC tk
  let i₀ : Tk ⟶ TP := Over.homMk (Spec.map fe) (by
    change Spec.map fe ≫ (Spec.map fC ≫ tk) ≫ T.hom = tk ≫ T.hom
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, hfe, Spec.map_id, Category.id_comp])
  have hi₀p : i₀ ≫ p = 𝟙 _ := by
    refine Over.OverMorphism.ext ?_
    change Spec.map fe ≫ Spec.map fC = 𝟙 _
    rw [← Spec.map_comp, hfe, Spec.map_id]
  let TL : Over S := spO (T := T) (Spec.map fξ ≫ tP)
  let η : TL ⟶ TP := spM (T := T) fξ tP
  let s : Tk ⟶ T := Over.homMk tk rfl
  let eL : Γ(TL.left, ⊤) ≃+* L := (Scheme.ΓSpecIso PL).commRingCatIsoToRingEquiv
  -- the universal point of `𝔸(N)`
  let c : APt (overO S) N (op TP) :=
    { toFun := fun n => (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
      map_one' := map_one (Scheme.ΓSpecIso R).inv.hom
      map_mul' := fun a b => by
        exact (congrArg (Scheme.ΓSpecIso R).inv.hom (by
          rw [AddMonoidAlgebra.single_mul_single, mul_one]
          rfl)).trans (map_mul (Scheme.ΓSpecIso R).inv.hom _ _) }
  have hc₀ : APt.res i₀.op c = APt.faceExt hF 1 := by
    refine MonoidHom.ext fun n => ?_
    have h := congrArg (fun k => k.hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) (1 : K)))
      (Scheme.ΓSpecIso_inv_naturality fe)
    have h' : (Scheme.ΓSpecIso Pk).inv.hom (e (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)) =
        i₀.left.appTop.hom (c n) := h
    refine h'.symm.trans ?_
    rw [he1]
    by_cases hn : ((Multiplicative.toAdd n : N) : M) ∈ F
    · rw [if_pos hn, APt.faceExt_pos hF 1 hn, map_one]
      rfl
    · rw [if_neg hn, APt.faceExt_neg hF 1 hn, map_zero]
      rfl
  let y := φ.app (p ≫ s) c
  have hy₀ : i₀ ≫ y = s ≫ u ≫ j := by
    have e₁ : i₀ ≫ y = φ.app (i₀ ≫ p ≫ s) (APt.res i₀.op c) := (φ.naturality i₀ (p ≫ s) c).symm
    have e₂ : i₀ ≫ p ≫ s = s := by rw [← Category.assoc, hi₀p, Category.id_comp]
    rw [e₁, e₂, hc₀]
    change (AttractorPt.ofFace hF φ).app s 1 = _
    have e₃ := (AttractorPt.ofFace hF φ).naturality s (𝟙 T) 1
    have hone : APt.res (𝒪 := overO S) (P := F.toAddSubmonoid) s.op 1 = 1 := by
      ext q
      simp
    rw [hone, Category.comp_id] at e₃
    refine e₃.trans ?_
    change s ≫ (AttractorPt.ofFace hF φ).toPoint = _
    rw [hu]
  let pL : Spec PL := ⟨⊥, Ideal.isPrime_bot⟩
  have hgen : y.left (η.left pL) ∈ Set.range j.left := by
    have hopen : IsOpen (y.left ⁻¹' Set.range j.left) :=
      (j.left.isOpenEmbedding.isOpen_range).preimage y.left.continuous
    have hsp : (η.left pL) ⤳ (i₀.left x) := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      intro t ht
      have h0 : ξ t = 0 := ht
      have h1 : e t = 0 := hξe t h0
      change fe.hom t ∈ (x : PrimeSpectrum K).asIdeal
      have h2 : fe.hom t = 0 := h1
      rw [h2]
      exact Ideal.zero_mem _
    refine hsp.mem_open hopen ?_
    rw [Set.mem_preimage]
    have : y.left (i₀.left x) = (i₀ ≫ y).left x := by
      rw [Over.comp_left, Scheme.Hom.comp_apply]
    rw [this, hy₀, Over.comp_left, Over.comp_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  -- the translation
  let χu : Multiplicative M →* Γ(TL.left, ⊤)ˣ := (Units.map (eL.symm : L →* Γ(TL.left, ⊤))).comp χ
  let χ' : APt (overO S) M (op TL) := (Units.coeHom _).comp χu
  let χi : APt (overO S) M (op TL) := (Units.coeHom _).comp χu⁻¹
  have hχi : χi * χ' = 1 := by
    refine MonoidHom.ext fun m => ?_
    change (((χu⁻¹) m : Γ(TL.left, ⊤)ˣ) : Γ(TL.left, ⊤)) * (χu m : Γ(TL.left, ⊤)ˣ) = 1
    rw [MonoidHom.inv_apply, Units.inv_mul]
  let q : TL ⟶ Tk := η ≫ p
  have hqa : APt.res q.op a₀ = APt.toMagnet N χ' * APt.res η.op c := by
    refine MonoidHom.ext fun n => ?_
    let n₀ : N := Multiplicative.toAdd n
    have h1 : η.left.appTop.hom (c n) = eL.symm (ξ (AddMonoidAlgebra.single n₀ 1)) :=
      (congrArg (fun k => k.hom (AddMonoidAlgebra.single n₀ (1 : K)))
        (Scheme.ΓSpecIso_inv_naturality fξ)).symm
    have h2 : p.left.appTop.hom (a₀ n) = (Scheme.ΓSpecIso R).inv.hom (fC.hom (a₁ n)) := by
      have ha : a₀ n = (Scheme.ΓSpecIso Pk).inv.hom (a₁ n) := (eK.symm_apply_apply (a₀ n)).symm
      rw [ha]
      exact (congrArg (fun k => k.hom (a₁ n)) (Scheme.ΓSpecIso_inv_naturality fC)).symm
    have h3 : η.left.appTop.hom ((Scheme.ΓSpecIso R).inv.hom (fC.hom (a₁ n))) =
        eL.symm (ξ (fC.hom (a₁ n))) :=
      (congrArg (fun k => k.hom (fC.hom (a₁ n))) (Scheme.ΓSpecIso_inv_naturality fξ)).symm
    have h4 : ξ (fC.hom (a₁ n)) = (χ (Multiplicative.ofAdd (n₀ : M)) : L) * ξ (AddMonoidAlgebra.single n₀ 1) :=
      (hξC _).trans (hχ n₀)
    change (η ≫ p).left.appTop.hom (a₀ n) =
      eL.symm (χ (Multiplicative.ofAdd (n₀ : M)) : L) * η.left.appTop.hom (c n)
    rw [Over.comp_left, Scheme.Hom.comp_appTop]
    change η.left.appTop.hom (p.left.appTop.hom (a₀ n)) = _
    rw [h2, h3, h4, h1, map_mul]
  let y' : TL ⟶ X := q ≫ φ.app s a₀
  have hy' : y' = sm aX χ' (η ≫ y) := by
    have e₂ := φ.naturality q s a₀
    have e₁ : y' = φ.app (q ≫ s) (APt.res q.op a₀) := e₂.symm
    rw [e₁, hqa]
    refine (φ.equivariant _ χ' _).trans ?_
    congr 1
    have e₃ := φ.naturality η (p ≫ s) c
    rw [show q ≫ s = η ≫ p ≫ s from Category.assoc _ _ _]
    exact e₃
  have hsub : Subsingleton (Spec PL) := spec_field_subsingleton L
  have hrange : Set.range (η ≫ y).left ⊆ Set.range j.left := by
    rintro _ ⟨b, rfl⟩
    have : b = pL := hsub.elim _ _
    rw [this, Over.comp_left, Scheme.Hom.comp_apply]
    exact hgen
  let v : TL ⟶ W := Over.homMk (IsOpenImmersion.lift j.left _ hrange) (by
    have e := Over.w j
    rw [← e, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (η ≫ y))
  have hv : v ≫ j = η ≫ y := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hy'j : y' = sm aW χ' v ≫ j := by
    rw [hj, hv, hy']
  have hq : q.left pL = x := (spec_field_subsingleton K).elim _ _
  have : (φ.app s a₀).left x = y'.left pL := by
    change _ = (q ≫ φ.app s a₀).left pL
    rw [Over.comp_left, Scheme.Hom.comp_apply, hq]
  change (φ.app s a₀).left x ∈ _
  rw [this, hy'j, Over.comp_left, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

include hj in
/-- The value at any point. -/
theorem mem_range_app_general {T : Over S} (φ : AttractorPt aX N T) (u : T ⟶ W)
    (hu : (AttractorPt.ofFace hF φ).toPoint = u ≫ j) {T' : Over S} (t : T' ⟶ T)
    (a : APt (overO S) N (op T')) (x : T'.left) : (φ.app t a).left x ∈ Set.range j.left := by
  let κ := T'.left.residueField x
  let K : Type u := AlgebraicClosure κ
  let m : Spec (CommRingCat.of K) ⟶ T'.left :=
    Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ T'.left.fromSpecResidueField x
  let tk : Spec (CommRingCat.of K) ⟶ T.left := m ≫ t.left
  let m' : spO (T := T) tk ⟶ T' := Over.homMk m (by
    change m ≫ T'.hom = (m ≫ t.left) ≫ T.hom
    exact (congrArg (m ≫ ·) (Over.w t).symm).trans (Category.assoc _ _ _).symm)
  have hs : (Over.homMk tk rfl : spO (T := T) tk ⟶ T) = m' ≫ t := Over.OverMorphism.ext rfl
  have pt : Nonempty (Spec (CommRingCat.of K)) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨z⟩ := pt
  have hz := mem_range_field_general j hj hF φ u hu K tk (APt.res m'.op a) z
  rw [hs, φ.naturality] at hz
  have e : (yoneda.obj X).map m'.op (φ.app t a) = m' ≫ φ.app t a := rfl
  rw [e, Over.comp_left, Scheme.Hom.comp_apply] at hz
  have hm : m'.left z = x := by
    change T'.left.fromSpecResidueField x _ = x
    exact Scheme.fromSpecResidueField_apply x _
  rwa [hm] at hz

include hj in
/-- **The reduction to `W`, for any `N`**: a point of `X^N` with vertex in the stable open `W` is a
point of `W^N`. -/
theorem exists_att_of_vertex_general {T : Over S} (φ : AttractorPt aX N T) (u : T ⟶ W)
    (hu : (AttractorPt.ofFace hF φ).toPoint = u ≫ j) :
    ∃ ψ : AttractorPt aW N T, AttractorPt.push (eqHom j hj) ψ = φ := by
  have hr : ∀ {T' : Over S} (t : T' ⟶ T) (a : APt (overO S) N (op T')),
      Set.range (φ.app t a).left ⊆ Set.range j.left := by
    rintro T' t a _ ⟨x, rfl⟩
    exact mem_range_app_general j hj hF φ u hu t a x
  let lf : ∀ {T' : Over S} (t : T' ⟶ T) (a : APt (overO S) N (op T')), T' ⟶ W := fun t a =>
    Over.homMk (IsOpenImmersion.lift j.left _ (hr t a)) (by
      have e := Over.w j
      rw [← e, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w (φ.app t a))
  have hlf : ∀ {T' : Over S} (t : T' ⟶ T) (a : APt (overO S) N (op T')), lf t a ≫ j = φ.app t a :=
    fun t a => Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hcancel : ∀ {T' : Over S} {a b : T' ⟶ W}, a ≫ j = b ≫ j → a = b := by
    intro T' a b h
    refine Over.OverMorphism.ext ((cancel_mono j.left).1 ?_)
    exact congrArg (fun k => k.left) h
  refine ⟨{ app := fun t a => lf t a
            naturality := fun s t a => hcancel ?_
            equivariant := fun t h a => hcancel ?_ }, ?_⟩
  · refine (hlf _ _).trans ?_
    refine (φ.naturality s t a).trans ?_
    change s ≫ φ.app t a = (s ≫ lf t a) ≫ j
    rw [Category.assoc, hlf]
  · refine (hlf _ _).trans ?_
    refine (φ.equivariant t h a).trans ?_
    rw [← hlf t a]
    exact (hj h (lf t a)).symm
  · refine AttractorPt.ext ?_
    funext T' t a
    exact hlf t a

end VertexGeneral

section MainGeneral

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] {X W : Over S}
  {aX : AAction (overO S) M (yoneda.obj X)} [IsAffineHom W.hom]
  (aW : AAction (overO S) M (yoneda.obj W)) (j : W ⟶ X) [IsOpenImmersion j.left]
  (hj : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ W), sm aW h x ≫ j = sm aX h (x ≫ j))
  {N : AddSubmonoid M} {F : AddSubgroup M} (hF : IsFace F.toAddSubmonoid N)
  {Zx Zf : Over S} (rx : RepresentsAttractor aX N (yoneda.obj Zx))
  (rf : RepresentsAttractor aX F.toAddSubmonoid (yoneda.obj Zf)) (z : Zx ⟶ Zf)
  (hz : ∀ (T : Over S) (w : T ⟶ Zx), rf.equiv T (w ≫ z) = AttractorPt.ofFace hF (rx.equiv T w))

include hz in
/-- `lift_N` without the weight. -/
theorem lift_N_general {T : Over S} (t : T ⟶ Zx)
    (u : T ⟶ Zatt aW F.toAddSubmonoid) (hc : t ≫ z = u ≫ eMap aW j hj rf) :
    ∃ l : T ⟶ Zatt aW N, l ≫ eMap aW j hj rx = t ∧ l ≫ faceZ aW N hF = u := by
  have e₁ : AttractorPt.ofFace hF (rx.equiv T t) =
      AttractorPt.push (eqHom j hj) (attEquiv aW F.toAddSubmonoid T u) := by
    refine (hz T t).symm.trans ?_
    change rEq rf T (t ≫ z) = _
    rw [hc, eMap_spec]
  have hv : (AttractorPt.ofFace hF (rx.equiv T t)).toPoint = (u ≫ iAtt aW F.toAddSubmonoid) ≫ j := by
    rw [e₁]
    change (attEquiv aW F.toAddSubmonoid T u).toPoint ≫ j = _
    rw [toPoint_attEquiv]
  obtain ⟨ψ, hψ⟩ := exists_att_of_vertex_general j hj hF (rx.equiv T t) _ hv
  refine ⟨(attEquiv aW N T).symm ψ, ?_, ?_⟩
  · apply (rEq rx T).injective
    rw [eMap_spec, Equiv.apply_symm_apply, hψ]
  · apply (attEquiv aW F.toAddSubmonoid T).injective
    rw [faceZ_spec, Equiv.apply_symm_apply]
    apply push_injective aW j hj
    rw [← e₁, ← hψ]
    refine AttractorPt.ext ?_
    funext T₁ t' a
    rfl

include hz in
/-- `W^N = X^N ×_{X^{N^×}} W^{N^×}`, for any `N`. -/
theorem isPullback_eMap_general :
    IsPullback (eMap aW j hj rx).left (faceZ aW N hF).left z.left (eMap aW j hj rf).left :=
  isPullback_of_over _ _ _ _ (eMap_square aW j hj hF rx rf z hz)
    (fun t u h => lift_N_general aW j hj hF rx rf z hz t u h)
    (fun l l' h _ => by
      apply (attEquiv aW N _).injective
      apply push_injective aW j hj
      rw [← eMap_spec aW j hj rx, ← eMap_spec aW j hj rx, h])

end MainGeneral

section ThmGeneral

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] {N : AddSubmonoid M}

/-- **Theorem 12.4**, schemes. `X → S` smooth with a Zariski locally linearizable action; `N` finitely
generated or `M` finitely generated (`M` is finitely generated throughout §12 of the paper, so `N` is
arbitrary and the alternative "`X` quasi-compact over `S`" of the statement is not needed). Every point
of `X^{N^×}` has an open neighbourhood `Spec B₀` over which `X^N` is `Spec B`, `B = Sym_{B₀}(P)`, with
`P` finite projective. -/
theorem thm124_general {X : Over S} {aX : AAction (overO S) M (yoneda.obj X)} [Smooth X.hom] (L : LocLin aX)
    [∀ i, IsAffineHom (L.W i).hom] (hfg : N.FG ∨ AddGroup.FG M) {Zx Zf : Over S}
    (rx : RepresentsAttractor aX N (yoneda.obj Zx))
    (rf : RepresentsAttractor aX (unitsOf N).toAddSubmonoid (yoneda.obj Zf)) (z : Zx ⟶ Zf)
    (hz : ∀ (T : Over S) (w : T ⟶ Zx),
      rf.equiv T (w ≫ z) = AttractorPt.ofFace (isFace_unitsOf N) (rx.equiv T w))
    (y : Zf.left) :
    ∃ (i : L.I) (U : S.Opens) (hU : IsAffineOpen U)
      (e : (Zloc (L.act i) (unitsOf N).toAddSubmonoid hU).left ⟶ Zf.left)
      (e' : (Zloc (L.act i) N hU).left ⟶ Zx.left),
      IsOpenImmersion e ∧ IsOpenImmersion e' ∧ y ∈ Set.range e ∧
      IsPullback e' (PhiMap hU (rho0 (L.act i) N (isFace_unitsOf N) hU)).left z.left e ∧
      letI := (rho0 (L.act i) N (isFace_unitsOf N) hU).toRingHom.toAlgebra
      (Module.Finite (Qalg (L.act i) (unitsOf N).toAddSubmonoid hU)
        (Conormal (piB (gZ (L.act i) hU (F := unitsOf N)) (Yq (unitsOf N) N)
          (hI₁' (L.act i) N (isFace_unitsOf N) hU) (hI₀' (L.act i) hU)
          (sharp_Yq N (isFace_unitsOf N)))) ∧
      Module.Projective (Qalg (L.act i) (unitsOf N).toAddSubmonoid hU)
        (Conormal (piB (gZ (L.act i) hU (F := unitsOf N)) (Yq (unitsOf N) N)
          (hI₁' (L.act i) N (isFace_unitsOf N) hU) (hI₀' (L.act i) hU)
          (sharp_Yq N (isFace_unitsOf N)))) ∧
      Nonempty (SymmetricAlgebra (Qalg (L.act i) (unitsOf N).toAddSubmonoid hU)
        (Conormal (piB (gZ (L.act i) hU (F := unitsOf N)) (Yq (unitsOf N) N)
          (hI₁' (L.act i) N (isFace_unitsOf N) hU) (hI₀' (L.act i) hU)
          (sharp_Yq N (isFace_unitsOf N)))) ≃ₐ[Qalg (L.act i) (unitsOf N).toAddSubmonoid hU]
        Qalg (L.act i) N hU)) := by
  have hF := isFace_unitsOf N
  obtain ⟨i, xw, hxw⟩ := L.covers ((vF rf).left y)
  have hO : IsOpenImmersion (L.j i).left := L.isOpen i
  have hsm : Smooth (L.W i).hom := by
    rw [← Over.w (L.j i)]
    infer_instance
  have hj : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ L.W i),
      sm (L.act i) h x ≫ L.j i = sm aX h (x ≫ L.j i) := @fun T h x => L.equivariant i h x
  let κ := Zf.left.residueField y
  let c : Spec κ := ⟨⊥, Ideal.isPrime_bot⟩
  have hc : Zf.left.fromSpecResidueField y c = y := Scheme.fromSpecResidueField_apply y _
  let T : Over S := Over.mk (Zf.left.fromSpecResidueField y ≫ Zf.hom)
  let t : T ⟶ Zf := Over.homMk (Zf.left.fromSpecResidueField y) rfl
  have hsub : Subsingleton (Spec κ) := inferInstanceAs (Subsingleton (PrimeSpectrum κ))
  have hr : Set.range (t ≫ vF rf).left ⊆ Set.range (L.j i).left := by
    rintro _ ⟨b, rfl⟩
    have hb : b = c := hsub.elim _ _
    rw [hb, Over.comp_left, Scheme.Hom.comp_apply]
    change (vF rf).left (Zf.left.fromSpecResidueField y c) ∈ _
    rw [hc]
    exact ⟨xw, hxw⟩
  let u : T ⟶ L.W i := Over.homMk (IsOpenImmersion.lift (L.j i).left _ hr) (by
    rw [← Over.w (L.j i), ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (t ≫ vF rf))
  have hu : t ≫ vF rf = u ≫ L.j i := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _).symm
  obtain ⟨l, hl, -⟩ := lift_F (L.act i) (L.j i) hj rf t u hu
  let p : (Zatt (L.act i) (unitsOf N).toAddSubmonoid).left := l.left c
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := (Zatt (L.act i) (unitsOf N).toAddSubmonoid).hom p) (U := ⊤) trivial
  let U : S.affineOpens := ⟨V, hV⟩
  let O := (Zatt (L.act i) (unitsOf N).toAddSubmonoid).hom ⁻¹ᵁ V
  let T₂ : Over S := Over.mk (O.ι ≫ (Zatt (L.act i) (unitsOf N).toAddSubmonoid).hom)
  let a₂ : T₂ ⟶ Zatt (L.act i) (unitsOf N).toAddSubmonoid := Over.homMk O.ι rfl
  have hT₂ : LiesOver T₂ U.1 := liesOver_of_forall fun x => by
    change (Zatt (L.act i) (unitsOf N).toAddSubmonoid).hom (O.ι x) ∈ V
    exact x.2
  obtain ⟨m, hm⟩ := exists_lift_iotaZ (L.act i) (unitsOf N).toAddSubmonoid U hT₂ a₂
  have hpr : p ∈ Set.range (iotaZ (L.act i) (unitsOf N).toAddSubmonoid U).left := by
    refine ⟨m.left ⟨p, hpV⟩, ?_⟩
    have e2 : (m ≫ iotaZ (L.act i) (unitsOf N).toAddSubmonoid U).left ⟨p, hpV⟩ = a₂.left ⟨p, hpV⟩ := by
      rw [hm]
    exact (Scheme.Hom.comp_apply m.left _ _).symm.trans e2
  obtain ⟨q, hq⟩ := hpr
  refine ⟨i, V, hV, (iotaZ (L.act i) (unitsOf N).toAddSubmonoid U).left ≫ (eMap (L.act i) (L.j i) hj rf).left,
    (iotaZ (L.act i) N U).left ≫ (eMap (L.act i) (L.j i) hj rx).left, inferInstance, ?_, ⟨q, ?_⟩, ?_, ?_⟩
  · have := MorphismProperty.of_isPullback
      (P := @IsOpenImmersion) (isPullback_eMap_general (L.act i) (L.j i) hj hF rx rf z hz).flip
      (instOpenEF (L.act i) (L.j i) hj rf)
    infer_instance
  · rw [Scheme.Hom.comp_apply, hq]
    have e2 : (l ≫ eMap (L.act i) (L.j i) hj rf).left c = t.left c := by rw [hl]
    exact ((Scheme.Hom.comp_apply l.left _ _).symm.trans e2).trans hc
  · exact (isPullback_chart_square (L.act i) hF U).paste_horiz
      (isPullback_eMap_general (L.act i) (L.j i) hj hF rx rf z hz)
  · exact printed_affine (L.act i) N hF hV hfg

end ThmGeneral

#print axioms AlgMag.Sec12Printed.thm124_general

end AlgMag.Sec12Printed

end PartP2

section PartP3

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism TensorProduct

open scoped Classical

universe u

namespace AlgMag.Sec12Printed

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

section Free

variable {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]

/-- A finite projective module is free on a basic open around any prime. -/
theorem exists_away_free [Module.Finite R P] [Module.Projective R P] (p : Ideal R) [p.IsPrime] :
    ∃ a, a ∉ p ∧ Module.Free (Localization (.powers a)) (LocalizedModule.Away a P) := by
  have : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  let A := Localization.AtPrime p
  let P' := LocalizedModule p.primeCompl P
  let l := LocalizedModule.mkLinearMap p.primeCompl P
  have hb : IsBaseChange A l := IsLocalizedModule.isBaseChange p.primeCompl A l
  have : Module.Projective A P' := Module.Projective.of_equiv hb.equiv
  have : Module.Finite A P' := Module.Finite.equiv hb.equiv
  have : Module.Free A P' := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl l A
  exact ⟨r, hr, hf⟩

variable {B : Type u} [CommRing B] [Algebra R B]

/-- `Sym` commutes with the base change to `A`, when `P_A` is free: `A ⊗_R Sym_R(P)` is a polynomial
ring over `A`. -/
theorem nonempty_tensor_sym {A PA : Type u} [CommRing A] [Algebra R A] [AddCommGroup PA] [Module R PA]
    [Module A PA] [IsScalarTower R A PA] {l : P →ₗ[R] PA} (hl : IsBaseChange A l) {ι : Type u}
    [Fintype ι] (b : Module.Basis ι A PA) (e : SymmetricAlgebra R P ≃ₐ[R] B) :
    Nonempty (A ⊗[R] B ≃ₐ[A] MvPolynomial ι A) := by
  let Mv := MvPolynomial ι A
  let κ : PA →ₗ[A] Mv := b.constr A (fun i => MvPolynomial.X i)
  let g : B →ₐ[R] Mv := (SymmetricAlgebra.lift ((κ.restrictScalars R).comp l)).comp e.symm.toAlgHom
  let Φ : A ⊗[R] B →ₐ[A] Mv :=
    Algebra.TensorProduct.lift (Algebra.ofId A Mv) g (fun _ _ => Commute.all _ _)
  let W := A ⊗[R] B
  let i₁ : P →ₗ[R] W := (Algebra.TensorProduct.includeRight.toLinearMap).comp
    (e.toAlgHom.toLinearMap.comp (SymmetricAlgebra.ι R P))
  let θ : PA →ₗ[A] W := hl.lift i₁
  let Ψ : Mv →ₐ[A] W := MvPolynomial.aeval (fun i => θ (b i))
  have hΨκ : Ψ.toLinearMap.comp κ = θ := by
    refine b.ext fun i => ?_
    simp only [LinearMap.comp_apply, κ, Module.Basis.constr_basis]
    exact MvPolynomial.aeval_X _ _
  have hΦθ : Φ.toLinearMap.comp θ = κ := by
    refine hl.algHom_ext _ _ fun x => ?_
    have : θ (l x) = i₁ x := hl.lift_eq i₁ x
    simp [this, i₁, Φ, g]
  refine ⟨AlgEquiv.ofAlgHom Φ Ψ ?_ ?_⟩
  · refine MvPolynomial.algHom_ext fun i => ?_
    have := congrArg (fun f => f (b i)) hΦθ
    simpa [Ψ, κ] using this
  · refine Algebra.TensorProduct.ext (by ext) ?_
    refine AlgHom.ext fun y => ?_
    obtain ⟨s, rfl⟩ := e.surjective y
    induction s using SymmetricAlgebra.induction with
    | algebraMap r => simp
    | ι x =>
      have h1 : Φ (1 ⊗ₜ e (SymmetricAlgebra.ι R P x)) = κ (l x) := by simp [Φ, g]
      have h2 : Ψ (κ (l x)) = θ (l x) := congrArg (fun f => f (l x)) hΨκ
      have h3 : θ (l x) = i₁ x := hl.lift_eq i₁ x
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
      change Ψ (Φ (1 ⊗ₜ e (SymmetricAlgebra.ι R P x))) = 1 ⊗ₜ e (SymmetricAlgebra.ι R P x)
      rw [h1, h2, h3]
      rfl
    | mul a b ha hb =>
      simp only [map_mul, AlgHom.comp_apply] at ha hb ⊢
      rw [ha, hb]
    | add a b ha hb =>
      simp only [map_add, AlgHom.comp_apply] at ha hb ⊢
      rw [ha, hb]

/-- **The local form `𝔸ⁿ` of the fibration, on rings and schemes.** If `B = Sym_R(P)`, `P` finite
projective, then around any point of `Spec R` there is a basic open `Spec A` over which `Spec B` is
`𝔸ⁿ_A`. -/
theorem exists_affineSpace_chart [Module.Finite R P] [Module.Projective R P]
    (e : SymmetricAlgebra R P ≃ₐ[R] B) (y : Spec (CommRingCat.of R)) :
    ∃ (a : R) (n : ℕ) (g : 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of (Localization (.powers a)))) ⟶
        Spec (CommRingCat.of B)),
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization (.powers a))))) ∧
      IsPullback g (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of (Localization (.powers a)))) ↘ _)
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization (.powers a))))) := by
  let y' : PrimeSpectrum R := y
  haveI : y'.asIdeal.IsPrime := y'.isPrime
  obtain ⟨a, ha, hfree⟩ := exists_away_free P y'.asIdeal
  let A := Localization (Submonoid.powers a)
  let PA := LocalizedModule.Away a P
  let l := LocalizedModule.mkLinearMap (Submonoid.powers a) P
  have hl : IsBaseChange A l := IsLocalizedModule.isBaseChange (Submonoid.powers a) A l
  have : Module.Finite A PA := Module.Finite.equiv hl.equiv
  have : Nontrivial A ∨ Subsingleton A := (subsingleton_or_nontrivial A).symm
  let bb := Module.Free.chooseBasis A PA
  let n := Fintype.card (Module.Free.ChooseBasisIndex A PA)
  let eι : ULift.{u} (Fin n) ≃ Module.Free.ChooseBasisIndex A PA :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  let b : Module.Basis (ULift.{u} (Fin n)) A PA := bb.reindex eι.symm
  obtain ⟨E⟩ := nonempty_tensor_sym P hl b e
  let RA : CommRingCat.{u} := CommRingCat.of A
  let n' := ULift.{u} (Fin n)
  let E' : CommRingCat.of (A ⊗[R] B) ⟶ CommRingCat.of (MvPolynomial n' A) :=
    CommRingCat.ofHom E.toAlgHom.toRingHom
  have hE : IsIso E' := (E.toRingEquiv.toCommRingCatIso : _ ≅ _).isIso_hom
  let po := CommRingCat.isPushout_tensorProduct R A B
  let pb := (isPullback_SpecMap_of_isPushout _ _ _ _ po).flip
  let iso : 𝔸(n'; Spec RA) ≅ Spec (CommRingCat.of (A ⊗[R] B)) :=
    AffineSpace.SpecIso n' RA ≪≫ Scheme.Spec.mapIso (asIso E').op
  have hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (S := A ⊗[R] B)
      Algebra.TensorProduct.includeLeftRingHom) = 𝔸(n'; Spec RA) ↘ Spec RA := by
    have h1 : (AffineSpace.SpecIso n' RA).hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
        𝔸(n'; Spec RA) ↘ Spec RA := by
      rw [← AffineSpace.SpecIso_inv_over, Iso.hom_inv_id_assoc]
    rw [← h1]
    change ((AffineSpace.SpecIso n' RA).hom ≫ Spec.map E') ≫ _ = _
    rw [Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun c => by
      change E (c ⊗ₜ 1) = _
      exact E.commutes c)
  refine ⟨a, n, iso.hom ≫ Spec.map (CommRingCat.ofHom (S := A ⊗[R] B)
    Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_⟩
  · have hr := PrimeSpectrum.localization_away_comap_range A a
    change y ∈ Set.range (PrimeSpectrum.comap (algebraMap R A))
    rw [hr]
    exact ha
  · refine IsPullback.of_iso pb iso.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [Iso.eq_inv_comp]
      exact hover
    · simp
    · simp

end Free

section Thm

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] {N : AddSubmonoid M}

attribute [local instance] gradedAlgebraOf

/-- **Theorem 12.4**: `X^N → X^{N^×}` is an affine space fibration, in local form `𝔸ⁿ`. `X → S` is
smooth with a Zariski locally linearizable action, `N` or `M` is finitely generated. Every point `y`
of `X^{N^×}` has an open neighbourhood `V` over which `X^N` is `𝔸ⁿ_V`. -/
theorem thm124_affineSpace {X : Over S} {aX : AAction (overO S) M (yoneda.obj X)} [Smooth X.hom]
    (L : LocLin aX) [∀ i, IsAffineHom (L.W i).hom] (hfg : N.FG ∨ AddGroup.FG M) {Zx Zf : Over S}
    (rx : RepresentsAttractor aX N (yoneda.obj Zx))
    (rf : RepresentsAttractor aX (unitsOf N).toAddSubmonoid (yoneda.obj Zf)) (z : Zx ⟶ Zf)
    (hz : ∀ (T : Over S) (w : T ⟶ Zx),
      rf.equiv T (w ≫ z) = AttractorPt.ofFace (isFace_unitsOf N) (rx.equiv T w))
    (y : Zf.left) :
    ∃ (V : Scheme.{u}) (n : ℕ) (e : V ⟶ Zf.left) (g : 𝔸(ULift.{u} (Fin n); V) ⟶ Zx.left),
      IsOpenImmersion e ∧ y ∈ Set.range e ∧
      IsPullback g (𝔸(ULift.{u} (Fin n); V) ↘ V) z.left e := by
  obtain ⟨i, U, hU, e₀, e₀', ho, -, ⟨q, hq⟩, hQ, hf, hp, ⟨E⟩⟩ :=
    thm124_general L hfg rx rf z hz y
  letI := (rho0 (L.act i) N (isFace_unitsOf N) hU).toRingHom.toAlgebra
  obtain ⟨a, n, g, ⟨w, hw⟩, hpb⟩ := exists_affineSpace_chart _ E q
  refine ⟨_, n, Spec.map (CommRingCat.ofHom (algebraMap _ (Localization (.powers a)))) ≫ e₀,
    g ≫ e₀', ?_, ⟨w, ?_⟩, hpb.paste_horiz hQ⟩
  · have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap
        (Qalg (L.act i) (unitsOf N).toAddSubmonoid hU) (Localization (.powers a))))) :=
      IsOpenImmersion.of_isLocalization a
    exact @IsOpenImmersion.comp _ _ _ _ _ this ho
  · exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg e₀ hw).trans hq)

end Thm

#print axioms AlgMag.Sec12Printed.thm124_affineSpace

end AlgMag.Sec12Printed

end PartP3

section PartP4

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag

section Topology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The topology of `|G|` (Stacks Tag 03BY) satisfies `AlgMag.SchemeContinuous`. -/
theorem schemeContinuous_pointTopology (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    SchemeContinuous (pointTopology B S hS G) := by
  intro U g
  letI := pointTopology B S hS G
  refine continuous_def.2 fun W hW => ?_
  obtain ⟨V, hV, hm⟩ := hW U (yonedaEquiv.symm g)
  convert hV using 1
  ext s
  let p : FieldValuedPoint B S hS (yoneda.obj U) :=
    { carrier := ((SCH).obj U).residueField s
      contained := BigFppfSite.residueField_spec_contains B U.left.2 s
      toBase := ((SCH).obj U).fromSpecResidueField s ≫ U.hom.hom
      value := overHom (((SCH).obj U).fromSpecResidueField s) rfl }
  have h := hm p
  rw [Set.mem_preimage, pointsMap_class] at h
  have hs : schemePoint B S hS U p = s := Scheme.fromSpecResidueField_apply s _
  rw [hs] at h
  exact h

end Topology

section Prop121

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {actX : AAction (fppfO B S hS) M X}

/-- **Proposition 12.1**, with the topology `|X|` of Stacks Tag 03BY. `N` is finitely generated and `X`
has a `N^×`-FPR atlas. `X^N`, `X^{N^×}` are algebraic spaces and `X^N → X^{N^×}` is affine (`r.affine_c`,
Theorem 8.3, which takes `X` separated). It has connected fibres over all field-valued points, and it
induces a bijection on the connected components of the underlying spaces. -/
theorem prop121_printed (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) {N : AddSubmonoid M}
    (hN : N.FG) (hat : ExistsZFPRAtlas actX (unitsSub N)) :
    ∃ r : Thm83Repr actX N,
      letI := pointTopology B S hS r.P
      letI := pointTopology B S hS r.Y
      Function.Bijective (continuous_pointsMap B S hS
        (repFace r.rP r.rY (isFace_unitsSub N))).connectedComponentsMap ∧
      ∀ q : FieldValuedPoint B S hS r.Y,
        @ConnectedSpace _ (pointTopology B S hS (faceFibre (isFace_unitsSub N) r.rP r.rY q)) := by
  obtain ⟨r⟩ := thm83_repr hX hsep N hat (Or.inl hN)
  refine ⟨r, ?_, fun q => ?_⟩
  · exact bijective_connectedComponents_repFace (isFace_unitsSub N) hN r.rP r.rY _ _
      (schemeContinuous_pointTopology _) _ (continuous_pointsMap B S hS _)
  · exact connectedSpace_faceFibre (isFace_unitsSub N) hN r.rP r.rY q _
      (schemeContinuous_pointTopology _)

end Prop121

section Prop122

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [Countable M] {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {aX : AAction (fppfO B S hS) M X} {aY : AAction (fppfO B S hS) M Y}

/-- **Proposition 12.2 (ii)**, as printed: (a) `f` is a closed immersion, (b) `Y` has a `N^×`-FPR
atlas, (c) `N` is finitely generated or `X` is separated. Then `f^N` is a closed immersion and
`X^N = Y^N ×_Y X`. The proof used does not need (b), (c) (`AlgMag.isPullback_repAttractorMap`). -/
theorem prop122_ii_printed (hg : EquivariantHom aX aY) (hf : IsClosedImm hg.hom) (N : AddSubmonoid M)
    {ZX ZY : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_ : IsAlgebraicSpace B S hS ZX) (_ : IsAlgebraicSpace B S hS ZY)
    (rX : RepresentsAttractor aX N ZX) (rY : RepresentsAttractor aY N ZY)
    (_ : ExistsZFPRAtlas aY (unitsSub N)) (_ : N.FG ∨ IsSeparatedOver X) :
    IsClosedImm (repAttractorMap hg N rX rY) ∧
      IsPullback (repAttractorMap hg N rX rY) (repToPoint rX) (repToPoint rY) hg.hom :=
  ⟨isClosedImm_repAttractorMap hg hf N rX rY, isPullback_repAttractorMap hg hf N rX rY⟩

end Prop122

#print axioms AlgMag.prop121_printed
#print axioms AlgMag.prop122_ii_printed

end AlgMag

end PartP4

section PartP5

open CategoryTheory Opposite AlgebraicGeometry

universe u v w

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "AFF" => BigAffineFppf B S hS
local notation "incl" => BigAffineFppf.inclusion B S hS
local notation "SITE" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS

/-! ### Remark 14.2: `Hom(X, Y) = lim_i colim_j Hom(X_i, Y_j)` -/

/-- The sieve on `T` of the arrows along which `x ∈ F(T)` comes from one of the `u i`. -/
def indCoverSieve {F : SITEᵒᵖ ⥤ Type u} {ι : Type u} {U : ι → AFF} (s : ∀ i, F.obj (op ((incl).obj (U i))))
    {T : SITE} (x : F.obj (op T)) : Sieve T where
  arrows W f := ∃ (i : ι) (a : W ⟶ (incl).obj (U i)), F.map f.op x = F.map a.op (s i)
  downward_closed := by
    rintro W W' f ⟨i, a, h⟩ g
    refine ⟨i, g ≫ a, ?_⟩
    rw [op_comp, op_comp, F.map_comp, F.map_comp]
    exact congrArg (F.map g.op) h

/-- Quasi-compactness of `F`, in the form used by Remark 14.2 ("every map `X_i → Y` factors over some
`Y_j` by quasi-compactness of `X_i`"): finitely many affine points of `F` cover `F` locally. -/
def IsFinitelyCovered (F : SITEᵒᵖ ⥤ Type u) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (U : ι → AFF) (s : ∀ i, F.obj (op ((incl).obj (U i)))),
    ∀ (T : SITE) (x : F.obj (op T)), indCoverSieve s x ∈ BigFppfOver.topology B S hS T

/-- An algebraic space with an atlas by an affine scheme is finitely covered. -/
theorem isFinitelyCovered_of_atlas {F : SITEᵒᵖ ⥤ Type u} (A : AFF) (f : yoneda.obj ((incl).obj A) ⟶ F)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f) :
    IsFinitelyCovered (B := B) (S := S) (hS := hS) F := by
  refine ⟨PUnit, inferInstance, fun _ => A, fun _ => yonedaEquiv f, fun T x => ?_⟩
  let g := yonedaEquiv.symm x
  let q := hs.rep.snd g
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (AlgebraicGeometry.Space.sieve_generate_singleton_mem_topology_over B S hS q (hs.property_snd g) ?_)
  · rintro W _ ⟨Z, a, b, ⟨⟩, rfl⟩
    let a₀ := yoneda.preimage (hs.rep.fst g)
    have hc' : yoneda.map a₀ ≫ f = yoneda.map q ≫ g := by
      rw [Functor.map_preimage]
      exact (hs.rep.isPullback g).w
    have e : f.app _ a₀ = F.map q.op x := by
      have := congrArg (fun t => t.app (op (hs.rep.pullback g)) (𝟙 (hs.rep.pullback g))) hc'
      simpa [g] using this
    have l : f.app _ a₀ = F.map a₀.op (yonedaEquiv f) := by
      have := hom_naturality_apply f a₀.op (𝟙 _)
      simpa [yonedaEquiv_apply] using this
    refine ⟨PUnit.unit, a ≫ a₀, ?_⟩
    have e1 : F.map q.op x = F.map a₀.op (yonedaEquiv f) := e.symm.trans l
    change F.map (a ≫ q).op x = F.map (a ≫ a₀).op _
    rw [op_comp, op_comp, F.map_comp, F.map_comp]
    exact congrArg (F.map a.op) e1
  · exact he.property_snd g

section Hom

variable {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {Y : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type w} (p : IndPresentation.{u, v, w} P Y)

theorem ind_π_injective (j : p.I) (A : AFF) {a b : (p.obj j).obj (op ((incl).obj A))}
    (h : p.π j A a = p.π j A b) : a = b := by
  obtain ⟨k, hk, e⟩ := p.inj j A a b h
  exact isClosedImm_injective (p.closed hk) e

/-- A section of a sheaf is determined by its restrictions to affine schemes. -/
theorem ind_sep_affine {Z : SITEᵒᵖ ⥤ Type u} (hZ : Presieve.IsSheaf (BigFppfOver.topology B S hS) Z)
    {T : SITE} {s s' : Z.obj (op T)}
    (h : ∀ (A : AFF) (a : (incl).obj A ⟶ T), Z.map a.op s = Z.map a.op s') : s = s' := by
  let I := ((SCH).obj T).affineOpens
  have hCI : ∀ i : I, B.Contains (i.1 : Scheme.{u}) := fun i =>
    Scheme.size_lt_of_isOpenImmersion i.1.ι T.left.property
  let W : I → SITE := fun i => siteObject B S hS (hCI i) (i.1.ι ≫ T.hom.hom)
  let π : ∀ i, W i ⟶ T := fun i => siteHom i.1.ι rfl
  have hcov : Sieve.ofArrows W π ∈ BigFppfOver.topology B S hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS π
      (fun i => inferInstanceAs (IsOpenImmersion i.1.ι)) fun x => ?_
    obtain ⟨_, ⟨W', hW', rfl⟩, hx, -⟩ := ((SCH).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((⊤ : ((SCH).obj T).Opens) : Set _) from trivial) (⊤ : ((SCH).obj T).Opens).isOpen
    exact ⟨⟨W', hW'⟩, ⟨⟨x, hx⟩, rfl⟩⟩
  refine (hZ _ hcov).isSeparatedFor.ext ?_
  rintro Y' g ⟨Z', a, b, ⟨i⟩, rfl⟩
  have hW : IsAffine ((SCH).obj (W i)) := i.2
  have := h (affOf (W i)) (π i)
  rw [op_comp, Z.map_comp]
  exact congrArg (Z.map a.op) this

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : ∀ A : (BigAffineFppf B S hS), F.obj (op ((BigAffineFppf.inclusion B S hS).obj A)) → Y.obj (op A))

/-- `y ∈ Y_j(W)` represents `x ∈ F(W)`: on every affine over `W`, `y` is `φ(x)`. -/
def IndRep (j : p.I) {W : SITE} (y : (p.obj j).obj (op W)) (x : F.obj (op W)) : Prop :=
  ∀ (A : AFF) (s : (incl).obj A ⟶ W), p.π j A ((p.obj j).map s.op y) = φ A (F.map s.op x)

variable {p φ}

lemma IndRep.res {j : p.I} {W W' : SITE} {y : (p.obj j).obj (op W)} {x : F.obj (op W)}
    (h : IndRep p φ j y x) (g : W' ⟶ W) :
    IndRep p φ j ((p.obj j).map g.op y) (F.map g.op x) := by
  intro A s
  have := h A (s ≫ g)
  rw [op_comp, Functor.map_comp, Functor.map_comp] at this
  exact this

lemma IndRep.tr {j k : p.I} (hk : j ≤ k) {W : SITE} {y : (p.obj j).obj (op W)} {x : F.obj (op W)}
    (h : IndRep p φ j y x) : IndRep p φ k ((p.tr hk).app _ y) x := by
  intro A s
  rw [← h A s, ← p.π_tr hk]
  congr 1
  exact (hom_naturality_apply (p.tr hk) s.op y).symm

lemma IndRep.unique (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (p.obj j)) {j : p.I}
    {W : SITE} {y y' : (p.obj j).obj (op W)} {x : F.obj (op W)}
    (h : IndRep p φ j y x) (h' : IndRep p φ j y' x) : y = y' :=
  ind_sep_affine (hZ j) fun A a => ind_π_injective p j A ((h A a).trans (h' A a).symm)

variable (p) in
omit φ in
/-- The core: a section of `F` is represented at the level `j` once the `s i` are. -/
theorem exists_indRep (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (p.obj j))
    (φ : ∀ A : AFF, F.obj (op ((incl).obj A)) → Y.obj (op A))
    (hφ : ∀ {A A' : AFF} (s : A' ⟶ A) (x : F.obj (op ((incl).obj A))),
      φ A' (F.map ((incl).map s).op x) = Y.map s.op (φ A x))
    {ι : Type u} {U : ι → AFF} {s : ∀ i, F.obj (op ((incl).obj (U i)))} {j : p.I}
    (y : ∀ i, (p.obj j).obj (op ((incl).obj (U i)))) (hy : ∀ i, p.π j _ (y i) = φ _ (s i))
    {T : SITE} (x : F.obj (op T)) (hcov : indCoverSieve s x ∈ BigFppfOver.topology B S hS T) :
    ∃ t : (p.obj j).obj (op T), IndRep p φ j t x := by
  have hyR : ∀ i, IndRep p φ j (y i) (s i) := fun i A a => by
    have e1 := p.π_map j (indAffHom a) (y i)
    have e2 := hφ (indAffHom a) (s i)
    exact e1.trans ((congrArg _ (hy i)).trans e2.symm)
  have hval : ∀ {W : SITE} (f : W ⟶ T), indCoverSieve s x f →
      ∃ v : (p.obj j).obj (op W), IndRep p φ j v (F.map f.op x) := by
    rintro W f ⟨i, a, h⟩
    exact ⟨_, h ▸ (hyR i).res a⟩
  let fam : Presieve.FamilyOfElements (p.obj j) (indCoverSieve s x).arrows :=
    fun W f hf => (hval f hf).choose
  have hfam : ∀ {W : SITE} (f : W ⟶ T) (hf : indCoverSieve s x f),
      IndRep p φ j (fam f hf) (F.map f.op x) := fun f hf => (hval f hf).choose_spec
  have hcomp : fam.Compatible := by
    intro Y₁ Y₂ Z' g₁ g₂ f₁ f₂ h₁ h₂ comm
    have r1 := (hfam f₁ h₁).res g₁
    have r2 := (hfam f₂ h₂).res g₂
    have e1 : F.map g₁.op (F.map f₁.op x) = F.map (g₁ ≫ f₁).op x := by
      rw [op_comp, F.map_comp]; rfl
    have e2 : F.map g₂.op (F.map f₂.op x) = F.map (g₂ ≫ f₂).op x := by
      rw [op_comp, F.map_comp]; rfl
    rw [e1] at r1
    rw [e2, ← comm] at r2
    exact IndRep.unique hZ r1 r2
  let t := (hZ j _ hcov).amalgamate fam hcomp
  have ht : ∀ {W : SITE} (f : W ⟶ T) (hf : indCoverSieve s x f), (p.obj j).map f.op t = fam f hf :=
    fun f hf => (hZ j _ hcov).valid_glue hcomp f hf
  refine ⟨t, fun A a => ?_⟩
  obtain ⟨l, z, hz⟩ := p.surj A (φ A (F.map a.op x))
  obtain ⟨k, hjk, hlk⟩ := exists_ge_ge j l
  have hzR : IndRep p φ k ((p.tr hlk).app _ z) (F.map a.op x) := fun A' b => by
    have e1 := p.π_map k (indAffHom b) ((p.tr hlk).app _ z)
    have e2 := hφ (indAffHom b) (F.map a.op x)
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [p.π_tr, hz]
  have heq : (p.tr hjk).app _ ((p.obj j).map a.op t) = (p.tr hlk).app _ z := by
    refine (hZ k _ ((BigFppfOver.topology B S hS).pullback_stable a hcov)).isSeparatedFor.ext ?_
    intro W g hg
    have r1 : IndRep p φ k ((p.obj k).map g.op ((p.tr hjk).app _ ((p.obj j).map a.op t)))
        (F.map (g ≫ a).op x) := by
      have := ((hfam (g ≫ a) hg).tr hjk)
      rw [← ht (g ≫ a) hg] at this
      have eq : (p.tr hjk).app _ ((p.obj j).map (g ≫ a).op t) =
          (p.obj k).map g.op ((p.tr hjk).app _ ((p.obj j).map a.op t)) := by
        rw [op_comp, Functor.map_comp]
        exact hom_naturality_apply (p.tr hjk) g.op _
      exact eq ▸ this
    have r2 := hzR.res g
    have e : F.map g.op (F.map a.op x) = F.map (g ≫ a).op x := by
      rw [op_comp, F.map_comp]; rfl
    rw [e] at r2
    exact IndRep.unique hZ r1 r2
  have := congrArg (p.π k A) heq
  rw [p.π_tr, p.π_tr, hz] at this
  exact this

variable (p) in
/-- **Remark 14.2**, "every map `X_i → Y` factors over some `Y_j` by quasi-compactness of `X_i`". -/
theorem exists_factor_term (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (p.obj j))
    (hF : IsFinitelyCovered (B := B) (S := S) (hS := hS) F)
    (φ : ∀ A : AFF, F.obj (op ((incl).obj A)) → Y.obj (op A))
    (hφ : ∀ {A A' : AFF} (s : A' ⟶ A) (x : F.obj (op ((incl).obj A))),
      φ A' (F.map ((incl).map s).op x) = Y.map s.op (φ A x)) :
    ∃ (j : p.I) (ψ : F ⟶ p.obj j), ∀ (A : AFF) (x : F.obj (op ((incl).obj A))),
      p.π j A (ψ.app _ x) = φ A x := by
  classical
  obtain ⟨ι, _, U, s, hcov⟩ := hF
  choose j₀ y₀ hy₀ using fun i => p.surj (U i) (φ _ (s i))
  obtain ⟨j, hj⟩ := Finite.bddAbove_range j₀
  have hj' : ∀ i, j₀ i ≤ j := fun i => hj ⟨i, rfl⟩
  let y := fun i => (p.tr (hj' i)).app _ (y₀ i)
  have hy : ∀ i, p.π j _ (y i) = φ _ (s i) := fun i => (p.π_tr _ _ _).trans (hy₀ i)
  have hex := fun (T : SITE) (x : F.obj (op T)) => exists_indRep p hZ φ hφ y hy x (hcov T x)
  let ψ : F ⟶ p.obj j :=
    { app := fun T => ↾ fun x => (hex (unop T) x).choose
      naturality := fun T T' g => by
        ext x
        exact IndRep.unique hZ (hex (unop T') _).choose_spec
          (IndRep.res (hex (unop T) x).choose_spec g.unop) }
  refine ⟨j, ψ, fun A x => ?_⟩
  have := (hex _ x).choose_spec A (𝟙 _)
  have h2 : p.π j A (hex _ x).choose = φ A x := by simpa using this
  exact h2

end Hom

section HomFormula

variable {P Q : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {X Y : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type w}
  (pX : IndPresentation.{u, v, w} P X) (pY : IndPresentation.{u, v, w} Q Y)

/-- **Remark 14.2**, `Hom(X, Y) = lim_i colim_j Hom(X_i, Y_j)`, the map to the limit: if each `X_i` is
quasi-compact and the `Y_j` are sheaves, every `f : X → Y` is given on `X_i` by a morphism
`X_i → Y_j`. The class in the colimit is unique, since the transition maps are injective
(`AlgMag.ind_π_injective`). -/
theorem exists_indHom_term (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i)) (f : X ⟶ Y) (i : pX.I) :
    ∃ (j : pY.I) (ψ : pX.obj i ⟶ pY.obj j), ∀ (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))),
      pY.π j A (ψ.app _ x) = f.app _ (pX.π i A x) :=
  exists_factor_term pY hZ (hX i) (fun A x => f.app _ (pX.π i A x)) fun s x => by
    rw [pX.π_map]
    exact hom_naturality_apply f s.op _

/-- **Remark 14.2**, the map to the limit is injective: `f` is determined by the `X_i → Y`. -/
theorem indHom_ext {f g : X ⟶ Y}
    (h : ∀ (i : pX.I) (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))),
      f.app _ (pX.π i A x) = g.app _ (pX.π i A x)) : f = g := by
  ext T x
  obtain ⟨i, x', rfl⟩ := pX.surj (unop T) x
  exact h i _ x'

/-- **Remark 14.2**, the map to the limit is surjective: a family `X_i → Y` of morphisms compatible
with the transition maps comes from a morphism `X → Y`. -/
theorem exists_indHom_of_compatible
    (φ : ∀ (i : pX.I) (A : AFF), (pX.obj i).obj (op ((incl).obj A)) → Y.obj (op A))
    (hφ : ∀ (i : pX.I) {A A' : AFF} (s : A' ⟶ A) (x : (pX.obj i).obj (op ((incl).obj A))),
      φ i A' ((pX.obj i).map ((incl).map s).op x) = Y.map s.op (φ i A x))
    (htr : ∀ {i k : pX.I} (h : i ≤ k) (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))),
      φ k A ((pX.tr h).app _ x) = φ i A x) :
    ∃ f : X ⟶ Y, ∀ (i : pX.I) (A : AFF) (x : (pX.obj i).obj (op ((incl).obj A))),
      f.app _ (pX.π i A x) = φ i A x := by
  have wd : ∀ (A : AFF) {i k : pX.I} (a : (pX.obj i).obj (op ((incl).obj A)))
      (b : (pX.obj k).obj (op ((incl).obj A))), pX.π i A a = pX.π k A b → φ i A a = φ k A b := by
    intro A i k a b h
    obtain ⟨m, him, hkm⟩ := exists_ge_ge i k
    have h' : pX.π m A ((pX.tr him).app _ a) = pX.π m A ((pX.tr hkm).app _ b) := by
      rw [pX.π_tr, pX.π_tr, h]
    rw [← htr him, ← htr hkm, ind_π_injective pX m A h']
  choose i₀ x₀ hx₀ using fun (T : AFFᵒᵖ) (x : X.obj T) => pX.surj (unop T) x
  refine ⟨{ app := fun T => ↾ fun x => φ _ _ (x₀ T x)
            naturality := fun T T' s => ?_ }, fun i A x => wd A _ _ (hx₀ _ _)⟩
  ext x
  change φ _ _ (x₀ T' (X.map s x)) = Y.map s (φ _ _ (x₀ T x))
  have e := hφ (i₀ T x) s.unop (x₀ T x)
  refine (wd _ _ _ ?_).trans e
  rw [hx₀, pX.π_map, hx₀]
  rfl

end HomFormula

#print axioms AlgMag.isFinitelyCovered_of_atlas
#print axioms AlgMag.exists_indHom_term
#print axioms AlgMag.exists_indHom_of_compatible

end AlgMag

end PartP5

section PartP6

open CategoryTheory Opposite AlgebraicGeometry

universe u v

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "AFF" => BigAffineFppf B S hS
local notation "incl" => BigAffineFppf.inclusion B S hS
local notation "SITE" => BigFppfOver B S hS

section Closed

variable {A A' A₂ B₁ B' C' D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- `A ×_{C} B₁ → A' ×_{C'} B'` is a closed immersion if `A → A'`, `B₁ → B'` are. The membership in the
source is tested by `hcond`. -/
theorem isClosedImm_fibre_map {a : A ⟶ D} {b : B₁ ⟶ D} {a' : A' ⟶ C'} {b' : B' ⟶ C'}
    (s : A ⟶ A') (t : B₁ ⟶ B') (hs : IsClosedImm s) (ht : IsClosedImm t)
    (hcond : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (x : A.obj W) (y : B₁.obj W),
      a.app W x = b.app W y ↔ a'.app W (s.app W x) = b'.app W (t.app W y))
    (τ : fibreProduct a b ⟶ fibreProduct a' b')
    (hτ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ) (p : (fibreProduct a b).obj W),
      (τ.app W p).1 = (s.app W p.1.1, t.app W p.1.2)) :
    IsClosedImm τ := by
  let M := fibreProduct a' (t ≫ b')
  let τ₁ : fibreProduct a b ⟶ M :=
    { app := fun W => ↾ fun p => ⟨(s.app W p.1.1, p.1.2), (hcond W _ _).1 p.2⟩
      naturality := fun W W' f => by
        ext p
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact hom_naturality_apply s f p.1.1
        · rfl }
  let τ₂ : M ⟶ fibreProduct a' b' :=
    { app := fun W => ↾ fun p => ⟨(p.1.1, t.app W p.1.2), p.2⟩
      naturality := fun W W' f => by
        ext p
        refine Subtype.ext (Prod.ext ?_ ?_)
        · rfl
        · exact hom_naturality_apply t f p.1.2 }
  have hτeq : τ = τ₁ ≫ τ₂ := by
    ext W p
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg Prod.fst (hτ W p)
    · exact congrArg Prod.snd (hτ W p)
  have h₁ : IsPullback τ₁ (fibreFst a b) (fibreFst a' (t ≫ b')) s := by
    refine IsPullback.of_forall_isPullback_app fun W => ?_
    rw [Limits.Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext p
      rfl
    · rintro p p' ⟨e₁, e₂⟩
      refine Subtype.ext (Prod.ext e₂ ?_)
      exact congrArg (fun r : M.obj W => r.1.2) e₁
    · intro r x hx
      refine ⟨⟨(x, r.1.2), (hcond W _ _).2 ?_⟩, ?_, rfl⟩
      · have hx' : s.app W x = r.1.1 := hx.symm
        rw [hx']
        exact r.2
      · exact Subtype.ext (Prod.ext hx.symm rfl)
  have h₂ : IsPullback τ₂ (fibreSnd a' (t ≫ b')) (fibreSnd a' b') t := by
    refine IsPullback.of_forall_isPullback_app fun W => ?_
    rw [Limits.Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext p
      rfl
    · rintro p p' ⟨e₁, e₂⟩
      refine Subtype.ext (Prod.ext ?_ e₂)
      exact congrArg (fun r : (fibreProduct a' b').obj W => r.1.1) e₁
    · intro r y hy
      have hy' : t.app W y = r.1.2 := hy.symm
      refine ⟨⟨(r.1.1, y), ?_⟩, ?_, rfl⟩
      · change a'.app W r.1.1 = b'.app W (t.app W y)
        rw [hy']
        exact r.2
      · exact Subtype.ext (Prod.ext rfl hy')
  have c₁ : IsClosedImm τ₁ :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h₁.flip hs
  have c₂ : IsClosedImm τ₂ :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h₂.flip ht
  rw [hτeq]
  have inst : MorphismProperty.IsStableUnderComposition (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) :=
    ⟨fun {X Y Z} f g hf hg => by
      have h1 : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map f) := hf
      have h2 : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g) := hg
      change IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (f ≫ g))
      rw [Functor.map_comp]
      infer_instance⟩
  exact MorphismProperty.comp_mem (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) _ _ c₁ c₂

end Closed

section Fibre

variable {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
  {X Y Z : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u}
  (pX : IndPresentation.{u, v, u} P X) (pY : IndPresentation.{u, v, u} P Y)
  (pZ : IndPresentation.{u, v, u} P Z) (f : X ⟶ Z) (g : Y ⟶ Z)

/-- **Remark 14.2**: ind-spaces with quasi-compact terms are closed under fibre products, for any
property `P` of the terms stable under fibre products of presheaves.
The quasi-compactness of the terms is an added assumption: the remark states closure without it, its
proof in the paper's source uses it to factor `X_i → Z` over a `Z_k`. -/
theorem exists_indPresentation_fibreProduct
    (hZ : ∀ k, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pZ.obj k))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i))
    (hY : ∀ j, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pY.obj j))
    (hP : ∀ (i : pX.I) (j : pY.I) (k : pZ.I) (a : pX.obj i ⟶ pZ.obj k) (b : pY.obj j ⟶ pZ.obj k),
      P (fibreProduct a b)) :
    Nonempty (IndPresentation.{u, v, u} P (fibreProduct f g)) := by
  classical
  choose kx α hα using exists_indHom_term pX pZ hZ hX f
  choose ky β hβ using exists_indHom_term pY pZ hZ hY g
  have hub : ∀ q : pX.I × pY.I, ∃ k, kx q.1 ≤ k ∧ ky q.2 ≤ k := fun q => exists_ge_ge _ _
  choose K hK₁ hK₂ using hub
  let a : ∀ q : pX.I × pY.I, pX.obj q.1 ⟶ pZ.obj (K q) := fun q => α q.1 ≫ pZ.tr (hK₁ q)
  let b : ∀ q : pX.I × pY.I, pY.obj q.2 ⟶ pZ.obj (K q) := fun q => β q.2 ≫ pZ.tr (hK₂ q)
  have ha : ∀ q A x, pZ.π (K q) A ((a q).app _ x) = f.app _ (pX.π q.1 A x) := fun q A x =>
    (pZ.π_tr _ _ _).trans (hα q.1 A x)
  have hb : ∀ q A y, pZ.π (K q) A ((b q).app _ y) = g.app _ (pY.π q.2 A y) := fun q A y =>
    (pZ.π_tr _ _ _).trans (hβ q.2 A y)
  -- membership in the term is tested on affine schemes, on `X`, `Y`
  have hcond : ∀ (q : pX.I × pY.I) (W : (BigFppfOver B S hS)ᵒᵖ) (x : (pX.obj q.1).obj W)
      (y : (pY.obj q.2).obj W), (a q).app W x = (b q).app W y ↔
      ∀ (A : BigAffineFppf B S hS) (s : (BigAffineFppf.inclusion B S hS).obj A ⟶ unop W),
        f.app _ (pX.π q.1 A ((pX.obj q.1).map s.op x)) = g.app _ (pY.π q.2 A ((pY.obj q.2).map s.op y)) := by
    intro q W x y
    constructor
    · intro h A s
      rw [← ha, ← hb, hom_naturality_apply, hom_naturality_apply]
      exact congrArg (fun z => pZ.π (K q) A ((pZ.obj (K q)).map s.op z)) h
    · intro h
      refine ind_sep_affine (hZ (K q)) (T := unop W) fun A s => ind_π_injective pZ _ A ?_
      have e₁ := hom_naturality_apply (a q) s.op x
      have e₂ := hom_naturality_apply (b q) s.op y
      refine (congrArg _ e₁.symm).trans (Eq.trans ?_ (congrArg _ e₂))
      rw [ha, hb]
      exact h A s
  have mono : ∀ {q q' : pX.I × pY.I} (_ : q ≤ q') (W : (BigFppfOver B S hS)ᵒᵖ) (x : (pX.obj q.1).obj W)
      (y : (pY.obj q.2).obj W), (hle : q.1 ≤ q'.1) → (hle' : q.2 ≤ q'.2) →
      ((a q).app W x = (b q).app W y ↔
        (a q').app W ((pX.tr hle).app W x) = (b q').app W ((pY.tr hle').app W y)) := by
    intro q q' _ W x y hle hle'
    rw [hcond q, hcond q']
    refine forall₂_congr fun A s => ?_
    have e₁ : pX.π q'.1 A ((pX.obj q'.1).map s.op ((pX.tr hle).app W x)) =
        pX.π q.1 A ((pX.obj q.1).map s.op x) := by
      rw [← hom_naturality_apply, pX.π_tr]
    have e₂ : pY.π q'.2 A ((pY.obj q'.2).map s.op ((pY.tr hle').app W y)) =
        pY.π q.2 A ((pY.obj q.2).map s.op y) := by
      rw [← hom_naturality_apply, pY.π_tr]
    rw [e₁, e₂]
  have : IsDirectedOrder (pX.I × pY.I) := ⟨fun q q' => by
    obtain ⟨i, h₁, h₂⟩ := exists_ge_ge q.1 q'.1
    obtain ⟨j, h₃, h₄⟩ := exists_ge_ge q.2 q'.2
    exact ⟨(i, j), ⟨h₁, h₃⟩, ⟨h₂, h₄⟩⟩⟩
  let trm : ∀ {q q' : pX.I × pY.I}, q ≤ q' → (fibreProduct (a q) (b q) ⟶ fibreProduct (a q') (b q')) :=
    fun {q q'} h =>
      { app := fun W => ↾ fun p => ⟨((pX.tr h.1).app W p.1.1, (pY.tr h.2).app W p.1.2),
          (mono h W _ _ h.1 h.2).1 p.2⟩
        naturality := fun W W' s => by
          ext p
          refine Subtype.ext (Prod.ext ?_ ?_)
          · exact hom_naturality_apply (pX.tr h.1) s p.1.1
          · exact hom_naturality_apply (pY.tr h.2) s p.1.2 }
  exact ⟨{ I := pX.I × pY.I
           obj := fun q => fibreProduct (a q) (b q)
           prop := fun q => hP _ _ _ _ _
           tr := trm
           tr_refl := fun q => by
             ext W p
             refine Subtype.ext (Prod.ext ?_ ?_)
             · exact congrArg (fun t => t.app W p.1.1) (pX.tr_refl q.1)
             · exact congrArg (fun t => t.app W p.1.2) (pY.tr_refl q.2)
           tr_trans := fun h₁ h₂ => by
             ext W p
             refine Subtype.ext (Prod.ext ?_ ?_)
             · exact congrArg (fun t => t.app W p.1.1) (pX.tr_trans h₁.1 h₂.1)
             · exact congrArg (fun t => t.app W p.1.2) (pY.tr_trans h₁.2 h₂.2)
           closed := fun {q q'} h =>
             isClosedImm_fibre_map (pX.tr h.1) (pY.tr h.2) (pX.closed h.1) (pY.closed h.2)
               (fun W x y => mono h W x y h.1 h.2) (trm h) (fun _ _ => rfl)
           π := fun q A p => ⟨(pX.π q.1 A p.1.1, pY.π q.2 A p.1.2), by
             rw [← ha q, ← hb q]
             exact congrArg _ p.2⟩
           π_map := fun q {A A'} s p => Subtype.ext (Prod.ext (pX.π_map _ _ _) (pY.π_map _ _ _))
           π_tr := fun h A p => Subtype.ext (Prod.ext (pX.π_tr _ _ _) (pY.π_tr _ _ _))
           surj := fun A p => by
             obtain ⟨i, x, hx⟩ := pX.surj A p.1.1
             obtain ⟨j, y, hy⟩ := pY.surj A p.1.2
             refine ⟨(i, j), ⟨(x, y), ind_π_injective pZ _ A ?_⟩, Subtype.ext (Prod.ext hx hy)⟩
             have e₁ := ha (i, j) A x
             have e₂ := hb (i, j) A y
             refine e₁.trans (Eq.trans ?_ e₂.symm)
             change f.app _ (pX.π i A x) = g.app _ (pY.π j A y)
             rw [hx, hy]
             exact p.2
           inj := fun q A p p' h => by
             have h₁ : pX.π q.1 A p.1.1 = pX.π q.1 A p'.1.1 := congrArg (fun r => r.1.1) h
             have h₂ : pY.π q.2 A p.1.2 = pY.π q.2 A p'.1.2 := congrArg (fun r => r.1.2) h
             obtain ⟨i, hi, e₁⟩ := pX.inj _ A _ _ h₁
             obtain ⟨j, hj, e₂⟩ := pY.inj _ A _ _ h₂
             exact ⟨(i, j), ⟨hi, hj⟩, Subtype.ext (Prod.ext e₁ e₂)⟩ }⟩

/-- **Remark 14.2**: ind-algebraic spaces with quasi-compact terms are closed under fibre products. -/
theorem isIndAlgebraicSpace_fibreProduct
    (pX : IndPresentation.{u, v, u} (IsAlgebraicSpace B S hS) X)
    (pY : IndPresentation.{u, v, u} (IsAlgebraicSpace B S hS) Y)
    (pZ : IndPresentation.{u, v, u} (IsAlgebraicSpace B S hS) Z) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i))
    (hY : ∀ j, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pY.obj j)) :
    IsIndAlgebraicSpace.{u, v} (fibreProduct f g) :=
  exists_indPresentation_fibreProduct pX pY pZ f g
    (fun k => (isSheaf_iff_isSheaf_of_type _ _).mp (pZ.prop k).isSheaf) hX hY
    (fun i j k a b => isAlgebraicSpace_of_isPullback (pX.prop i) (pY.prop j) (pZ.prop k).isSheaf
      (pZ.prop k).diagonal_representable (isPullback_fibreProduct a b))

end Fibre

#print axioms AlgMag.isIndAlgebraicSpace_fibreProduct

end AlgMag

end PartP6
