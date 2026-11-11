/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartFormal
import AlgMag.ChartFormalC

/-!
# The bridge from the orbit tower to `T = Spec C → X` (chart-lemma proof, §§2–4)

* `exists_section5_input`: from `X`, the closed orbit `o : O → X` and Theorem 4.1, the object
  `T = Spec C`, the map `φ : T → X`, and the inputs of §5.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

set_option synthInstance.maxHeartbeats 400000

namespace AlgMag.ChartAssembly

open ChartMain ChartS5 ChartPoint

section Rings

variable {A K M : Type*} [CommRing A] [CommRing K] [AddCommGroup M] [DecidableEq M]
  {N : AddSubgroup M} (𝒜 : M → AddSubgroup A) [GradedRing 𝒜]
  (ψ : A →+* AddMonoidAlgebra K N)
  (hdeg : ∀ d, ∀ a ∈ 𝒜 d, ∀ z : N, (ψ a).coeff z ≠ 0 → (z : M) = d)

include hdeg in
lemma coeff_decompose (x : A) (y : N) :
    (ψ x).coeff y = (ψ (decompose 𝒜 x (y : M) : A)).coeff y := by
  induction x using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    by_cases h : (y : M) = i
    · rw [h, decompose_coe, of_eq_same]
    · rw [decompose_of_mem_ne 𝒜 a.2 (Ne.symm h), map_zero]
      by_contra hne
      exact h (hdeg i a a.2 y hne)
  | add a b ha hb =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb, decompose_add, DirectSum.add_apply,
      AddMemClass.coe_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

include hdeg in
lemma exists_homog_lift_single (hψ : Function.Surjective ψ) (z : N) (b : K) :
    ∃ w ∈ 𝒜 (z : M), ψ w = AddMonoidAlgebra.single z b := by
  classical
  obtain ⟨w0, hw0⟩ := hψ (AddMonoidAlgebra.single z b)
  refine ⟨_, SetLike.coe_mem (decompose 𝒜 w0 (z : M)), ?_⟩
  ext y
  by_cases hy : y = z
  · subst hy
    rw [← coeff_decompose 𝒜 ψ hdeg, hw0]
  · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (fun e => hy e.symm)]
    by_contra hne
    exact hy (Subtype.ext (hdeg _ _ (SetLike.coe_mem _) y hne))

include hdeg in
/-- `C/m = K[N]` is generated over `ℤ` by finitely many homogeneous elements, for `K` finite and `N`
finitely generated. -/
theorem exists_hgen [Finite K] [AddMonoid.FG N] (hψ : Function.Surjective ψ) (m : Ideal A)
    (hm : ∀ a, a ∈ m ↔ ψ a = 0) :
    ∃ T : Finset A, (∀ t ∈ T, ∃ d, t ∈ 𝒜 d) ∧
      ∀ c : A, ∃ p ∈ Algebra.adjoin ℤ (T : Set A), c - p ∈ m := by
  classical
  haveI := Fintype.ofFinite K
  choose w hw hψw using exists_homog_lift_single 𝒜 ψ hdeg hψ
  obtain ⟨Sg, hSg⟩ := (AddMonoid.fg_def.1 (inferInstance : AddMonoid.FG N))
  let T : Finset A := Finset.univ.image (fun b => w 0 b) ∪ Sg.image (fun z => w z 1)
  refine ⟨T, ?_, fun c => ?_⟩
  · intro t ht
    rcases Finset.mem_union.1 ht with h | h
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 h
      exact ⟨_, hw 0 b⟩
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 h
      exact ⟨_, hw z 1⟩
  let Sb := (Algebra.adjoin ℤ (T : Set A)).map ψ.toIntAlgHom
  have h0 : ∀ b, AddMonoidAlgebra.single (0 : N) b ∈ Sb := fun b =>
    ⟨w 0 b, Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ b)))), hψw 0 b⟩
  have h1 : ∀ z : N, AddMonoidAlgebra.single z (1 : K) ∈ Sb := by
    intro z
    have hz : z ∈ AddSubmonoid.closure (Sg : Set N) := by rw [hSg]; trivial
    induction hz using AddSubmonoid.closure_induction with
    | mem z hz =>
      exact ⟨w z 1, Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ hz))), hψw z 1⟩
    | zero => exact h0 1
    | add a b _ _ ha hb =>
      have := Sb.mul_mem ha hb
      rwa [AddMonoidAlgebra.single_mul_single, one_mul] at this
  have hall : ∀ y : AddMonoidAlgebra K N, y ∈ Sb := by
    intro y
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => exact Sb.zero_mem
    | add p q hp hq => exact Sb.add_mem hp hq
    | single z b =>
      have := Sb.mul_mem (h0 b) (h1 z)
      rwa [AddMonoidAlgebra.single_mul_single, zero_add, mul_one] at this
  obtain ⟨p, hp, hpe⟩ := hall (ψ c)
  refine ⟨p, hp, (hm _).2 ?_⟩
  rw [map_sub, sub_eq_zero]
  exact hpe.symm

end Rings

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  [IsAffine S] [AddMonoid.FG M] [DecidableEq M]

/-- A map invariant under the action is in degree `0`. -/
theorem mem_homog_zero_of_invariant {U V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (t : U ⟶ V)
    (h : ∀ (W : BigFppfOver B S hS) (t0 : W ⟶ U)
      (g : Multiplicative M →* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)),
      smulAt actU g t0 ≫ t = t0 ≫ t) (a : RT V) :
    ((BigFppfOver.toScheme B S hS).map t).appTop.hom a ∈ homog actU 0 := by
  change ChartMain.coact actU _ = _
  apply (spSec_bijective U (ι1 U (M := M)) contains1).1
  rw [spSec_coact, ← cmapComp]
  have e : univMap actU ≫ t = spToT U (ι1 U (M := M)) contains1 ≫ t := h _ _ _
  rw [e, cmapComp, spToT_appTop]
  rfl

/-- `Γ(P) → Γ(O)` is in degree `0`. -/
theorem oπ_mem {P : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] (N : AddSubgroup M) [AddMonoid.FG N] (a : RT P) :
    ((BigFppfOver.toScheme B S hS).map (Oπ P N)).appTop.hom a ∈ homog (oAct (P := P) N) 0 :=
  mem_homog_zero_of_invariant (oAct (P := P) N) (Oπ P N) (fun _ t g => oSmul_π N g t) a

/-- **§1**: `κ(x)` is finite: `S` of finite type over `ℤ`, `X` locally of finite type over `S`
(`AlgMag.ChartPoint.finite_of_chartPoint` uses only this). -/
theorem finite_of_chartPoint_lft (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X)
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (p : AlgMag.ChartPoint X) : Finite (RT p.P) := by
  obtain ⟨U, φ, hs, he⟩ := hX.exists_atlas
  have hK := isField_of_chartPoint p
  let T1 : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let hT : IsTerminal T1 := Over.mkIdTerminal
  let hY : IsTerminal (yoneda.obj T1) := Limits.IsTerminal.isTerminalObj yoneda T1 hT
  let b : yoneda.obj T1 ≅ ⊤_ _ := hY.uniqueUpToIso terminalIsTerminal
  have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b.hom := Space.presheaf_etale_of_iso B S hS b
  have hl : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (hT.from U)) :=
    hlft U T1 φ b.hom (hT.from U) he hb (Subsingleton.elim _ _ |>.trans rfl)
  have sq := hs.rep.isPullback p.x
  let Y := hs.rep.pullback p.x
  let toP : Y ⟶ p.P := hs.rep.snd p.x
  obtain ⟨toU, htoU⟩ := yoneda.map_surjective (hs.rep.fst p.x)
  have sq' : IsPullback (yoneda.map toP) (yoneda.map toU) p.x φ := by
    rw [htoU]; exact sq.flip
  have hcl : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map toU) :=
    p.isClosed.property _ _ _ sq'
  have hsu : Surjective ((BigFppfOver.toScheme B S hS).map toP) := hs.property_snd p.x
  have hP : IsAffine ((BigFppfOver.toScheme B S hS).obj p.P) := isAffine_of_chartPoint p
  letI : Field (RT p.P) := hK.toField
  letI := p.field
  let y0 : (BigFppfOver.toScheme B S hS).obj p.P :=
    p.iso.inv (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum p.k)
  obtain ⟨y, -⟩ := ((BigFppfOver.toScheme B S hS).map toP).surjective y0
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI := hl
  haveI hSft' : LocallyOfFiniteType
      (terminal.from ((BigFppfOver.toScheme B S hS).obj T1)) := hSft
  let e := terminalIsoIsTerminal specULiftZIsTerminal.{u}
  let g : (BigFppfOver.toScheme B S hS).obj Y ⟶ Spec (.of (ULift.{u} ℤ)) :=
    (BigFppfOver.toScheme B S hS).map toU ≫ (BigFppfOver.toScheme B S hS).map (hT.from U) ≫
      terminal.from ((BigFppfOver.toScheme B S hS).obj T1) ≫ e.hom
  have hg : LocallyOfFiniteType g := inferInstance
  have hft1 := g.finiteType_appLE (U := ⊤) (V := W) (isAffineOpen_top _) hW le_top
  let R : Type u := Γ((BigFppfOver.toScheme B S hS).obj Y, W)
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
  haveI : Nontrivial R := Scheme.component_nontrivial _ W
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  let φ0 : ULift.{u} ℤ →+* R :=
    (g.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv.hom
  have hφ0 : φ0.FiniteType := hft1.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv).2)
  haveI : Finite (R ⧸ m) := finite_quot_of_ft φ0 hφ0 m
  letI := Ideal.Quotient.field m
  let ψ : RT p.P →+* R ⧸ m :=
    (Ideal.Quotient.mk m).comp
      (((BigFppfOver.toScheme B S hS).obj Y).presheaf.map (homOfLE le_top).op).hom |>.comp
      ((BigFppfOver.toScheme B S hS).map toP).appTop.hom
  exact Finite.of_injective ψ ψ.injective

/-- A closed immersion from an object into an iso-image: `F ≃ Z`, `Z ⊂ X` closed. -/
lemma closedP_of_range {U : BigFppfOver B S hS} {c : yoneda.obj U ⟶ X} [Mono c] {Z : Subfunctor X}
    (hr : Subfunctor.range c = Z) (hZ : ClosedP Z.ι) : ClosedP c := by
  have hi := Subfunctor.isIso_lift hr.le hr.ge
  have e : Subfunctor.lift c hr.le ≫ Z.ι = c := Subfunctor.lift_ι _ _
  have hp := Space.closedImmersionPresheafProperty B S hS
  rw [← e]
  refine MorphismProperty.comp_mem _ _ _ ?_ hZ
  exact MorphismProperty.of_isIso _ _

lemma closedP_yoneda_iso {U V : BigFppfOver B S hS} (l : U ⟶ V) [IsIso l] : ClosedP (X := yoneda.obj V) (yoneda.map l) :=
  MorphismProperty.of_isIso _ _

/-- The ideal of a closed `o'`, given any base change square. -/
lemma idealOf_eq_ker_of_isPullback {O' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {o' : O' ⟶ X}
    (ho' : ClosedP o') {Z V : BigFppfOver B S hS} {s : Z ⟶ V} {k : yoneda.obj Z ⟶ O'}
    {e : yoneda.obj V ⟶ X} (sq : IsPullback k (yoneda.map s) o' e) :
    idealOf ho' e = ((BigFppfOver.toScheme B S hS).map s).ker := by
  have s1 := ho'.rep.isPullback e
  let i := sq.isoIsPullback _ _ s1
  have hi : i.hom ≫ yoneda.map (ho'.rep.snd e) = yoneda.map s := sq.isoIsPullback_hom_snd _ _ s1
  let i' : Z ≅ ho'.rep.pullback e := yoneda.preimageIso i
  have hi' : i'.hom ≫ ho'.rep.snd e = s := yoneda.map_injective (by
    rw [Functor.map_comp, ← hi]
    simp [i'])
  have e2 : (BigFppfOver.toScheme B S hS).map s =
      (BigFppfOver.toScheme B S hS).map i'.hom ≫ (BigFppfOver.toScheme B S hS).map (ho'.rep.snd e) := by
    rw [← Functor.map_comp, hi']
  rw [e2, Scheme.Hom.ker_comp_of_isIso]
  rfl

/-- **The inputs of §5**, on `T = Spec C`: see `section5Output_of_input`. -/
structure Section5Input (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (actT : AAction (fppfO B S hS) M (yoneda.obj T))
    (m : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (φ : yoneda.obj T ⟶ X) (u : p.P ⟶ T) : Prop where
  complete : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m
  noeth : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
  equivariant : IsEquivariant actT actX φ
  liesOver : yoneda.map u ≫ φ = p.x
  kills : ∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map u).appTop.hom c = 0
  surj : Function.Surjective ((BigFppfOver.toScheme B S hS).map u).appTop.hom
  hgen : ∃ T₀ : Finset Γ((BigFppfOver.toScheme B S hS).obj T, ⊤), (∀ t ∈ T₀, ∃ d, t ∈ homog actT d) ∧
    ∀ c, ∃ q ∈ Algebra.adjoin ℤ (T₀ : Set Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)), c - q ∈ m
  hOfC : ∀ d, ∀ c ∈ homog actT d, c ∉ m → ∃ c', c * c' - 1 ∈ m
  hMono : ∀ {T' : BigFppfOver B S hS} (a b : T' ⟶ T),
    (∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map a).appTop.hom c = 0) →
    (∀ c ∈ m, ((BigFppfOver.toScheme B S hS).map b).appTop.hom c = 0) →
    φ.app (op T') a = φ.app (op T') b → a = b
  thick : ∀ j : ℕ, 1 ≤ j → ∃ ho : ClosedP (yoneda.map (Chart.immι T
      (Chart.closedι ((BigFppfOver.toScheme B S hS).obj T) (m ^ j))) ≫ φ),
    ∀ {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      (e : yoneda.obj V ⟶ X) (v : p.P ⟶ V), yoneda.map v ≫ e = p.x →
      (idealOf ho e).ideal ⟨⊤, isAffineOpen_top _⟩ ≤
        RingHom.ker ((BigFppfOver.toScheme B S hS).map v).appTop.hom ^ j

lemma appTop_bijective_of_iso {U V : BigFppfOver B S hS} (l : U ⟶ V) [IsIso l] :
    Function.Bijective ((BigFppfOver.toScheme B S hS).map l).appTop.hom := by
  refine Function.bijective_iff_has_inverse.2 ⟨((BigFppfOver.toScheme B S hS).map (inv l)).appTop.hom,
    fun x => ?_, fun x => ?_⟩
  · change ((BigFppfOver.toScheme B S hS).map (inv l)).appTop.hom (((BigFppfOver.toScheme B S hS).map l).appTop.hom x) = x
    rw [← cmapComp, IsIso.inv_hom_id]
    simp
  · rw [← cmapComp, IsIso.hom_inv_id]
    simp

section CT

variable {C : Type u} [CommRing C] {𝒞 : M → AddSubgroup C} [GradedRing 𝒞]
  (D : CTower B S hS M C 𝒞) (c : ∀ n, yoneda.obj (D.U n) ⟶ X)
  (hcj : ∀ n, yoneda.map (D.j n) ≫ c (n + 1) = c n)
  (actX : AAction (fppfO B S hS) M X) (hce : ∀ n, IsEquivariant (D.act n) actX (c n))
  {φ : yoneda.obj D.Tb ⟶ X}
  (hφ : ∀ n, φ.app (op (D.Vn n)) (D.ιn n) = D.pt c (D.ιn n) n (D.ι_kills' n))
  (hφe : IsEquivariant D.actTb actX φ)

include hce in
/-- `O → T` is equivariant. -/
lemma equivariant_i {P : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
    {N : AddSubgroup M} [AddMonoid.FG N] {o : yoneda.obj (Ob P N) ⟶ X}
    (hoe : IsEquivariant (oAct N) actX o) (e0 : Ob P N ⟶ D.U 0) (he0 : yoneda.map e0 ≫ c 0 = o)
    (hm : Mono (c 0)) : IsEquivariant (oAct N) D.actTb (yoneda.map (e0 ≫ D.sn 0)) := by
  have hinj := fun A => (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hm A)
  have h1 : IsEquivariant (oAct N) (D.act 0) (yoneda.map e0) := fun {A} g t => hinj A (by
    have e1 : ∀ x, (c 0).app A ((yoneda.map e0).app A x) = o.app A x := fun x =>
      congrArg (fun z => z.app A x) he0
    rw [e1, hoe, hce 0, e1])
  have h2 : IsEquivariant (D.act 0) D.actTb (yoneda.map (D.sn 0)) :=
    equivariant_rLift D.ρ D.hC 𝒞 D.h0 (D.act 0) (D.ev 0) (D.ev_ρ 0) (D.ev_mem 0)
  intro A g t
  rw [Functor.map_comp]
  exact (congrArg _ (h1 g t)).trans (h2 g _)

variable (p : AlgMag.ChartPoint X) {N : AddSubgroup M} [AddMonoid.FG N]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj p.P)] {o : yoneda.obj (Ob p.P N) ⟶ X}

include hcj hφ hφe hce in
/-- **§§3–4**: the inputs of §5 for a `CTower`. -/
theorem CTower.section5Input (hK : IsField (RT p.P)) (hfin : Finite (RT p.P))
    (ho : ClosedP o) (hoe : IsEquivariant (oAct N) actX o)
    (u : p.P ⟶ Ob p.P N) (hux : yoneda.map u ≫ o = p.x)
    (e0 : Ob p.P N ⟶ D.U 0) [IsIso e0] (he0 : yoneda.map e0 ≫ c 0 = o)
    (hcm : Mono (c 0)) (hcl : ∀ n, ClosedP (c n))
    (hth : ∀ (n : ℕ) {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      (e : yoneda.obj V ⟶ X), ∃ (Z : BigFppfOver B S hS) (s : Z ⟶ V) (k : yoneda.obj Z ⟶ yoneda.obj (D.U n)),
        IsPullback k (yoneda.map s) (c n) e ∧
        IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s) ∧
        RingHom.ker ((BigFppfOver.toScheme B S hS).map s).appTop.hom = chartIdeal ho e ^ (n + 1)) :
    Section5Input actX p D.actTb D.mTb φ (u ≫ e0 ≫ D.sn 0) := by
  let G := BigFppfOver.toScheme B S hS
  let i : Ob p.P N ⟶ D.Tb := e0 ≫ D.sn 0
  have hsn : Function.Surjective (G.map (D.sn 0)).appTop.hom := fun y => by
    obtain ⟨a, rfl⟩ := D.ev_surj 0 y
    exact ⟨D.sec a, D.sn_appTop 0 a⟩
  have hisurj : Function.Surjective (G.map i).appTop.hom := fun y => by
    obtain ⟨a, rfl⟩ := (appTop_bijective_of_iso e0).2 y
    obtain ⟨b, rfl⟩ := hsn a
    exact ⟨b, cmapComp e0 (D.sn 0) b⟩
  have hicl : IsClosedImmersion (G.map i) :=
    IsClosedImmersion.of_surjective_of_isAffine _ (by exact hisurj)
  have hker : ∀ x, x ∈ D.mTb ↔ (G.map i).appTop.hom x = 0 := fun x => by
    rw [D.mem_mTb_iff]
    change _ ↔ (G.map (e0 ≫ D.sn 0)).appTop.hom x = 0
    rw [cmapComp]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      exact (appTop_bijective_of_iso e0).1 (h.trans (map_zero _).symm)
  have hieq : IsEquivariant (oAct N) D.actTb (yoneda.map i) :=
    equivariant_i D c actX hce hoe e0 he0 hcm
  -- `u` is a closed immersion
  have hmo : Mono o := mono_of_closedP ho
  have hucl : IsClosedImmersion (G.map u) :=
    (Space.presheaf_yoneda_map_iff B S hS inferInstance u).1
      (closedP_of_comp_mono p.isClosed o hux)
  have husurj : Function.Surjective (G.map u).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (G.map u)).2
  have hcomp : ∀ x, (G.map (u ≫ e0 ≫ D.sn 0)).appTop.hom x =
      (G.map u).appTop.hom ((G.map i).appTop.hom x) := fun x => cmapComp _ _ x
  have hsn_phi := D.sn_phi c hcj hφ
  refine
    { complete := D.complete_Tb
      noeth := ?_
      equivariant := hφe
      liesOver := ?_
      kills := fun x hx => by rw [hcomp, (hker x).1 hx, map_zero]
      surj := fun y => by
        obtain ⟨a, rfl⟩ := husurj y
        obtain ⟨b, rfl⟩ := hisurj a
        exact ⟨b, hcomp b⟩
      hgen := ?_
      hOfC := ?_
      hMono := fun a b ha hb hab => D.hMono c hcj hφ hcm a b ha hb hab
      thick := ?_ }
  · letI := gradedRingOfAction D.actTb
    exact D.complete_Tb.noeth
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hsn_phi, he0, hux]
  · letI := gradedRingOfAction D.actTb
    let ee := RingEquiv.ofBijective (spSec p.P (AddMonoidAlgebra.singleZeroRingHom : RT p.P →+* RN p.P N) (containsN N))
      (spSec_bijective p.P (AddMonoidAlgebra.singleZeroRingHom : RT p.P →+* RN p.P N) (containsN N))
    let ψ : Γ(G.obj D.Tb, ⊤) →+* RN p.P N := (ee.symm : _ →+* _).comp (G.map i).appTop.hom
    refine exists_hgen (homog D.actTb) ψ ?_ (ee.symm.surjective.comp hisurj) D.mTb fun a => ?_
    · intro d a ha z hz
      refine coeff_eq_zero_of_homog N (d := d) (y := ψ a) ?_ hz
      have h1 := map_mem_homog (U := Ob p.P N) (V := D.Tb) (oAct (P := p.P) N) D.actTb hieq ha
      have e' : spSec p.P (AddMonoidAlgebra.singleZeroRingHom : RT p.P →+* RN p.P N) (containsN N) (ψ a) =
          (G.map i).appTop.hom a := ee.apply_symm_apply _
      rw [e']
      exact h1
    · rw [hker]
      exact (map_eq_zero_iff _ ee.symm.injective).symm
  · intro d x hx hxm
    have hI : ∀ y, y ∈ D.mTb ↔ y ∈ RingHom.ker (G.map i).appTop.hom := fun y => by
      rw [hker, RingHom.mem_ker]
    obtain ⟨c', hc'⟩ := hOf_of_orbit N hK D.actTb i hieq hicl hx (fun h => hxm ((hI x).2 h))
    exact ⟨c', (hI _).2 hc'⟩
  · intro j hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    have hl := D.isIso_trunc n
    have htr := D.trunc_phi c hcj hφ n
    have ho' : ClosedP (yoneda.map (D.ιn (n + 1)) ≫ φ) := by
      rw [htr]
      exact MorphismProperty.comp_mem _ _ _ (closedP_yoneda_iso _) (hcl n)
    refine ⟨ho', fun {V} _ e v hv => ?_⟩
    obtain ⟨Z, s, k, sq, hsc, hsk⟩ := hth n e
    let l := D.lift (D.ιn (n + 1)) n (D.ι_kills n)
    let W : yoneda.obj (D.U n) ≅ yoneda.obj (D.Vn (n + 1)) := (asIso (yoneda.map l)).symm
    have sq' : IsPullback (k ≫ W.hom) (yoneda.map s) (yoneda.map (D.ιn (n + 1)) ≫ φ) e := by
      refine IsPullback.of_iso sq (Iso.refl _) W (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
      rw [htr]
      simp [W]
    have hkk := idealOf_eq_ker_of_isPullback ho' sq'
    have hI : (idealOf ho' e).ideal ⟨⊤, isAffineOpen_top _⟩ = RingHom.ker (G.map s).appTop.hom := by
      rw [hkk]
      simp only [Scheme.Hom.ker_apply]
      rfl
    have hle : chartIdeal ho e ≤ RingHom.ker (G.map v).appTop.hom := by
      have hw : yoneda.map u ≫ o = yoneda.map v ≫ e := hux.trans hv.symm
      let τ := ho.rep.lift' u v hw
      have hτ : τ ≫ ho.rep.snd e = v := ho.rep.lift'_snd _ _ _
      intro x hx
      rw [RingHom.mem_ker] at hx ⊢
      rw [← hτ, cmapComp, hx, map_zero]
    change (idealOf ho' e).ideal ⟨⊤, isAffineOpen_top _⟩ ≤ _
    rw [hI, hsk]
    exact Ideal.pow_right_mono hle _

end CT

section Concrete

/-- A mono from an object with image `Z ⊂ X` is `≃ Z`. -/
lemma exists_iso_of_range {U : BigFppfOver B S hS} {c : yoneda.obj U ⟶ X} [Mono c] {Z : Subfunctor X}
    (hr : Subfunctor.range c = Z) :
    ∃ W : yoneda.obj U ≅ Z.toFunctor, W.hom ≫ Z.ι = c := by
  have hi := Subfunctor.isIso_lift hr.le hr.ge
  exact ⟨asIso (Subfunctor.lift c hr.le), Subfunctor.lift_ι c hr.le⟩

variable {O : BigFppfOver B S hS} {o : yoneda.obj O ⟶ X} (ho : ClosedP o)
  {Ua : BigFppfOver B S hS} {φa : yoneda.obj Ua ⟶ X}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φa)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φa)

include hs he in
/-- `X_n ×_X V` for an affine `V`: the data `hth` of `CTower.section5Input`. -/
lemma thick_data {U : BigFppfOver B S hS} {c : yoneda.obj U ⟶ X} [Mono c] (n : ℕ)
    (hr : Subfunctor.range c = thickening ho φa n) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (e : yoneda.obj V ⟶ X) :
    ∃ (Z : BigFppfOver B S hS) (s : Z ⟶ V) (k : yoneda.obj Z ⟶ yoneda.obj U),
      IsPullback k (yoneda.map s) c e ∧
      IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s) ∧
      RingHom.ker ((BigFppfOver.toScheme B S hS).map s).appTop.hom = chartIdeal ho e ^ (n + 1) := by
  obtain ⟨W, hW⟩ := exists_iso_of_range hr
  obtain ⟨k, sq⟩ := exists_isPullback_thickening ho hs he e n
  refine ⟨thickChart ho e n, thickChartι ho e n, k ≫ W.inv, ?_, thickChartι_closed ho e n,
    ker_thickChartι_appTop ho e n⟩
  refine IsPullback.of_iso sq (Iso.refl _) W.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    (by simp)
  rw [← hW]
  simp

include hs he in
/-- `X_0 = O`. -/
lemma exists_orbit_iso {U : BigFppfOver B S hS} {c : yoneda.obj U ⟶ X} [Mono c]
    (hr : Subfunctor.range c = thickening ho φa 0) :
    ∃ e0 : O ⟶ U, IsIso e0 ∧ yoneda.map e0 ≫ c = o := by
  have hmo : Mono o := mono_of_closedP ho
  -- `o` lies in `X_0`
  have h1 : o.app (op O) (𝟙 O) ∈ (thickening ho φa 0).obj (op O) := by
    refine (mem_thickening_iff ho hs he 0 _).2 ?_
    have e : yonedaEquiv.symm (o.app (op O) (𝟙 O)) = 𝟙 _ ≫ o := by
      apply yonedaEquiv.injective
      simp [yonedaEquiv_apply]
    rw [e, idealOf_eq_bot_of_factors, zero_add, pow_one]
  rw [← hr] at h1
  obtain ⟨e0, he0⟩ := h1
  have he0' : yoneda.map e0 ≫ c = o := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact he0
  -- `c` factors through `o`
  have h2 : c.app (op U) (𝟙 U) ∈ (thickening ho φa 0).obj (op U) := by
    rw [← hr]
    exact ⟨𝟙 U, rfl⟩
  have h3 := (mem_thickening_iff ho hs he 0 _).1 h2
  have e : yonedaEquiv.symm (c.app (op U) (𝟙 U)) = c := by
    apply yonedaEquiv.injective
    simp [yonedaEquiv_apply]
  rw [e, zero_add, pow_one] at h3
  obtain ⟨f', hf'⟩ := exists_factors_of_idealOf_eq_bot ho c h3
  obtain ⟨f, rfl⟩ := yoneda.map_surjective f'
  refine ⟨e0, ⟨f, ?_, ?_⟩, he0'⟩
  · apply yoneda.map_injective
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, ← cancel_mono o, Category.assoc, hf', he0',
      Category.id_comp]
  · apply yoneda.map_injective
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, ← cancel_mono c, Category.assoc, he0', hf',
      Category.id_comp]

/-- **Lemma 3.2** for the tower of the orbit `O = Spec k[N]`. -/
theorem tower_complete {P : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
    (hK : IsField (RT P)) {N : AddSubgroup M} [AddMonoid.FG N] (Y : AffineTower B S hS M)
    (f0 : Y.U 0 ⟶ Ob P N) [IsIso f0] (hf0 : IsEquivariant (Y.act 0) (oAct N) (yoneda.map f0)) :
    ChartGraded.IsCompletePair Y.toThickeningSystem.𝒞 Y.toThickeningSystem.m ∧
      ∀ n, RingHom.ker (Y.toThickeningSystem.ev n) = Y.toThickeningSystem.m ^ (n + 1) := by
  let G := BigFppfOver.toScheme B S hS
  let r : RT P →+* Y.toThickeningSystem.O 0 := (G.map (f0 ≫ Oπ P N)).appTop.hom
  letI : Algebra (RT P) (Y.toThickeningSystem.O 0) := r.toAlgebra
  letI := hK.toField
  have hn : IsNoetherianRing (RT P) := inferInstance
  have halg : ∀ a : RT P, algebraMap (RT P) (Y.toThickeningSystem.O 0) a ∈ Y.toThickeningSystem.𝒜 0 0 := fun a => by
    change (G.map (f0 ≫ Oπ P N)).appTop.hom a ∈ homog (Y.act 0) 0
    rw [cmapComp]
    exact map_mem_homog (Y.act 0) (oAct N) hf0 (oπ_mem N a)
  have hft : Algebra.FiniteType (RT P) (Y.toThickeningSystem.O 0) := by
    refine (RingHom.finiteType_algebraMap).1 ?_
    change r.FiniteType
    have h1 : (AddMonoidAlgebra.singleZeroRingHom : RT P →+* RN P N).FiniteType := by
      change (algebraMap (RT P) (RN P N)).FiniteType
      exact (RingHom.finiteType_algebraMap).2 (AddMonoidAlgebra.finiteType_of_fg _ _)
    have e : r = ((G.map f0).appTop.hom.comp (spSec P _ (containsN N))).comp
        (AddMonoidAlgebra.singleZeroRingHom : RT P →+* RN P N) := RingHom.ext fun b => by
      change (G.map (f0 ≫ Oπ P N)).appTop.hom b = (G.map f0).appTop.hom (spSec P _ (containsN N) _)
      rw [cmapComp, spToT_appTop]
    rw [e]
    refine RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ ?_) h1
    exact (appTop_bijective_of_iso f0).2.comp (spSec_bijective P _ (containsN N)).2
  obtain ⟨h1, h2, -, -⟩ := Y.toThickeningSystem.lemma_3_2 (k := RT P) halg
  exact ⟨h1, fun n => (h2 n).1⟩

/-- The `CTower` of an affine tower. -/
noncomputable def ofAffineTower (Y : AffineTower B S hS M)
    (hc : ChartGraded.IsCompletePair Y.toThickeningSystem.𝒞 Y.toThickeningSystem.m)
    (hk : ∀ n, RingHom.ker (Y.toThickeningSystem.ev n) = Y.toThickeningSystem.m ^ (n + 1)) :
    CTower B S hS M Y.toThickeningSystem.C Y.toThickeningSystem.𝒞 where
  ρ := rhoC Y
  hC := contains_specC Y
  h0 := rhoC_mem Y
  m := Y.toThickeningSystem.m
  U := Y.U
  aff := Y.aff
  act := Y.act
  j := Y.j
  ev := Y.toThickeningSystem.ev
  ev_surj := Y.toThickeningSystem.ev_surj
  ev_ρ n := RingHom.ext fun s => ev_rhoC Y n s
  ev_mem _ _ _ hu := Y.toThickeningSystem.ev_mem hu
  ev_j n u := Y.toThickeningSystem.π_ev n u
  ker_ev := hk
  complete := hc

/-- **The bridge** (§§2–4 of the chart-lemma proof): `T = Spec C`, `φ : T → X` from
Theorem 4.1, and the inputs of §5. -/
theorem exists_section5_input (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X)
    (N : AddSubgroup M) [AddMonoid.FG N] (o : yoneda.obj (Ob p.P N) ⟶ X) (u : p.P ⟶ Ob p.P N)
    (ho : ClosedP o) (hoe : IsEquivariant (oAct N) actX o) (hux : yoneda.map u ≫ o = p.x)
    (heff : ChartConclude.EquivariantEffectivity X actX) :
    Finite (RT p.P) ∧
    ∃ (T : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
      (actT : AAction (fppfO B S hS) M (yoneda.obj T))
      (m : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (φ : yoneda.obj T ⟶ X) (u' : p.P ⟶ T),
      Section5Input actX p actT m φ u' := by
  haveI hP := isAffine_of_chartPoint p
  have hK := isField_of_chartPoint p
  have hfin := finite_of_chartPoint_lft hSft hX hlft p
  refine ⟨hfin, ?_⟩
  obtain ⟨Ua, φa, hs, he⟩ := hX.exists_atlas
  have hN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Ua) := by
    haveI := lft_chart hSft hlft he
    haveI : IsLocallyNoetherian (⊤_ Scheme.{u}) := terminal_noeth
    exact LocallyOfFiniteType.isLocallyNoetherian (terminal.from _)
  let D0 : OrbitInput actX := ⟨Ob p.P N, inferInstance, oAct N, o, ho, hoe⟩
  obtain ⟨Y, c, hcm, hcr, hce, hcj⟩ := exists_affineTower D0 hX hsep hs he hN
  haveI := hcm 0
  obtain ⟨e0, he0i, he0⟩ := exists_orbit_iso ho hs he (hcr 0)
  haveI := he0i
  have hinj := fun A => (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 (mono_of_closedP ho) A)
  have hf0 : IsEquivariant (Y.act 0) (oAct N) (yoneda.map (inv e0)) := fun {A} g t => hinj A (by
    have e1 : ∀ x, o.app A ((yoneda.map (inv e0)).app A x) = (c 0).app A x := fun x => by
      have : yoneda.map (inv e0) ≫ o = c 0 := by
        rw [← he0, ← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp]
      exact congrArg (fun z => z.app A x) this
    rw [e1, hoe, e1]
    exact hce 0 g t)
  obtain ⟨hc, hk⟩ := tower_complete hK Y (inv e0) hf0
  let D := ofAffineTower Y hc hk
  obtain ⟨φ, hφe, hφ⟩ := D.exists_phi c hcj actX hce heff
  have hcl : ∀ n, ClosedP (c n) := fun n => by
    haveI := hcm n
    exact closedP_of_range (hcr n) (isClosedSubspace_thickening ho hX hs he n).2
  refine ⟨D.Tb, inferInstance, D.actTb, D.mTb, φ, u ≫ e0 ≫ D.sn 0, ?_⟩
  let e0' : Ob p.P N ⟶ D.U 0 := e0
  haveI : IsIso e0' := he0i
  exact CTower.section5Input D c hcj actX hce hφ hφe p hK hfin ho hoe u hux e0' he0 (hcm 0) hcl
    (fun n V _ e => by
      haveI := hcm n
      exact thick_data ho hs he n (hcr n) e)

end Concrete

end Site

end AlgMag.ChartAssembly

#print axioms AlgMag.ChartAssembly.exists_section5_input
