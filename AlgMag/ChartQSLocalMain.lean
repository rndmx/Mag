/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSLocalCharts
import AlgMag.ChartStratumDecent

/-!
# `LocalModelStep` and noetherian algebraization for `X` quasi-separated

The non-graded Lemmas 3.4, 4.3, 4.4 are the
graded ones for the trivial group (`ChartQSLocalTriv`). The induction is on closed subspaces of `|X|`, all
thickenings at once, as `ChartQS.effective_of_noetherian`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS.ChartQSLocal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

set_option maxHeartbeats 4000000 in
/-- `θ = φ_n` on `Y/Iⁿ`: Step 3 for `b`, in the Jacobson radical of `Y/Iⁿ`. -/
theorem theta_restrict (hX : IsAlgebraicSpace B S hS X) {T Y : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤)] (p : Y ⟶ T)
    {m b : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)}
    (hb : b.map (sec p) ≤ Ideal.jacobson ⊥)
    (x : ∀ n, X.obj (op (Vc T (m ^ n)))) (χ : ∀ k, X.obj (op (Vc T (b ^ k))))
    (hχx : ∀ (k n : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ Vc T (b ^ k)) (g₂ : W ⟶ Vc T (m ^ n)),
      g₁ ≫ ιc T (b ^ k) = g₂ ≫ ιc T (m ^ n) → X.map g₁.op (χ k) = X.map g₂.op (x n))
    (θ : X.obj (op Y))
    (hθ : ∀ (l : ℕ) ⦃W : BigFppfOver B S hS⦄ (i : W ⟶ Y) (s : W ⟶ Vc T (b ^ l)),
      s ≫ ιc T (b ^ l) = i ≫ p → X.map i.op θ = X.map s.op (χ l))
    (n : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y) (s : W ⟶ Vc T (m ^ n))
    (hs : s ≫ ιc T (m ^ n) = i ≫ p) : X.map i.op θ = X.map s.op (x n) := by
  let En : Ideal Γ((SCH).obj Y, ⊤) := (m ^ n).map (sec p)
  obtain ⟨r, hr⟩ := exists_sY p n (m := m)
  haveI hNn : IsNoetherianRing Γ((SCH).obj (Vc Y En), ⊤) :=
    isNoetherianRing_of_surjective _ _ (sec (ιc Y En)) (ιc_surj _)
  let A : Ideal Γ((SCH).obj (Vc Y En), ⊤) := (b.map (sec p)).map (sec (ιc Y En))
  have hA : A ≤ Ideal.jacobson ⊥ := Ideal.map_le_iff_le_comap.2 fun c hc =>
    jac_lift (sec (ιc Y En)) ⊥ bot_le (fun z => by
      obtain ⟨c', hc'⟩ := ιc_surj En z
      exact ⟨c', by rw [hc', sub_self]; exact Ideal.zero_mem _⟩) (hb hc)
  have key : X.map (ιc Y En).op θ = X.map r.op (x n) := by
    refine ChartQS.eq_of_agree_pow hX (Vc Y En) A hA _ _ fun k => ?_
    let e := ιc (Vc Y En) (A ^ k)
    have hk0 : ∀ z ∈ b ^ k, (sec (e ≫ ιc Y En ≫ p)) z = 0 := fun z hz => by
      have h1 : (sec (e ≫ ιc Y En ≫ p)) z = (sec e) ((sec (ιc Y En)) ((sec p) z)) :=
        (sec_comp e _ z).trans (congrArg (sec e) (sec_comp _ p z))
      refine h1.trans ((ιc_ker _ _).2 ?_)
      have h2 : A ^ k = (b ^ k).map ((sec (ιc Y En)).comp (sec p)) := by
        rw [Ideal.map_pow]
        change (Ideal.map _ (Ideal.map _ b)) ^ k = _
        rw [Ideal.map_map]
      exact h2 ▸ Ideal.mem_map_of_mem _ hz
    obtain ⟨sk, hsk⟩ := exists_factor_closed (e ≫ ιc Y En ≫ p) (b ^ k) hk0
    have h1 : X.map (e ≫ ιc Y En).op θ = X.map sk.op (χ k) :=
      hθ k (e ≫ ιc Y En) sk (hsk.trans (Category.assoc _ _ _).symm)
    have h2 : X.map sk.op (χ k) = X.map (e ≫ r).op (x n) := hχx k n sk (e ≫ r) (by
      rw [hsk, Category.assoc, hr])
    change X.map e.op (X.map (ιc Y En).op θ) = X.map e.op (X.map r.op (x n))
    rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp]
    exact h1.trans h2
  obtain ⟨g, hg⟩ := exists_factor_closed i En (by
    have : ∀ z ∈ m ^ n, (sec i) ((sec p) z) = 0 := fun z hz => by
      refine (sec_comp i p z).symm.trans ?_
      refine (congrArg (fun c => (sec c) z) hs.symm).trans ((sec_comp s _ z).trans ?_)
      rw [(ιc_ker _ z).2 hz, map_zero]
    intro z hz
    refine Submodule.span_induction ?_ (map_zero _) (fun _ _ _ _ h₁ h₂ => by
      rw [map_add, h₁, h₂, add_zero]) (fun c _ _ h => by
      rw [smul_eq_mul, map_mul, h, mul_zero]) hz
    rintro _ ⟨c, hc, rfl⟩
    exact this c hc)
  haveI hm : Mono (ιc T (m ^ n)) :=
    (SCH).mono_of_mono_map (inferInstanceAs (Mono (Chart.closedι ((SCH).obj T) (m ^ n))))
  have hgr : g ≫ r = s := (cancel_mono (ιc T (m ^ n))).1 (by
    rw [Category.assoc, hr, ← Category.assoc, hg, hs])
  rw [← hg, ← hgr, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, key]

/-- The trivial action. -/
def trivAct (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : AAction (fppfO B S hS) Mt.{u} F where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  map_smul _ _ _ := rfl

set_option maxHeartbeats 8000000 in
/-- **`LocalModelStep X`**: Lemmas 3.4 and 4.3 non-graded with the `ChartOf` for `X` quasi-separated, `Y` and `θ`, for
the tower `Z^(k)` of the complement of an affine open `U`, given the algebraization on the `Z^(k)`. -/
theorem localModelStep [IsAffine S] (actX : AAction (fppfO B S hS) Mt.{u} X) (hX : IsAlgebraicSpace B S hS X)
    (hch : HasCharts X)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (φ : yoneda.obj V ⟶ X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (hNV : IsNoetherianRing Γ((SCH).obj V, ⊤))
    (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) Mt.{u} (yoneda.obj U))
    (f : yoneda.obj U ⟶ X) (hUa : IsAffine ((SCH).obj U)) (hfe : IsEquivariant actU actX f)
    (hfo : Space.IsOpenImmersion B S hS f)
    (hZ : ∀ k, Effective ((complTower actX hs he hX hfo).actZ k)) :
    ChartQSAlg.LocalModelStep X := by
  intro T _ _ I _ x hx
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUa
  let actT : AAction (fppfO B S hS) Mt.{u} (yoneda.obj T) := trivAct _
  have hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) I :=
    isCompletePair_of_complete actT I
  have hιm : ∀ J : Ideal Γ((SCH).obj T, ⊤), Mono (ιc T J) := fun J =>
    (SCH).mono_of_mono_map (inferInstanceAs (Mono (Chart.closedι ((SCH).obj T) J)))
  have hxs : IsEquivSystem actT actX I x :=
    ⟨hx, fun n => by
      haveI := hιm (I ^ n)
      exact equivAlong_triv actT actX _ (x n)⟩
  let ho := complP₀_closedP hX hfo
  have hT := Space.range_pointsMap_ι_reducedClosedSubspace B S hS X hX _ (isClosed_compl_open hfo)
  let C : Ctx actX actU f φ :=
    { idl := fun y => idlP actX ho hs he hX y
      idl_map := fun q y => idlP_map actX ho hs he hX q y
      idl_smul := fun h y => idlP_smul actX ho hs he hX h y
      lift_U := fun y h => lift_U_of_top actX ho hs he hX hfo hT y h
      equiv := hfe
      mono := mono_of_open hfo
      noethV := hNV
      chart := fun τ => hch V φ hs he τ }
  obtain ⟨a, gens, hgens, hhom, hak, hax⟩ := exists_ideal C hP x hxs
  obtain ⟨y₀, hy₀⟩ := exists_y₀ C hP hxs hax hgens hhom
  subst hgens
  let tow := complTower actX hs he hX hfo
  have hfac : ∀ (k n : ℕ) (W : BigFppfOver B S hS) (g₁ : W ⟶ Vc T (Ideal.span gens ^ k)) (g₂ : W ⟶ Vc T (I ^ n)),
      g₁ ≫ ιc T (Ideal.span gens ^ k) = g₂ ≫ ιc T (I ^ n) →
      ∃ z : (tow.Z k).obj (op W), (tow.i k).app _ z = X.map g₂.op (x n) :=
    fun k n W g₁ g₂ h => hfac_aux actX ho hs he hX hax k n g₁ g₂ h
  choose χ hχ hχx using fun k => lemma44 actT actX (tow.actZ k) (tow.i k) (tow.equiv k)
    (tow.mono k) (hZ k) (hak k) hP x hxs (hfac k)
  have hχc : ∀ (n k : ℕ) (e : Vc T (Ideal.span gens ^ n) ⟶ Vc T (Ideal.span gens ^ k)),
      e ≫ ιc T (Ideal.span gens ^ k) = ιc T (Ideal.span gens ^ n) → X.map e.op (χ k) = χ n := by
    intro n k e he'
    exact ChartQS.chi_compat_aux actT actX hX _ (closedAct actT (hak n))
      (fun {W} h s => closedAct_spec actT (hak n) h s) _ (fun r => (Ideal.map_pow _ I r).symm)
      (isCompletePair_closedAct actT (hak n) hP) x (χ n) (hχ n) (hχx n) (χ k) _ e he' (hχ k) (hχx k)
  obtain ⟨Y, p, θ, hYa, hYN, hpf, hcov, hIj, hbj, hθ⟩ :=
    exists_model he I (Ideal.span gens) χ hχc (hch V φ hs he (χ (0 + 1))).some
  haveI := hYa
  haveI := hYN
  have hθx : ∀ (n : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y) (s : W ⟶ Vc T (I ^ n)),
      s ≫ ιc T (I ^ n) = i ≫ p → X.map i.op θ = X.map s.op (x n) :=
    theta_restrict hX p hbj x χ (fun k n _ g₁ g₂ h => hχx k n g₁ g₂ h) θ hθ
  refine ⟨Ideal.span gens, UTo gens, Y, jo gens, p, f.app (op _) y₀, θ, hYa, isOpenImmersion_jo gens,
    jo_range gens, hpf, fun y hy => hcov y fun g hg hyg => hy ((jo_range gens y).2 ⟨g, hg, hyg⟩),
    ?_, ?_, ?_, ?_⟩
  · intro W g₁ g₂ h
    exact tau_thetaY C hax p hIj hθx rfl y₀ hy₀
      (fun g f' => exists_val C hP hxs hax rfl hhom g f') hX g₁ g₂ h
  · intro k W g₁ g₂ h hk
    exact ChartQSAlg.hthick_of_psi p (Ideal.span gens) θ χ (fun k W i s h' => hθ k i s h'.symm) k g₁ g₂ h hk
  · intro n W g₁ g₂ h
    exact tau_x C hP hxs hax rfl hhom y₀ hy₀ hX n g₁ g₂ h
  · intro n W g₁ g₂ h
    exact (hθx n W g₁ g₂ h.symm).symm ▸ rfl

section Induction

attribute [local instance] Space.pointTopology

variable {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option maxHeartbeats 4000000 in
/-- **Noetherian induction over closed subspaces** for the trivial group. -/
theorem effective_triv [IsAffine S] {act₀ : AAction (fppfO B S hS) Mt.{u} X₀}
    (hX₀ : IsAlgebraicSpace B S hS X₀) [TopologicalSpace.NoetherianSpace (points B S hS X₀)]
    (hA : ∀ C : ClosedStable act₀, HasAffineAtlas C.Z)
    (hch : ∀ C : ClosedStable act₀, HasCharts C.Z)
    (hN : ∀ (C : ClosedStable act₀) (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ C.Z),
      IsAffine ((SCH).obj V) → (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ →
      IsNoetherianRing Γ((SCH).obj V, ⊤))
    (hAb : ∀ C : ClosedStable act₀, Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal C.Z)
    (C : ClosedStable act₀) : Effective C.actZ := by
  suffices h : ∀ (K : TopologicalSpace.Closeds (points B S hS X₀)) (C : ClosedStable act₀),
      C.pts hX₀ = K → Effective C.actZ from h _ C rfl
  intro K
  induction K using WellFoundedLT.induction with
  | ind K IH =>
    intro C hCK
    by_cases hne : ∃ W : BigFppfOver B S hS, Nonempty ((SCH).obj W) ∧ Nonempty (C.Z.obj (op W))
    · obtain ⟨W, ⟨w⟩, ⟨x₀⟩⟩ := hne
      have hpt : Nonempty (Space.points B S hS C.Z) :=
        ⟨Space.pointsMap B S hS (yoneda.obj W) (yonedaEquiv.symm x₀)
          ((Space.pointsEquivScheme B S hS W).symm w)⟩
      obtain ⟨U, f, hUa, hUn, hfo⟩ := ChartStratum.exists_affine_open_of_absQS C.alg (hAb C) hpt
      let actU : AAction (fppfO B S hS) Mt.{u} (yoneda.obj U) := trivAct _
      have hfe : IsEquivariant actU C.actZ f := isEquivariant_triv actU C.actZ f
      obtain ⟨V, φ, hV, hs, he⟩ := hA C
      haveI := hV
      obtain ⟨h1, h2, h3⟩ := complTower_spec C.actZ hs he C.alg hfe hfo
      have hdis : ∀ k, Disjoint (Set.range (pointsMap B S hS _ ((complTower C.actZ hs he C.alg hfo).i k)))
          (Set.range (pointsMap B S hS _ f)) := fun k => by
        rw [h3 k]
        exact disjoint_compl_left
      have hZ : ∀ k, Effective ((complTower C.actZ hs he C.alg hfo).actZ k) := fun k => by
        let tow := complTower C.actZ hs he C.alg hfo
        let C' : ClosedStable act₀ :=
          { Z := tow.Z k
            actZ := tow.actZ k
            i := tow.i k ≫ C.i
            equiv := fun h x => (C.equiv h _).symm ▸ congrArg (C.i.app _) (tow.equiv k h x)
            mono := fun V => (C.mono V).comp (tow.mono k V)
            closed := MorphismProperty.comp_mem _ _ _ (h1 k) C.closed
            alg := h2 k }
        refine IH (C'.pts hX₀) ?_ C' rfl
        have hle : C'.pts hX₀ ≤ K := by
          rw [← hCK]
          rintro _ ⟨q, rfl⟩
          refine ⟨pointsMap B S hS _ (tow.i k) q, ?_⟩
          change _ = pointsMap B S hS _ (tow.i k ≫ C.i) q
          rw [pointsMap_comp]
          rfl
        refine lt_of_le_of_ne hle fun heq => ?_
        obtain ⟨u⟩ := hUn
        obtain ⟨p, -⟩ := (pointsEquivScheme B S hS U).surjective u
        have hmemK : pointsMap B S hS _ C.i (pointsMap B S hS _ f p) ∈ (K : Set _) := by
          rw [← hCK]
          exact ⟨_, rfl⟩
        rw [← heq] at hmemK
        obtain ⟨q, hq⟩ := hmemK
        haveI : Mono C.i := (NatTrans.mono_iff_mono_app _).2 fun V =>
          (mono_iff_injective _).2 (C.mono V)
        have hq' : pointsMap B S hS _ (tow.i k ≫ C.i) q = _ := hq
        rw [pointsMap_comp] at hq'
        have hinj := pointsMap_injective_of_mono B S hS C.i hq'
        exact Set.disjoint_left.1 (hdis k) ⟨q, hinj⟩ ⟨p, rfl⟩
      exact effective_of_alg C.actZ (ChartQSAlg.noetherianAlgebraization_of_localModel C.alg
        (localModelStep C.actZ C.alg (hch C) V φ hs he (hN C V φ hV he) U actU f hUa hfe hfo hZ))
    · exact effective_of_isEmpty C.actZ hne

end Induction

end AlgMag.ChartMain.DeligneQS.ChartQSLocal
