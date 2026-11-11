[
 {
  "k": "chart-qs",
  "rs": [
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSStab.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean"
    ],
    "proved": [
     "AlgMag.ChartPoint.exists_equalizer_closedPoint, AlgMag/ChartQSStab.lean:53. For x : P -> X a closed immersion, P affine, X any presheaf: the equalizer of a point a with x o t is closed in W. It replaces AlgMag.exists_equalizer for closed points, with no separatedness.",
     "AlgMag.ChartPoint.exists_stab_ideal_closedPoint, AlgMag/ChartQSStab.lean:131. The stabilizer of a closed point is V(J) in D(M)_P, without X separated. This is note §1, the sentence 'H closed (X separated)'. #print axioms: propext, Classical.choice, Quot.sound. Compiled with cma/k.sh, EXIT 0, no sorry. Import appended to AlgMag.lean; the file was not lake-built.",
     "Hand argument, no Lean: Stabilizers. For a closed point, separatedness is not needed, as the compiled lemmas show.",
     "Hand argument, no Lean: Equalizers (corrected uniqueness). Let E -> Spec R be the equalizer of two equivariant maps, for R a complete pair. E is mono and locally of finite type. Then E is etale at V(m), by the completion: E -> Spec R is unramified with a section on every thickening, so the completions agree, and R is noetherian. Hence E is an open immersion near V(m). E is stable, and a stable open containing V(m) is everything, since 1 + m_0 consists of units. This is my own argument and has had no independent check.",
     "Hand argument, no Lean: Equalizers (Lemma 4.5). When R is noetherian the same completion argument gives E open near each point of V(a), so with agreement off V(a) we get E = Spec R. This covers equivariant_of_agree (R = O(G) tensor C) and restrict_aux. Not proved by hand for non-noetherian R: see notDone item 2, kernel pair.",
     "Hand argument, no Lean: Algebraization for Spec C-hat -> X. If T^(1) is affine and T^(1) -> X lifts to an affine etale neighbourhood Y -> X, then T^(k) lifts by etaleness and T-hat -> Y is a limit of rings, with no 0GHK and no separatedness. Existence of the lift over all of T^(1) is not settled: 0BBP gives neighbourhoods of a point only, and a closed affine neighbourhood version needs T^(1) -> X to be handled when it is not a closed immersion (notDone item 3)."
    ],
    "notDone": [
     "The main target is NOT reached: no qs chart lemma, and no Thm 6.8(ii) without the chart-family hypothesis of thm68_ii_of_charts. I found no concrete mathematical obstruction, but several steps below are open on paper as well as in Lean, so I cannot claim the route closes. Only the stabilizer step is in Lean.",
     "Paper-level open step, Lemma 4.5 for non-noetherian R: eq_on_kernelPair (ChartEffectiveMain.lean:132) has R = C-hat tensor_C C-hat, flat over noetherian C but not noetherian. With p, q : Spec R -> X, the equalizer is mono, and after an etale localization it is a closed immersion V(I) near a point of V(a). I lies in every a^k R', but a^s I = 0 does NOT follow, because p, q agreeing in X on D(a) does not make their lifts to an etale chart agree: V(I) meets D(a) only in a clopen part. In the case C = k[x] a divisibility argument produces an idempotent in R' and closes it. The multi-generator case is unproved. Alternatives: Bhatt Thm 1.4(1) (not in the tree), or use the factorisation through Y from item 3.",
     "Paper-level open step, NoetherianAlgebraization for qs X: ChartEffectiveAlg.rb_props uses Stacks 0GHK, which requires separated. A map T^(1) -> X is not a closed immersion, so 0BBP (a point neighbourhood) does not directly lift it over all of T^(1). Bhatt Thm 1.1 covers qcqs spaces but is not in the tree.",
     "Paper-level open step, Lemma 4.2 for qs X: the Lean route takes the generic stabilizer from Chart.exists_eqLocus (ChartStratumStab.lean:36), a closed equalizer, and that fails for a non-closed point. Proposed replacement: a dense stable separated open X \\ closure(pr1(closure(Delta) \\ Delta)), then apply ChartStratum.affineStratum unchanged. This argument was sketched for reduced X with valuative reasoning and is not checked for spaces.",
     "Lemma 1.1 (ChartPointL11*, ChartPointLemma11, ChartPointOrbitInput), not adapted. exists_pull (ChartPointL11Image.lean:91) makes O x_X U affine using separatedness. For qs X this pullback is only quasi-affine, so the ring-level proof must be rewritten on quasi-affine schemes. About 1500 lines depend on it.",
     "Direct replacement, not done: ChartEffective.eq_of_agree_of_iInf is FALSE for qs X in its present non-equivariant form. Counterexample: W = A^1, J_n = (t^n), X = line with doubled point at t = 1, p and q the two inclusions. They agree on all V(t^n) and differ at t = 1. Its users thm41_unique and chi_univ (ChartDeligneCompat.lean:116) must be restated with equivariance and a complete pair. I have not checked that chi_univ has the equivariance available.",
     "Mechanical once the steps above are settled, not done: re-derive the chain that takes hsep. Existing files cannot be edited, and Lean signatures require Space.IsSeparatedOver, so about 25 modules must be re-proved under a qs hypothesis: ChartTower (X_n affine; O closed gives this without separatedness), ChartTowerChart.isAffine_relation, ChartDeligneInst.exists_chartOf, ChartDeligneCompat/Theta, ChartEffective*, ChartMain, ChartPointAssemble/Reduce, ChartS5Close, ChartStubs.exists_chart_at_point (decent_of_sep becomes qs implies decent, which is available). Then conclude with isZFPRAtlas_of_family_irreducible. ChartQSStab.lean is the only ChartQS file; exists_stabilizer (ChartPoint.lean:140) is not yet restated on exists_stab_ideal_closedPoint."
    ],
    "addedAssumptions": [
     "exists_equalizer_closedPoint and exists_stab_ideal_closedPoint assume x is a closed immersion from an affine P, which is the ChartPoint.isClosed field. These are the only added hypotheses in the Lean delivered."
    ],
    "paperIssues": [
     "No suspected error in the printed paper was found in this pass. Thm A.2 for quasi-separated X cites AHR Cor 20.2. I did not check that citation against the published AHR text in this pass.",
     "notes/ahr-specialized-proof.md cannot be transferred to qs X by replacing 'closed equalizer' with 'immersion'. For spaces the equalizer is only a monomorphism, not an immersion (it can look like A^1 minus a point mapping to a nodal curve), and uniqueness in Thm 4.1 needs equivariance (see the counterexample under notDone)."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSCore.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSAgree.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSStab.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\chart-qs-proof.md"
    ],
    "proved": [
     "AlgMag.ChartQS.eq_of_lift_etale, AlgMag/ChartQSAgree.lean:132. Let v : V -> X be etale, V and P affine, s, t : P -> V, Gamma(P) flat over a noetherian C, g in C. If v s = v t on D(g) and s = t on every V(g^k), then v s = v t. No separatedness; s, t may differ on D(g). This is the Lean core of the kernel pair step reported open last round. #print axioms: propext, Classical.choice, Quot.sound. Compiled with cma/k.sh, EXIT 0, no sorry.",
     "AlgMag.ChartQS.exists_mul_eq_zero, AlgMag/ChartQSCore.lean:32. Ring form: I in all g^k R, R flat over noetherian C, e in R_g with eI = 0 and 1 - e in I R_g. Then (1 - g w) I = 0 for some w. Same axioms.",
     "AlgMag.ChartQS.exists_idempotent_of_open, AlgMag/ChartQSCore.lean:96. The ideal of the equalizer is generated by an idempotent over D(g), from the open diagonal of V x_X V. Same axioms.",
     "AlgMag.ChartQS.isOpenImmersion_section (ChartQSAgree.lean:23) and eq_of_two_opens (ChartQSAgree.lean). Same axioms. Imports of both new files appended to AlgMag.lean; neither was lake-built.",
     "Hand argument, no Lean, no independent check (notes/chart-qs-proof.md Steps 1-3): the kernel pair open step is closed on paper. Principal ideal: an etale P -> C1 tensor_C C1 near the diagonal, then eq_of_lift_etale. Several generators: iterated completion C -> C1 -> ... -> C^, reduced to one generator each time. Uniqueness: agreement on all V(a^k), a in the Jacobson radical, by the same chart P and Krull.",
     "Hand argument, no Lean, no independent check (Step 4): noetherian algebraization for qs X without Bhatt 1.1 or 0GHK. Noetherian induction on |X|: affine open U and Deligne map on D(b); then Stacks 07ST/08GM squares W -> X, an isomorphism over a closed Z', so maps along thickenings of Z' land in the affine W and pass to the limit of rings; glue by Steps 2-3. The Deligne step is used in a non-graded form that is not yet written.",
     "Hand sketch, not checked for spaces (Step 5): Lemma 4.2 via a dense G-stable separated open, X minus closure(pr1 closure(closure(Delta) minus Delta)), by a dimension count."
    ],
    "notDone": [
     "The main target is NOT reached: no qs chart lemma and no Thm 6.8(ii) without the chart-family hypothesis of thm68_ii_of_charts. I found no mathematical obstruction: no step found needs X separated. The route now closes on paper, but that is my own argument with no independent read.",
     "Lean, next: construct P (idempotent lift of the diagonal in B/g tensor B/g, flatness of Gamma(P) over C), then qs versions of eq_on_kernelPair/existsUnique_pushout for principal g, uniqueness (Step 3), and the iteration over generators (Step 2).",
     "Lean: Step 4 not started: non-graded ideal algebraization and non-graded Deligne map; 07ST/08GM are found in the Stacks tree (Spaces/Decent/FiniteSchemeFiltration/Strata.lean, Spaces/Perfect/ElementaryDistinguishedSquare.lean) but not yet linked. It discharges NoetherianAlgebraization X (ChartEffectiveMain) for qs X.",
     "Lean: Lemma 4.2 for qs X (Step 5). Paper sketch only.",
     "Lean: Lemma 1.1 not adapted. exists_pull (ChartPointL11Image.lean:91) needs X separated for O x_X U affine; the printed argument is local, so the ring-level proof must be redone on a quasi-affine fibre product. About 1500 lines depend on it.",
     "Lean: re-derive the chain that takes hsep, about 25 modules (33 Chart files mention IsSeparatedOver): ChartTower, ChartTowerChart, ChartDeligneInst/Compat/Theta, ChartEffective*, ChartMain, ChartPointAssemble/Reduce, ChartS5Close, ChartStubs.exists_chart_at_point. Then conclude with isZFPRAtlas_of_family_irreducible. Only a chart through x is needed for case (ii): G_u = G_x can be dropped, since Thm A.1 gives Z-FPR."
    ],
    "addedAssumptions": [
     "eq_of_lift_etale takes a principal ideal (g) and Gamma(P) flat over a noetherian C. Several generators are to be handled by iterated completion (Step 2, not in Lean). No hypothesis of the printed Thm 6.8 is changed, since it is not yet proved in this form.",
     "Inherited from the previous round: exists_equalizer_closedPoint and exists_stab_ideal_closedPoint assume x is a closed immersion from an affine P."
    ],
    "paperIssues": [
     "No error found in the printed paper. The cited AHR Cor 20.2 was not checked against the published text in this pass; the local copy is arXiv v4, where the corresponding Cor 10.2 reads 'quasi-separated algebraic space S' and 'group'. The published version still has to be resolved.",
     "Warning for the route, not a paper error: stabilizers on qs X can be non-closed even generically near a point. X = (G_m x A^1)/H, with H = {1} over s = 0 and {+-1} over s != 0, has no separated stable open around the points s = 0, yet it has an affine etale chart G_m x A^1. So reducing to a stable separated open around x is impossible, and the chart proof really must be run on qs X."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSLift.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSChart.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSEq.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSFlatQuot.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSEqGens.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSUnique.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSMain.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\chart-qs-proof.md"
    ],
    "proved": [
     "All items below: compiled with cma/k.sh (EXIT 0), no sorry, #print axioms = propext, Classical.choice, Quot.sound. Not lake-built. The checks are by the compiler only; the mathematics has had no independent read.",
     "AlgMag.ChartQS.exists_chart_agree, ChartQSChart.lean:80. X any algebraic space, W affine, p, q in X(W) agreeing on every V(J^k), y in V(J). There is an etale P -> W with P affine and y in its image, an affine etale chart V -> X, and lifts s, t : P -> V of p, q with s = t on every V(J^k Gamma(P)). No kernel pair or idempotent lift is needed, which simplifies Step 1 of the note.",
     "AlgMag.ChartQS.eq_of_agree_principal, ChartQSEq.lean:38. Gamma(W) flat over a noetherian C, g in C. Two points of X over W agreeing on D(g) and on all V(g^k) are equal.",
     "AlgMag.ChartQS.eq_of_agree_basicOpen_of_agree_thickening, ChartQSEqGens.lean:166. Same statement as Chart.eq_of_agree_basicOpen_of_agree_thickening (the equalizer killing after Lemma 4.5), with X any algebraic space instead of separated. Proved by induction on the number of generators through C/(g^k) (eq_of_agree_list, line 66), using AlgMag.ChartQS.flat_quot, ChartQSFlatQuot.lean:24. No iterated completion is needed for equalities.",
     "AlgMag.ChartQS.eq_of_agree_pow, ChartQSUnique.lean:66. W affine noetherian, a in the Jacobson radical of Gamma(W): two points of X agreeing on all V(a^k) are equal. Krull input: exists_one_sub_mul_eq_zero, line 26.",
     "AlgMag.ChartQS.eq_on_kernelPair (ChartQSMain.lean:34), existsUnique_pushout (:105), equivariant_of_agree (:177), exists_glue (:258), restrict_eq_of_strata (:373), thm41_exists_of_strata (:398): the statements of ChartEffectiveMain, same proofs, with hX in place of hsep. exists_glue and thm41_exists_of_strata still take hB : NoetherianAlgebraization X.",
     "AlgMag.ChartQS.eq_of_family, ChartQSLift.lean: points of an algebraic space are determined on any jointly surjective family of open flat maps."
    ],
    "notDone": [
     "The main target is NOT reached: no qs chart lemma and no Thm 6.8(ii) without the chart-family hypothesis of thm68_ii_of_charts. No step found needs X separated, except the non-equivariant uniqueness below, which is false and must be replaced.",
     "Equivariant replacement of ChartMain.thm41_unique, not written. chi_compat_aux in ChartEffectiveFinal uses thm41_unique. Hand argument only: the agreement locus is open, stable, and contains V(m); a stable closed set missing V(m) is empty by the complete pair.",
     "Step 4, NoetherianAlgebraization X for qs X: not started in Lean, and the non-graded Deligne step is unwritten. I checked the two Stacks results that might discharge it. 0GHK in the tree is the separated case, and 0AQH (MapsToAlgebraicSpace) covers only complete local R.",
     "Step 5, Lemma 4.2 for qs X: paper sketch only, not checked for spaces.",
     "Lemma 1.1: exists_pull (ChartPointL11Image.lean:91) needs X separated for O x_X U affine; to be redone on a quasi-affine fibre product.",
     "The rest of the hsep chain: 38 Chart files mention hsep or IsSeparatedOver, some only by passing it on. It must be re-derived in new files, by the same mechanical copy as ChartQSMain where only the equalizer lemma is used. Then conclude with isZFPRAtlas_of_family_irreducible; for case (ii) only a chart through x is needed."
    ],
    "addedAssumptions": [
     "No hypothesis of the printed Thm 6.8 is changed, since it is not yet proved in this form.",
     "eq_of_agree_pow assumes a in the Jacobson radical and Gamma(W) noetherian. The old Chart.eq_of_agree_of_iInf assumed any family of ideals with zero intersection, a form that is false for non-separated X.",
     "Inherited from an earlier round: exists_equalizer_closedPoint and exists_stab_ideal_closedPoint assume x is a closed immersion from an affine P."
    ],
    "paperIssues": [
     "No error found in the printed paper in this pass. Whether the printed Thm 4.1 uniqueness is affected was not checked: I did not reread that passage of am.txt against the counterexample below.",
     "Warning from the Lean side, not a paper error: the repo's ChartMain.thm41_unique (any two points, graded complete pair m) would be false if X were only quasi-separated. T = A^1, m = (t), X = A^1 with a doubled point at s = 1, and phi, psi the two sections: they agree on all V(t^k) and differ. The theorem as stated takes X separated, so it is not wrong; the qs replacement must assume phi, psi equivariant. My Step 3 in the note did not cover this, because a graded complete pair m need not lie in the Jacobson radical; the note now says so.",
     "Carried over: AHR Cor 20.2 not checked against the published text; the local copy is arXiv v4."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSEquivUnique.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\ChartQSEffective.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\chart-qs-proof.md"
    ],
    "proved": [
     "All items below compiled with cma/k.sh (EXIT 0) and contain no sorry. Printed #print axioms: propext, Classical.choice, Quot.sound for the three theorems so marked. Not lake-built. The checks are by the compiler only; the mathematics has had no independent read.",
     "AlgMag.ChartQS.thm41_unique_equivariant, ChartQSEquivUnique.lean:349. X any algebraic space, (Gamma(T), m) a graded complete pair: two equivariant points of X over T agreeing on all V(m^n) are equal. Axioms printed. This replaces ChartMain.thm41_unique, whose non-equivariant form is false for non-separated X.",
     "Supporting lemmas in ChartQSEquivUnique.lean: exists_etale_agree (the chart step of eq_of_agree_pow, with no Jacobson radical hypothesis), agreeOn_of_family, agreeOn_of_cover, agree_coact, pr_flat_open, isUnit_one_sub, coeff_mem_of_mem_map.",
     "AlgMag.ChartQS.effective_of_stratum, ChartQSEffective.lean:119. Theorem 4.1 existence, inductive step, X any algebraic space. Takes hB : NoetherianAlgebraization X and hL : ChartQS.OpenStratumMap tow (line 34). Axioms printed.",
     "AlgMag.ChartQS.effective_of_noetherian, ChartQSEffective.lean:168. The noetherian induction, X any algebraic space. Takes NoetherianAlgebraization of the strata, h42 and ChartQS.StrataOver as hypotheses. Axioms printed."
    ],
    "notDone": [
     "The main target is still NOT reached: no qs chart lemma and no Thm 6.8(ii) without the chart-family hypothesis of thm68_ii_of_charts. So far no step has been shown to need X separated; nothing below is a mathematical obstruction, though steps 2, 3 and 5 are not proved even on paper at Lean level of detail.",
     "1. Lemma 4.3 for qs X (ChartQS.StrataOver) is not proved. ChartDeligneCore.ChartOf asks Z x_X V to be affine with its universal property, and exists_chartOf (ChartDeligneInst:28) gets this from exists_eqLocus. For qs X this product is only quasi-affine. ChartDeligneCore uses ChartOf at lines 401, 408, 511 and 632, and the Gam/descend route depends on it. It must be redone with a finite affine cover of Z x_X V, or with Gam defined on all affine W over V. chi_univ (ChartDeligneCompat:107) must take chi equivariant as a hypothesis, which ChartQS.OpenStratumMap now supplies, and must stop using eq_of_agree_of_iInf. Not started in Lean.",
     "2. NoetherianAlgebraization X for qs X (Step 4 of the note): not started in Lean, and the non-graded Deligne step is unwritten. 0GHK in the tree is the separated case; 0AQH covers complete local R only.",
     "3. Lemma 4.2 for qs X (Step 5): paper sketch only, not checked for spaces.",
     "4. Lemma 1.1: exists_pull (ChartPointL11Image:91) gives an affine O x_X U, which needs separated X. Tower: exists_affine_thickening, isAffine_relation, ChartTowerChart:276 and 367 have the same quasi-affine issue. Not started.",
     "5. Assembly: the qs analogues of effective_of_noetherian_atlas, effective_of_lft, the Section 5 close, and the point charts. Then conclude with isZFPRAtlas_of_family_irreducible; for case (ii) only a chart through x is needed. Not started."
    ],
    "addedAssumptions": [
     "No hypothesis of the printed Thm 6.8 is changed, since it is not yet proved in this form.",
     "thm41_unique_equivariant assumes p and q equivariant, relative to the old thm41_unique. This is forced: the non-equivariant form is false for non-separated X (doubled-point example from the earlier round).",
     "ChartQS.OpenStratumMap assumes the chi_k equivariant, relative to ChartMain.OpenStratumMap. This holds in the induction, since lemma44 gives it. I did not prove that the old form fails for qs X; I only expect it can, because the uniqueness that would control it is available only for equivariant points.",
     "Inherited, still open: effective_of_stratum and effective_of_noetherian take NoetherianAlgebraization, h42 and StrataOver as hypotheses. exists_glue and thm41_exists_of_strata take hB. exists_equalizer_closedPoint and exists_stab_ideal_closedPoint assume x is a closed immersion from an affine P."
    ],
    "paperIssues": [
     "No error found in the printed paper in this pass. I did not reread am.txt in this round; all work was against the note and the Lean files.",
     "Correction to my own note, not to the paper: the claim in notes/chart-qs-proof.md that a stable closed set missing V(m) is empty is too quick when D(M) is not reduced, because the ideal of a stable closed set need not be homogeneous (mu_p on A^1, the point t = 1). The Lean proof goes around this: the coaction of f in the ideal K is nilpotent modulo K, so a power of f is used and its degree 0 component is taken. The fix is recorded in the note.",
     "Carried over: AHR Cor 20.2 not checked against the published text; the local copy is arXiv v4."
    ]
   }
  ],
  "check": {
   "problems": [
    {
     "where": "notes/chart-qs-proof.md Step 5 (line 26); report notDone item 3",
     "detail": "The Step 5 construction is false as written for spaces. Counterexample, char not 2 (for example over Z[1/2]): X = A^1/R, with R = Delta union {(x,-x), x != 0}. This X is quasi-separated, irreducible and of finite type, and G_m acts by scaling. The preimage of |Delta_X| in A^1 x A^1 is the closed cross {y = x} union {y = -x}, so |Delta_X| is closed and closure(Delta) minus Delta is empty. Hence F is empty and X minus closure(pr1 F) = X. But X is not separated, because R -> A^1 x A^1 is not a closed immersion. So the claimed 'dense, stable and separated open' is not produced, and ChartStratum.affineStratum cannot be applied to it. Lemma 4.2 itself still holds here, with U = X minus {0}. Recommended repair: drop Step 5 and use the Claim of notes/thm68-ii-proof.md section 4.4, which replaces exists_generic_stabilizer and which the earlier review (notes/thm68-ii-review.md) passed step by step. A set-theoretic count cannot work; it would have to use the locus where Delta -> closure(Delta) fails to be an isomorphism, and stability of that locus would need proof."
    },
    {
     "where": "notes/chart-qs-proof.md Step 4 (line 23)",
     "detail": "The citation does not give what the proof uses. The note says 'Stacks 07ST filtration (08GM squares): W -> X affine étale' and later 'W affine, so Spec D^c -> W -> X by a limit of rings'. The tree's 07ST (Spaces/Decent/FiniteSchemeFiltration/Strata.lean:419) gives V_p only as a quasi-compact separated scheme, not affine. Shrinking V_p to an affine makes Z' only open in its stratum, so Z' is no longer closed. Taking a closed point and 0BBP gives an affine W but breaks the induction: X minus z1, minus z2, and so on is a descending chain of opens with no well-foundedness. Two repairs work. (a) Keep 07ST and apply 0GHK to the separated V_p, which gives up the note's claim of no 0GHK. (b) Build the filtration from the open side: U_p = U_{p+1} union f(V), with V affine étale elementary at a generic point of X minus U_{p+1}, shrunk so that it is an isomorphism over the stratum; ACC on opens terminates. Separately, Claim S is not well-formed as stated. D(b) and V(b^l) do not meet, so 'tau compatible' is no overlap condition. Without a definition S is false: X = A^1, D = k[[t]], psi_l given by x = t, tau given by x = 2t. S must define tau as the Deligne map of psi_l and must assume psi_l^*J = b/b^l. This is the part the report calls unwritten, and it has to be fixed before Step 4 counts as closed on paper."
    },
    {
     "where": "ChartQSEffective.lean:119,168; report labels 'X any algebraic space'",
     "detail": "The generality is empty beyond quasi-separated X, so the label overclaims. Take X_0 = A^1_Q/Z with trivial action. |X_0| is noetherian, since its only opens are the empty set and X_0. The only nonempty open is X_0, which is not affine, so h42 (AffineStratum) is false and effective_of_noetherian says nothing about X_0. NoetherianAlgebraization is known only for quasi-separated targets (Bhatt); the docstring of 0GHK in the tree records that the general case is open. These two theorems should be described as conditional, with content only for quasi-separated X. The compiled uniqueness and equality lemmas, which take no such hypotheses, do hold for any algebraic space."
    },
    {
     "where": "Report notDone item 4 (Tower); ChartTowerChart.lean:276,367",
     "detail": "The 'same quasi-affine issue' is overstated for the tower. Once O -> X is a closed immersion, O -> X_n is a surjective closed immersion with affine source. The tree's 07VT, Space.isAffineSpace_of_isClosedImmersion_of_isSurjective, already used at ChartStratumBack.lean:151, then gives X_n affine for any algebraic space. notes/ahr-specialized-proof.md section 2 already argues this way. isClosedSubspace_thickening supplies the algebraic-space input without hsep. So exists_affine_thickening should be re-provable directly, without isAffine_relation and without a quasi-affine argument. I have not compiled this. The issue is real for exists_pull (Lemma 1.1) and for ChartOf (Lemma 4.3), where the fibre product is genuinely only quasi-affine; A^1/R gives R = A^1 disjoint union G_m."
    },
    {
     "where": "Report notDone item 5 (list of remaining work)",
     "detail": "The list omits the globalization of the print's reduction (R) of Theorem A.2, from general S and X locally of finite presentation to S affine and S, X of finite type over Z. SpacesLimitThm68.lean:176, 233, 257, 279, 310 all carry hsep, and line 187 and following transfer separatedness to the descended space. The earlier review flagged this as gap 5, and no qs form exists. Case (ii) of printed Thm 6.8 is not reached without it. decent_of_sep (ChartThm68.lean:79) also needs a qs replacement; isDecentSpace_of_isAbsolutelyQuasiSeparated exists as a stub."
    },
    {
     "where": "notes/chart-qs-proof.md line 31 (stabilizer)",
     "detail": "The sentence 'The stabilizer of a non-closed point need not be closed' is false as written. A field-valued stabilizer is a closed subgroup scheme (SGA 3 VI_B 1.4.2, per notes/thm68-ii-proof.md section 4.1). In the note's example the generic stabilizer is mu_2, which is closed in G_kappa. What fails is the family Stab_V in G x V over a chart meeting s = 0. The instruction 'do not assume generic closedness before Step 5' also conflicts with the section 4.4 Claim, which obtains Stab_V' = D(M/Z) x V' by generic flatness after shrinking. It should be reworded, because it points away from the working route."
    }
   ],
   "verdict": "No compiled Lean statement was refuted, but two hand steps fail or are unsupported, and the main target is still not reached, as the report says. No compile was run; I read the sources and logs. The compile logs are newer than the sources, show no errors, and every printed #print axioms output, including the three named theorems, lists only propext, Classical.choice, Quot.sound. There is no sorry and no use of a stub.\n\nHand-checked and found correct:\n- thm41_unique_equivariant: coaction nilpotent mod K, degree 0 component, unit by completeness.\n- The doubled-point example against the non-equivariant form.\n- Flatness and induction through C/(g^k).\n- exists_chart_agree.\n- The direction of the change to OpenStratumMap: the new hypothesis is weaker, so nothing was smuggled in. By the same direction, the old proved separated case still implies it, so the QS theorems are not vacuous there.\n\nNo hypothesis assumes its conclusion. NoetherianAlgebraization, h42 and h43 remain real open inputs, as reported. Tannaka and AHR confirm that the target is true for quasi-separated X, and Lemma 4.3 and compatibility on V survive my tests when chi is equivariant.\n\nProblems, as listed:\n- Step 5 is false on A^1/R. Use the section 4.4 Claim of thm68-ii-proof instead.\n- Step 4's 'W affine' is not what 07ST gives, and its Claim S is not well-formed. Both can be repaired.\n- 'Any algebraic space' on the two effective theorems has content only for quasi-separated X.\n- The tower obstruction is overstated.\n- The S-globalization is missing from the remaining-work list.\n\nThe print was compared for Thm 6.8 and for Thm A.2 with its proof; no new discrepancy."
  }
 },
 {
  "k": "nonqc",
  "rs": [
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCAtlas.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCFact.lean"
    ],
    "proved": [
     "Thm 6.8 (i) for X not quasi-compact, with no coproduct hypothesis: AlgMag.Final.thm68_atlas, FinalNonQCAtlas.lean:106. X separated and l.f.p. over a separated S, one strongly-FPR atlas. The site cutoff is met directly: one chart per point of an atlas W of X, #W <= 2^size W (mk_scheme_le), each chart has size <= size S (Scheme.size_le_of_locallyOfFiniteType), so the coproduct lies in the site (exists_cofan_of_size, line 49).",
     "Thm 8.3, X not qc, no coproduct hypothesis, arbitrary N, no atlas hypothesis: thm83_nonqc, FinalNonQCAtlas.lean:134.",
     "Prop 14.4 first assertion, terms not qc, no coproduct hypothesis: prop144_nonqc, FinalNonQCAtlas.lean:147.",
     "Fact 3.34 (ii), arbitrary family (infinite allowed), X not qc: fact334_nonqc, FinalNonQCFact.lean:190. Departure from the suggested W = D(M)V route: no stable open W is built. Take the finite intersection K with rank K^x minimal (exists_units_min, line 60). For L <= K in the family, L meets K^x exactly in L^x, so the vertex of A(L) is the image of the vertex of A(K) (vertex_eq, line 87) and the vertex point v does not depend on L. Finitely many charts over v are fixed first, then the finite subfamily J as in fact334_strong. This also closes the 'Fact 3.34 infinite families' item for X separated l.f.p., and the circularity recorded in notes/fact334-attempt.md.",
     "Thm 15.3, X not qc: thm153_nonqc, FinalNonQCFact.lean:294; attractorOrder_nonqc in the same file.",
     "Axioms, all five statements: [propext, sorryAx, Classical.choice, Quot.sound]. No sorry in my files. They reach exists_charts, whose stubs are listed in notes/chart-stubs.md; I did not run a constant walk on the new files, so 'sorryAx only from those stubs' is inferred from the import path. Compile: cma/k.sh, logs cma/FinalNonQCAtlas.log and cma/FinalNonQCFact.log. Imports appended to AlgMag.lean, line added to notes/REQUIRES_FULL_STACKS.md."
    ],
    "notDone": [
     "Removing S separated: all five statements still assume [S.IsSeparated]. No mathematical obstruction found, the bridge is simply not written. Its source: isAffineHom_structMap, because chart_lift, isFaceCartesian_of_separated and exists_closure_of_affine_base need U->S affine. Route: for T affine over S, pass to the site of T with X_T = Over.map(T.hom).op composed with X, prove it is an algebraic space, separated, l.f.p., with the descended action (descAct, isAlgebraicSpace_fib in SpacesLimitStage are the starting point), and write a bijection between AttractorPt of X over W and AttractorPt of X_T over W. Fact 3.34 and Thm 15.3 are per-T and should come through this. Thm 8.3 and Prop 14.4 also need the S-affine atlas pieces of Def 6.1 (HasAffineDecomposition), so for them the change is not only local.",
     "Thm 6.8 quasi-compact clause with X->S quasi-compact and S not quasi-compact: not proved, no counterexample. Lean only has X absolutely qc (thm68_qc_spaces). The pieces of the coproduct atlas are affine, but their union need not be affine or qc over S: over an affine V of S infinitely many charts can appear unless the cover of S is locally finite. Whether an S-affine atlas exists for an S with no locally finite affine cover (for instance a nontrivial P(E) over such an S) is unsettled.",
     "Prop 14.4 last assertion (closed immersion) was not revisited here; prop144_closed_corrected stays as it was.",
     "Thm 6.8 (ii) with X not separated: not addressed, still blocked as in notes/partial-state.md (chart lemma only for X separated, input AHR Cor 20.2). Printed Thm 8.3 case (b) without X separated and printed Prop 14.4 with N f.g. and X not separated are not covered by these new theorems for the same reason."
    ],
    "addedAssumptions": [
     "S separated, in all five statements; not printed (printed S is arbitrary).",
     "X separated and l.f.p. in thm83_nonqc and for each term in prop144_nonqc; printed Thm 8.3 assumes an atlas plus (a) or (b), and printed Prop 14.4 allows N f.g. with X not separated. Separatedness is the printed case (a); l.f.p. is what discharges the atlas through Thm 6.8.",
     "X l.f.p. in fact334_nonqc and thm153_nonqc; printed Fact 3.34 (ii) only says X separated, M f.g. Without l.f.p. it stays open, per notes/fact334-attempt.md.",
     "M a finitely generated abelian group, as printed in Fact 3.34 (ii) and Thm 6.8. The hM, hZ site-membership hypotheses (Spec Z[M] and the terminal scheme lie in B) are bookkeeping for the site."
    ],
    "paperIssues": [
     "Fact 3.34, printed proof: the colimit step fails, as already recorded. New here: for infinite families with M f.g., the rank-minimal K gives a uniform vertex, which is the input the printed proof lacks. Worth reviewing by the author; it is a proof replacement, not a counterexample.",
     "Thm 6.8 parenthetical 'quasi-compact (in particular S-affine here) if X -> S is quasi-compact': for S not quasi-compact the printed proof gives no global S-affine atlas that I could reconstruct. To review; this is a suspicion, not a refutation."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCBase.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCLocal.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCRelQC.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\REQUIRES_FULL_STACKS.md",
     "C:\\Users\\Arnaud\\AppData\\Local\\Temp\\claude\\C--Users-Arnaud\\b7814f6f-6cc1-4071-93de-731ed0478fb7\\scratchpad\\nb\\kq.sh"
    ],
    "proved": [
     "Fact 3.34 (ii), S arbitrary (S separated removed), arbitrary family, X separated, l.f.p., not necessarily qc, no atlas and no coproduct hypothesis: AlgMag.Final.fact334_general, FinalNonQCLocal.lean:66. Printed reduction 'local over S': a point over T lands Zariski locally on T in an affine open O of S; there fact334_nonqc applies on the site of O (fact334_step, same file).",
     "Thm 15.3, S arbitrary, same X: AlgMag.Final.thm153_general, FinalNonQCLocal.lean:121.",
     "Site-change layer, for any object T0 of the site, FinalNonQCBase.lean: Res X T0 is X as a presheaf on the site of T0, with resAct. attrDown (line 88) and attrUp (line 126) pass attractor points between X over T0-objects and Res, compatibly with toPoint. res_alg, res_lfp (line 194) and res_sep (line 217) transfer algebraic space, l.f.p. and separated.",
     "Thm 6.8 (i), quasi-compact clause relative to S: X -> S quasi-compact, S quasi-compact and separated, gives an S-affine strongly-FPR atlas: AlgMag.Final.thm68_relqc, FinalNonQCRelQC.lean:33. Earlier Lean only had X absolutely qc.",
     "Thm 6.8 (i), quasi-compact clause, local form: X -> S quasi-compact, S arbitrary, O an affine open of S, gives an O-affine strongly-FPR atlas of X restricted to O: AlgMag.Final.thm68_relqc_local, FinalNonQCRelQC.lean:63.",
     "Axioms of all four named statements: [propext, sorryAx, Classical.choice, Quot.sound]. No sorry in the three new files. No constant walk was run, so 'sorryAx only from the stubs of notes/chart-stubs.md' is inferred from the import path, not checked. All compiled with cma/k.sh; logs are cma/FinalNonQCLocal.log and cma/FinalNonQCRelQC.log. Real Stacks modules RelocalizeComposite and QuasiCompactSmallerBase were compiled into cma/ov with nb/kq.sh. Imports appended to AlgMag.lean; line added to notes/REQUIRES_FULL_STACKS.md. No lake build was run on these files."
    ],
    "notDone": [
     "Thm 6.8 quasi-compact clause, global S-affine atlas with S not quasi-compact: neither proved nor refuted. The charts over affine opens are affine and qc over those opens, but a global U -> S affine needs finitely many components over each affine, and an irreducible non-qc S (for example A^infinity minus 0) has no locally finite affine cover. Over such S a connected-component count shows U has finitely many components, each affine over S, so X must be covered by finitely many images of S-affine etale maps. I found no construction and no counterexample. This is the open item, and it is not a stated obstruction.",
     "Thm 8.3 and Prop 14.4 without an atlas, S not separated: not written; thm83_nonqc and prop144_nonqc still assume [S.IsSeparated]. This matches the author decision of 2026-11-06 for the S-affine form of Thm 6.8. For S not separated, an affine chart U -> S need not be affine, so no atlas of the Def 6.1 kind comes from the charts. thm83 with a given atlas already works for any S. Route to the direct statement, not attempted: take P as the image subfunctor of X (toPoint is injective for X separated), identify its restriction to each affine open O with thm83_nonqc on Res X O, then glue with isAlgebraicSpace_of_open_cover (Tag 02WR) and isAlgebraicSpace_coproduct_of_size_le (Tag 02WQ). The tree's AlgebraicityOnBaseCover handles finite covers only, and it and CoproductAlgebraicSizeBound are not in cma/ov.",
     "Prop 14.4 last assertion (closed immersion): not revisited; prop144_closed_corrected is unchanged.",
     "Thm 6.8 (ii), X not separated: not addressed. It is still blocked as in notes/partial-state.md (chart lemma only for X separated, printed input AHR Cor 20.2). Printed Thm 8.3 case (b) without X separated and printed Prop 14.4 with N f.g. and X not separated are not covered, for the same reason.",
     "Fact 3.34 (ii) and Thm 15.3 without X l.f.p.: not addressed. All statements here still assume l.f.p."
    ],
    "addedAssumptions": [
     "X l.f.p. in fact334_general and thm153_general; printed Fact 3.34 (ii) only says X separated, M f.g.",
     "S separated in thm68_relqc, with S also quasi-compact; thm83_nonqc and prop144_nonqc keep S separated. Separatedness matches the author decision of 2026-11-06. The S quasi-compact hypothesis is not printed.",
     "thm68_relqc_local concludes only over each affine open O of S, not globally as printed.",
     "X separated in all statements; printed Thm 6.8 also has case (ii).",
     "hM, hZ site membership (Spec Z[M] and the terminal scheme lie in B) are site bookkeeping, as before."
    ],
    "paperIssues": [
     "Thm 6.8 and Thm A.2: printed proof of the clause says 'The final claim that U -> X can be chosen quasi-compact if X -> S is quasi-compact is obvious.' and the statement adds '(in particular S-affine here)'. For S not quasi-compact I cannot reconstruct this: the local atlases over affine opens do not assemble into one S-affine atlas unless the cover of S is locally finite. For S qc it is correct (thm68_relqc). This is a suspicion, not a refutation; author to review.",
     "Fact 3.34, printed proof: the colimit step fails, as already recorded. The replacement via the rank-minimal K now holds for S arbitrary as well (fact334_general)."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCBaseLocal.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCBaseLocal2.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCSmallAtlas.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCAttRes.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCAttAlg.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCGeneral.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\REQUIRES_FULL_STACKS.md",
     "C:\\Users\\Arnaud\\AppData\\Local\\Temp\\claude\\C--Users-Arnaud\\b7814f6f-6cc1-4071-93de-731ed0478fb7\\scratchpad\\gl\\stub\\StacksFrontier\\AlgebraicGeometry\\Spaces\\CoveringRestrictionCoproduct.lean"
    ],
    "proved": [
     "Thm 8.3, X separated, l.f.p., not necessarily qc, arbitrary magnet, S arbitrary (S separated removed), no atlas and no coproduct hypothesis: AlgMag.Final.thm83_general, FinalNonQCGeneral.lean:121. Conclusions: X^N algebraic, X^N -> X^{N^x} affine, X^{N^x} -> X closed immersion, quasi-separated, separated, qc if X is, l.f.p. Representability alone: thm83_repr_general, line 55.",
     "Prop 14.4 first assertion, terms separated, l.f.p., not necessarily qc, S arbitrary, no atlas: AlgMag.Final.prop144_general, FinalNonQCGeneral.lean:138.",
     "X^K is an algebraic space for S arbitrary: AlgMag.Final.attP_alg, FinalNonQCAttAlg.lean. Proof: over each member of an affine open cover of S it is thm83_nonqc on the site of that member. Gluing is Stacks 04SK (isAlgebraicSpace_of_isCovering_of_atlas_size_le). The atlas bound comes from X^K -> X being a monomorphism: one affine chart per point of a fixed atlas of X (exists_small_atlas, FinalNonQCSmallAtlas.lean).",
     "Representable properties local on the base: exists_rep_over (FinalNonQCBaseLocal.lean) and presheaf_of_openBase (FinalNonQCBaseLocal2.lean). Identification of the restricted attractor with any representing presheaf: attResIso (FinalNonQCAttRes.lean).",
     "Earlier round, still standing: fact334_general, thm153_general (FinalNonQCLocal.lean), thm68_relqc, thm68_relqc_local (FinalNonQCRelQC.lean).",
     "All six new files compile with cma/k.sh, EXIT 0, no sorry in them. #print axioms of attP_alg, thm83_general, prop144_general: [propext, sorryAx, Classical.choice, Quot.sound]. sorryAx is inferred to come only from the stubs of notes/chart-stubs.md plus the one new 04SK stub; no constant walk was run. No lake build was run on these files. Imports appended to AlgMag.lean, line added to notes/REQUIRES_FULL_STACKS.md."
    ],
    "notDone": [
     "Thm 6.8 quasi-compact clause, one global S-affine atlas with X -> S qc and S not qc: neither proved nor refuted, unchanged from the earlier round. No obstruction is established. For S irreducible, an S-affine U has finitely many components, but a connected S-affine etale U can still surject onto a non-affine open, so the component count alone gives no counterexample. Thm 8.3 and Prop 14.4 no longer depend on this clause.",
     "Stub to discharge: isAlgebraicSpace_of_isCovering_of_atlas_size_le is stubbed in cma/ov because its real closure is 1572 modules. The signature was copied by hand from HEAD and not machine-compared. It exists in the Stacks tree with a full proof; a full lake build replaces the stub.",
     "Thm 6.8 (ii), X not separated, and through it printed Thm 8.3 case (b) and printed Prop 14.4 with N f.g. and X not separated: not addressed. Blocked as in notes/partial-state.md (chart lemma only for X separated, printed input AHR Cor 20.2).",
     "Fact 3.34 (ii), Thm 15.3, Thm 8.3 and Prop 14.4 without X l.f.p.: not addressed. All statements here assume l.f.p.",
     "Prop 14.4 last assertion (closed immersion) in atlas-free form with S arbitrary: not written. prop144_closed_corrected still takes atlases; hat is not available for S non-separated, so it needs a rewrite using thm83_repr_general.closed_i. Not attempted.",
     "Thm 8.3 (vi), (vii) with S arbitrary: not restated. thm83_vi takes any r, so (vi) follows from thm83_repr_general; thm83_vii not checked."
    ],
    "addedAssumptions": [
     "X l.f.p. in thm83_general, prop144_general and attP_alg. The printed Thm 8.3 assumes it only for (iv), and printed case (a) gets its magnet handling via Tag 049J-type limits; Prop 14.4 prints l.f.p.",
     "X separated in all statements (printed Thm 8.3 case (a); Prop 14.4 alternative 'X separated').",
     "M f.g. as abelian group (AddGroup.FG M), needed to obtain the atlas that the printed Thm 8.3 assumes; it comes from Thm 6.8.",
     "hZ, hM site membership: Spec Z[M] and the terminal scheme lie in B. Site bookkeeping, as before.",
     "thm68_relqc still has S qc and separated; thm68_relqc_local concludes only over affine opens. Unchanged."
    ],
    "paperIssues": [
     "Thm 6.8 / Thm A.2: 'The final claim that U -> X can be chosen quasi-compact if X -> S is quasi-compact is obvious' and '(in particular S-affine here)'. For S not quasi-compact I could not reconstruct this. It is a suspicion, not a refutation; author to review. For S qc and separated it holds (thm68_relqc).",
     "Thm 8.3 proof uses an S-affine atlas, which for S not separated need not come from the charts (an affine chart is not S-affine). The statement still holds with no atlas when X is separated and l.f.p. (thm83_general): the proof works locally on S and glues. This is a strengthening, not an error; it belongs in REMARKS.",
     "Fact 3.34 printed proof: the colimit step fails, as already recorded."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalNonQCClauses.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\REQUIRES_FULL_STACKS.md"
    ],
    "proved": [
     "All in AlgMag.Final, FinalNonQCClauses.lean; X (or each term) separated, l.f.p., not necessarily qc, S arbitrary, no atlas and no coproduct hypothesis. Thm 8.3 (v) in relative form: thm83_v_general.",
     "Thm 8.3 (vi): thm83_vi_general.",
     "Thm 8.3 (vii): thm83_vii_general, with X only isomorphic to a representable; on a given representation: scheme_of_repr.",
     "Prop 14.4, X^N -> X representable by algebraic spaces: prop144_rep_general.",
     "Prop 14.4, last assertion, X^Z -> X representable by a closed immersion, atlas-free: prop144_closed_general.",
     "Prop 14.4, ind-scheme variant, both the ind-scheme statement and representability by schemes: prop144_scheme_general.",
     "Compile: cma/k.sh FinalNonQCClauses produced the olean with no error reported, no sorry in the file. The exit code line itself was lost when the shell was stopped by an unrelated stray command, so this rests on the olean timestamp (after the last edit) and an error-free log. #print axioms of all six: [propext, sorryAx, Classical.choice, Quot.sound]. sorryAx is inferred to come from the stubs of notes/chart-stubs.md and the 04SK stub; no constant walk was run. No lake build was run.",
     "The 04SK stub signature (isAlgebraicSpace_of_isCovering_of_atlas_size_le) now machine-compared with Stacks HEAD: identical after whitespace normalization. Sec12Final, Sec14Final, Sec14Strong compiled into cma/ov.",
     "Earlier rounds, still standing: fact334_general, thm153_general, thm83_general, prop144_general, attP_alg, thm68_relqc, thm68_relqc_local."
    ],
    "notDone": [
     "Thm 6.8 quasi-compact clause, one global S-affine atlas with X -> S qc and S not qc: neither proved nor refuted. thm83 and prop144 no longer depend on it. New partial reasoning this round, by hand and unchecked: for S irreducible, normal and locally noetherian, an S-affine etale U has finitely many components, each of bounded generic degree over X, so a counterexample would need a non-qc irreducible S (e.g. infinitely iterated blow-up) with bundles P(E) lacking bounded-degree multisections. However boundary divisors of S can absorb that obstruction, so no counterexample results.",
     "Thm 6.8 (ii), X not separated, and through it printed Thm 8.3 case (b) and printed Prop 14.4 with N f.g. and X not separated: not addressed. Blocked as in notes/partial-state.md: chart lemma only for X separated, printed input AHR Cor 20.2.",
     "Fact 3.34 (ii), Thm 15.3 without X l.f.p.: not addressed in Lean. notes/fact334-attempt.md has a hand proof for X a separated scheme (Hahn series route, about 8 steps, only algebra steps in Lean, not formalized here). For X a non-scheme algebraic space it records the case as undecided, with no obstruction theorem.",
     "Thm 8.3 without X l.f.p.: the atlas-free statements need l.f.p. because the atlas comes from Thm 6.8, which prints l.f.p. The printed atlas-hypothesis form exists separately (thm83_repr). Not a mathematical obstruction to the printed theorem, but S non-separated with an atlas hypothesis and no l.f.p. was not restated.",
     "The 04SK stub and chart stubs remain stubs in cma/ov. The real closure is 1572 modules; a full lake build replaces the stub, which was not run. FinalNonQCClauses is not in AlgMagBuilt."
    ],
    "addedAssumptions": [
     "X l.f.p. in all atlas-free statements. Printed Thm 8.3 assumes an atlas instead and l.f.p. only for (iv); Prop 14.4 prints l.f.p.",
     "X (each term) separated: printed Thm 8.3 case (a), Prop 14.4 alternative 'X separated'.",
     "M f.g. as abelian group (AddGroup.FG M), used to obtain the atlas via Thm 6.8. Countable M follows from it.",
     "hZ, hM site membership: Spec Z[M] and the terminal scheme lie in B. Site bookkeeping.",
     "thm68_relqc still has S qc and separated; thm68_relqc_local concludes only over affine opens. Unchanged."
    ],
    "paperIssues": [
     "Thm 6.8 / Thm A.2: 'The final claim that U -> X can be chosen quasi-compact if X -> S is quasi-compact is obvious' and '(in particular S-affine here)'. For S not quasi-compact I could not reconstruct this. It is a suspicion, not a refutation; author to review. It holds for S qc and separated (thm68_relqc). Author decision 2026-11-06 already makes S separated official; the recorded fix in notes/corrections-verified.md assumes X quasi-compact.",
     "Thm 8.3 proof uses an S-affine atlas, which for S not separated need not come from the charts. The conclusions, including (v), (vi), (vii) and Prop 14.4's last assertions, still hold with no atlas when X is separated and l.f.p. This is a strengthening, not an error; it belongs in REMARKS.",
     "Thm 8.3 proof and Prop 14.4 text: no new error found this round. X^N -> X is not the composite X^N -> X^{N^x} -> X (the first map is the limit map), which is why prop144_rep_general and prop144_scheme_general use attToX directly. This is a formalization note, not a misprint.",
     "Fact 3.34 printed proof: the colimit step fails, as already recorded."
    ]
   }
  ],
  "check": {
   "verdict": "No claimed Lean statement is refuted. I compiled nothing: I read the 12 FinalNonQC files and the definitions they use, and compared them with the print. No vacuity and no assumed conclusions found. The new mathematics holds up by hand: the minimal-rank vertex argument in fact334_nonqc, the site change, and the bounded atlas behind attP_alg. Compile evidence holds: no sorry, axiom or native_decide in the 12 files; no 'error' in their logs; each .olean checked (the Clauses one by exact time) is later than its source; the axioms printed are as reported. A script compared all sorry stubs in the overlay sources with Stacks HEAD: 04SK matches, and the only differences were the renamings and inlined variable blocks already recorded, plus the hasSheafify alias and four declarations the script could not locate (three recorded as located in other HEAD files), not re-read here. Corrections: printed Thm 15.3 is false for M not finitely generated (new counterexample, not in the notes); one stub is missing from the stated sorryAx sources; the blocker given for printed Thm 8.3 (b) is wrong; Fact 3.34 (iii) is missing from notDone; hZ and hM are not real assumptions. Reachability of stubs remains inferred: no constant walk was run.",
   "problems": [
    {
     "where": "Printed Thm 15.3 (section 15 standing hypotheses, am.txt:3239 and 3263-3282); missing from paperIssues and notDone",
     "detail": "New counterexample, by hand, not in notes/corrections-verified.md. Section 15 assumes only M an abelian monoid and X separated. The proof cites Fact 3.34 outside its hypotheses (i)-(iii), and the theorem then fails. Take S = Spec Z, M = direct sum of Z e_i (i >= 1), N_k = {a : a_i >= 0 for i <= k}, N_inf = intersection of the N_k = direct sum of N e_i. Z[N_{k+1}] -> Z[N_k] inverts x_{k+1}, so A(N_k) is the open D(x_{k+1}) of A(N_{k+1}). Let X = union of the A(N_k), a separated scheme (increasing union of affine opens) with D(M) action, neither qc nor l.f.p. For T affine and x in A(N_j)(T), put i = max(j,k); chi^n -> x(n) chi^n on N_i gives an equivariant A(N_k)_T -> A(N_i) inside X extending x, so X^{N_k} = X for all k. X^{N_inf}(T) is empty for T nonempty: the composite to A(N_inf) is graded, so it sends the origin of A(N_inf)_kappa to all coordinates 0, and every point of X has cofinitely many nonzero coordinates. For Y = X, E(Y) lies in N_inf, so X^{E(Y)} lies in X^{N_inf} and is not Y. A pure N with X^N = X would lie in E(X), which forces X^N empty. So the attractor X is not hit, and 'Y = X^{E(Y)}' fails. Fact 3.34 itself is untouched, since M is not f.g. Fix: Thm 15.3 needs one of Fact 3.34 (i)-(iii). Consequence: the report's 'M f.g., used to obtain the atlas' understates this, because for Thm 15.3 some such hypothesis is necessary (this example is not l.f.p., so it does not show f.g. is needed when X is l.f.p.). The new Lean statements thm153_nonqc and thm153_general are not affected."
    },
    {
     "where": "AlgMag/FinalNonQCBase.lean:186 (res_alg); report line 'sorryAx is inferred to come from the stubs of notes/chart-stubs.md and the 04SK stub'; notes/REQUIRES_FULL_STACKS.md:38,42,43",
     "detail": "The inference is wrong. res_alg uses Space.isAlgebraicSpace_fibreOfSection directly. In cma/ov it is the sorry stub lmf/src/.../Stacks/PresheafRepresentability.lean; that olean contains sorryAx, and FinalNonQCBase.olean names the constant. It is not in notes/chart-stubs.md, and the note's walk output has no such root. It reaches fact334_general, thm153_general, thm68_relqc_local, attP_alg, thm83_general, prop144_general and all of FinalNonQCClauses. Harmless for truth: the signature is identical to HEAD Stacks/PresheafRepresentability.lean:114, which has no sorry. Still, the stub list and REQUIRES lines must add it, and a constant walk on the new roots should replace the inference. Direct search of the new oleans finds only this stub and 04SK; transitive reach through other non-clean modules was not walked."
    },
    {
     "where": "Report notDone: 'Thm 6.8 (ii) ... and through it printed Thm 8.3 case (b) and printed Prop 14.4 with N f.g. and X not separated'",
     "detail": "Wrong dependency for Thm 8.3 (b). Printed Thm 8.3 takes the N^x-FPR atlas as a hypothesis, so case (b) does not go through Thm 6.8 (ii). Its blocker is Prop 5.1 (i) for X not separated: STATUS.md:279 says the non-separated case is open, and notes it as an agreed correction. For Prop 14.4 the route does use Thm 6.8, but finishing 6.8 (ii) would still not suffice. 6.8 (ii) needs M/N^x torsion-free, and printed 14.4 has no such condition. With the doubled line, M = Z/2, N = 0 (STATUS.md:283), X^0 -> X is not closed, so by Prop 8.1 no 0-FPR atlas exists, and the printed chain gives no proof of the first assertion there, even though X^0 is representable in that example. This is a printed gap to record; it is not a refutation."
    },
    {
     "where": "Report notDone: omitted items",
     "detail": "Fact 3.34 (iii) atlas-free is not listed. fact334_general covers (ii) only; (iii) is still fact334_iii_finite_scheme and fact334_iii_atlas (notes/fidelity-grades.md:26). It is not a corollary, because Thm 6.8 and the chart lemma are for groups M and (iii) has M a cancellative monoid. It should be listed as not done."
    },
    {
     "where": "Report addedAssumptions: 'hZ, hM site membership. Site bookkeeping'",
     "detail": "These are not real assumptions and can be removed from every statement. B.Contains X is X.size < B.cutoff (Topologies/Fppf.lean:194), and B has aleph0 < cutoff with cutoff a strong prelimit. Spec Z and Spec Z[M] with M f.g. have countable rings, and Scheme.size_Spec_lt_of_mk_le (Size/Cutoff.lean:241) looks designed for this bound. I did not read its exact hypotheses; the terminal scheme also needs size transfer along an iso. A short lemma should discharge both, which removes one item from the fidelity penalty."
    },
    {
     "where": "AlgMag/FinalNonQCAtlas.lean:106 thm68_atlas; AlgMag/FinalNonQCRelQC.lean:33 thm68_relqc; notes/fidelity-grades.md:48",
     "detail": "Mislabelled scope. Both conclude a strongly-FPR atlas, which is printed Conjecture 6.9 (am.txt:1770-1775), restricted to S separated (thm68_atlas, clause (i)) and S separated and qc (thm68_relqc, clause (ii)), on stubs. Printed Thm 6.8 only asks for Z-FPR. The report files them under Thm 6.8, and fidelity-grades.md:48 still says Conj 6.9 (i) has no Lean statement. The S-separated restriction is forced for clause (i), by the doubled-plane counterexample already in corrections-verified.md:260. This should be reported as the conjecture's status, not as Thm 6.8."
    },
    {
     "where": "Report notDone, first item: 'a counterexample would need a non-qc irreducible S'",
     "detail": "This does not follow from the reasoning given. The finite-components claim only sees the generic fibre, so it needs X irreducible or dominating S: components of U over closed parts of S are invisible there (X = S disjoint union a locally finite family of closed points, for instance). Nothing given excludes reducible non-qc S: a locally finite chain of qc pieces still needs atlases that match over the intersections, and no gluing argument is given. The S-affine clause stays open for S separated and not qc, as already recorded in corrections-verified.md:634. The reasoning does not narrow the search."
    }
   ]
  }
 },
 {
  "k": "f334",
  "rs": [
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\Fact334InfAlgebra.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\fact334-attempt.md",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean"
    ],
    "proved": [
     "By hand, no independent review (notes/fact334-attempt.md, 'Second pass'), for arbitrary separated X (no l.f.p., not qc), T affine, arbitrary R. Pinching case: N_k = cone((1,0),(k,1)), N_inf = N(1,0): p in X^{N_k}(T) for all k implies p in X^{N_inf}(T), by closed equalizer on A(N_1) x_{A(N_inf)} A(N_1) plus fpqc descent.",
     "By hand, no independent review, same generality for X and R. Cone case: N_k = {a>=0, b>=-a/k}, N_inf = N^2. More generally N_1 sharp f.g., N_inf f.g., with e in N_inf and e + N_1 inside N_inf. Route: the affine open U around the vertex section gives phi: O(U) -> localization of R[N_1]; its series is supported in N_inf; Krull on a f.g. coefficient subring puts the denominators in 1 + J_inf; this gives Spec Lambda -> X; then descent along the fpqc cover G x Spec Lambda -> A(N_inf)_T extends p. The 'no stable affine neighbourhood' wall of the first attempt is not an obstruction. These are pointwise statements, stronger than the printed hypothesis needs.",
     "Lean: AlgMag.Fact334Inf.pinching_iInf_eq_zero, AlgMag/Fact334InfAlgebra.lean:23, axioms propext, Classical.choice, Quot.sound. It is the ideal step (b) of the pinching case.",
     "Lean: AlgMag.Fact334Inf.krull_step, AlgMag/Fact334InfAlgebra.lean:33, axioms propext, Classical.choice, Quot.sound. It is the denominator step of the cone case. Compiled with lean -o into the scratchpad f334 dir; import appended to AlgMag.lean."
    ],
    "notDone": [
     "General Fact 3.34 for infinite families, X separated without l.f.p.: STILL OPEN. Neither proved nor refuted; no counterexample found, and no mathematical obstruction established.",
     "N_inf of smaller rank that is not a face, e.g. N_k = cone((k,k+1),(k+1,k)), N_inf = N(1,1): the first-pass step (b) or a mix of the two proofs is not done.",
     "N_1 not sharp with varying unit groups: only the case where all N_k are groups is argued, by hand; the mixed case is not done.",
     "N_1 or N_inf not f.g.: krull_step needs a noetherian ring. Example N_inf = {0} + {a>=1,b>=0}: the series condition alone is insufficient (x/(1+y) has support in N_inf and is not in Lambda); one must also use that f is constant on the fibre over the vertex. Not finished.",
     "The scheme-level parts of the pinching and cone proofs (fpqc descent, equalizers, the cover G x Spec Lambda, the identification with attractor points) are NOT formalized. Only the two algebra lemmas are checked, so these cases are paper proofs, not Lean theorems about attractors. Existing STATUS row for Fact 3.34 is unchanged and stays PARTIAL.",
     "Noetherian approximation route abandoned: equivariant X = lim X_i needs [X/G] -> BG of approximation type, which Rydh's Questions 2.13 leaves open for representable morphisms (read in arXiv version, not the journal J. Algebra 422 (2015), since not accessed)."
    ],
    "addedAssumptions": [
     "The paper proofs of pinching and cone cases are for N_1 sharp and f.g., and N_inf f.g.: these restrict the printed Fact 3.34 (ii). The family is taken as a decreasing chain, which assumes the reduction to finite intersections (Prop 3.32) as in the first attempt."
    ],
    "paperIssues": [
     "No new error in the printed text. Already recorded: the printed proof step 'A(cap N_l)_S = colim_J A(cap_J N_l)_S' fails in schemes (chain_no_point). Whether the printed statement (ii) holds for infinite families in full generality remains undecided."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\Fact334InfDiagonal.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\fact334-attempt.md",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean"
    ],
    "proved": [
     "By hand, no independent review (notes/fact334-attempt.md, 'Third pass'). Fact 3.34 (ii) for arbitrary families when X is a separated SCHEME over S, M is f.g., and some N_1 has its unit group contained in every N_i (for example N_1 sharp). Then X^{N_1} = X^{cap N_i}. There is no finiteness condition on X, on the N_i, on the intersection Q or on R, and the rank of Q may drop. This subsumes the pinching case, the cone case, cone((k,k+1),(k+1,k)) and the non-f.g. cases of the earlier rounds, so krull_step is no longer needed.",
     "New idea, the diagonal trick. The vertex v is fixed by G, so the action pulls an affine neighbourhood U back to an open set containing G x v. For u in O(U) and c = phi(u) this gives, in Hahn series over R[M], tau(c) Psi = rho, where Psi = 1 - sum g^m d_m and rho = sum g^l e_l are finite sums with coefficients in phi(O(U)), and the d_m have constant term 0. Taking the diagonal Delta (coefficient of g^s at chi^s) gives c g0 = a', with g0 in 1 + J_Q R[Q] and a' in R[Q]. So phi(O(U)) lies in Lambda = (1+J_Q)^{-1} R[Q]. Descent along G x Spec Lambda -> A(Q)_T then uses an injective-ring argument in place of torus density, which is what handles rank drop.",
     "By hand, verified directly. The plain intersection statement 'c in (1+J_k)^{-1}R[N_k] for all k implies c in Lambda' is FALSE, so any proof must use the fixed vertex. Example: Q = {0} u {a>=1,b>=0}, N_k = Q u {b>=L_k, a>=-b/k} with L_k -> infinity, c = x/(1+y). This is not a counterexample to Fact 3.34; the theorem covers this family.",
     "Lean: AlgMag.Fact334Inf.diag_tau_mul, AlgMag/Fact334InfDiagonal.lean:32. Delta(tau(c) B) = c Delta(B). Axioms propext, Classical.choice, Quot.sound.",
     "Lean: AlgMag.Fact334Inf.mul_diag_eq_diag, AlgMag/Fact334InfDiagonal.lean:47. Same axioms.",
     "Lean: AlgMag.Fact334Inf.diag_coeff_term, AlgMag/Fact334InfDiagonal.lean:52. Same axioms. All three compiled with lean -o into the scratchpad f334 dir, zero sorry; import appended to AlgMag.lean."
    ],
    "notDone": [
     "General Fact 3.34 (ii) is STILL OPEN when the unit groups of the N_i have no minimum, i.e. no member's units lie in all the others. Example shape: N_i = {b>=1} u (iZ x {0}). Neither proved nor refuted, no counterexample, no obstruction established. Blocker: the affine neighbourhood lives over a piece of A(H_1), and after localizing the coefficients in R[H_1], 'support in N_i' has no meaning inside the graded pieces. Evidence only: on the vertex line, mu_i-invariance plus density of the mu_i shows that N_i = iZ x N and the vertex line of the example shape can be handled; these are not a general argument.",
     "X a separated algebraic space that is not a scheme: not covered, because the proof uses affine open neighbourhoods. The atlas case remains the existing fact334_strong.",
     "Scheme-level part of the theorem is NOT formalized: the map phi, the open Omega and element w, the fpqc cover G x Spec Lambda, and the descent. Only the diagonal algebra is in Lean, so the theorem is a paper proof, not a Lean theorem about attractors. The Lean is stated for linearly ordered M; torsion in M is treated by hand. The STATUS row for Fact 3.34 was not edited (rule: no edits to existing files); it stays PARTIAL and should gain the three new lemma names.",
     "The proof needs an independent review; nobody but me has checked it."
    ],
    "addedAssumptions": [
     "The paper theorem adds to printed (ii): X is a scheme, and some N_1 has its units contained in every N_i. Both hypotheses are absent from the printed statement.",
     "Printed case (iii) (M cancellative) was not separately reworked; it reduces to (ii) through the existing fact334_iii_of pattern, but I did not check this reduction for the new theorem."
    ],
    "paperIssues": [
     "No new error in the printed statement. Already recorded: the printed step 'A(cap N_l)_S = colim_J A(cap_J N_l)_S' fails in schemes (chain_no_point). For X a scheme with the unit condition above, the printed conclusion holds by the new proof, so that printed step can be replaced there. Printed (ii) in full generality remains undecided."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\Fact334InfUnits.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\Fact334InfDiagonal.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\fact334-attempt.md",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean"
    ],
    "proved": [
     "By hand, no independent review (notes/fact334-attempt.md, 'Fourth pass'): printed Fact 3.34 (ii) in full for X a separated SCHEME. M is a f.g. abelian group, the family (N_i) is arbitrary with all X^{N_i} equal, and the conclusion is X^{N_i} = X^{cap N_l}. No hypothesis is added, so the earlier condition 'some N_1 has units contained in all N_i' is removed.",
     "New step for unit groups without a minimum. Close the family under finite intersections and take N_1 of minimal unit rank; then N_i n H_1 = H_i. The vertex map on A(H_1)_T is invariant under every D(H_1/H_i), hence under D(H_1/H) because the ideals meet in 0, so it descends to a G'-fixed v : A(H)_T -> X with G' = D(M/H). Over affine opens T1 of A(H)_T with v(T1) in an affine open of X, the third-pass argument runs with M' = M/H, Q' sharp and Q' n H_1' = 0. It uses a twisted Hahn ring because H need not split, and the diagonal Delta on graded pieces. The local solutions glue by separatedness and injectivity of R[Q] -> R[N_1].",
     "Lean: AlgMag.Fact334Inf.neg_mem_of_mem_units, AlgMag/Fact334InfUnits.lean. Axioms: propext.",
     "Lean: AlgMag.Fact334Inf.iInf_inter_eq_zero, AlgMag/Fact334InfUnits.lean. Axioms: propext, Classical.choice, Quot.sound.",
     "Lean: AlgMag.Fact334Inf.exists_nsmul_mem_of_finrank_eq, AlgMag/Fact334InfUnits.lean. Same rank implies a positive multiple lies in the subgroup. Axioms: propext, Classical.choice, Quot.sound.",
     "Lean: AlgMag.Fact334Inf.mapDomain_eq_zero_of_directed, AlgMag/Fact334InfUnits.lean. R[A/H] injects into the product of the R[A/H_i] for a directed family. Axioms: propext, Classical.choice, Quot.sound.",
     "All four compiled with lean -o into the scratchpad f334 directory, zero sorry; import appended to AlgMag.lean. Earlier Lean algebra (diag_tau_mul and companions) is unchanged."
    ],
    "notDone": [
     "X a separated algebraic space that is not a scheme: STILL OPEN, neither proved nor refuted, no counterexample and no established obstruction. The printed statement is about algebraic spaces, so printed (ii) is not settled in full. Reductions R0-R2 do carry over, and G' x Spec Lambda^h is still an fpqc cover, so it would suffice to show c in Lambda^h. Blocker: with only an etale neighbourhood, tau(c) lies in a henselization rather than being rational, and the diagonal Delta is only tau-linear, so it does not pass through polynomial relations (diagonals of algebraic series need not be algebraic).",
     "The scheme theorem is NOT a Lean theorem about attractors: phi, the twisted Hahn rings, Omega and w, the fpqc cover, the descent and the gluing are paper only. Only algebra steps are in Lean, and diag_tau_mul is stated for linearly ordered M, without the twisted graded or torsion form. I did not attempt the full formalization in this round.",
     "The proof has had no independent review; I checked it once line by line myself.",
     "The Levi total order and the surjectivity computation in step 5 are by hand.",
     "Printed (iii) was not reworked for the new theorem. X^{cap_J N_l} need not be a scheme, so the scheme theorem may not apply to it directly.",
     "The STATUS.md row for Fact 3.34 was not edited (rule: no edits to existing files); it stays PARTIAL and should gain the new lemma names and the scheme result. notes/partial-state.md also still says open."
    ],
    "addedAssumptions": [
     "The paper theorem adds exactly one restriction to printed (ii): X is a scheme, not an algebraic space. The unit-group hypothesis of the previous round is gone.",
     "Lean lemma exists_nsmul_mem_of_finrank_eq assumes M is finite over Z and the two ranks are equal; this is what minimal rank provides."
    ],
    "paperIssues": [
     "No new error in the printed statement. Already recorded: the printed step 'A(cap N_l)_S = colim_J A(cap_J N_l)_S' fails in schemes (chain_no_point). For X a scheme, the printed conclusion of (ii) holds by this new proof, which replaces that step. For non-scheme algebraic spaces, printed (ii) remains undecided."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\Fact334InfConductor.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\fact334-attempt.md",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean"
    ],
    "proved": [
     "By hand, no independent review (notes/fact334-attempt.md, 'Fifth pass'): the pinching case holds for X a separated ALGEBRAIC SPACE and every R. It uses only the closed equalizer, fpqc descent along the free map R[x] -> R[x,w], and pinching_iInf_eq_zero (already in Lean). The same two tools are claimed for the case where all N_i are groups; that one was not rewritten in detail.",
     "By hand, one line of argument, not written in detail: printed (iii) for X a separated scheme follows from the fourth-pass theorem applied over M^gp, via the route of fact334_iii_of. This resolves the earlier worry: X^{cap_J N_l} need not be a scheme, because only X is used.",
     "Lean, AlgMag/Fact334InfConductor.lean: AlgMag.Fact334Inf.exists_common_shift (finitely many elements of Q-Q have a common shift into Q). Axioms: propext, Classical.choice, Quot.sound.",
     "Lean, same file: AlgMag.Fact334Inf.cone_no_conductor (N_1 = {a>=0, b>=-a} has no conductor into N^2). Axioms: propext, Classical.choice, Quot.sound.",
     "Both compiled with lean -o into the scratchpad f334 directory, zero sorry; import appended to AlgMag.lean. Full lake build not run (not allowed here)."
    ],
    "notDone": [
     "The cone case for X a separated non-scheme algebraic space is STILL OPEN, so printed (ii) and (iii) remain undecided for non-scheme spaces. There is no counterexample and no obstruction theorem. For schemes the cone case is covered by the third and fourth passes.",
     "Exact blocker for the cone case on spaces: c = phi(u) lies in the henselization E_1^h with support in Q, but the auxiliary coordinates of its etale presentation have support in N_1, not Q, and cone_no_conductor shows no monomial moves them into Q. So Artin approximation over R_0[Q]^h has no unknowns in the completion. A field-coefficient sketch via algebraicity over Frac k[Q] exists, but it does not give X^{N_1} = X^Q, which needs all T, including nilpotents in R_0.",
     "Second blocker, for rank drop on spaces (other than pinching): Lambda^h tensor_Lambda Lambda^h has non-diagonal sheets killed by the map to series, and there is no open q_0 to control them by density, so third-pass step 7 does not transfer. With ZQ = M and N_1 f.g., exists_common_shift supplies q_0 on D(chi^e), but this helps only conditionally on the first blocker.",
     "The scheme theorem (fourth pass) is still NOT a Lean theorem about attractors: phi, the twisted Hahn rings, the fpqc cover, descent and gluing are on paper only. Formalization not attempted this round. Pinching on spaces is also not formalized as an attractor statement; only its ideal lemma is in Lean.",
     "The fourth-pass proof still has no independent review. Levi order and surjectivity computations are by hand.",
     "STATUS.md and notes/partial-state.md were not edited (rule: no edits to existing files). They should gain the scheme result and these lemma names; partial-state.md still says open without qualification."
    ],
    "addedAssumptions": [
     "Pinching on spaces: no added assumption.",
     "The scheme theorem still adds exactly one restriction to printed (ii) and (iii): X is a scheme.",
     "exists_common_shift assumes each element of the finite set is a difference of elements of Q, i.e. ZQ contains them. No paper statement depends on it yet."
    ],
    "paperIssues": [
     "No new error in the printed statement. Already recorded: the printed step 'A(cap N_l)_S = colim_J A(cap_J N_l)_S' fails in schemes (chain_no_point). For non-scheme spaces the printed conclusion is undecided.",
     "Error in my own earlier note, not in the paper: section B of notes/fact334-attempt.md claimed its conductor hypothesis 'e + N_1 in N_inf' covered the cone example, and it does not (cone_no_conductor). The cone case for schemes is still proved by the third and fourth passes, which do not use that hypothesis. Corrected in the note."
    ]
   }
  ],
  "check": {
   "problems": [
    {
     "where": "notes/fact334-attempt.md:82 and :95; last report, notDone, first blocker",
     "detail": "The stated blocker looks wrong. Line 82 says Delta 'does not pass through polynomial relations'. That fails for relations whose unknowns are tau(c_j) with coefficients in phi(A) tensor R', since tau(c)^alpha = tau(c^alpha) and Delta(tau(c^alpha) X) = c^alpha Delta(X). The 'auxiliary coordinates with support in N_1' (line 95) can also be avoided. Let V = (G x U) x_{a,X} U. It is etale over G x U, and it is CLOSED in G x U x_T U because X is separated. So C = O(V) is generated over B = A tensor R' by finitely many 1 tensor u_j, u_j in A, and all phi(u_j) have support in Q. Since I/I^2 = C^n for an etale algebra, choose P_1..P_n in I = ker(B[Y] -> C) with d_j P_i = delta_ij in C. In H', P_i(tau c) = 0 with Jacobian Id. Delta then gives Ptilde_i in R[Q][Y] with Ptilde(c) = 0 and Jacobian Id at c. Hence c lies in the image of the henselization Lambda^h of (R[Q], J_Q), by uniqueness of roots in the henselian pair (series supported in Q, positive part). Lambda^h -> H is injective: descend an etale neighbourhood to f.g. R_0 and f.g. Q_0, where R_0[[Q_0]] injects in H, and apply Krull. This gives h : Spec Lambda^h -> U with no Artin approximation, valid with nilpotents. The third-pass rational case is the degree-1 instance. Checked by hand once by this reviewer; not independently reviewed."
    },
    {
     "where": "notes/fact334-attempt.md:97; last report, notDone, second blocker",
     "detail": "The rank-drop descent blocker also looks avoidable, with no q_0 and no density argument. Do not test on Lambda^h tensor Lambda^h -> series. Test on Y' = Spec(E_1 tensor_Lambda Lambda^h). The ring injects into H: by flatness it lies in R[M] tensor_{R[Q]} Lambda^h, which is the direct sum over x in M/ZQ of chi^x Lambda^h[1/Q], and these summands have disjoint supports. So f_1 pr_1 = h pr_2 on Y' by the closed equalizer. Pull back to E_1 tensor_Lambda (Lambda^h tensor_Lambda Lambda^h), into which Lambda^h tensor_Lambda Lambda^h injects because Lambda -> E_1 is injective and the algebra is flat. This gives h p_1 = h p_2, so h descends to Spec Lambda -> X (X is an fpqc sheaf, 0APL), and third-pass steps 6-8 run unchanged. With the previous item this proves the sharp nested case, including the cone case, for separated SPACES on paper. So 'STILL OPEN' and 'undecided' reflect a missed argument for this case, not an obstruction. Reviewer sketch only; it needs a written proof and an independent check."
    },
    {
     "where": "notes/fact334-attempt.md:82 versus :71; last report, notDone",
     "detail": "Unflagged gap for spaces. Line 82 says 'The whole reduction R0-R2 works (descent and separatedness only)', but R0 closes the family under finite intersections using fact334_finite_scheme, which is a scheme theorem. For spaces, the two-magnet case in Lean needs IsStronglyFPRAtlas (attractorImage_inf_of_eq, via exists_inf_of_bi, AlgMag/Sec3Intersections.lean:515-525). So the report's blocker list is incomplete: finite non-nested families on atlas-free spaces are also unproved, and printed Prop 3.32 (ii) is affected too. The all-groups claim at line 90 has the same issue for non-directed families. A possible fix, by hand only: exists_iter_of_image_eq already takes spaces and gives F on A(N) x A(L). Work over M + M with magnet N + L. F is invariant under the antidiagonal D((M+M)/Delta M), which forces series support in (N+L) n Delta M = Delta(N n L). Then the first two items run with Q = Delta(N n L), since the unit-group reduction goes through the same invariance."
    },
    {
     "where": "AlgMag/Fact334InfDiagonal.lean:19, Fact334InfUnits.lean, Fact334InfAlgebra.lean, Fact334InfConductor.lean; report phrase 'Lean algebra'",
     "detail": "No new Lean statement mentions an attractor, an action or X. All of them import only Mathlib. Nothing is vacuous and no stubs are used, but none is Fact 3.34 even in a special case, so STATUS must stay PARTIAL. There is also a mismatch with the fourth pass: diag_tau_mul assumes LinearOrder and IsOrderedAddMonoid on M (so M is torsion-free) and an untwisted R[M]. The fourth pass uses M' with torsion, twisted pieces B_m, and support PWO only in M'/tors, so the Lean lemma does not cover that case. tau is only a coefficient map; its multiplicativity, the identity tau(c) Psi = rho, and Hahn inverses are not in Lean."
    },
    {
     "where": "notes/fact334-attempt.md:30-33; AlgMag/Fact334InfAlgebra.lean:14 and :31",
     "detail": "Stale false claim. Section B still reads 'Cone: ... PROVED for every R', and the correction appears only at line 86. The krull_step docstring still calls it the 'Cone case' with A = R_0[N_inf], but step 3 needs b = chi^e h in A, and cone_no_conductor shows this fails for that example. The Lean theorem itself is correct and unused. The cone case stands only through the third and fourth passes."
    }
   ],
   "verdict": "The scheme theorem survived. I went through the third and fourth passes line by line against printed Fact 3.34 (Semigroup Forum text) and found no error, covering the vertex, w, Delta, the Hahn order, surjectivity of alpha, the injectivity of Pi, gluing and rank drop. So printed (ii) for separated schemes holds on paper, with X a scheme as the only restriction. Printed (iii) for schemes follows by the fact334_iii_of route, whose reduction hypothesis hZ is exactly this statement. Pinching on spaces and the false-intersection example x/(1+y) also check out. All of this is a by-hand review; I compiled nothing. The refutable part is the account of what remains open on spaces. Both stated blockers look like missed arguments, and sketches removing them are in problems 1-2. The real gap the report omits is finite intersections (R0) on atlas-free spaces, in problem 3. No counterexample was found. Nothing here is a Lean theorem about attractors. Recommended next step: write the spaces argument (problems 1-3) in full, get it independently reviewed, then formalize."
  }
 },
 {
  "k": "misc",
  "rs": [
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMisc164.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMisc331Ring.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMisc331.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMiscProp91.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMiscCor103.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean (imports appended)"
    ],
    "proved": [
     "§16.4 (i) by the printed route, `AlgMag.FinalMisc.sec164_i_printed`: Prop 3.31 for L=Zα -> M on X^L, in the universe of X^L (`prop331InnerEquiv`, on `BigPt`). Remarks 3.11 and 3.12 agree through D(M)->D(L) (`magnet_smul_toMagnet`), and D(M)->D(L) is an fppf epimorphism. X an algebraic space, M finitely generated. Compiled against the real build; axioms clean (fin/k.sh).",
     "Prop 3.31 (ii) for a separated algebraic space with Z=Z, Y=N, any f: M->Z including d>=2: `AlgMag.FinalMisc.prop331_ii_spaces`, S in universe 0. It uses the fppf cover (u,x)|->u x^d (`cover_jnD`: free, finitely presented, surjective, in FinalMisc331Ring). The fibre product is handled by the explicit monoid Q in Z x Z x N (`Qd`, `hQ`, normal form `nfA`, `nfC`), and the closed equalizer goes through `dense_specAlong`/`gVal_eq`. Compiled against the real build; axioms clean.",
     "Prop 9.1 as a natural isomorphism, `AlgMag.FinalMisc.prop91_natIso`: T |-> A(T) tensor G(T) (`tenF`) is isomorphic to f_*f^*G (`pushF`) on the affine base, with the printed value on pure tensors. Compiled in the b2 overlay; `sorryAx` comes only from the two existing b2 stubs, and the file itself has no sorry.",
     "Cor 10.3, printed square for algebraic spaces with X' affine, `AlgMag.SpacesLift.cor103_spaces`: the non-equivariant filler comes from formal smoothness, the equivariant one from the integration route. Compiled in the sl overlay; `sorryAx` comes from the existing Sec11Spaces stubs in sl/src."
    ],
    "notDone": [
     "Prop 3.31 (ii) for spaces with general Z, Y. There is a concrete obstruction to the route through the cover: D(M) x A(Y) -> A(N) is not flat in general. Example: M = L = Z(1,1)+2Z^2 in Z=Z^2, Y=N^2, where N is the cone <(2,0),(1,1),(0,2)> and the source is regular over a singular target. The general case needs A(N) to be a categorical quotient in algebraic spaces. The scheme proof (`SQ.exists_desc`) does not extend, and no such result was found in the tree. Only Y=N, Z=Z is done.",
     "Cor 10.3 for spaces in the LiftTorsor frame: not ported. Only the integration route covers spaces. The port means redoing about 2400 lines of Sec10Printed{Lifts,Act,Torsor,Diff,Pl,Int,Vanish,Main} with functor sections in place of scheme morphisms and 07SY in place of the scheme push-out. This is work, not a mathematical obstruction.",
     "Thm 12.4 through 067U and 063M: not done. The theorem itself stands through formal smoothness (`printed_ring`), but the printed route is not formalized. Pieces located in Stacks git: `isRegularImmersion_of_smooth_of_smooth` (067U), `isQuasiRegularImmersion_of_isRegularImmersion`, `isFiniteLocallyFree_conormalSheaf_of_isQuasiRegularImmersion` (063M), `affineConormalIsoCotangent`, `finite_projective_moduleSpecΓ_of_isFiniteLocallyFree`. No Conormal module is built, and no bridge between `conormalSheaf` and `(Spec A).Modules` was written.",
     "Lem A.5 for general G: not attempted, still D(M) only. 02LK is at Flatness/FiniteNeighborhood.lean (`exists_etaleNeighborhood_finiteAt`). Still missing: the stub of SGA3 VII_B 5.5.1, a group-scheme statement, the slicing step, and Lemma A.4 for regular sequences of powers.",
     "Rem A.7, second proof: not formalized. A grep of Stacks git found no quotient of an algebraic space by a finite locally free group with infinitesimal stabilizer ([30, Th. 5.3]); it found 07S7 (free group scheme quotient, Spaces/FreeGroupSchemeQuotient.lean) and Groupoids/FiniteFlat* modules, not inspected in detail. The conclusion stays proved by `remA7`.",
     "notes/REQUIRES_FULL_STACKS.md and STATUS.md were not updated (rules: no editing existing files). FinalMiscProp91 is b2 overlay only and FinalMiscCor103 sl overlay only. FinalMisc331 imports DoubleScalarSpaces, which an earlier note in notes/REQUIRES_FULL_STACKS.md lists as outside AlgMagBuilt, though its olean is in .lake/build."
    ],
    "addedAssumptions": [
     "`prop331_ii_spaces`: X separated is added; the printed Prop 3.31 (ii) does not assume it. It is used for the closed equalizer on the fibre product. S in universe 0, because Z : Type 0, as in `prop64_space`.",
     "`cor103_spaces`: X' = Spec A1 affine with a square-zero surjection, the earlier agreed correction. It also carries the `SR`/`SM` site-size classes of Sec11SpacesCore, and hypotheses `hρt`, `h₀ρ`, `h₀c` (compatibility with the structure map).",
     "`prop91_natIso`: the tensor product is read on affine objects, as a presheaf on the base; it is not sheafified as an object. Whether this counts as a sheaf isomorphism in the printed sense is a judgement call. `PrintedQCoh G` and `AffOver X` carry the hypotheses."
    ],
    "paperIssues": [
     "Prop 3.31 (ii), printed proof: the D(K)-quotient description is not an fppf quotient in general. For Y=N, f=d the action on D(Z) x A^1 has stabilizer mu_d along x=0, so the fibre product of (u,x)|->u x^d is only schematically dominated by the orbit map. Separatedness of X is what makes the equalizer step work, and the printed statement does not assume it."
    ]
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMiscThm124Cited.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMiscThm124Local.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean (imports appended)"
    ],
    "proved": [
     "Thm 12.4, ring step without formal smoothness: `AlgMag.Sec12Printed.printed_ring_cited` (FinalMiscThm124Cited.lean:56). If I/I^2 is projective and Sym(I/I^2) -> gr_I is injective (`GrInjective`), then Sym_{A0}(I/I^2) is isomorphic to B. Compiled with fin/k.sh against the real build; axioms propext, Classical.choice, Quot.sound.",
     "Tags 062Z/063M, ring form: `AlgMag.Sec12Printed.grInjective_of_isQRAt` (FinalMiscThm124Local.lean:139). If I is generated at each maximal ideal of A0 by a quasi-regular sequence (`IsQRAt`), then Sym(I/I^2) -> gr_I is injective. Same compile; same axioms.",
     "`AlgMag.Sec12Printed.printed_ring_qr` (FinalMiscThm124Local.lean:337) combines the two: I/I^2 projective plus local quasi-regular generators give Sym_{A0}(I/I^2) isomorphic to B. Same compile; same axioms. This is the ring half of the printed route; it is not yet connected to schemes or to the group action."
    ],
    "notDone": [
     "Thm 12.4 through 067U and 063M, scheme bridge: not written, so the printed route is still incomplete. The theorem itself stands through `printed_ring` (formal smoothness). Two links are missing for Spec(A0) -> Spec(B) smooth over a base. (1) `IsQuasiRegularImmersion` (from `isRegularImmersion_of_smooth_of_smooth` and `isQuasiRegularImmersion_of_isRegularImmersion`) to `IsQRAt`: this needs the stalk reading of `quasiRegularMap` on `coborderRange`, clearing denominators, and the identification of `definingIdeal` with I. (2) `Module.Projective A0 (I/I^2)`, using `conormalSheaf_isFiniteLocallyFree`, `affineConormalIsoCotangent` and `finite_projective_moduleSpecΓ_of_isFiniteLocallyFree`. Projectivity cannot come from `IsQRAt`: that condition is stalkwise only, and a finite module with free stalks need not be projective, so link (2) needs the sheaf statement on an open. Stacks modules RegularIdealSheaf/Immersion, MoreMorphisms/RegularIdealSheaf/RegularToQuasiRegular and MoreMorphisms/RelativeRegularImmersion/SyntomicIntoSmooth have no olean in the sparse build, so an overlay is needed. This is work, not a mathematical obstruction.",
     "Prop 3.31 (ii) for spaces with general Z, Y: unchanged this round. Only Z=Z, Y=N is done (`prop331_ii_spaces`). Stated obstruction: D(M) x A(Y) -> A(N) is not flat in general (M = L = Z(1,1)+2Z^2 in Z^2, Y=N^2), so the cover route fails. The general case needs A(N) to be a categorical quotient in algebraic spaces, and no such result was found in the tree.",
     "Cor 10.3 for spaces in the printed LiftTorsor frame: not attempted this round. Only the integration route covers spaces (`cor103_spaces`). The port is about 2400 lines. This is work, not a mathematical obstruction.",
     "Lem A.5 for general G: not attempted this round, still D(M) only. 02LK is available (`exists_etaleNeighborhood_finiteAt`). Still missing: a stub of SGA3 VII_B 5.5.1, a group-scheme statement, the slicing step, and regular powers with Lemma A.4.",
     "Rem A.7, second proof: not attempted this round. No Rydh quotient [30, Th. 5.3] was found in the earlier grep; Groupoids/FiniteFlat* is still not inspected. The conclusion stays proved by `remA7`.",
     "Not checked this round: the imports appended to AlgMag.lean were not built with lake (per the rules). FinalMiscThm124Cited and FinalMiscThm124Local compile only into scratchpad/fin/out so far. notes/REQUIRES_FULL_STACKS.md and STATUS.md were not updated (rule: no editing existing files)."
    ],
    "addedAssumptions": [
     "`printed_ring_cited`, `printed_ring_qr`: `[Module.Projective A0 (I/I^2)]` and the quasi-regularity condition are hypotheses, not derived. They stand for the outputs of the cited tags 067U, 063M, 062Z until the scheme bridge exists.",
     "`GrInjective` is stated through any section s of I -> I/I^2 rather than as a map Sym -> gr_I. The map J^k/J^(k+1) -> I^k/I^(k+1) does not depend on s, but that independence is argued in the docstring, not proved in Lean.",
     "`IsQRAt` is my ring-level reading of Stacks 061M/063D (4), not the Stacks definition. Its derivation from `IsQuasiRegularImmersion` is the missing link (1), so its match with the Stacks notion is not yet checked in Lean."
    ],
    "paperIssues": []
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMiscThm124Smooth.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMiscThm124Printed.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean (two imports appended)",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\REQUIRES_FULL_STACKS.md (one line appended)"
    ],
    "proved": [
     "Thm 12.4, X affine over S, printed route: `AlgMag.Sec12Printed.printed_affine_067U` (FinalMiscThm124Printed.lean:112). X -> S smooth, N f.g. or M f.g., F a face subgroup of N. Then the conormal I/I^2 of A/J_F -> A/J_N is projective and Sym(I/I^2) is isomorphic to A/J_N. It uses Cor 11.2, not Cor 11.10; `printed_affine` remains the Cor 11.10 version. #print axioms: propext, Classical.choice, Quot.sound.",
     "Cor 11.2 on charts: `smooth_Qalg` (FinalMiscThm124Printed.lean:81). A/J_N is smooth over Γ(S,U), through `smooth_Zatt` (X^N -> S smooth). Axioms: same three.",
     "Tag 067U content read at a prime: `isQRAt_of_smooth` (FinalMiscThm124Smooth.lean:71). For A0, B smooth over R and π an R-algebra retraction, `IsQRAt π q` holds at every prime q. This closes link (1) of the earlier report at ring level, using exists_isRegular_fibre_of_smooth_of_syntomic, the spreading-out theorems (Tags 062Y, 046Y) and Tag 00LN. It goes through their ring-level content, not the scheme statements `isRegularImmersion_of_smooth_of_smooth` or `IsQuasiRegularImmersion`. Axioms: same three.",
     "Projectivity: `projective_conormal_of_smooth` (FinalMiscThm124Smooth.lean:216). I/I^2 is a direct summand of A0 ⊗_B Ω_{B/R} (Tag 031I). This closes link (2) of the earlier report, by a different argument from the printed Tag 063M. Axioms: same three.",
     "Ring statement: `printed_ring_smooth` (FinalMiscThm124Smooth.lean:256). Sym_{A0}(I/I^2) is isomorphic to B for A0, B smooth over R, with no formal smoothness of A0 -> B assumed. Axioms: same three.",
     "Checked from the files, no new work this round: §16.4 (i) `sec164_i_printed` (FinalMisc164.lean:107); Prop 3.31 (ii) for spaces, Z=Z, Y=N, d>=2, by fppf cover and closed equalizer (`gVal_eq`, `cover_jnD`, FinalMisc331.lean, assumes X separated; not re-compiled this round); Prop 9.1 `prop91_natIso` (FinalMiscProp91.lean:141), an isomorphism of presheaves on the affine base, not yet stated as an isomorphism of sheaves."
    ],
    "notDone": [
     "Thm 12.4, global statement: `thm124_attP`, `thm124_general` etc. still use the Cor 11.10 route. `printed_affine_067U` is a parallel chart statement and those theorems were not rewired to it. It does not assert Module.Finite, which `printed_affine` does. The theorem itself is already proved, so this concerns fidelity of the proof only.",
     "Not checked: lake has not built these files. They compile with `lean -o` against an overlay of 8 Stacks modules compiled at scratchpad q124/out. Their sources are in the sparse checkout; they are listed in notes/REQUIRES_FULL_STACKS.md and lake must build them. Compile script: scratchpad q124/k.sh Module; overlay builder: q124/b.sh.",
     "Prop 3.31 (ii) for spaces, general Z, Y: not attempted, unchanged. D(M) x A(Y) -> A(N) is not flat in general, so the cover route fails. It needs A(N) to be a categorical quotient in algebraic spaces, and no such result was found in the tree.",
     "Prop 9.1 as a sheaf isomorphism: not attempted. Only the presheaf isomorphism on affines exists; the sheaf form is not stated.",
     "Cor 10.3 for spaces in the printed LiftTorsor frame: not attempted. Only `cor103_spaces` exists (integration route, X' affine). The earlier estimate for the port is about 2400 lines. This is work, not a mathematical obstruction.",
     "Lem A.5 for general G: not attempted, still D(M) only. 02LK is available. Still missing: a stub of SGA3 VII_B 5.5.1, the slicing step, and regular powers with Lemma A.4.",
     "Rem A.7, second proof: not formalized. It needs Rydh's quotient [30, Th. 5.3] for a non-free action with finite infinitesimal stabilizers on an algebraic space. Groupoids/FiniteFlatAffine/AffineQuotient.lean only treats finite flat equivalence relations on affine schemes (from its header; the rest of the directory was not read), which does not cover this. A stub would be needed. The conclusion stays proved by `remA7`."
    ],
    "addedAssumptions": [
     "None in `printed_affine_067U` beyond the existing `printed_affine` hypotheses: `N.FG ∨ AddGroup.FG M`, X affine over S, and F a face subgroup. In `printed_ring_smooth`, the retraction π is required to be R-linear through φ with hφ; this holds for `piR`."
    ],
    "paperIssues": []
   },
   {
    "done": false,
    "files": [
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMiscProp91Sheaf.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag\\FinalMiscThm124Face.lean",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\AlgMag.lean (two imports appended)",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\REQUIRES_FULL_STACKS.md (one line appended)",
     "C:\\Users\\Arnaud\\Desktop\\algmag-stacks\\notes\\partial-state.md (section appended)"
    ],
    "proved": [
     "Prop 9.1 as a sheaf isomorphism: `AlgMag.FinalMisc.prop91_sheaf` (FinalMiscProp91Sheaf.lean:407). f: X -> B affine, G printed quasi-coherent, J any topology on the site of B that contains the Zariski coverings and for which G is a sheaf. The printed canonical morphism `canon` from the presheaf tensor product (T |-> A(T) tensor_{O(T)} G(T), on all objects, A = f_*O_X) to f_*f^*G is locally injective and locally surjective, its target is a J-sheaf, and every morphism to a J-sheaf factors uniquely through it. So f_*f^*G is the sheafification of the presheaf tensor product. #print axioms: propext, sorryAx, Classical.choice, Quot.sound. The sorryAx is not new: it comes from `prop91_printed`, which sits on the two existing b2 stubs (fpqcDescentOfQuasicoherentHoms, exists_bijective_sectionsBaseChange).",
     "Supporting statements for Prop 9.1 in the same file: `canonAt_bijective` (:264), bijectivity at affine T, same two stubs; `canon_isLocallyInjective` (:306) and `canon_isLocallySurjective` (:322), same axioms; `pushF_isSheaf` (:338), f_*f^*G is a J-sheaf whenever G is, axioms propext, Classical.choice, Quot.sound.",
     "Thm 12.4, global statement, printed route: `AlgMag.Sec12SpacesThm.thm124_attP_printed` (FinalMiscThm124Face.lean:120), with face form `thm124_induced_face_printed` (:84). The statement is identical to `thm124_attP`, but the chart statement comes from Cor 11.2 and the ring-level content of Tags 067U, 063M, 062Z, not Cor 11.10. Axioms of `thm124_attP_printed`: propext, Classical.choice, Quot.sound. `thm124_general` (schemes) was not rewired.",
     "Finiteness of the conormal module on this route: `finite_conormal_of_smooth` (FinalMiscThm124Face.lean:29), I/I^2 is a quotient of A0 tensor_B Omega_{B/R} (Tag 031I). `symOver_printed` (:65) gives the full `SymOver` by this route."
    ],
    "notDone": [
     "Not checked by lake: both new files compile with `lean -o` only, FinalMiscThm124Face in the q124 overlay (scratchpad q124/k.sh) and FinalMiscProp91Sheaf in the b2 overlay (scratchpad b2/k.sh). The lake build must still confirm them; they are recorded in notes/REQUIRES_FULL_STACKS.md.",
     "Cor 10.3 for spaces in the printed LiftTorsor frame: not attempted this round, estimate about 2400 lines from an earlier round. Only `cor103_spaces` exists (integration route, X' affine). This is work, not a mathematical obstruction.",
     "Lem A.5 for general G: not formalized, still D(M) only. Available: 02LK (`exists_etaleNeighborhood_finiteAt`), 046Z, 00ME/00MF/00MG, 062Y in the Stacks git. Missing: a stub of SGA3 VII_B 5.5.1, the lifting of the sequence to augmentation functions, an openness step for fibrewise regularity (needed so the powers stay flat at all points of F), the transfer of the 02LK open back into G, and Lemma A.4 assembly. The statement also needs settling first; see paperIssues.",
     "Rem A.7, second proof: not formalized. It needs a stub of Rydh [30, Th. 5.3]; I found no such quotient in the Stacks git (the checks were 04S6 for free actions and an earlier read of AffineQuotient), though the search was not exhaustive. The tree also has no general infinitesimal G. The conclusion stays proved for D(M) by `remA7`.",
     "Prop 3.31 (ii) for spaces, general Z, Y: unchanged. Only Z=Z, Y=N, d>=2 exists (FinalMisc331.lean, X separated). The cover route fails in general because D(M) x A(Y) -> A(N) is not flat, and it would need A(N) to be a categorical quotient in algebraic spaces.",
     "§16.4 (i): no new work; the existing `sec164_i_printed` (FinalMisc164.lean:107) was not re-examined this round.",
     "`thm124_general` (schemes) still uses the Cor 11.10 route; only the spaces statement `thm124_attP_printed` was rewired."
    ],
    "addedAssumptions": [
     "`prop91_sheaf` takes J as a parameter with `hJ` (J contains the Zariski cover sieves) and `hGJ` (G is a J-sheaf). I did not instantiate J at the printed fppf topology, because `PrintedQCoh` only gives the Zariski sheaf condition, so fppf-sheafness of G would have to be supplied. `Presieve.finestTopologySingle` could give a J from Zariski sheafness alone, but I did not write that instance or prove its `hJ`.",
     "`thm124_attP_printed`: none beyond `thm124_attP`, whose charts use the `Or.inr` branch (M finitely generated, standing in §12)."
    ],
    "paperIssues": [
     "Lem A.5, suspected and not formally refuted. The printed proof ends: \"The containments (I1)d(n-1)+1 ⊂ In ⊂ (I1)n show that the sequences of ideals {In} and {(I1)n} are cofinal\" (this is the proof of Lem A.4, which the proof of A.5 invokes). This gives cofinality with powers of I1, not with the n-th order thickenings of the unit section that the statement asks for. That needs J^k ⊂ I_n for J the augmentation ideal, which requires F to be supported on the unit section, while the printed proof only isolates e in the fibre over s. Example with a disconnected fibre: for G = mu_2 over Z_(2), the generic fibre of F has a second point. The D(M) Lean form `lemmaA5` makes this direction conditional on `TorsionResidue` for this reason. I have no counterexample with connected fibres; I expect the general G direction to hold only near s, and this should be decided before formalizing."
    ]
   }
  ],
  "check": {
   "problems": [
    {
     "where": "Lem A.5, printed statement (Romagny appendix), general G; report's paperIssues entry and STATUS.md:254",
     "detail": "The statement is FALSE, not just suspected, and the fibres of the counterexample are connected. Proved by hand; the identity below was also machine-checked in char 2, t = 0..4.\n\nThe example. R a DVR of characteristic 2 with uniformizer π, for instance k[π]_(π). G = V(F) in G_a² over R, with F = x⁴ + πx² + π²y. F is additive in char 2, so G is a subgroup scheme. F is primitive, so G is flat, and it is finitely presented. G_η ≅ A¹ with coordinate x. G_s = α_4 × A¹_y. Both fibres are connected.\n\nThe key identity. Put y = (x⁴+πx²)/π² on G_η and w = x²/π, so y = w²+w. Then g_t := x² + π(y + y² + ... + y^(2^t)) equals π^(1-2^(t+1)) · x^(2^(t+2)) on G_η.\n\nThe argument. Let S'→S be étale at s', and let F' be finite locally free with support the unit section. Over the DVR O_{S',s'}, F' is flat, so it is the closure of its generic fibre V(x^m), and O_F' embeds in K'[x]/x^m. For 2^(t+2) ≥ m this gives g_t = 0 in O_F', so x² ∈ πO_F'. Hence x² = 0 on the special fibre of every such F'. But x² ≠ 0 in O_G/(π, J³) = k[x,y]/(x,y)³. So V(J³) is contained in no F', and no infinitesimal sequence is cofinal.\n\nHow this relates to the report. The printed F_n = V(x_i^n) always contains V(J^n), because (x_i^n) ⊂ J^n. So they are cofinal exactly when they are infinitesimal, and here they never are. Concretely, x₁ = x+y is regular on G_s and gives F = V(x(x-π)), with the extra section (π,π) specialising to e(s); x₁ = y gives x²(x²+π) = 0. This settles the report's open points 'no counterexample with connected fibres' and 'should be decided before formalizing'. Its guess 'holds only near s' is also wrong: the failure is at s.\n\nConsequences. Do not formalize general-G A.5. STATUS.md:254 and notes/partial-state.md:7 list a library blocker (SGA3 VII_B 5.5.1, EGA IV 18.12.1); that is not the real obstacle. The D(M) form `lemmaA5` is unaffected, since it has V(I^n) ⊂ F_n and, under `TorsionResidue`, I^k ≤ J_n. The uses in Thm A.2 are for D(M/Z), so the main text is unaffected. This belongs in the corrigendum, subject to the author's reading."
    },
    {
     "where": "Thm A.1, printed proof, general flat f.p. G with connected fibres",
     "detail": "The same G breaks the printed proof of A.1, and the report does not say so. The step \"Since Spec(A') is artinian, it is included in one of the Fn × X0\" fails, and so does X^G = X_0.\n\nTest case. X = Spec k[u]/u² over s, with G_s acting through x ↦ x² by u ↦ u + x². Every infinitesimal F_n acts trivially, so X_0 = X, while X^G is empty.\n\nThe one-way sequence V(y^n) contains the thickenings, but it is not infinitesimal, so Lemma A.3's closedness does not apply to it.\n\nThe statement of A.1 is NOT refuted: in this test the empty set is closed in X. What is lost is the printed proof for general G. Only the D(M) form in Lean (`a1_closed`, `thmA1_closed`) is proved, and that one stands."
    },
    {
     "where": "AlgMag/FinalMisc164.lean:107, `sec164_i_printed`",
     "detail": "The statement is weaker than Prop 3.31 as used in §16.4 (i). The two conjuncts `Nonempty (∀ T, Y₁.obj (op T) ≃ ...)` and `Nonempty (∀ T, Y₂.obj (op T) ≃ BigPt ...)` assert unspecified, unnatural bijections for each T. As written, they say only that cardinalities agree.\n\nThe printed content is an identification of functors. It exists in the file (`prop331InnerEquiv` is explicit, and `prop331Inner_baseChange` gives naturality), but the headline theorem discards it. It should state the explicit map, with its compatibility with `r₂.equiv` and base change.\n\nThe theorem also stops at `innerMagnet N L` under D(L). The printed sentence \"[α⟩ ⊂ ⟨α⟩ ≃ N ⊂ Z ... attractor under Gm\" needs α non-torsion and the identification D(L) = G_m; that step appears only in the docstring of `stage_i_fppf`, not in this statement.\n\nThe mathematics of `prop331InnerEquiv` is correct: f = L → M, the printed Prop 3.31 with its M := L and Z := M, and D(M) → D(L) an fppf epi."
    },
    {
     "where": "AlgMag/FinalMiscProp91Sheaf.lean:402-413, `prop91_sheaf`",
     "detail": "The theorem is correct but not instantiated. `GrothendieckTopology (SB Bsp)` occurs only as this parameter: no fppf or Zariski topology on SB Bsp is defined anywhere in AlgMag/. So the docstring's \"for instance the fppf topology of the print\" has no witness. The report flags that J was left uninstantiated, but the docstring reads as if the instance were available.\n\nTo reach the printed identity one still needs three things: the fppf topology on SB Bsp, `hJ` for it, and `hGJ` derived from `PrintedQCoh`, which gives only Zariski sheaves plus `IsQCohAt` on affine T. A Zariski J is an easy non-vacuity witness and should be written.\n\nThe site is schemes over B, not the printed B_spaces,fppf; this is a known gap (notes/partial-state.md, §9 bridge), but it is still between this theorem and the print."
    },
    {
     "where": "Stubs: b2/src (`fpqcDescentOfQuasicoherentHoms`, `exists_bijective_sectionsBaseChange`) and sl/src (0616, 04AM, 07SY section form)",
     "detail": "No problem found; recorded so this need not be rechecked. All five stub statements match the real declarations at Stacks HEAD 012108f61, the only difference being `top_le_preimage_top'`, a proof-irrelevant rename. The real proofs exist, and a grep of StacksFrontier finds no real `sorry` (the two hits are docstrings).\n\nSo `sorryAx` in `prop91_*` and `cor103_spaces` is a build limitation, not an unproved mathematical input. It stays until the closure compiles, and these theorems must not be reported as clean."
    },
    {
     "where": "Thm 12.4 route labels: `thm124_attP_printed`, `printed_affine_067U`, docstring FinalMiscThm124Face.lean:11",
     "detail": "\"Printed route\" holds only from Cor 11.2 downward. Upstream, `smooth_repMap` goes through Sec11Schemes.lean:325 and `exists_equivariant_of_lift` (Sec10LiftsCore), which is the integration route. It does not use the printed Prop 10.1/9.13 torsor, per REMARKS.md:27-28.\n\nProjectivity uses Tag 031I, not Tag 063M; the report says so, but the docstrings \"content of Tags 067U, 063M, 062Z\" do not. The tree does have scheme-level `@[stacks 067U]` (SyntomicIntoSmooth.lean:128) and `@[stacks 063M]` (RegularImmersion/FinitePresentation.lean:98), and neither is used here.\n\nThese are labelling points. I found no mathematical fault: `isQRAt_of_smooth`, `grInjective_of_isQRAt`, `projective_conormal_of_smooth`, `finite_conormal_of_smooth`, `IsAug` and the weight `wZ` are correct and non-vacuous, and the §12 hypothesis change is the one recorded at REMARKS.md:48."
    },
    {
     "where": "AlgMag/FinalMisc331.lean:16-17 and :318-321, `prop331_ii_spaces`, `gVal_eq`",
     "detail": "`hsep` is not in printed (ii). The docstring calls the fibre-product equalizer \"the printed closed equalizer\", which misattributes it. The printed equalizer lives on D(K) × D(M) × A(Y), where p: D(Z) → D(K) is an fppf epi, so no separatedness is needed. The fibre product over Q appears only because the printed free quotient is false.\n\n`hsep` looks removable. Hand sketch, not in Lean and not checked at source: the equalizer of A, C on V = Spec R[Q] is a locally finite type monomorphism, hence unramified, hence étale-locally a closed immersion at points of its image. It contains the open {x≠0}, which is schematically dense because x is a monomial non-zero-divisor in R[Q]. It also meets every point: at a field point with x = 0, the equivariance of ψ gives h^d · ψ(0) = ψ(0), and d-th powers are an fppf epi, so G_m fixes ψ(0) and A = C. So the equalizer is open and surjective, hence everything.\n\nThe case f = 0 should go the same way, using that the fibre of a chart over a K-point is étale over K. Worth trying: it would give the case Z = ℤ, Y = ℕ of (ii) with no added hypothesis."
    }
   ],
   "verdict": "I found no mathematical error in the Lean theorems reviewed: Thm 12.4 printed route, Prop 9.1 as sheaves, §16.4 (i), Prop 3.31 (ii) with Z=ℤ, Cor 10.3 with X' affine. All line numbers and `#print axioms` lines I checked against the logs match the report (the §16.4 (i), Prop 3.31 (ii), Prop 9.1 sheaf and Thm 12.4 logs; not the `cor103_spaces` log). This was read-only: nothing compiled, nothing edited.\n\nThe main result is a counterexample to Lem A.5 as printed, with connected fibres: G = V(x⁴+πx²+π²y) in G_a² over a characteristic 2 DVR. No finite locally free infinitesimal neighbourhood contains the second-order thickening of the unit section. So general-G A.5 should be dropped from the to-do list and moved to corrections. It also breaks the printed proof of Thm A.1 for general G, but not its statement. The D(M) forms in Lean and the main text are unaffected.\n\nThree fidelity gaps remain:\n- `sec164_i_printed` states only bare bijections.\n- `prop91_sheaf` has no topology instance anywhere in the tree.\n- 'Printed route' for Thm 12.4 holds only from Cor 11.2 down.\n\nThe separated hypothesis in `prop331_ii_spaces` looks removable, by a hand sketch not checked in Lean. All five stubs match real, sorry-free Stacks statements, so the `sorryAx` is a build limitation only. The hand-checked counterexample needs the author's reading before it enters the corrigendum."
  }
 }
]