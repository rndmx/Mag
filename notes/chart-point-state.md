# Section 1 of ahr-specialized-proof: state

PROVED, axioms propext, Classical.choice, Quot.sound, compiled with scratchpad cm2/c.sh (not lake):
- AlgMag/ChartPointRing.lean: stable_ideal_top_or_nil (transitivity: stable closed subset of Spec k[N] is empty or all), surjective_of_residue_surjective (Nakayama step), coact.
- AlgMag/ChartPointFinal.lean: isField_of_chartPoint, isAffine_of_chartPoint, isSeparatedOver_of_space, orbitInput_of_closed.
- AlgMag/ChartPointReduce.lean: finPair, exists_Zp (Z' = Gamma(S)[t]/(t^q-t) standard etale, P -> Z' mono), XP, actProd, isPullback_XP, xp_props, isChartAt_of_XP.
- AlgMag/ChartPointAssemble.lean: finite_of_chartPoint, exists_orbitInput_of_lemma11.

NOT PROVED: Lemma 1.1. AlgMag.ChartPoint.Lemma11Statement is a statement; exists_orbitInput_of_lemma11 takes it as hypothesis.

Remaining for Lemma 1.1:
A. Y = scheme-theoretic image of o (Space.schemeTheoreticImageSubfunctor) is D(M)-stable. Needs image compatible with the FLAT map act: G x X -> X; the library's Stacks 082Z(3) (QuasiCompactImageEtaleLocal, schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact') is etale only. It does NOT need a reduced source: it needs o quasi-compact, which holds as X is separated and O affine. Module not in the sparse build.
B. Generic flatness of O -> Y: artinian local step; surjective_of_residue_surjective is the Nakayama input; injectivity comes from the kernel of W -> Y_U being 0.
C. The flat locus in |O| is stable (shear on G x O, descent of flatness along G x Y -> Y); then stable_ideal_top_or_nil gives flat everywhere.
D. IsOpenImmersion.of_flat_of_mono on charts; X' = complement of |Y| minus |O| (openComplementOfClosedSubspace, BlowupIsomorphismOffCentre); X' stable; O -> X' closed.

Point closedness of the lift x' in XP was not needed and not proved: exists_chart_of_etaleAt can be applied to p on X with W -> XP -> X.

## 2026-11-06: Lemma 1.1 done
Lemma11Statement is FALSE as written (M = 0, Spec k(x,y) -> A^2: no stable open makes it closed); it lacks the note's "finite type". Not proved, left in place.
Proved instead: AlgMag.ChartPoint.lemma11 (ChartPointLemma11.lean), with added S affine and o locally of finite presentation; and exists_orbitInput (ChartPointOrbitInput.lean), unconditional replacement of exists_orbitInput_of_lemma11, with the clause u : P -> O, u then j then inclusion = lift of p.
Departures: X' defined directly as a subfunctor; no flatLocusOpenSubspace or openComplementOfClosedSubspace; flat locus replaced by GoodAt on a basic open and the shear; A_y = B_y spreads out by finite type.
Axioms: sorryAx only through the two stubs in REQUIRES_FULL_STACKS.md.
