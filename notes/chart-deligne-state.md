# Lemma 4.3 / StrataOverChart: state

PROVED: AlgMag.ChartMain.DeligneInst.strataOverChart_proved (AlgMag/ChartDeligneInst.lean).
#print axioms: propext, Classical.choice, Quot.sound. Compiled with scratchpad st/sc.sh (stub tree on LEAN_PATH), not yet by lake build.
Added hypotheses: S affine; X separated over S; Gamma(V) noetherian for each affine etale V -> X.

Route: elementwise, no sheaf psi, no module descent, no 07UM.
- ChartDeligneCore: Ctx, Gam, Graph, exists_cross (torsion exponent on V x_X V and V[M] x_X V), exists_pole, Lift, lift_exists (exp = 2 E0, descent of q(c) t'), lift_unique, lift_smul, lift_formula.
- ChartDeligneLim: exists_ideal, LL, exists_LL_homog.
- ChartDeligneOpen: Lam, exists_y0, tau_x, tau_equiv.
- ChartDeligneCompat: chi_univ, le_idl_chi, le_idl_theta (Nakayama).
- ChartDeligneTheta: cmp_k, cmp_Y, tau_theta.
- ChartDeligneInst: exists_chartOf, idlP, hfac_aux, final theorem.
DeligneCalc (ChartDeligne.lean) has no instance: its `ideal` is total on all W with ideal_map exact, impossible for non-affine W. Ctx replaces it; homog_of_lift copied as homog_lift.
Not used: J_V = imgI comparison.
