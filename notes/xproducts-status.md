# X-products note (Semigroup Forum, doi 10.1007/s00233-026-10695-7): formalization status

Files: AlgMag/XProducts{Glue,Action,Thm,Rep,Example,ExampleCoord,ExampleClass,F1,F1Glue,F1Base}.lean, all compiled, no sorry, axioms clean.
Compile: scratchpad xp/c.sh Module (xp/out holds hard links to .lake/build oleans).

Done: Def 2.1-2.3, Prop 3.1, 3.2, 3.3, Thm 4.1, Def 4.2, Prop 4.3 (1), (2), moreover, Prop 4.5.
Example 4.4: family, action formula, the points z -> az and 0, infinity, distinctness, failure of X^N = X^{cap N}, and over a connected base the classification of X^N, of X^{+N} = (P1 - infinity) + {infinity}, and X^0 = {0, infinity}. P1 is taken to be the glued scheme; no comparison with Mathlib's Proj; no decomposition statement over disconnected T.

Remarks for the report: conditions 1, 2 of Thm 4.1 and (a), (b) of Prop 4.3 are not needed (X^Z is the fixed point subfunctor, Prop 3.35); A finite is not needed in Prop 4.5; A nonempty is implicit in the printed text; Prop 3.3 is stated for schemes while the proof of Thm 4.1 applies it to algebraic spaces after base change (handled by existsUnique_glue).
