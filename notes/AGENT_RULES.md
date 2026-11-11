# Rules for agents formalizing "Algebraic Magnetism" (Mayeux)

Paper text: C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad\am\am.txt (am.pdf alongside). Status: STATUS.md (partly stale; grep AlgMag/ before writing anything). Chart proof: notes\ahr-specialized-proof.md.

- Follow printed statements and proofs; depart only at a wrong step, minimally, and report it. Reductive material is excluded.
- No sorry, axiom, native_decide. A hypothesis must be in the paper's statement, or be reported as added. Docstrings name the numbered statement.
- Magnet language, no cocharacters.
- Create only your own files. Do not edit existing files, except appending your import at the end of AlgMag.lean once compiled.
- Clash check: grep your top-level names in AlgMag/ first.
- A background lake build holds the lock. Never run lake build/update/exe cache or setup.sh, never compile Mathlib.
- Compile with `lean -o` into a new directory under C:\Users\Arnaud\AppData\Local\Temp\claude\C--Users-Arnaud\b7814f6f-6cc1-4071-93de-731ed0478fb7\scratchpad, absolute paths, toolchain v4.34.0-rc2, options autoImplicit=false, maxSynthPendingDepth=3, LEAN_NUM_THREADS=1. Reuse oleans in .lake/build and existing scratchpad dirs on LEAN_PATH (sq\out, sw\ol, sm\out, s10\out, s12\out, lim049). Retry spurious "failed to read file" / "no such file" errors.
- Disk is tight: never copy large directories; stop and report if `df` shows under 3 GB free on C:. No stray files in the repo root.
- If a Stacks module is missing from the sparse checkout, read it with `git -C .lake/packages/Stacks show HEAD:<path>`, and report the module to add.
- Fetch any source needed into a new empty scratchpad directory. Do not reinvent what the literature has; cite exact results you read.
- Size is no reason to stop. Save compiled progress as you go.
- Final report, concise: statement, Lean name file:line, `#print axioms`, added assumptions, suspected paper errors with quotes, exact blockers.
- Find library results by citation first: `git -C .lake/packages/Stacks grep -n "@\[stacks TAG"` (also `@[ega "..."]`, `@[sga "..."]`, `add_to_stacks`). Stacks claims every formalizable tag is formalized, so assume a cited tag exists and search the whole git tree, not the sparse checkout.
- Sources: always the published journal version, never arXiv, unless none exists; say which you used.
