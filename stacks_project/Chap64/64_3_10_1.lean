/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

/-!
# 64.3.10.1 (03SX): the second preliminary trace display

Source: `trace-equation-trace-formula-second`,
`source/stacks-official-a04446e57ec1/tex/trace.tex`, lines 283–311.

The source defines the geometric Frobenius π_x on the stalk at a rational point
as the action of frob_k⁻¹. For a finite type dimension-one scheme X over a finite
field k and a constructible flat Z/ℓⁿZ-sheaf F, it then writes

  ∑ x ∈ X(k), Tr(π_x | F_x̄) = ∑ i = 0,…,2, (-1)^i Tr(π_X* | H_c^i(X_k̄,F)).

It explicitly calls this a more precise statement “albeit a false one” and says
the right-hand traces do not make sense for the stated sheaves. The preceding
03SK display and this display are explanatory preliminaries; neither is a
universally asserted equality or a proposition constantly equal to False.
The later construction uses traces on perfect derived cohomology complexes.

This companion preserves that source distinction without recalling the invalid
`lefschetzTraceFormula` declaration. It introduces no mathematical declaration.
-/
