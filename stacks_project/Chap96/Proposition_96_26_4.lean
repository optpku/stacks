/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap96.Proposition_96_26_4_Comparison

/-!
# Quasi-coherent derived objects on a representable category fibred in groupoids
-/

@[expose] public section

universe u

/- Proposition 96.26.4: let `S` be a scheme and let `𝒳 → (Sch/S)_fppf` be a
category fibred in groupoids representable by an algebraic space `X`. Then
`QC(𝒳)` is canonically equivalent to `D_QCoh(𝒪_X)`. -/
@[stacks 0H0K]
#check AlgebraicGeometry.GroupoidsOver.qcEquivalence
