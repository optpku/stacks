/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open SheafOfModules.RingedSite

/- Equation 17.31.0.2 (08TI): the canonical conormal map
`I / I ^ 2 ⟶ B ⊗[A[B]] Ω(A[B]/A)` has cokernel `Ω(B/A)`.  ReasLib records this as exactness of
the canonical conormal sequence. -/
@[stacks 08TI]
#check @NaiveCotangent.Presentation.conormalSequence_exact
