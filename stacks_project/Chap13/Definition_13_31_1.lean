/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.KInjective.Characterization
import StacksCheckRecall

@[expose] public section

/- Definition 13.31.1: the textbook notion is Mathlib's canonical
`CochainComplex.IsKInjective`: every cochain map from an acyclic complex is null-homotopic. -/
@[stacks 070H] #check CochainComplex.IsKInjective

/- Definition 13.31.1: equivalently, every morphism from an acyclic complex to the given complex
is zero in the homotopy category. -/
#check @CochainComplex.IsKInjective.iff_homotopy_zero
