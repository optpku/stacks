/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect
import StacksCheckRecall

@[expose] public section

/- Definition 21.44.1 (08FL): a strictly perfect complex is bounded and each
term is a retract of a finite free module sheaf. -/
@[stacks 08FL] #check @RingedSite.CochainComplex.strictlyPerfect
#check @RingedSite.CochainComplex.isStrictlyPerfect_iff
#check @RingedSite.CochainComplex.IsStrictlyPerfect.term_retract_free
