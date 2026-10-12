/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.StrongGenerator
import StacksCheckRecall

/-!
# Proposition 15.80.6 (0FXM)

@stack 0FXM
-/

@[expose] public section

open CategoryTheory

/- Proposition 15.80.6 (0FXM): regular finite-dimensional rings are exactly those whose perfect
derived category has a strong generator, equivalently the canonical generator `R[0]` is strong. -/
@[stacks 0FXM "Proposition 15.80.6"]
#check @regularFiniteKrullDimension_tfae_perfectDerived_hasStrongGenerator_ringSingleStrongGenerator

#check @PerfectDerived
#check @ringSingleInPerfectDerived
