/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree.Criteria
import StacksCheckRecall

/-!
# Criteria for finite locally free modules

@stack 00NX
-/

@[expose] public section

@[stacks 00NX "source eight-clause form"]
#check @Module.FiniteLocallyFree.tfae

@[stacks 00NX "finite-presentation and flatness criterion"]
#check @Module.FiniteLocallyFree.iff_finitePresentation_and_flat

@[stacks 00NX "finite-projective criterion"]
#check @Module.FiniteLocallyFree.iff_finiteProjective

@[stacks 00NX "finite-presentation and flatness constructor"]
#check @Module.FiniteLocallyFree.of_finitePresentation_of_flat

@[stacks 00NX "free-locus and rank criterion"]
#check @Module.FiniteLocallyFree.of_freeLocus_eq_univ_of_isLocallyConstant_rankAtStalk
