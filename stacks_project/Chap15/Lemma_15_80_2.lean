/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.StrongGenerator
import StacksCheckRecall

/-!
# Lemma 15.80.2 (0FXI)

@stack 0FXI
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.80.2 (0FXI): strong generation by `R[0]` forces regularity and finite Krull
dimension. -/
@[stacks 0FXI "Lemma 15.80.2"]
#check @regularFiniteKrullDimension_of_ringSingleInPerfectDerived_isStrongGenerator
