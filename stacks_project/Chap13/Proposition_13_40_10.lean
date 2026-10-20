/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Admissible.Localization
import ReasLib.CategoryTheory.Pretriangulated.Admissible.Pair
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Proposition 13.40.10 (Stacks 0H0P): admissible orthogonal pairs are exactly
semiorthogonal decompositions, and each side is canonically compared with the
Verdier quotient by the other side. -/

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Pair.tfae

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Pair.eq_rightOrthogonal

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Pair.eq_leftOrthogonal

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Right.comparison

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Right.kernel_eq

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Right.adjointIsLocalization

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Right.comparisonIsEquivalence

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Right.adjointIso

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Left.comparison

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Left.kernel_eq

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Left.adjointIsLocalization

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Left.comparisonIsEquivalence

@[stacks 0H0P]
#check @CategoryTheory.ObjectProperty.Admissible.Left.adjointIso
