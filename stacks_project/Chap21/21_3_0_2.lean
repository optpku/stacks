/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-
21.3.0.2 (05U6): the degree-`i` right derived functor is the degree-`i` homology of a
bounded-below total right-derived functor.  The reusable owner is
`Functor.RightDerived.degree`; its ordinary injective-resolution view is supplied by
`Functor.RightDerived.Bounded.degree.isIsomorphic_rightDerived`.
-/
@[stacks 05U6 "degreewise right-derived functor"] #check
  @Functor.RightDerived.degree

#check @Functor.rightDerivedFunctorPlus
#check @Functor.rightDerivedFunctorPlusUnit

@[stacks 05U6 "ordinary right-derived comparison"] #check
  @Functor.RightDerived.Bounded.degree.isIsomorphic_rightDerived

#check @Functor.rightDerived
#check @Functor.rightDerivedNatIso
#check @Functor.rightDerivedUnique

end
