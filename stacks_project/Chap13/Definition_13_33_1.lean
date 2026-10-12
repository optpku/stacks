/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.33.1

The neutral telescope map is owned by `Limits.Sequential`; the
pretriangulated construction is the intrinsic predicate
`HomotopyColimit.IsOf`.
-/

@[stacks 090Z] #check @CategoryTheory.Limits.Sequential.CoproductCocone.telescopeMap

@[stacks 090Z] #check @CategoryTheory.HomotopyColimit.IsOf

#check @CategoryTheory.Limits.Sequential.CoproductCocone.inclusion_comp_telescopeMap
#check @CategoryTheory.Limits.Sequential.CoproductCocone.telescopeMap_naturality
