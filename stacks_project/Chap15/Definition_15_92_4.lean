/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
import StacksCheckRecall

/-!
# Definition 15.92.4 compatibility entry point

The reusable derived-completeness predicates for module derived categories are owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness`.

@stack 091S
-/

@[expose] public section

/- Definition 15.92.4 (1), tag `091S`: derived-complete complexes. -/
@[stacks 091S "(1), derived-complete complex"]
#check @DerivedCategory.IsDerivedCompleteWithRespectTo

/- Definition 15.92.4 (2), tag `091S`: derived-complete modules. -/
@[stacks 091S "(2), derived-complete module"]
#check @ModuleCat.IsDerivedCompleteWithRespectTo
