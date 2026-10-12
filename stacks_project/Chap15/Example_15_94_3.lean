/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.PrincipalPresentation
import StacksCheckRecall

/-!
# Example 15.94.3 (09AT)

The principal derived-completeness presentation criterion is owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness.PrincipalPresentation`.

@stack 09AT
-/

@[expose] public section

/- Example 15.94.3 (09AT): derived completeness for a regular principal element is equivalent to
a short exact presentation by complete modules with zero principal torsion. -/
@[stacks 09AT]
#check @ModuleCat.IsDerivedCompleteWithRespectTo.principal_iff_exists_adicCompletePresentation
