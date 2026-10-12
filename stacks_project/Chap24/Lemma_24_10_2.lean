/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.ProjectionFormula
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.10.2

The reusable owner is the relative-tensor projection formula for a monoidal adjunction.  In the
localized graded-sheaf application, `L` is extension by zero, `R` is restriction, and the two
curried variables are the localized right module and the ambient bimodule.
-/

open CategoryTheory

/- Lemma 24.10.2 (0FRB): extension by zero commutes with relative tensor against an ambient
bimodule, functorially in both module variables. -/
@[stacks 0FRB] #check @Adjunction.RelativeTensor.natIso

/- The objectwise component is a specified isomorphism of right modules, not merely a
proposition asserting that two independently supplied objects are isomorphic. -/
@[stacks 0FRB "objectwise relative tensor projection formula"]
#check @Adjunction.RelativeTensor.iso

/- Its forward map is induced from the balanced-tensor coequalizer and the projection-formula
isomorphism. -/
#check @Adjunction.RelativeTensor.comparison

/- Its inverse is the adjoint transpose of the map induced by the projection-formula mate. -/
#check @Adjunction.RelativeTensor.inverse

/- The two sides are exposed as reusable curried bifunctors. -/
#check @Adjunction.RelativeTensor.sourceFunctor
#check @Adjunction.RelativeTensor.targetFunctor
