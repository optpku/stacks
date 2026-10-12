/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteConnected
import StacksCheckRecall

/-!
@stack 018N

# Lemma 14.21.3 compatibility facade

The finite truncated-simplex indexing and pointwise left-Kan-extension API is owned by
`ReasLib.AlgebraicTopology.SimplexCategory.Truncated.{Finite,KanExtension}`.
This module retains the historical Chapter 14 import path and source traceability.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
variable (m : ℕ) (U : SimplicialObject.Truncated C m)

/- Lemma 14.21.3: finite colimits provide the pointwise left Kan extensions defining
the skeleton, and the unit of the skeleton/truncation adjunction is an isomorphism. -/
#check SimplexCategory.Truncated.inclusion.costructuredArrow.finCategory
#check SimplexCategory.Truncated.inclusion.finiteConnected.pointwise.left.kanExtension

#check SimplicialObject.skAdj

@[stacks 018N]
#check (inferInstance : IsIso ((SimplicialObject.skAdj m).unit.app U))

/- The pointwise statement is assembled naturally: the whole adjunction unit is an
isomorphism of natural transformations. -/
#check (inferInstance : IsIso (SimplicialObject.skAdj m).unit)

end CategoryTheory
