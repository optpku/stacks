module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfBase
import StacksCheckRecall

/-!
# Change-of-base constructions for algebraic stacks

This source-facing module checks the promoted change-of-base constructions.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStacks

#check (AlgebraicStack.viewedOver : ∀ {S S' : Scheme.{u}}, (S ⟶ S') → GroupoidsOver S → GroupoidsOver S')
#check (toOverSlice : ∀ {S S' : Scheme.{u}}, ∀ (g : S ⟶ S'), StrictPseudofunctor (AlgebraicStacks S) (OverSlice g))
#check (ofOverSlice : ∀ {S S' : Scheme.{u}}, ∀ (g : S ⟶ S'), StrictPseudofunctor (OverSlice g) (AlgebraicStacks S))

end AlgebraicGeometry.AlgebraicStacks
