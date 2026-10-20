module

import ReasLib.CategoryTheory.MorphismProperty.Triangulated.Calculus
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Lemma 13.5.2 (Stacks 05R3): triangle compatibility and the two
cancellation conditions are exposed through the canonical morphism-property
and calculus-of-fractions owners. -/

@[stacks 05R3]
#check @CategoryTheory.MorphismProperty.Triangulated.isomorphisms_le

@[stacks 05R3]
#check @CategoryTheory.MorphismProperty.Triangulated.hasLeftCalculus

@[stacks 05R3]
#check @CategoryTheory.MorphismProperty.Triangulated.hasRightCalculus
