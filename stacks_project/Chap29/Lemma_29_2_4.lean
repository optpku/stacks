module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic owner check:
mathlib already owns the canonical base-change stability theorem for scheme closed immersions,
so this Chapter 29 item is a pure source-facing reference to that owner. -/

/- Lemma 29.2.4: the base change of a closed immersion is a closed immersion. -/
@[stacks 01QR]
#check (AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange :
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange
    @AlgebraicGeometry.IsClosedImmersion)

end AlgebraicGeometry
