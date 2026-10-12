/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

section Source

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]

/- Lemma 26.21.1: the diagonal of a morphism between affine schemes is a closed immersion.
The two affine hypotheses retain the source formulation. -/
@[stacks 01KI] #check
  (IsSeparated.isClosedImmersion_diagonal : IsClosedImmersion (pullback.diagonal f))

end Source

section Generalization

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X]

/- The canonical instance only needs the source to be affine: an affine scheme is absolutely
separated, and separatedness of its terminal morphism implies separatedness of every morphism
with that source. This does not assert that an arbitrary morphism from an affine scheme is affine. -/
#check (IsSeparated.isClosedImmersion_diagonal : IsClosedImmersion (pullback.diagonal f))

end Generalization

end AlgebraicGeometry
