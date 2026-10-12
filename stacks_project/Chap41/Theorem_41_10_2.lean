/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyOpen.Noetherian
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Theorem 41.10.2: A flat morphism locally of finite type over a locally Noetherian
scheme is universally open. -/
@[stacks 039K] #check
  (AlgebraicGeometry.UniversallyOpen.of_flat_of_locallyOfFiniteType :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [Flat f]
      [LocallyOfFiniteType f], UniversallyOpen f)
