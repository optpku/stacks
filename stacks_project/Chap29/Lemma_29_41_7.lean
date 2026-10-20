/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.41.7: if `X ⟶ S` is universally closed in a commutative triangle
`X ⟶ Y ⟶ S` with `Y ⟶ S` separated, then `X ⟶ Y` is universally closed. -/
@[stacks 01W6] #check
  (AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S),
      [AlgebraicGeometry.UniversallyClosed (f ≫ g)] →
        [AlgebraicGeometry.IsSeparated g] → AlgebraicGeometry.UniversallyClosed f)

#check
  (AlgebraicGeometry.IsProper.of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S),
      [AlgebraicGeometry.IsProper (f ≫ g)] →
        [AlgebraicGeometry.IsSeparated g] → AlgebraicGeometry.IsProper f)

section

variable {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

variable [AlgebraicGeometry.UniversallyClosed (f ≫ g)] [AlgebraicGeometry.IsSeparated g]

#check
  ((@AlgebraicGeometry.Scheme.Hom.isClosedMap _ _ f
      (AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated f g)).isClosed_range :
    IsClosed (Set.range f.base))

end

section

variable {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

variable [AlgebraicGeometry.IsProper (f ≫ g)] [AlgebraicGeometry.IsSeparated g]

#check
  ((@AlgebraicGeometry.Scheme.Hom.isClosedMap _ _ f
      (@AlgebraicGeometry.IsProper.toUniversallyClosed _ _ f
        (AlgebraicGeometry.IsProper.of_comp f g))).isClosed_range :
    IsClosed (Set.range f.base))

end
