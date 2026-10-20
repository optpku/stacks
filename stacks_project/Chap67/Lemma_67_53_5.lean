/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
import StacksCheckRecall

/-!
# Composition of universal homeomorphisms of algebraic spaces

The composition of a pair of universal homeomorphisms of algebraic spaces is a
universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.53.5: The composition of a pair of universal homeomorphisms of algebraic
spaces is a universal homeomorphism. -/
@[stacks 0CFU]
#check (AlgebraicGeometry.AlgebraicSpace.universalHomeomorphism_isStableUnderComposition :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
    (@UniversalHomeomorphism S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.universalHomeomorphism_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversalHomeomorphism f] [UniversalHomeomorphism g],
    UniversalHomeomorphism (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
