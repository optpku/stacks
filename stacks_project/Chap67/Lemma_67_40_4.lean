/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.Composition
import StacksCheckRecall

/-!
# Composition of proper morphisms of algebraic spaces

The composition of a pair of proper morphisms of algebraic spaces is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.40.4: A composition of proper morphisms of algebraic spaces is
proper. -/
@[stacks 04XY] #check
  (AlgebraicGeometry.AlgebraicSpace.proper_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@Proper S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.proper_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Proper f] [Proper g], Proper (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
