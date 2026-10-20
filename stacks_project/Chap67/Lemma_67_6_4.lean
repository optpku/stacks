/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.Composition
import StacksCheckRecall

/-!
# Composition of open morphisms of algebraic spaces

The composition of a pair of open morphisms of algebraic spaces is open, and
the composition of a pair of universally open morphisms of algebraic spaces is
universally open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.6.4 (1): The composition of a pair of open morphisms of algebraic spaces
is open. -/
@[stacks 03Z4] #check
  (AlgebraicGeometry.AlgebraicSpace.open_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.Open S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.open_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.AlgebraicSpace.Open f]
    [AlgebraicGeometry.AlgebraicSpace.Open g],
    AlgebraicGeometry.AlgebraicSpace.Open (f ≫ g))

/- Lemma 67.6.4 (2): The composition of a pair of universally open morphisms of
algebraic spaces is universally open. -/
@[stacks 03Z4] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyOpen_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.UniversallyOpen S :
        MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.universallyOpen_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.AlgebraicSpace.UniversallyOpen f]
    [AlgebraicGeometry.AlgebraicSpace.UniversallyOpen g],
    AlgebraicGeometry.AlgebraicSpace.UniversallyOpen (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
