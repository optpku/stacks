/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion.Composition
import StacksCheckRecall

/-!
# Composition of immersions of algebraic stacks

A composition of immersions, closed immersions, or open immersions of algebraic
stacks is again an immersion, closed immersion, or open immersion respectively.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 100.9.3 (1): compositions of immersions of algebraic stacks are
immersions. -/
@[stacks 0502] #check (AlgebraicGeometry.Groupoids.Hom.Immersion.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [Immersion f] [Immersion g], Immersion (f ≫ g))

/- Lemma 100.9.3 (2): compositions of closed immersions of algebraic stacks are
closed immersions. -/
@[stacks 0502] #check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [ClosedImmersion f] [ClosedImmersion g],
    ClosedImmersion (f ≫ g))

/- Lemma 100.9.3 (3): compositions of open immersions of algebraic stacks are
open immersions. -/
@[stacks 0502] #check (AlgebraicGeometry.Groupoids.Hom.OpenImmersion.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [OpenImmersion f] [OpenImmersion g],
    OpenImmersion (f ≫ g))

#check (AlgebraicGeometry.Groupoids.Hom.isImmersion_isStableUnderComposition :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@Immersion S : MorphismProperty (GroupoidsOver S)))

#check (AlgebraicGeometry.Groupoids.Hom.isClosedImmersion_isStableUnderComposition :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@ClosedImmersion S : MorphismProperty (GroupoidsOver S)))

#check (AlgebraicGeometry.Groupoids.Hom.isOpenImmersion_isStableUnderComposition :
  ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@OpenImmersion S : MorphismProperty (GroupoidsOver S)))

end AlgebraicGeometry.Groupoids.Hom
