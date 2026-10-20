/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Composition
import StacksCheckRecall

/-!
# Composition of integral and finite morphisms of algebraic spaces

The composition of integral morphisms of algebraic spaces is integral, and the
composition of finite morphisms of algebraic spaces is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.45.4 (1) -/
@[stacks 03ZR] #check
  (AlgebraicGeometry.AlgebraicSpace.isIntegralHom_isStableUnderComposition :
    ∀ {S : Scheme.{u}},
      MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.AlgebraicSpace.IsIntegralHom S :
          MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.isIntegralHom_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicSpace.IsIntegralHom f]
    [AlgebraicGeometry.AlgebraicSpace.IsIntegralHom g],
    AlgebraicGeometry.AlgebraicSpace.IsIntegralHom (f ≫ g))

/- Lemma 67.45.4 (2) -/
@[stacks 03ZR] #check
  (AlgebraicGeometry.AlgebraicSpace.isFinite_isStableUnderComposition :
    ∀ {S : Scheme.{u}},
      MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.AlgebraicSpace.IsFinite S :
          MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.isFinite_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicSpace.IsFinite f]
    [AlgebraicGeometry.AlgebraicSpace.IsFinite g],
    AlgebraicGeometry.AlgebraicSpace.IsFinite (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
