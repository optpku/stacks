/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine
import StacksCheckRecall

/-!
# Composition of affine morphisms of algebraic stacks

The composition of a pair of affine morphisms of algebraic stacks is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.9.3: compositions of affine morphisms of algebraic stacks are
affine. -/
@[stacks 0CHS] #check
  (AlgebraicGeometry.Groupoids.Hom.Affine.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      (f : X ⟶ Y) (g : Y ⟶ Z) [Groupoids.Hom.Affine f] [Groupoids.Hom.Affine g],
      Groupoids.Hom.Affine (f ≫ g))

#check
  (AlgebraicGeometry.Groupoids.Hom.Affine.instIsStableUnderComposition :
    ∀ {S : Scheme.{u}},
    MorphismProperty.IsStableUnderComposition
      (@Groupoids.Hom.Affine S : MorphismProperty (GroupoidsOver S)))
