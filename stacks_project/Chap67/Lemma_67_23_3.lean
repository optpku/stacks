/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange
import StacksCheckRecall

/-!
# Base change of finite-type morphisms of algebraic spaces

The base change of a finite-type morphism of algebraic spaces by any morphism
of algebraic spaces is again of finite type. The same holds for morphisms
locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

/- Lemma 67.23.3. A base change of a finite type morphism is finite type.
The same holds for locally of finite type. -/
@[stacks 03XH] #check
  (AlgebraicGeometry.AlgebraicSpace.finiteType_isStableUnderBaseChange :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.AlgebraicSpace.FiniteType S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_isStableUnderBaseChange :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType S :
        CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
