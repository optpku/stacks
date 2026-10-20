/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.51.9: for integral schemes and dominant locally finite type morphisms with finite
induced function-field extensions, the degree of the composite is the product of the degrees. -/
@[stacks 02NZ] #check
  (AlgebraicGeometry.Scheme.Hom.inducedFunctionFieldDegree_comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
      [LocallyOfFiniteType f] [LocallyOfFiniteType g]
      [IsDominant f] [IsDominant g],
      f.FiniteFunctionFieldExtension → g.FiniteFunctionFieldExtension →
        (f ≫ g).inducedFunctionFieldDegree =
          f.inducedFunctionFieldDegree * g.inducedFunctionFieldDegree)
