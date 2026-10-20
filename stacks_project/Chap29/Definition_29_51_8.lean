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

/- Definition 29.51.8: for a dominant locally finite type morphism `f : X ⟶ Y` of integral
schemes whose induced extension `R(Y) → R(X)` is finite-dimensional, the degree of `X` over
`Y` is the natural-number finrank of that induced extension. -/
@[stacks 02NY] #check
  (fun {X Y : Scheme.{u}} (f : X ⟶ Y)
      [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType f] [IsDominant f]
      (_ : f.FiniteFunctionFieldExtension) ↦ f.inducedFunctionFieldDegree)

/- Finiteness means finite-dimensionality for the function-field algebra induced by the
dominant morphism. -/
#check (AlgebraicGeometry.Scheme.Hom.FiniteFunctionFieldExtension :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f], Prop)

/- The induced degree is the finrank of the induced function-field algebra. -/
#check (AlgebraicGeometry.Scheme.Hom.inducedFunctionFieldDegree_eq_finrank :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f],
    f.inducedFunctionFieldDegree =
      -- Local instance justification (instance diamond): select the algebra induced by `f`
      -- because distinct morphisms can induce competing structures.
      letI : Algebra Y.functionField X.functionField :=
        f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant
      Module.finrank Y.functionField X.functionField)

/- A finite induced function-field extension has positive degree. -/
#check (AlgebraicGeometry.Scheme.Hom.inducedFunctionFieldDegree_pos :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f],
    f.FiniteFunctionFieldExtension → 0 < f.inducedFunctionFieldDegree)
