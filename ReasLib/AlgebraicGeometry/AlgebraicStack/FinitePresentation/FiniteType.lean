/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType

/-!
# Finite presentation morphisms of algebraic stacks are of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks which is locally of finite presentation is
locally of finite type. -/
instance locallyOfFiniteType_of_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    LocallyOfFiniteType f :=
  sorry

/-- A morphism of algebraic stacks of finite presentation is of finite type. -/
instance finiteType_of_finitePresentation {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [FinitePresentation f] :
    FiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
