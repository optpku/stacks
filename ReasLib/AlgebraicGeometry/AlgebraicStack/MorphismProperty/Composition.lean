/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleSmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.SmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Composition

/-!
# Composition of local morphism properties of algebraic stacks

If a morphism property of algebraic spaces is smooth local on the
source-and-target and stable under composition, then so is its lift to
morphisms of algebraic stacks. An étale-smooth-local-on-source-and-target
property stable under composition likewise lifts to a composition-stable
property of DM morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace hasSmoothLocalAtSourceAndTarget

/-- If a morphism property `P` of algebraic spaces is smooth local on the
source-and-target and stable under composition, its lift to morphisms of
algebraic stacks is stable under composition. -/
theorem comp {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] [P.IsStableUnderComposition]
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : hasSmoothLocalAtSourceAndTarget P f)
    (hg : hasSmoothLocalAtSourceAndTarget P g) :
    hasSmoothLocalAtSourceAndTarget P (f ≫ g) :=
  sorry

end hasSmoothLocalAtSourceAndTarget

namespace hasEtaleSmoothLocalAtSourceAndTarget

/-- If a morphism property `P` of algebraic spaces is étale-smooth local on the
source-and-target and stable under composition, its lift to DM morphisms of
algebraic stacks is stable under composition. -/
theorem comp {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P] [P.IsStableUnderComposition]
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] {f : X ⟶ Y} {g : Y ⟶ Z} [DM f] [DM g]
    (hf : hasEtaleSmoothLocalAtSourceAndTarget P f)
    (hg : hasEtaleSmoothLocalAtSourceAndTarget P g) :
    hasEtaleSmoothLocalAtSourceAndTarget P (f ≫ g) :=
  sorry

end hasEtaleSmoothLocalAtSourceAndTarget

end AlgebraicGeometry.AlgebraicStack
