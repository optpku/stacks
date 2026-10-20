/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion

/-!
# Composition of the valuative criterion for morphisms of algebraic spaces

The existence part and the uniqueness part of the valuative criterion are each
stable under composition of morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Morphisms of algebraic spaces satisfying the existence part of the valuative
criterion are stable under composition. -/
instance valuativeCriterionExistence_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@ValuativeCriterion.Existence S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of morphisms of algebraic spaces satisfying the existence
part of the valuative criterion satisfies the existence part. -/
instance valuativeCriterionExistence_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [ValuativeCriterion.Existence f] [ValuativeCriterion.Existence g] :
    ValuativeCriterion.Existence (f ≫ g) :=
  MorphismProperty.comp_mem (@ValuativeCriterion.Existence S) f g inferInstance inferInstance

/-- Morphisms of algebraic spaces satisfying the uniqueness part of the valuative
criterion are stable under composition. -/
instance valuativeCriterionUniqueness_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@ValuativeCriterion.Uniqueness S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of morphisms of algebraic spaces satisfying the uniqueness
part of the valuative criterion satisfies the uniqueness part. -/
instance valuativeCriterionUniqueness_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [ValuativeCriterion.Uniqueness f] [ValuativeCriterion.Uniqueness g] :
    ValuativeCriterion.Uniqueness (f ≫ g) :=
  MorphismProperty.comp_mem (@ValuativeCriterion.Uniqueness S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
