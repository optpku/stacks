/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

/-!
# Evaluation of field-valued points in the residue fibre
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Evaluating a field-valued morphism on the identity slice object lies over
the structure morphism of its source field. -/
theorem fiberObj_over (x0 : FieldValuedPoint X) :
    X.p.obj ((toFunctor x0.hom).obj (Over.mk (𝟙 (Over.mk x0.structureHom)))) =
      Over.mk x0.structureHom :=
  sorry

/-- The object in the residue fibre obtained by evaluating a field-valued morphism
on the identity slice object. -/
def fiberObj (x0 : FieldValuedPoint X) :
    X.p.Fiber (Over.mk x0.structureHom) :=
  Fiber.mk (fiberObj_over x0)

/-- The residue fibre object is the evaluation on the identity slice object,
and its projection is the structure morphism of the source field. -/
theorem fiberObj_spec (x0 : FieldValuedPoint X) :
    Fiber.fiberInclusion.obj x0.fiberObj =
        (toFunctor x0.hom).obj (Over.mk (𝟙 (Over.mk x0.structureHom))) ∧
      X.p.obj ((toFunctor x0.hom).obj
          (Over.mk (𝟙 (Over.mk x0.structureHom)))) =
        Over.mk x0.structureHom :=
  sorry

end AlgebraicGeometry.AlgebraicStack.FieldValuedPoint
