module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import ReasLib.CategoryTheory.GradedObject.Preadditive

/-!
# Homology in categories of graded objects

This file isolates the compatibility bridge between the pointwise zero-morphism instance on
graded objects and the canonical homology package of an abelian category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.GradedObject

variable {β : Type w} {C : Type u} [Category.{v} C]

/-- The canonical homology package is available for graded objects in an abelian category,
independently of the selected zero-morphism instance.

The zero-morphism structures on a graded preadditive category are propositionally equal but not
definitionally equal. Quantifying over the selected structure lets the package be used both by
pointwise APIs and by homotopy APIs, whose types use the preadditive zero morphisms. -/
@[stacks 05RZ "graded-object homology package"]
noncomputable instance categoryWithHomology [Abelian C]
    [hzero : HasZeroMorphisms (GradedObject β C)] :
    @CategoryWithHomology (GradedObject β C) _ hzero := sorry

end CategoryTheory.GradedObject
