module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap99.Lemma_99_13_1_Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category

/-!
# The category of families of curves

The category of families of curves over schemes over a base is the full
subcategory of `FpFlatProperGroupoids` on objects whose structure morphism has
relative dimension at most `1`. Morphisms are the inherited cartesian squares,
and the forgetful functor to `Over S` presents the category over `Sch_fppf`.
-/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.p :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    CategoryTheory.Functor (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.Obj S)
      (CategoryTheory.Over S))
