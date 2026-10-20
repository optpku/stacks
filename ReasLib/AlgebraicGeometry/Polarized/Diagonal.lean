module

public import ReasLib.AlgebraicGeometry.Polarized.Groupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Polarized

/-- The canonical diagonal of the category of polarized proper schemes is
representable by algebraic spaces. -/
@[stacks 0D42]
theorem relativelyRepresentableByAlgebraicSpaces_diagonal :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

/-- The canonical diagonal of the category of polarized proper schemes is
separated as a morphism representable by algebraic spaces. -/
@[stacks 0DPT]
theorem has_separated_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.Separated specZ)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

/-- The canonical diagonal of the category of polarized proper schemes is
of finite presentation as a morphism representable by algebraic spaces. -/
@[stacks 0DPT]
theorem has_finitePresentation_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.FinitePresentation specZ)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

end AlgebraicGeometry.Polarized
