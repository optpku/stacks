module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Principal.Category
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Principal

/-- Each fiber of the principal-homogeneous-space projection is essentially small. -/
instance fibers_essentiallySmall {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((forget G).Fiber U)) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Principal
