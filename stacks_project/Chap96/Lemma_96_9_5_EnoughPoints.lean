module

public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import ReasLib.CategoryTheory.Sites.Point.Enough

/-!
# Enough points of associated sites

A category fibred in groupoids over `(Sch/S)_fppf` inherits enough points
on each associated standard site `𝒳_τ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The associated `τ`-site of a category fibred in groupoids over `(Sch/S)_fppf`
has enough points. -/
instance hasEnoughPoints {S : Scheme.{u}} (X : GroupoidsOver S)
    (τ : StandardTopology) :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (X.associatedTopology τ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
