module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Algebraic stacks from étale descent

An étale stack in groupoids with diagonal representable by algebraic spaces
and a smooth surjective scheme atlas is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An étale stack in groupoids over a scheme, whose diagonal is representable
by algebraic spaces and which admits a smooth surjective scheme atlas, is an
algebraic stack for the fppf topology. -/
theorem of_etale_smooth_surjective {S : Scheme.{u}} {X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.etaleTopology.over S) X.p]
    (hΔ : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    {U : Over S} (u : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth u] [Groupoids.Hom.Surjective u] :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
