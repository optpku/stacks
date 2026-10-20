module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving

/-!
# Stacks that are limit preserving on objects but not limit preserving
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids

/-- Over every nonempty scheme, there exists a stack in groupoids for the fppf topology
whose canonical projection is limit preserving on objects, but whose underlying category
fibred in groupoids is not limit preserving. -/
@[stacks 07Z1]
theorem exists_limitPreservingOnObjects_not_limitPreserving
    {S : Scheme.{u}} [Nonempty S] :
    ∃ (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u}
        (Scheme.fppfTopology.over S)),
      LimitPreservingOnObjects
          (baseProjection.{u + 1, u, u + 1} 𝒳.toGroupoids) ∧
        ¬ LimitPreserving 𝒳.toGroupoids := sorry

end AlgebraicGeometry.Groupoids
