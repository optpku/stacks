module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving

/-!
# Limit preservation and the structure morphism

A category fibred in groupoids over a scheme is limit preserving if and only
if its structure morphism is limit preserving.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.LimitPreserving

/-- A category fibred in groupoids over `(Sch/S)_fppf` is limit preserving if and
only if its structure morphism to `(Sch/S)_fppf` is limit preserving. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S) :
    LimitPreserving X ↔
      Hom.LimitPreserving (baseProjection.{u + 1, u, u + 1} X) := sorry

end AlgebraicGeometry.Groupoids.LimitPreserving
