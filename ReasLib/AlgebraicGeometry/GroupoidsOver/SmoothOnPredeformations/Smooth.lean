module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnPredeformations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness from the predeformation criterion

Over a locally Noetherian scheme, a representable morphism of groupoid fibrations
that is smooth on predeformations is smooth if its source structure projection is
limit preserving on objects and its target is limit preserving.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of categories fibred in groupoids over a locally Noetherian scheme
that is representable by algebraic spaces and smooth on predeformations is smooth
if its source structure projection is limit preserving on objects and its target
is limit preserving. -/
@[stacks 07XX]
theorem Smooth.of_isSmoothOnPredeformations {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [IsSmoothOnPredeformations f]
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    [LimitPreserving Y] :
    Smooth f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
