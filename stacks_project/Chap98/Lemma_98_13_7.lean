module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnPredeformations.Smooth
import StacksCheckRecall

/-!
# Smoothness from the predeformation criterion

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces, satisfies (98.13.2.1), is limit preserving
on objects over `(Sch/S)_fppf`, and has a limit-preserving target, is smooth
when `S` is locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 98.13.7: if `S` is locally Noetherian and `f : X ⟶ Y` is a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces, satisfies (98.13.2.1), has
`X ⟶ (Sch/S)_fppf` limit preserving on objects, and has `Y` limit
preserving, then `f` is smooth. -/
@[stacks 07XX] #check
  (AlgebraicGeometry.Groupoids.Hom.Smooth.of_isSmoothOnPredeformations :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [IsSmoothOnPredeformations f]
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    [LimitPreserving Y],
    Smooth f)

end AlgebraicGeometry.Groupoids.Hom
