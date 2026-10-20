module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Proper

/-!
# Proper morphisms of completions

If a morphism of algebraic spaces is proper, then the induced morphism of
formal completions along a closed subset is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper morphism `f : X' ⟶ X` induces a proper morphism
`completionAlong.map f T` from the completion along the inverse image of a
closed subset `T` of `Points X` to the completion along `T`. -/
instance proper_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.Proper f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.Proper (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
