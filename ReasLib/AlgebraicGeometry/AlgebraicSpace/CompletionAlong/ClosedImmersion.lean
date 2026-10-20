module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion

/-!
# Closed immersions of completions

If a morphism of algebraic spaces is a closed immersion, then the induced
morphism of formal completions along a closed subset is a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A closed immersion `f : X' ⟶ X` induces a closed immersion
`completionAlong.map f T` from the completion along the inverse image of a
closed subset `T` of `Points X` to the completion along `T`. -/
instance closedImmersion_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.IsClosedImmersion f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.ClosedImmersion (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
