module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types

/-!
# Formal-space types of completions

Completion along a closed subset produces a formal algebraic space and preserves
local Noetherianity.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The formal completion of an algebraic space along a closed subset is a
formal algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlong X T) :=
  sorry

/-- The formal completion of a locally Noetherian algebraic space along a closed
subset is a locally Noetherian formal algebraic space. -/
instance instIsLocallyNoetherian_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian (completionAlong X T) :=
  sorry

/-- Completing the source of a locally of finite type morphism into a locally
Noetherian algebraic space along the closed preimage of `T` yields a locally
Noetherian formal algebraic space. -/
instance instIsLocallyNoetherian_completionAlong_preimage_locallyOfFiniteType
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} [IsLocallyNoetherian X]
    (f : X' ⟶ X) [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian
      (completionAlong X' (T.preimage (Points.continuous_map f))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
