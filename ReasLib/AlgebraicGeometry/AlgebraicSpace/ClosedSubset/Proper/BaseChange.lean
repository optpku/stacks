module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Base change of proper closed subsets of algebraic spaces

Properness of a closed subset over a base is preserved by inverse image in a
cartesian square of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver

/-- Properness of a closed subset over a base is preserved by inverse image in a
cartesian square of algebraic spaces along a locally-of-finite-type morphism. -/
theorem preimage {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (T : Closeds (Points X)) (hT : ProperOver f T) :
    ProperOver f' (T.preimage (Points.continuous_map g')) :=
  sorry

/-- Properness of a closed subset over a base along a locally-of-finite-type
morphism is preserved by inverse image along the source projection of a chosen
pullback. -/
theorem preimage_pullback {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [HasPullback f g] [LocallyOfFiniteType f]
    (T : Closeds (Points X)) (hT : ProperOver f T) :
    ProperOver (pullback.snd f g)
      (T.preimage (Points.continuous_map (pullback.fst f g))) :=
  preimage (IsPullback.of_hasPullback f g) T hT

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver
