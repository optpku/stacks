module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver

/-!
# Inverse images of closed subsets proper over a base

Properness of a closed subset of an algebraic space over a base is preserved by
topological inverse image along a cartesian square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

/-- Properness of a closed subset over a base is preserved by inverse image in a
cartesian square of algebraic spaces. -/
theorem IsProperOver.preimage {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (T : Closeds (Points X)) [IsProperOver f T] :
    IsProperOver f' (T.preimage (Points.continuous_map g')) :=
  sorry

/-- Properness of a closed subset over a base is preserved by inverse image along
the source projection of a chosen pullback. -/
theorem IsProperOver.preimage_pullback {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType f]
    (T : Closeds (Points X)) [IsProperOver f T] :
    IsProperOver (pullback.snd f g)
      (T.preimage (Points.continuous_map (pullback.fst f g))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
