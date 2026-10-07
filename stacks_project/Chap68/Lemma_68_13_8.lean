module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_25_4_Regular
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Reduced locally Noetherian singleton algebraic spaces are regular

A reduced, locally Noetherian algebraic space whose space of points is a
singleton is regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsRegular

/-- Lemma 68.13.8: A reduced, locally Noetherian algebraic space `Z` whose space of
points is a singleton is regular. -/
@[stacks 06R1]
instance of_singleton_points {S : Scheme.{u}} (Z : AlgebraicSpace S)
    [IsReduced Z] [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    IsRegular Z := sorry

end IsRegular

end AlgebraicGeometry.AlgebraicSpace
