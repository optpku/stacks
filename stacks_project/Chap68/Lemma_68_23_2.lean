module

public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint
public import stacks_project.Chap68.Lemma_68_23_1_Jacobson

/-!
# Finite-type points lift to closed points over Jacobson algebraic spaces

A finite-type point of a Jacobson algebraic space that lies in the image of a
locally of finite type morphism from a scheme is the image of a closed point of
that scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsJacobson

/-- Lemma 68.23.2: Let `S` be a scheme. Let `X` be a Jacobson algebraic space over
`S`. For `x ∈ finiteTypePoints X` and `g : ofOver W ⟶ X` locally of finite type
with `W` a scheme, if `x ∈ Set.range (Points.mapOfOver g)`, then there exists a
closed point of `W` mapping to `x`. -/
@[stacks 0BA4]
theorem exists_mem_closedPoints_mapOfOver_eq {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsJacobson X] {W : Over S} (g : ofOver W ⟶ X)
    [LocallyOfFiniteType g] {x : Points X} (hx : x ∈ finiteTypePoints X)
    (hgx : x ∈ Set.range (Points.mapOfOver g)) :
    ∃ w ∈ closedPoints W.left, Points.mapOfOver g w = x :=
  sorry

/-- Finite-type points of a Jacobson algebraic space that lie in the image of a
locally of finite type morphism from a scheme are images of closed points of
that scheme. -/
theorem finiteTypePoints_inter_range_subset_image_closedPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsJacobson X] {W : Over S}
    (g : ofOver W ⟶ X) [LocallyOfFiniteType g] :
    finiteTypePoints X ∩ Set.range (Points.mapOfOver g) ⊆
      Points.mapOfOver g '' closedPoints W.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsJacobson
