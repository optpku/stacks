module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Jacobson
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

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

/-- A finite-type point of a Jacobson algebraic space in the image of a locally
of finite type morphism from a scheme has a closed-point preimage. -/
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
      Points.mapOfOver g '' closedPoints W.left := by
  intro x hx
  obtain ⟨w, hw, hgw⟩ := exists_mem_closedPoints_mapOfOver_eq g hx.1 hx.2
  exact ⟨w, hw, hgw⟩

end AlgebraicGeometry.AlgebraicSpace.IsJacobson
