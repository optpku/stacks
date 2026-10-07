module

public import stacks_project.Chap100.Lemma_100_10_1_Points
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_38_1_SchemeTheoreticImage

/-!
# Topology of scheme-theoretic images of algebraic stacks

If `f : X ⟶ Y` is a quasi-compact morphism of algebraic stacks and
`ι : Z ⟶ Y` is a scheme-theoretic image of `f`, then `|Z| ⊆ |Y|` is the
closure of the image of `|f|`. There is no chosen image carrier: the
comparison is a statement about a given factorization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage

/-- Factoring through a scheme-theoretic image places the image of `|f|` in the
image of `|ι|` as subsets of `|Y|`. -/
theorem range_subset {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] :
    Set.range (Points.map f) ⊆ Set.range (Points.map ι) :=
  sorry

/-- For a quasi-compact morphism of algebraic stacks, the induced map on points
from the source to a scheme-theoretic image is dense. -/
theorem denseRange_toImage {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) [QuasiCompact f] (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι]
    {τZ : TopologicalSpace (Points Z)} (hZ : IsPointsTopology Z τZ) :
    @Dense (Points Z) τZ (Set.range (Points.map toImage)) :=
  sorry

/-- For a quasi-compact morphism of algebraic stacks, the image of `|ι|` is the
closure of the image of `|f|` in a canonical topology on `|Y|`. -/
theorem closure_range_eq {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) [QuasiCompact f] (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι]
    {τY : TopologicalSpace (Points Y)} (hY : IsPointsTopology Y τY) :
    @closure (Points Y) τY (Set.range (Points.map f)) =
      Set.range (Points.map ι) :=
  sorry

/-- Packaged as a closed substack of `Y`, the scheme-theoretic image of a
quasi-compact morphism has underlying point set equal to the closure of the
image of `|f|`. -/
theorem closure_range_eq_pointsSet {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] (Z : ClosedSubstack Y) (toImage : X ⟶ Z.Y)
    [IsSchemeTheoreticImage f toImage Z.ι]
    {τY : TopologicalSpace (Points Y)} (hY : IsPointsTopology Y τY) :
    @closure (Points Y) τY (Set.range (Points.map f)) = Z.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage
