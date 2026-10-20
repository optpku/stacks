module

public import Mathlib.Topology.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact

/-!
# Topology of scheme-theoretic images of algebraic stacks

The underlying point set of a scheme-theoretic image of a quasi-compact
morphism is the closure of the image on points in the canonical topology.
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
from the source to a scheme-theoretic image has dense range. -/
theorem denseRange_toImage {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) [QuasiCompact f] (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] :
    DenseRange (Points.map toImage) :=
  sorry

/-- For a quasi-compact morphism of algebraic stacks, the image of `|ι|` is the
closure of the image of `|f|` in the canonical topology on `|Y|`. -/
theorem closure_range_eq {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) [QuasiCompact f] (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] :
    closure (Set.range (Points.map f)) = Set.range (Points.map ι) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage
