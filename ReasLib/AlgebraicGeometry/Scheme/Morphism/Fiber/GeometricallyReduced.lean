module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

/-!
# Geometrically reduced fibre loci

This module defines the locus where the geometric fibres of a scheme morphism
are reduced and records its invariance under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The locus in the target of a scheme morphism where its fibres are geometrically
reduced. -/
def geometricallyReducedFiberLocus {X Y : Scheme.{u}} (f : X ⟶ Y) : Set Y :=
  {y | GeometricallyReduced (f.fiberToSpecResidueField y)}

/-- Membership in the geometrically reduced fibre locus is geometric reducedness of the
corresponding fibre over the residue field. -/
theorem mem_geometricallyReducedFiberLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    y ∈ f.geometricallyReducedFiberLocus ↔
      GeometricallyReduced (f.fiberToSpecResidueField y) := sorry

/-- Geometric reducedness of a fibre is preserved and reflected by a pullback square of
scheme morphisms. -/
theorem geometricallyReducedFiber_iff_of_isPullback {Y X Y' X' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (y' : Y') :
    GeometricallyReduced (f'.fiberToSpecResidueField y') ↔
      GeometricallyReduced (f.fiberToSpecResidueField (g y')) := sorry

/-- The geometrically reduced fibre locus of a base-changed scheme morphism is the inverse
image of the original locus. -/
theorem geometricallyReducedFiberLocus_baseChange {Y X Y' X' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) :
    f'.geometricallyReducedFiberLocus = g ⁻¹' f.geometricallyReducedFiberLocus := sorry

end AlgebraicGeometry.Scheme.Hom
