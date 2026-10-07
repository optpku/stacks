module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

/-!
# Geometrically irreducible fibre loci

This module defines the locus where the geometric fibres of a scheme morphism
are irreducible and records its invariance under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The locus in the target of a scheme morphism where its fibres are geometrically
irreducible. -/
def geometricallyIrreducibleFiberLocus {X Y : Scheme.{u}} (f : X ⟶ Y) : Set Y :=
  {y | GeometricallyIrreducible (f.fiberToSpecResidueField y)}

/-- Membership in the geometrically irreducible fibre locus is geometric irreducibility of the
corresponding fibre over the residue field. -/
theorem mem_geometricallyIrreducibleFiberLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    y ∈ f.geometricallyIrreducibleFiberLocus ↔
      GeometricallyIrreducible (f.fiberToSpecResidueField y) := sorry

/-- Geometric irreducibility of a fibre is preserved and reflected by a pullback square of
scheme morphisms. -/
theorem geometricallyIrreducibleFiber_iff_of_isPullback {Y X Y' X' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (y' : Y') :
    GeometricallyIrreducible (f'.fiberToSpecResidueField y') ↔
      GeometricallyIrreducible (f.fiberToSpecResidueField (g y')) := sorry

/-- The geometrically irreducible fibre locus of a base-changed scheme morphism is the inverse
image of the original locus. -/
theorem geometricallyIrreducibleFiberLocus_baseChange {Y X Y' X' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) :
    f'.geometricallyIrreducibleFiberLocus =
      g ⁻¹' f.geometricallyIrreducibleFiberLocus := sorry

end AlgebraicGeometry.Scheme.Hom
