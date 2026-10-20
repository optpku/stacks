module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Semicontinuity.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ConnectedComponents

/-!
# Connected components of fibres of finitely presented morphisms

This module records semicontinuity properties of the number of geometric connected components
of fibres of finitely presented scheme morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace FinitePresentation

/-- For a finite-presentation morphism of schemes, each natural-number level set of the number
of geometric connected components of its fibres is locally constructible. -/
theorem geometricFiberComponentCount_levelSet_isLocallyConstructible {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Scheme.Hom.FinitePresentation f] (n : ℕ) :
    Topology.IsLocallyConstructible {y : Y | f.geometricFiberComponentCount y = n} := sorry

/-- For a flat proper finite-presentation morphism of schemes, the number of geometric connected
components of its fibres is lower semicontinuous on the base. -/
theorem lowerSemicontinuous_geometricFiberComponentCount {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f] :
    LowerSemicontinuous f.geometricFiberComponentCount := sorry

/-- For a flat proper finite-presentation morphism of schemes with geometrically reduced fibres,
the number of geometric connected components of the fibres is locally constant on the base. -/
theorem isLocallyConstant_geometricFiberComponentCount {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f] [GeometricallyReduced f] :
    IsLocallyConstant f.geometricFiberComponentCount := sorry

end FinitePresentation
end AlgebraicGeometry.Scheme.Hom
