module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.Point

/-!
# Generic multiplicities of algebraic spaces
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The multiplicity of a generic point is the finite étale-stalk length of `𝒪_Y` at any
geometric point over that generic point. -/
noncomputable def genericMultiplicity {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (η : genericPoints Y) : ℕ :=
  (Modules.lengthAt (SheafOfModules.unit (structureSheaf Y) : Y.Modules) η.1).toNat

/-- The generic-point multiplicity recovers the étale-stalk length of `𝒪_Y` at any
geometric point over the generic point. -/
theorem genericMultiplicity_eq_length {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (η : genericPoints Y)
    (xbar : GeometricPoint Y) (hx : xbar.liesOver η.1) :
    (genericMultiplicity η : ℕ∞) =
      Modules.lengthAtGeometricPoint
        (SheafOfModules.unit (structureSheaf Y) : Y.Modules) xbar :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
