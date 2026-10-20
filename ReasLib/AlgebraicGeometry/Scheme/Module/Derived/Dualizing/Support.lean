module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.MaximalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualizingModule

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace RingedSpace.ModuleDerived.IsDualizingModule

/-- A dualizing module is coherent by definition. -/
theorem coherent_of
    {X : Scheme.{u}} (K : RingedSpace.ModuleDerived X.toRingedSpace)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)) (n : ℤ) (M : X.Modules)
    (hω : IsDualizingModule K H n M) : M.IsCoherent := hω.coherent

/-- The support of a dualizing module on a connected Noetherian scheme is the union of the
irreducible components of maximal dimension for any dimension function. -/
theorem support_eq_maximalDimensionComponentSupport
    {X : Scheme.{u}} [IsNoetherian X] [ConnectedSpace X]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) (ωX : X.Modules)
    (hω : IsDualizingModule K H n ωX)
    (δ : X → ℤ) [IsDimensionFunction δ] :
    RingedSpace.moduleSupport ωX = Scheme.maximalDimensionComponentSupport X δ := sorry

/-- A dualizing module on a connected Noetherian scheme satisfies Serre's condition `(S₂)`. -/
theorem satisfiesSerreConditionSTwo
    {X : Scheme.{u}} [IsNoetherian X] [ConnectedSpace X]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) (ωX : X.Modules)
    (hω : IsDualizingModule K H n ωX) :
    @Scheme.Modules.satisfiesSerreConditionS X inferInstance ωX hω.coherent 2 := sorry

end RingedSpace.ModuleDerived.IsDualizingModule
end AlgebraicGeometry
