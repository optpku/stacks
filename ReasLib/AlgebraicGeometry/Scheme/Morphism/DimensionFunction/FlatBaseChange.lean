module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility
public import ReasLib.Topology.IrreducibleCloseds.Soberification.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom

/-- Under a flat base change compatible with dimension functions up to a shift `c`, every
irreducible component of the base change of an integral scheme of `δ`-dimension `k` has
`δ'`-dimension `k + c`. -/
theorem deltaDimension_pullback_component {S S' X : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsIntegral X] (k : ℤ)
    (hX : f.deltaDimension δ (toIrreducibleCloseds (genericPoint X)) = k)
    (Z' : irreducibleComponents (pullback f g : Scheme)) :
    (pullback.snd f g).deltaDimension δ'
      (toIrreducibleCloseds (genericPoints.ofComponent Z')) = k + c := sorry

end Hom
end Scheme
end AlgebraicGeometry
