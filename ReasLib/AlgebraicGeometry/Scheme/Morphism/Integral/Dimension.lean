module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import ReasLib.RingTheory.KrullDimension.Integral
public import ReasLib.Topology.KrullDimension.Maps

@[expose] public section

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- An integral morphism of schemes does not increase topological Krull dimension. -/
theorem topologicalKrullDim_le_of_isIntegralHom [IsIntegralHom f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := sorry

/-- A surjective integral morphism of schemes preserves topological Krull dimension. -/
theorem topologicalKrullDim_eq_of_surjective_isIntegralHom [IsIntegralHom f] [Surjective f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  apply le_antisymm
  · exact topologicalKrullDim_le_of_isIntegralHom f
  · exact Continuous.topologicalKrullDim_le_of_surjective_of_specializing_or_generalizingMap
      f.continuous f.surjective (.inl f.isClosedMap.specializingMap)

end AlgebraicGeometry
