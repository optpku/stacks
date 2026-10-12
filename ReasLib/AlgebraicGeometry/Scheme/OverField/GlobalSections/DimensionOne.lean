/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A proper one-dimensional scheme over a field with only constant global sections is connected. -/
theorem connectedSpace_of_dim_one_of_globalSectionsMap_bijective
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    ConnectedSpace X.left := sorry

/-- A proper one-dimensional scheme over a field with only constant global sections is
Cohen–Macaulay. -/
theorem cohenMacaulay_of_dim_one_of_globalSectionsMap_bijective
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    Scheme.CohenMacaulay X.left := sorry

/-- A proper one-dimensional scheme over a field with only constant global sections is
equidimensional. -/
theorem equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    TopologicalSpace.EquidimensionalSpace X.left := sorry

end AlgebraicGeometry.SchemeOverField
