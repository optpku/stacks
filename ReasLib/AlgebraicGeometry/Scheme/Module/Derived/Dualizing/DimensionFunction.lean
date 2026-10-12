/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NormalizationDegree
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

open AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- The canonical normalization-degree function of a dualizing complex is a dimension function. -/
@[instance]
theorem normalizationDegreeIsDimensionFunction
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : Scheme.IsDualizingComplex ω) :
    IsDimensionFunction (normalizationDegree hω) := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
