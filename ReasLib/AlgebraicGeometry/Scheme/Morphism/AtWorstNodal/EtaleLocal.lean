module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AtWorstNodal

/-- At-worst-nodality of scheme morphisms of relative dimension one is étale local
on the source and target. -/
instance isEtaleLocalAtSourceAndTarget :
    IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) := sorry

/-- At-worst-nodal scheme morphisms of relative dimension one are stable under
arbitrary base change. -/
instance instIsStableUnderBaseChange :
    IsStableUnderBaseChange
      (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) := sorry

end AlgebraicGeometry.AtWorstNodal
