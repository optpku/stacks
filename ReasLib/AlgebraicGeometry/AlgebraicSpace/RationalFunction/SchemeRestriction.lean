module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.ChartPullback

/-! # Restriction of rational functions to integral scheme charts -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- Restriction of rational functions to the function field of an integral étale scheme chart. -/
def rationalFunctionToSchemeFunctionField (ι : ofOver U ⟶ X) [Etale ι]
    [AlgebraicGeometry.IsIntegral U.left] : RationalFunction X →+* U.left.functionField :=
  (U.left.rationalFunctionRing_equiv_functionField.toRingHom).comp
    (RationalFunctionChart.map U ι)

/-- Restriction to the function field is chart pullback followed by the canonical
scheme rational-function equivalence. -/
theorem rationalFunctionToSchemeFunctionField_apply (ι : ofOver U ⟶ X) [Etale ι]
    [AlgebraicGeometry.IsIntegral U.left] (f : RationalFunction X) :
    rationalFunctionToSchemeFunctionField ι f =
      U.left.rationalFunctionRing_equiv_functionField (RationalFunctionChart.map U ι f) :=
  rfl

/-- Restriction of rational units to the function field of an integral étale scheme chart. -/
def rationalUnitToSchemeFunctionField (ι : ofOver U ⟶ X) [Etale ι]
    [AlgebraicGeometry.IsIntegral U.left] : (RationalFunction X)ˣ →* U.left.functionFieldˣ :=
  Units.map (rationalFunctionToSchemeFunctionField ι).toMonoidHom

/-- The underlying function of a restricted rational unit is the restriction of
its underlying rational function. -/
theorem rationalUnitToSchemeFunctionField_coe (ι : ofOver U ⟶ X) [Etale ι]
    [AlgebraicGeometry.IsIntegral U.left] (f : (RationalFunction X)ˣ) :
    (rationalUnitToSchemeFunctionField ι f : U.left.functionField) =
      rationalFunctionToSchemeFunctionField ι (f : RationalFunction X) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
