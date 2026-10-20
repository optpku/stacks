module

public import ReasLib.AlgebraicGeometry.Scheme.RationalFunction
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Rational functions as fractions in local rings of integral schemes -/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical identification of rational functions with fractions in the local ring.
Both maps are the implemented function-field and localization maps. -/
def rationalFunctionEquivLocalFraction (X : Scheme.{u}) [IsIntegral X] (x : X) :
    RationalFunction X ≃+* FractionRing (X.presheaf.stalk x) :=
  (rationalFunctionRing_equiv_functionField X).trans
    (FractionRing.algEquiv (A := X.presheaf.stalk x) X.functionField).symm.toRingEquiv

/-- The forward local-fraction map is the function-field map followed by the canonical
inverse localization equivalence. -/
theorem rationalFunctionEquivLocalFraction_apply (X : Scheme.{u}) [IsIntegral X]
    (x : X) (f : RationalFunction X) :
    rationalFunctionEquivLocalFraction X x f =
      (FractionRing.algEquiv (A := X.presheaf.stalk x) X.functionField).symm
        (rationalFunctionRing_equiv_functionField X f) := rfl

end AlgebraicGeometry.Scheme
