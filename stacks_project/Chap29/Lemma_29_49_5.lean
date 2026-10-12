/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.RationalFunction.GenericPoints
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 29.49.5: for a scheme with finitely many irreducible components, the rational-function
ring maps bijectively to the product of the stalks at the component generic points. -/
@[stacks 01RV] #check
  (AlgebraicGeometry.Scheme.rationalFunctionRingToPiStalk_bijective :
    ∀ (X : Scheme.{u}) [Finite (irreducibleComponents X)],
      Function.Bijective
        (X.rationalFunctionRingToPiStalk :
          X.rationalFunctionRing → ∀ η : genericPoints X, X.presheaf.stalk η.1))

/- If the scheme is reduced, its rational-function ring maps bijectively to the product of the
residue fields at the component generic points. -/
#check
  (AlgebraicGeometry.Scheme.rationalFunctionRingToPiResidueField_bijective :
    ∀ (X : Scheme.{u}) [Finite (irreducibleComponents X)] [IsReduced X],
      Function.Bijective
        (X.rationalFunctionRingToPiResidueField :
          X.rationalFunctionRing → ∀ η : genericPoints X, X.residueField η.1))

/- For an integral scheme, its rational-function ring is canonically equivalent to its function
field, namely the stalk at the generic point. -/
#check
  (AlgebraicGeometry.Scheme.rationalFunctionRing_equiv_functionField :
    ∀ (X : Scheme.{u}) [IsIntegral X], X.rationalFunctionRing ≃+* X.functionField)

/- For an integral scheme, its rational-function ring maps bijectively to the residue field at
the generic point. -/
#check
  (AlgebraicGeometry.Scheme.rationalFunctionRingToResidueField_genericPoint_bijective :
    ∀ (X : Scheme.{u}) [IsIntegral X],
      Function.Bijective
        (X.rationalFunctionRingToResidueField_genericPoint :
          X.rationalFunctionRing → X.residueField (genericPoint X)))

end AlgebraicGeometry.Scheme
