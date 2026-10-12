/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Additive
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Evaluation
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Points
public import ReasLib.AlgebraicGeometry.RingedSpace.Skyscraper

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf
open TopCat.Sheaf.Skyscraper
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- The canonical commutative-ring skyscraper sheaf at a scheme point. -/
#check (AlgebraicGeometry.pointRingSheaf :
  ∀ (X : Scheme.{u}) (x : X) (k : Type u) [CommRing k],
    TopCat.Sheaf CommRingCat.{u} X.toTopCat)

#check SchemeOverField.rationalPoint
#check additiveSheaf
#check additiveSheafMap
#check additiveStructureMap
#check unitsStructureMap
#check additiveEvaluationDifference
#check additiveEvaluationDifference_app
#check unitsEvaluationDifference
#check unitsEvaluationDifference_app
#check IsEvaluationAt
#check isEvaluationAt_iff
#check unitsStructureMap_comp_evaluationDifference
#check unitsShortExact_of_glueingPoints

end AlgebraicGeometry
