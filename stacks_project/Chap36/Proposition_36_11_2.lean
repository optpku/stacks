/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Comparison

open AlgebraicGeometry CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsNoetherian X]
variable [HasDerivedCategory.{w} (SheafOfModules X.ringCatSheaf)]
variable [HasDerivedCategory.{w}
  (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory]

/- Proposition 36.11.2 (1): for a Noetherian scheme, the canonical functor from bounded-above
complexes of coherent modules to bounded-above complexes with coherent cohomology is an
equivalence. -/
@[stacks 0FDB] #check
  (AlgebraicGeometry.Scheme.coherentMinusComparisonIsEquivalence (X := X) :
    CategoryTheory.Functor.IsEquivalence
      (CategoryTheory.DerivedCategory.Minus.CohomologyIn.Comparison.functor
        (SheafOfModules.isCoherent X.ringCatSheaf)))

/- Proposition 36.11.2 (2): for a Noetherian scheme, the canonical functor from bounded
complexes of coherent modules to bounded complexes with coherent cohomology is an equivalence. -/
@[stacks 0FDB] #check
  (AlgebraicGeometry.Scheme.coherentBoundedComparisonIsEquivalence (X := X) :
    CategoryTheory.Functor.IsEquivalence
      (CategoryTheory.DerivedCategory.Bounded.CohomologyIn.Comparison.functor
        (SheafOfModules.isCoherent X.ringCatSheaf)))

end AlgebraicGeometry.Scheme
