/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Regular
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

universe u

/- Lemma 36.11.8 (1): on a regular scheme, a bounded derived module with coherent
cohomology is perfect. -/
@[stacks 0FDC] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_of_boundedCoherentCohomology_of_regular :
    ∀ {X : Scheme.{u}} [Scheme.Regular X]
      (E : RingedSpace.ModuleDerived X.toRingedSpace),
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E →
        (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E →
          RingedSpace.ModuleDerived.IsPerfect E)

/- Lemma 36.11.8 (2): on a Noetherian regular scheme, a perfect derived module has
bounded coherent cohomology. -/
@[stacks 0FDC] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.boundedCoherentCohomology_of_regular :
    ∀ {X : Scheme.{u}} [Scheme.Regular X] [IsNoetherian X]
      (E : RingedSpace.ModuleDerived X.toRingedSpace),
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E ∧
          (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E)
