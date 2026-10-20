/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.Pushforward
import StacksCheckRecall

@[expose] public section

/- Lemma 20.34.1 (0A3B): exact derived pushforward from a closed subset is left adjoint to
derived sections with support.  The reusable owner is indexed by `Z : Closeds X`; a raw closed
set with proof `hZ` is represented by `Closeds.mk Z hZ`.  The owner also supplies canonical
adjointness instances and the positive-homology vanishing for a degree-zero pushforward. -/

@[stacks 0A3B]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.ModuleDerived
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Pushforward.derived
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.SectionsWithSupport.derived
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.adjunction
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.pushforwardIsLeftAdjoint
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.sectionsWithSupportIsRightAdjoint
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Pushforward.single
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Pushforward.localCohomology
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Pushforward.higherHomology_isZero
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Pushforward.underivedSingle_higherHomology_isZero
