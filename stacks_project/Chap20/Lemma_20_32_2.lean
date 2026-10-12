/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived.Notation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped RingedSpace.Hom RingedSpaceDerivedRestriction

/- Lemma 20.32.2 (0D5V): the derived restriction of `K` to an open subspace `U` is
isomorphic to the intrinsic restricted representative `K↾[U]`.  The reusable object-level owner is
`OpenSubspace.Restriction.derivedObjIsoRestricted`; the two endpoint abbreviations are checked
below so downstream statements can choose either presentation without rebuilding the comparison. -/
@[stacks 0D5V "derived restriction and intrinsic open representative"]
#check @AlgebraicGeometry.RingedSpace.OpenSubspace.Restriction.derivedObjIsoRestricted

#check @AlgebraicGeometry.RingedSpace.moduleRestrictionToOpenDerived
#check @AlgebraicGeometry.RingedSpace.restrictedModuleDerivedOnOpen

end
