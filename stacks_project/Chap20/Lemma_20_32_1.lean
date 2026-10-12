/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.32.1: restriction to an open subspace preserves K-injective complexes.  ReasLib
registers this canonical fact as an instance, so downstream derived-Hom statements need no
proof-local `letI`. -/

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

@[stacks 08BS "restriction to an open preserves K-injectives"]
#check
  moduleRestrictionToOpen_isKInjective (X := X) U

end AlgebraicGeometry.RingedSpace
