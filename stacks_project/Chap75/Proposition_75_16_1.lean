/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Compact
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
  AlgebraicGeometry.AlgebraicSpace.SmallEtale CategoryTheory

universe u

/- Proposition 75.16.1 -/
@[stacks 09M8] #check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.DerivedQCoh.isCompactObject_iff_isPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (E : DerivedQCoh X),
      IsCompactObject E ↔ ModuleDerived.IsPerfect E.obj)
