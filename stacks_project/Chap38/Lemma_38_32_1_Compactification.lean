/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

#check (Of.ι : {S : Scheme.{u}} → {X : Over S} →
  (P : Of S X) → X.left ⟶ P.obj.right.left)

end AlgebraicGeometry.Scheme.Compactification
