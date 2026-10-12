/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection

@[expose] public section

universe u

#check (AlgebraicGeometry.LocallyOfType.instHasRingHomPropertyIsLocalCompleteIntersection :
  AlgebraicGeometry.HasRingHomProperty
    (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsLocalCompleteIntersection)
    RingHom.IsLocalCompleteIntersection)
