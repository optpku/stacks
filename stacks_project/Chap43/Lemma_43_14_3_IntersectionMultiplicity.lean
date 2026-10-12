/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Proper intersection of closed subschemes is proper intersection of their closed supports. -/
abbrev IntersectsProperly (V W : X.IdealSheafData) : Prop :=
  Closeds.IntersectProperly V.support W.support

end AlgebraicGeometry.Scheme.IdealSheafData
