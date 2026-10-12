/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution

open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.IsResolution :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) →
    [AlgebraicGeometry.IsNoetherian Y] → [AlgebraicGeometry.IsIntegral Y] → Prop)
