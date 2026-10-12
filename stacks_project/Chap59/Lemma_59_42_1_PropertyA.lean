/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyA

@[expose] public section

open AlgebraicGeometry

universe u

/- The source-facing Property (A) notation is provided by the shared algebraic-geometric owner. -/
#check (AlgebraicGeometry.hasPropertyA : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Prop)
