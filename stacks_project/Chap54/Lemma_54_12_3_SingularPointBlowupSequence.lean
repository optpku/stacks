/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.SingularPointSequence

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- The finite singular-point blowup sequence is owned by the shared blowup API. -/
#check (AlgebraicGeometry.Scheme.SingularPointBlowupSequence :
  Scheme.{u} → Scheme.{u} → Type (u + 1))
