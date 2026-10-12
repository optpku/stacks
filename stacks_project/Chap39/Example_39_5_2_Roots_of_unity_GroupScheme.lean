/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RootsOfUnity.GroupScheme

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- The compatibility module exports the reusable roots-of-unity group-scheme construction. -/
#check (AlgebraicGeometry.RootsOfUnity.baseChange :
  (n : ℕ) → [NeZero n] → (S : Scheme.{u}) → CommGrp (Over S))
