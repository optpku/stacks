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
