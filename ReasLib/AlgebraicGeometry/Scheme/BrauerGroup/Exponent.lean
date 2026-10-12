/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BrauerGroup

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme

/-- The Brauer class of an Azumaya algebra finite locally free of rank `d ^ 2` is annihilated
by `d`. -/
theorem classOf_pow_eq_one {S : Scheme.{u}} (A : S.Modules) [MonObj A] [IsAzumaya A] (d : ℕ)
    [IsFiniteLocallyFreeOfRank (d ^ 2) A] :
    classOf A ^ d = 1 := sorry

end AlgebraicGeometry.Scheme
