/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Refinement

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary

/-- The category of elementary étale neighborhoods of a point of a scheme is cofiltered. -/
instance instIsCofiltered (S : Scheme.{u}) (s : S) :
    IsCofiltered (Elementary S s) := sorry

end AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary
