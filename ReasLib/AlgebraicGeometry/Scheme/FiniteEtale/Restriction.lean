/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Restriction of finite étale schemes along a closed immersion is faithful when
the immersion meets every connected component of the base scheme. -/
instance finiteEtaleBaseChange_faithful_of_meetsConnectedComponents
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    [h_meets : Fact (∀ x : X, ∃ y : Y, i y ∈ connectedComponent x)] :
    (finiteEtaleBaseChange i).Faithful := sorry

end AlgebraicGeometry.Scheme
