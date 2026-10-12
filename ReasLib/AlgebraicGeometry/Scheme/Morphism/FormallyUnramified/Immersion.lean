/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsImmersion

/-- Every immersion of schemes is formally unramified. -/
theorem formallyUnramified {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    FormallyUnramified i := sorry

end AlgebraicGeometry.IsImmersion
