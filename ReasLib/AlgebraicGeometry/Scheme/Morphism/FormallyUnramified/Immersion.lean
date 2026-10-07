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
