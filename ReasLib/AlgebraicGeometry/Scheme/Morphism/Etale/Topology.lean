module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- An étale morphism of schemes is flat and lifts generalizations. -/
theorem flatAndGeneralizingMap {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    Flat f ∧ GeneralizingMap f := sorry

end AlgebraicGeometry.Etale
