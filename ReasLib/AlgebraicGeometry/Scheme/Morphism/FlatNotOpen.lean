module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Some closed immersion of schemes is flat but is not open on underlying topological spaces. -/
theorem exists_isClosedImmersion_flat_not_isOpenMap :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsClosedImmersion f ∧ Flat f ∧ ¬ IsOpenMap f.base := sorry

end AlgebraicGeometry
