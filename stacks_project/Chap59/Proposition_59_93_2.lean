module

public import stacks_project.Chap59.Definition_59_93_1_LocalAcyclicity
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open CategoryTheory AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Proposition 59.93.2: a smooth morphism of schemes is universally locally acyclic. -/
@[stacks 0GJQ]
instance UniversallyLocallyAcyclic.of_smooth {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] : UniversallyLocallyAcyclic f :=
  sorry

end AlgebraicGeometry.Scheme
