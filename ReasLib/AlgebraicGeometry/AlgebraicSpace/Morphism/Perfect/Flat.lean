module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Flat perfect morphisms of algebraic spaces

A morphism of algebraic spaces is flat and perfect if and only if it is flat
and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is flat and perfect if and only if it is
flat and locally of finite presentation. -/
theorem flat_and_perfect_iff_flat_and_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (Flat f ∧ Perfect f) ↔ (Flat f ∧ LocallyOfFinitePresentation f) := sorry

end AlgebraicGeometry.AlgebraicSpace
