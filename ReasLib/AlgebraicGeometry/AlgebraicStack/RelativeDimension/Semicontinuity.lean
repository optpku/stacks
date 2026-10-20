module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Semicontinuity.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth

/-!
# Semicontinuity of relative dimension

Relative dimension of locally Noetherian algebraic stacks is upper semicontinuous
for locally finite type morphisms and locally constant for smooth morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The relative dimension of a locally of finite type morphism of locally
Noetherian algebraic stacks is upper semicontinuous on the source's space of
points with its canonical topology. -/
theorem upperSemicontinuous_relativeDimensionAt {S : Scheme.{u}}
    {T X : GroupoidsOver S} [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] (f : T ⟶ X)
    [LocallyOfFiniteType f] :
    UpperSemicontinuous (relativeDimensionAt f) := sorry

/-- The relative dimension of a smooth, locally of finite type morphism of locally
Noetherian algebraic stacks is locally constant on the source's space of points
with its canonical topology. -/
theorem isLocallyConstant_relativeDimensionAt {S : Scheme.{u}}
    {T X : GroupoidsOver S} [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] (f : T ⟶ X)
    [LocallyOfFiniteType f] [Smooth f] :
    IsLocallyConstant (relativeDimensionAt f) := sorry

end AlgebraicGeometry.AlgebraicStack
