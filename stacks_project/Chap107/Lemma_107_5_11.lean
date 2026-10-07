module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Semicontinuity.Defs
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap107.Lemma_107_5_9_RelativeDimension

/-!
# Semicontinuity of relative dimension

For a locally of finite type morphism of locally Noetherian algebraic stacks,
relative dimension is upper semi-continuous on the space of points, and locally
constant when the morphism is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.5.11 (1): if `f : T ⟶ X` is a locally of finite type morphism of
locally Noetherian algebraic stacks, then `relativeDimensionAt f` is upper
semi-continuous on `Points T` in the canonical topology. -/
@[stacks 0DRQ]
theorem upperSemicontinuous_relativeDimensionAt {S : Scheme.{u}}
    {T X : GroupoidsOver S} [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] (f : T ⟶ X)
    [LocallyOfFiniteType f] {τ : TopologicalSpace (Points T)}
    (hτ : IsPointsTopology T τ) :
    @UpperSemicontinuous (Points T) EInt τ inferInstance (relativeDimensionAt f) :=
  sorry

/-- Lemma 107.5.11 (2): if in addition `f` is smooth, then
`relativeDimensionAt f` is locally constant on `Points T` in the canonical
topology. -/
@[stacks 0DRQ]
theorem isLocallyConstant_relativeDimensionAt {S : Scheme.{u}}
    {T X : GroupoidsOver S} [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] (f : T ⟶ X)
    [LocallyOfFiniteType f] [Smooth f] {τ : TopologicalSpace (Points T)}
    (hτ : IsPointsTopology T τ) :
    @IsLocallyConstant (Points T) EInt τ (relativeDimensionAt f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
