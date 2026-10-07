module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Dimension formula for dominant morphisms of integral algebraic spaces

A dominant locally finite-type morphism of integral algebraic spaces with
locally Noetherian target obeys the inequality
`dimension X ≤ dimension Y + residueFieldTrdegAt f x` at a generic point `x`.
If the morphism is proper, equality holds.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.15.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is `IsLocallyNoetherian`, `X` and `Y` are
`IsIntegral`, `f` is `Dominant`, and `f` is `LocallyOfFiniteType`. If
`x ∈ genericPoints X`, and write `y` for `Points.map f x`, the generic point of
`Y`, then `dimension X ≤ dimension Y + residueFieldTrdegAt f x`. -/
@[stacks 0EDC]
theorem dimension_le_add_residueFieldTrdegAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Dominant f] [LocallyOfFiniteType f] {x : Points X}
    (hx : x ∈ genericPoints X) :
    dimension X ≤ dimension Y + (residueFieldTrdegAt f x : WithBot ℕ∞) :=
  sorry

/-- Lemma 72.15.2 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `Y` is `IsLocallyNoetherian`, `X` and `Y` are
`IsIntegral`, `f` is `Dominant`, and `f` is `Proper` (hence
`LocallyOfFiniteType`). If `x ∈ genericPoints X`, and write `y` for
`Points.map f x`, the generic point of `Y`, then
`dimension X = dimension Y + residueFieldTrdegAt f x`. -/
@[stacks 0EDC]
theorem dimension_eq_add_residueFieldTrdegAt_of_proper {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Dominant f] [Proper f] {x : Points X}
    (hx : x ∈ genericPoints X) :
    dimension X = dimension Y + (residueFieldTrdegAt f x : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
