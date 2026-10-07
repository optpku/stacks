module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_13_12_ResidualSpace

/-!
# Closed points via residual spaces

On a locally Noetherian algebraic space, a point is closed if and only if its
residual-space monomorphism is a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsResidualSpace

/-- Lemma 68.13.12: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x ∈ |X|` with residual space `Z ⊂ X`. Assume `X` is locally Noetherian.
Then `x` is a closed point of `|X|` if and only if the morphism `Z ⟶ X` is a
closed immersion. -/
@[stacks 0H1U]
theorem mem_closedPoints_iff_isClosedImmersion {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} [IsLocallyNoetherian X] {x : Points X}
    (ι : Z ⟶ X) [IsResidualSpace ι x] :
    x ∈ closedPoints (Points X) ↔ IsClosedImmersion ι :=
  sorry

/-- If a residual-space monomorphism is a closed immersion, then the marked point
is a closed point of `|X|`. -/
theorem mem_closedPoints {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] [IsClosedImmersion ι] :
    x ∈ closedPoints (Points X) :=
  sorry

/-- On a locally Noetherian algebraic space, the residual-space monomorphism of a
closed point is a closed immersion. -/
theorem isClosedImmersion_of_mem_closedPoints {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} [IsLocallyNoetherian X] {x : Points X}
    (ι : Z ⟶ X) [IsResidualSpace ι x] (hx : x ∈ closedPoints (Points X)) :
    IsClosedImmersion ι :=
  sorry

end IsResidualSpace

end AlgebraicGeometry.AlgebraicSpace
