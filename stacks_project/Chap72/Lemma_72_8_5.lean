module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap72.Definition_72_8_3_Alteration

/-!
# Alterations inside a proper surjective morphism

A proper surjective morphism of algebraic spaces onto an integral target
restricts to an alteration along some integral closed subspace of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.8.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a proper
surjective morphism of algebraic spaces over `S`. Assume `Y` is integral.
Then there exists an integral closed subspace `X' ⊂ X` such that
`f' = X'.ι ≫ f : X'.X ⟶ Y` is an alteration. -/
@[stacks 0DMN]
theorem exists_integralClosedSubspace_isAlteration
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral Y]
    (f : X ⟶ Y) [Proper f] [Surjective f] :
    ∃ (X' : ClosedSubspace X) (hX' : IsIntegral X'.X),
      IsAlteration (X'.ι ≫ f) :=
  sorry

/-- There exists an integral closed subspace of the source whose restriction
to the integral target is proper, dominant, and finite over some nonempty
open of the target. -/
theorem exists_integralClosedSubspace_isAlteration_spec
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral Y]
    (f : X ⟶ Y) [Proper f] [Surjective f] :
    ∃ X' : ClosedSubspace X,
      IsIntegral X'.X ∧ Proper (X'.ι ≫ f) ∧ Dominant (X'.ι ≫ f) ∧
        ∃ U : OpenSubspace Y,
          U.pointsSet.Nonempty ∧
            IsFinite (pullback.snd (X'.ι ≫ f) U.ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
