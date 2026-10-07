module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Minimal nonscheme algebraic spaces

An algebraic space is a minimal nonscheme when it is not a scheme, but every
closed subspace whose inclusion is not an isomorphism is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is a minimal nonscheme if it is not a scheme, while every
closed subspace whose inclusion is not an isomorphism is a scheme. -/
def IsMinimalNonscheme {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ¬ IsScheme X ∧ ∀ Z : ClosedSubspace X, ¬ IsIso Z.ι → IsScheme Z.X

/-- `IsMinimalNonscheme X` means that `X` is not a scheme, while every closed
subspace of `X` whose inclusion is not an isomorphism is a scheme. -/
theorem isMinimalNonscheme_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsMinimalNonscheme X ↔
      ¬ IsScheme X ∧ ∀ Z : ClosedSubspace X, ¬ IsIso Z.ι → IsScheme Z.X :=
  sorry

/-- A minimal nonscheme algebraic space is not a scheme. -/
theorem not_isScheme_of_isMinimalNonscheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (hX : IsMinimalNonscheme X) : ¬ IsScheme X :=
  sorry

/-- Every closed subspace of a minimal nonscheme whose inclusion is not an
isomorphism is a scheme. -/
theorem isScheme_of_isMinimalNonscheme_of_not_isIso {S : Scheme.{u}}
    {X : AlgebraicSpace S} (hX : IsMinimalNonscheme X) (Z : ClosedSubspace X)
    (hZ : ¬ IsIso Z.ι) : IsScheme Z.X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
