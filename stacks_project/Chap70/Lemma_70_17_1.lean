module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap70.Lemma_70_17_1_MinimalNonscheme

/-!
# Minimal closed subspaces that are not schemes

A quasi-compact quasi-separated algebraic space that is not a scheme contains a
closed subspace which is not a scheme, while every strictly smaller closed
subspace of that closed subspace is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.17.1: Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Quasi-separatedness is absolute
(Stacks Definition 66.3.1), in the same sense as Lemma 70.5.11. If `X` is not
a scheme, then there exists a closed subspace `Z ⊂ X` such that `Z` is not a
scheme, but every proper closed subspace `Z' ⊂ Z` is a scheme. A closed
subspace of `Z` is proper when its inclusion is not an isomorphism. -/
@[stacks 0B7Y]
theorem exists_closedSubspace_isMinimalNonscheme {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : ¬ IsScheme X) :
    ∃ Z : ClosedSubspace X, IsMinimalNonscheme Z.X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
