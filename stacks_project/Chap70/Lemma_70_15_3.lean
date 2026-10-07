module

public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Lemma 70.15.3

If the reduction of an algebraic space is a scheme, then the algebraic space
itself is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsScheme

/-- Lemma 70.15.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `reduction X` is a scheme, then `X` is a scheme. -/
@[stacks 07VU]
theorem of_reduction {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsScheme (reduction X)] : IsScheme X :=
  sorry

end IsScheme

end AlgebraicGeometry.AlgebraicSpace
