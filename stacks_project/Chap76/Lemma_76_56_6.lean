module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_28_1_ResolutionProperty

/-!
# Affine diagonal from the resolution property of algebraic spaces

A quasi-compact quasi-separated algebraic space with the resolution property
has affine diagonal over the terminal scheme, in the sense of Definition 66.3.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.56.6: a quasi-compact and quasi-separated algebraic space `X` over a
scheme `S` with the resolution property has affine diagonal over `ℤ` as in
Definition 66.3.1, i.e. `diag (extendBaseTerminal X)` is representable affine. -/
@[stacks 0GV3]
theorem affineDiagonal_of_hasResolutionProperty {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (hX : HasResolutionProperty X) :
    (MorphismProperty.over (@IsAffineHom)).presheaf (diag (extendBaseTerminal X)) := sorry

end AlgebraicGeometry.AlgebraicSpace
