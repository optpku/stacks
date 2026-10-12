/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Absolute affine diagonal of algebraic spaces

An algebraic space has affine diagonal over the terminal scheme when the diagonal
of its base change along `terminal.from S` is a representable affine morphism of
schemes, in the same sense as the absolute separation axioms of Definition 66.3.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space has affine diagonal over the terminal scheme if the diagonal
of the viewed space is a representable affine morphism. -/
@[mk_iff]
class IsAbsolutelyAffineDiagonal {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- The diagonal of `extendBaseTerminal X` is a representable affine morphism. -/
  isAffineHom_diag_extendBase :
    (MorphismProperty.over (@IsAffineHom)).presheaf (diag (extendBaseTerminal X))

/-- Absolute affine-diagonality means the diagonal of the viewed space is a
representable affine morphism. -/
theorem IsAbsolutelyAffineDiagonal.spec {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsAbsolutelyAffineDiagonal X ↔
      (MorphismProperty.over (@IsAffineHom)).presheaf (diag (extendBaseTerminal X)) :=
  sorry

/-- An affine algebraic space has affine diagonal over the terminal scheme. -/
instance instIsAbsolutelyAffineDiagonal_of_isAffine {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsAffine X] : IsAbsolutelyAffineDiagonal X :=
  sorry

/-- An algebraic space with affine diagonal over the terminal scheme is absolutely
quasi-separated. -/
instance (priority := 900) instIsAbsolutelyQuasiSeparated_of_isAbsolutelyAffineDiagonal
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAbsolutelyAffineDiagonal X] :
    IsAbsolutelyQuasiSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
