module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Absolute affine diagonal of algebraic spaces

An algebraic space has affine diagonal over the terminal scheme when the diagonal
of its base change along `terminal.from S` is a representable affine morphism of
schemes.
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
