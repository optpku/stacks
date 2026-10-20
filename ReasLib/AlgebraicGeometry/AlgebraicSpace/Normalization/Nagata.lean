module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Nagata
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute

/-!
# Finiteness of the absolute normalization of a Nagata algebraic space
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The absolute normalization morphism of a Nagata algebraic space is finite. -/
theorem isFinite_normalizationTo_of_isNagata {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNagata X] : IsFinite X.normalizationTo :=
  sorry

/-- Finiteness of the absolute normalization morphism of a Nagata algebraic space is
available canonically. -/
instance instIsFiniteNormalizationToOfIsNagata {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNagata X] : IsFinite X.normalizationTo :=
  isFinite_normalizationTo_of_isNagata X

end AlgebraicGeometry.AlgebraicSpace
