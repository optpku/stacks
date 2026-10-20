module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Alteration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents.Noetherian

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsAlteration

/-- A Noetherian integral algebraic space admitting an alteration from a regular integral
algebraic space has a finite absolute normalization morphism. -/
theorem isFinite_normalizationTo {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y)
    [IsAlteration f] [IsRegular X] : IsFinite Y.normalizationTo :=
  sorry

/-- A Noetherian integral algebraic space admitting an alteration from a regular integral
algebraic space contains a dense regular open subspace. -/
theorem exists_dense_open_regular {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y)
    [IsAlteration f] [IsRegular X] :
    ∃ U : OpenSubspace Y, Dense (U.pointsSet : Set (Points Y)) ∧ IsRegular U.X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsAlteration
