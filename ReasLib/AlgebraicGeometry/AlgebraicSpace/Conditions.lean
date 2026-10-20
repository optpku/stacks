module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyAlpha
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyBeta
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteAbove

/-!
# Implications among finiteness and separation conditions on algebraic spaces

Decency is equivalent to properties (α) and (β) together. Absolute Zariski-local
quasi-separatedness implies very reasonableness, which implies reasonableness,
which in turn implies decency.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is decent if and only if it has both property (α) and
property (β). -/
theorem isDecent_iff_hasPropertyAlpha_and_hasPropertyBeta {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    IsDecent X ↔ HasPropertyAlpha X ∧ HasPropertyBeta X :=
  sorry

/-- A decent algebraic space has property (α). -/
instance instHasPropertyAlpha_of_isDecent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [h : IsDecent X] : HasPropertyAlpha X :=
  ((isDecent_iff_hasPropertyAlpha_and_hasPropertyBeta X).mp h).1

/-- A decent algebraic space has property (β). -/
instance instHasPropertyBeta_of_isDecent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [h : IsDecent X] : HasPropertyBeta X :=
  ((isDecent_iff_hasPropertyAlpha_and_hasPropertyBeta X).mp h).2

/-- Properties (α) and (β) together yield a decent algebraic space. -/
instance instIsDecent_of_hasPropertyAlpha_of_hasPropertyBeta
    {S : Scheme.{u}} (X : AlgebraicSpace S) [hα : HasPropertyAlpha X]
    [hβ : HasPropertyBeta X] : IsDecent X :=
  (isDecent_iff_hasPropertyAlpha_and_hasPropertyBeta X).mpr ⟨hα, hβ⟩

/-- Decency is equivalent to finiteness of the chart and self-relation fibres
of every affine étale scheme chart over every point. -/
theorem isDecent_iff_forallAffineEtaleFiniteAbove {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    IsDecent X ↔ ∀ x : Points X, forallAffineEtaleFiniteAbove X x :=
  sorry

/-- A reasonable algebraic space is decent. -/
instance (priority := 900) instIsDecent_of_isReasonable {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsReasonable X] : IsDecent X :=
  sorry

/-- A very reasonable algebraic space is reasonable. -/
instance (priority := 900) instIsReasonable_of_isVeryReasonable {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsVeryReasonable X] : IsReasonable X :=
  sorry

/-- An absolutely Zariski locally quasi-separated algebraic space is very
reasonable. -/
instance (priority := 900) instIsVeryReasonable_of_isAbsolutelyZariskiLocallyQuasiSeparated
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] : IsVeryReasonable X :=
  sorry

/-- An algebraic space represented by a scheme is absolutely Zariski locally
quasi-separated. -/
instance (priority := 900) instIsAbsolutelyZariskiLocallyQuasiSeparated_of_isScheme
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X] :
    IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
