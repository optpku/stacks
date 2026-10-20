/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Product

/-!
# Diagonals of regular varieties

The diagonal of a regular variety over an algebraically closed field is a regular immersion,
and its conormal sheaf has rank equal to the dimension of the variety.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The diagonal of a regular variety over an algebraically closed field is a regular
immersion. -/
@[instance]
theorem diagonal_isRegularImmersion (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] :
    IsRegularImmersion (pullback.diagonal X.hom) := sorry

/-- The conormal sheaf of the diagonal of a regular variety over an algebraically closed
field is finite locally free of rank equal to the dimension of the variety. -/
@[instance]
theorem diagonal_conormal_isFiniteLocallyFreeOfRank
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left] :
    Scheme.Modules.IsFiniteLocallyFreeOfRank
      (baseFieldTrdegAt X (genericPoint X.left))
      (Scheme.Hom.conormalSheaf (pullback.diagonal X.hom)) := sorry

end AlgebraicGeometry.SchemeOverField
