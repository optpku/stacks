/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Codimension-zero points and open scheme neighbourhoods

On a quasi-separated algebraic space, codimension zero, local-ring dimension zero,
and being a generic point of an irreducible component are equivalent. Every such
point has an open neighbourhood which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- On a quasi-separated algebraic space, codimension zero, local-ring dimension
zero, and being a generic point of an irreducible component are equivalent. -/
theorem codimZero_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAbsolutelyQuasiSeparated X] (x : Points X) :
    List.TFAE
      [ x ∈ codimZeroPoints X
      , localRingDimAt x = 0
      , x ∈ genericPoints X ] :=
  sorry

/-- Every point of local-ring dimension zero on a quasi-separated algebraic space
has an open neighbourhood which is a scheme. -/
theorem exists_open_isScheme_of_localRingDimAt_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X] (x : Points X)
    (hx : localRingDimAt x = 0) :
    ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet :=
  sorry

/-- On an absolutely quasi-separated algebraic space, a generic point of an
irreducible component of `|X|` lies in an open subspace which is a scheme. -/
theorem exists_open_isScheme_of_mem_genericPoints {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X] {x : Points X}
    (hx : x ∈ genericPoints X) :
    ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
