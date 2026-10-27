/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Nagata
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-!
# Finiteness of relative and absolute normalizations over Nagata algebraic spaces
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

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The relative normalization of a quasi-separated finite-type morphism of algebraic
spaces with reduced source and Nagata target is finite. -/
theorem isFinite_fromNormalization_of_isNagata_of_finiteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsNagata Y] [IsReduced X] :
    IsFinite (fromNormalization f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace.IsFinite

open AlgebraicGeometry.AlgebraicSpace.Hom

/-- The relative normalization of a quasi-separated finite-type morphism of algebraic
spaces with reduced source and Nagata target is canonically a finite morphism. -/
instance fromNormalization_of_isNagata_of_finiteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsNagata Y] [IsReduced X] :
    IsFinite (fromNormalization f) :=
  isFinite_fromNormalization_of_isNagata_of_finiteType f

end AlgebraicGeometry.AlgebraicSpace.IsFinite
