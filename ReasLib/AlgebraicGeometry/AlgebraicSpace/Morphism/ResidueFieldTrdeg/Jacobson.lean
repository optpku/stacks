/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Jacobson
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg

/-!
# Residue-field transcendence degree over Jacobson algebraic spaces

A locally finite-type morphism into a Jacobson algebraic space has residue-field
transcendence degree zero at every finite-type point of its source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The residue-field transcendence degree of a locally finite-type morphism
into a Jacobson algebraic space vanishes at every finite-type point. -/
@[stacks 0ECY]
theorem residueFieldTrdegAt.eq_zero_of_isFiniteTypePoint
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsJacobson Y]
    {x : Points X} (hx : IsFiniteTypePoint x) :
    residueFieldTrdegAt f x = 0 :=
  sorry

/-- The residue-field transcendence degree of a locally finite-type morphism
into a Jacobson algebraic space vanishes on `finiteTypePoints`. -/
theorem residueFieldTrdegAt.eq_zero_of_mem_finiteTypePoints
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsJacobson Y]
    {x : Points X} (hx : x ∈ finiteTypePoints X) :
    residueFieldTrdegAt f x = 0 :=
  residueFieldTrdegAt.eq_zero_of_isFiniteTypePoint f hx

end AlgebraicGeometry.AlgebraicSpace
