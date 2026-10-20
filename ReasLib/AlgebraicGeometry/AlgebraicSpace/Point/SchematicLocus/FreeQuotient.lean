/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Finite.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient.Torsor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-! # Schematic locus of a finite free quotient -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFreeQuotient

/-- A point of the quotient of an algebraic space by a free action of a finite
group lies in the schematic locus if and only if an affine open subspace of
the original space contains its entire fibre. -/
theorem mem_schematicLocus_iff_exists_affineOpen {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {G : Type u} [Group G] [Finite G]
    (ρ : G →* Aut X) (q : X ⟶ Y) [IsFree ρ] [IsFreeQuotient ρ q]
    (y : Points Y) :
    y ∈ (schematicLocus Y).pointsSet ↔
      ∃ U : OpenSubspace X, IsAffine U.X ∧ Points.map q ⁻¹' {y} ⊆ U.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFreeQuotient
