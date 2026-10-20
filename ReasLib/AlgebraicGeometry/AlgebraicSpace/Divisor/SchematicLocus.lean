/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Order
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.SchemeRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing

/-! # Prime divisors and orders of vanishing on the schematic locus -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

namespace PrimeDivisor

/-- A prime divisor meets the schematic locus if and only if its generic point
lies in the schematic locus. -/
theorem meetsSchematicLocus_iff [IsIntegral X] (Z : PrimeDivisor X) :
    (Z.pointsSet ∩ (schematicLocus X).pointsSet).Nonempty ↔
      Z.genericPoint ∈ (schematicLocus X).pointsSet :=
  sorry

/-- A prime divisor whose generic point lies in the schematic locus has a
locally Noetherian integral open scheme neighborhood with a corresponding prime divisor. -/
theorem exists_openImmersion_of_mem_schematicLocus [IsLocallyNoetherian X] [IsIntegral X]
    (Z : PrimeDivisor X)
    (h_meets : Z.genericPoint ∈ (schematicLocus X).pointsSet) :
    ∃ (U : Over S) (ι : ofOver U ⟶ X) (Z' : AlgebraicGeometry.PrimeDivisor U.left),
      IsOpenImmersion ι ∧ AlgebraicGeometry.IsLocallyNoetherian U.left ∧
        AlgebraicGeometry.IsIntegral U.left ∧
          Points.mapOfOver ι Z'.genericPoint = Z.genericPoint :=
  sorry

/-- For a prime divisor meeting the schematic locus, the henselian order of a
rational unit equals its scheme order after restriction to any locally Noetherian
integral open scheme chart with a corresponding prime divisor. -/
theorem ord_eq_primeDivisorOrder [IsLocallyNoetherian X] [IsIntegral X]
    (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (h_meets : (Z.pointsSet ∩ (schematicLocus X).pointsSet).Nonempty)
    {U : Over S} (ι : ofOver U ⟶ X) [IsOpenImmersion ι]
    [AlgebraicGeometry.IsLocallyNoetherian U.left]
    [AlgebraicGeometry.IsIntegral U.left]
    (Z' : AlgebraicGeometry.PrimeDivisor U.left)
    (hξ : Points.mapOfOver ι Z'.genericPoint = Z.genericPoint) :
    Z.ord f = Scheme.primeDivisorOrder U.left Z' (rationalUnitToSchemeFunctionField ι f) :=
  sorry

end PrimeDivisor

end AlgebraicGeometry.AlgebraicSpace
