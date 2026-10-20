/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.GenericPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated.LocallyOfFiniteType

/-!
# Separatedness from DVR-valuative uniqueness at generic points

This module compares separatedness with unrestricted valuative uniqueness,
DVR-valuative uniqueness, and the restriction to canonical residue-field maps
at generic points of irreducible components.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- For a locally finite type morphism to a locally Noetherian scheme, separatedness,
valuative uniqueness, DVR-valuative uniqueness, and DVR-valuative uniqueness at the generic
points of irreducible components are equivalent. -/
@[stacks 0207 "Noetherian DVR-valuative criterion for separatedness"]
theorem isSeparated_tfae_valuativeCriterion_dvr_genericPoint
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    List.TFAE [
      IsSeparated f,
      ValuativeCriterion.Uniqueness f,
      ValuativeCriterion.DVR.Uniqueness f,
      GenericPointDvrValuativeCriterionUniqueness f] := sorry

end AlgebraicGeometry
