/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemePullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalGeneration
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Data.Set.Lattice

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Fitting closed subspaces of a finite-type quasi-coherent module have empty intersection. -/
theorem fittingClosedSubspace_pointsSet_iInter_eq_empty
    {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] :
    (⋂ r : ℕ, (fittingClosedSubspace F r).pointsSet) = (∅ : Set (Points X)) :=
  sorry

/-- The Fitting open complement represents local generation by at most the given number of sections on scheme pullbacks. -/
theorem fittingOpenComplement_nonempty_over_hom_iff_isLocallyGeneratedBy
    {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (g : ofOver T ⟶ X) (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) :
    Subsingleton (Over.mk g ⟶ Over.mk (fittingOpenComplement F r).ι) ∧
      (Nonempty (Over.mk g ⟶ Over.mk (fittingOpenComplement F r).ι) ↔
        SheafOfModules.IsLocallyGeneratedBy (Modules.pullbackToScheme g F) r) :=
  sorry

/-- The Fitting rank locus represents fixed-rank local freeness on scheme pullbacks. -/
theorem fittingRankLocus_nonempty_over_hom_iff_isFiniteLocallyFreeOfRank
    {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (g : ofOver T ⟶ X) (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) :
    Subsingleton (Over.mk g ⟶ Over.mk (fittingRankLocus F r).ι) ∧
      (Nonempty (Over.mk g ⟶ Over.mk (fittingRankLocus F r).ι) ↔
        SheafOfModules.IsFiniteLocallyFreeOfRank r
          (Modules.pullbackToScheme g F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
