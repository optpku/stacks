/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Locus.Representability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Locus.FinitePresentation
import StacksCheckRecall

/-!
# Lemma 71.5.6

Fitting loci represent local generation and fixed-rank local freeness on scheme
pullbacks. Their inclusions are of finite presentation for finitely presented modules.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.5.6 (1): The Fitting closed subspaces of a finite-type quasi-coherent module have empty intersection. -/
@[stacks 0CZ9] #check (AlgebraicGeometry.AlgebraicSpace.fittingClosedSubspace_pointsSet_iInter_eq_empty :
  ∀
    {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent],
    (⋂ r : ℕ, (fittingClosedSubspace F r).pointsSet) = (∅ : Set (Points X)))

/- Lemma 71.5.6 (2): The Fitting open complement represents local generation by at most the given number of sections on scheme pullbacks. -/
@[stacks 0CZ9] #check (AlgebraicGeometry.AlgebraicSpace.fittingOpenComplement_nonempty_over_hom_iff_isLocallyGeneratedBy :
  ∀
    {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (g : ofOver T ⟶ X) (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ),
    Subsingleton (Over.mk g ⟶ Over.mk (fittingOpenComplement F r).ι) ∧
      (Nonempty (Over.mk g ⟶ Over.mk (fittingOpenComplement F r).ι) ↔
        SheafOfModules.IsLocallyGeneratedBy (Modules.pullbackToScheme g F) r))

/- Lemma 71.5.6 (3): The Fitting rank locus represents fixed-rank local freeness on scheme pullbacks. -/
@[stacks 0CZ9] #check (AlgebraicGeometry.AlgebraicSpace.fittingRankLocus_nonempty_over_hom_iff_isFiniteLocallyFreeOfRank :
  ∀
    {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (g : ofOver T ⟶ X) (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ),
    Subsingleton (Over.mk g ⟶ Over.mk (fittingRankLocus F r).ι) ∧
      (Nonempty (Over.mk g ⟶ Over.mk (fittingRankLocus F r).ι) ↔
        SheafOfModules.IsFiniteLocallyFreeOfRank r
          (Modules.pullbackToScheme g F)))

/- Lemma 71.5.6 (4): The Fitting closed-subspace inclusion is of finite presentation for a finitely presented module. -/
@[stacks 0CZ9] #check (AlgebraicGeometry.AlgebraicSpace.fittingClosedSubspace_finitePresentation :
  ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFinitePresentation] (r : ℕ),
    FinitePresentation (fittingClosedSubspace F r).ι)

/- Lemma 71.5.6 (5): The Fitting open-complement inclusion is of finite presentation for a finitely presented module. -/
@[stacks 0CZ9] #check (AlgebraicGeometry.AlgebraicSpace.fittingOpenComplement_finitePresentation :
  ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFinitePresentation] (r : ℕ),
    FinitePresentation (fittingOpenComplement F r).ι)

/- Lemma 71.5.6 (6): The Fitting rank-locus inclusion is of finite presentation for a finitely presented module. -/
@[stacks 0CZ9] #check (AlgebraicGeometry.AlgebraicSpace.fittingRankLocus_finitePresentation :
  ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFinitePresentation] (r : ℕ),
    FinitePresentation (fittingRankLocus F r).ι)

