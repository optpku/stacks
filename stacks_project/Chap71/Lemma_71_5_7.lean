/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Locus.Flat
import StacksCheckRecall

/-!
# Lemma 71.5.7

The coproduct of the Fitting rank loci of a finitely presented module on an
algebraic space represents the functor on schemes over `X` that is a singleton
exactly when the pulled-back module is flat. The restriction to each rank
locus is finite locally free of that rank, and both the rank-locus inclusions
and the coproduct structure map are of finite presentation.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.5.7 (1): the coproduct of the Fitting rank loci represents the
functor on `Sch/X` that is a singleton exactly when the pulled-back module is
flat. -/
@[stacks 0CZA] #check
  (AlgebraicGeometry.AlgebraicSpace.fittingFlatLocus_nonempty_over_hom_iff_isFlat :
    ∀
    {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (g : ofOver T ⟶ X) (F : X.Modules) [F.IsFinitePresentation],
    Subsingleton (Over.mk g ⟶ Over.mk (fittingFlatLocusι F)) ∧
      (Nonempty (Over.mk g ⟶ Over.mk (fittingFlatLocusι F)) ↔
        SheafOfModules.IsFlat (Modules.pullbackToScheme g F)))

/- Lemma 71.5.7 (2): the restriction of a finitely presented module to its
rank-`r` Fitting locus is finite locally free of rank `r`. -/
@[stacks 0CZA] #check
  (AlgebraicGeometry.AlgebraicSpace.fittingRankLocus_pullback_isFiniteLocallyFreeOfRank :
    ∀
    {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFinitePresentation] (r : ℕ),
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Modules.pullback (fittingRankLocus F r).ι).obj F))

/- Lemma 71.5.7 (3): if `F` is of finite presentation, then each rank-locus
immersion `X_r ⟶ X` is of finite presentation. -/
@[stacks 0CZA] #check
  (AlgebraicGeometry.AlgebraicSpace.fittingRankLocus_finitePresentation :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
      [F.IsFinitePresentation] (r : ℕ),
      FinitePresentation (fittingRankLocus F r).ι)

/- Lemma 71.5.7 (4): the structure morphism from the coproduct of the Fitting
rank loci to the ambient algebraic space is of finite presentation. -/
@[stacks 0CZA] #check
  (AlgebraicGeometry.AlgebraicSpace.fittingFlatLocus_finitePresentation :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
      [F.IsFinitePresentation],
      FinitePresentation (fittingFlatLocusι F))

end AlgebraicGeometry.AlgebraicSpace
