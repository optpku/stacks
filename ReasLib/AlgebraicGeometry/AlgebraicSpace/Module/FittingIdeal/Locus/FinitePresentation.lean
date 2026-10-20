/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Fitting closed-subspace inclusion is of finite presentation for a finitely presented module. -/
theorem fittingClosedSubspace_finitePresentation {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFinitePresentation] (r : ℕ) :
    FinitePresentation (fittingClosedSubspace F r).ι :=
  sorry

/-- The Fitting open-complement inclusion is of finite presentation for a finitely presented module. -/
theorem fittingOpenComplement_finitePresentation {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFinitePresentation] (r : ℕ) :
    FinitePresentation (fittingOpenComplement F r).ι :=
  sorry

/-- The Fitting rank-locus inclusion is of finite presentation for a finitely presented module. -/
theorem fittingRankLocus_finitePresentation {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFinitePresentation] (r : ℕ) :
    FinitePresentation (fittingRankLocus F r).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
