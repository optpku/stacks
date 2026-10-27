/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Triple
import StacksCheckRecall

/-!
# Remark 98.27.3

This remark gives a heuristic analytic interpretation of the compatibility
condition for a contraction triple. The analytic category and analytification
functor in the source are explicitly fictitious; the formal compatibility
notion is the existing algebraic `IsCompatible` predicate.
-/

@[expose] public section

open CategoryTheory

universe u

/- Remark 98.27.3 -/
@[stacks 0GID] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.IsCompatible :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : AlgebraicGeometry.AlgebraicSpace.ContractionSituation S)
      (V : CategoryTheory.Over S) [AlgebraicGeometry.IsLocallyNoetherian V.left]
      (Z : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.ofOver V).Points)
      (u' : (AlgebraicGeometry.AlgebraicSpace.ofOver V).openComplementAlong Z ⟶
        σ.openComplement)
      (hatx : (AlgebraicGeometry.AlgebraicSpace.ofOver V).completionAlong Z ⟶ σ.W),
      Prop)
