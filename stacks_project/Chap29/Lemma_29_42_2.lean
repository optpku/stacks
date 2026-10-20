/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DenseRange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.42.2 (1): restricted valuative existence and uniqueness along a quasi-compact
morphism with dense range implies universal closedness. -/
@[stacks 0894] #check
  (AlgebraicGeometry.ValuativeCriterion.Along.universallyClosed :
    ∀ {U X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiCompact h],
      DenseRange h →
        AlgebraicGeometry.ValuativeCriterion.Along.ExistsUnique h f →
          AlgebraicGeometry.UniversallyClosed f)

/- Lemma 29.42.2 (2): under the same hypotheses, a quasi-separated morphism is separated. -/
@[stacks 0894] #check
  (AlgebraicGeometry.ValuativeCriterion.Along.isSeparated :
    ∀ {U X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiCompact h]
      [AlgebraicGeometry.QuasiSeparated f],
      DenseRange h →
        AlgebraicGeometry.ValuativeCriterion.Along.ExistsUnique h f →
          AlgebraicGeometry.IsSeparated f)
