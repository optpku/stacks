/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Cohomology.Lichtenbaum

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/- Theorem 48.34.2 -/
@[stacks 0G5F]
#check (AlgebraicGeometry.SchemeOverField.topCohomology_isZero_tfae :
  ∀ {k : Type _} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.Algebraic X] [IsSeparated X.hom] [Nonempty X.left]
    (d : ℕ) (h_dimension : topologicalKrullDim X.left = d),
    List.TFAE [
      ∀ F : X.left.Modules,
        F.IsCoherent → IsZero (AlgebraicGeometry.Scheme.Modules.cohomology F d),
      ∀ F : X.left.Modules,
        F.IsQuasicoherent → IsZero (AlgebraicGeometry.Scheme.Modules.cohomology F d),
      ∀ Z : irreducibleComponents X.left,
        topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = d →
          ¬ IsProper (X.left.irreducibleComponentSubschemeι Z ≫ X.hom)])
