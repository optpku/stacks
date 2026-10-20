/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.CompleteIntersection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry RelativeDerivation

universe u

/- Lemma 53.19.15: a locally algebraic, equidimensional `k`-scheme of dimension one has
at-worst-nodal singularities exactly when it is a local complete intersection over `k` and
the closed subscheme cut out by the first Fitting ideal of `Ω[X.hom.toShHom]` is unramified
over `k`. -/
@[stacks 0C4E] #check
  (AlgebraicGeometry.SchemeOverField.atWorstNodal_iff_localCompleteIntersection_and_unramified_firstFitting :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
      [EquidimensionalSpace X.left] (h_dimension : topologicalKrullDim X.left = 1),
    SchemeOverField.atWorstNodal X ↔
      IsLocalCompleteIntersectionOver k X.hom ∧
        Unramified ((Scheme.fittingIdealSheaf (Ω[X.hom.toShHom]) 1).subschemeι ≫ X.hom))
