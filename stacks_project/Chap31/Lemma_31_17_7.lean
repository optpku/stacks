/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.FunctionField
import StacksCheckRecall

/-!
# Lemma 31.17.7

Norms from finite extensions of function fields.

@stack 0BD3
-/

@[expose] public section

universe u

/- Lemma 31.17.7: A finite surjective morphism between integral schemes with normal target
admits a norm whose degree is the degree of the induced extension of function fields. -/
@[stacks 0BD3] #check
  (AlgebraicGeometry.Scheme.exists_norm_of_isFinite_of_surjective_of_isNormal :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ Y)
        [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
        [AlgebraicGeometry.IsFinite π] [AlgebraicGeometry.Surjective π],
      Y.isNormal →
        ∃ N : AlgebraicGeometry.Scheme.FiniteMorphismNorm π,
          AlgebraicGeometry.Scheme.IsFiniteMorphismNorm π π.inducedFunctionFieldDegree N)
