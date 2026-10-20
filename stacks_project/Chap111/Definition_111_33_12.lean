/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Integral
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Definition 111.33.12: a scheme `X` is integral if and only if it is nonempty and
every nonempty affine open has a domain of sections. -/
@[stacks 028Y] #check
  (AlgebraicGeometry.IsIntegral.iff_forall_affineOpen :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.IsIntegral X ↔
        Nonempty X ∧
          ∀ U : X.Opens,
            AlgebraicGeometry.IsAffineOpen U →
              Nonempty U → IsDomain Γ(X, U))
