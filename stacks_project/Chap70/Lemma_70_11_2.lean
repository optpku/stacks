/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral.Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.11.2: an integral morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, with `Y` quasi-compact and quasi-separated, presents `X` as a
directed inverse limit of algebraic spaces `X_i` over `Y` whose structure maps
`X_i ⟶ Y` are finite and of finite presentation. -/
@[stacks 09YA] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_integralFiniteApproximation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.IsIntegralHom f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      Nonempty (IntegralFiniteApproximation f))
