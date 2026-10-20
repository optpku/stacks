/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Affine.TopologicalInvariance
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

/- Remark 59.45.3: in the situation of Theorem 59.45.2, `V ↦ V_X` induces an
equivalence between étale morphisms `V ⟶ Y` with `V` affine and étale morphisms
`U ⟶ X` with `U` affine. -/
@[stacks 05YX] #check
  (AlgebraicGeometry.Scheme.AffineEtale.pullback_isEquivalence_of_universalHomeomorphism :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f],
      (AlgebraicGeometry.Scheme.AffineEtale.pullback f).IsEquivalence)
