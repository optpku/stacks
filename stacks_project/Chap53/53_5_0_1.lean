/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- 53.5.0.1: For a finite locally free module `E` of constant rank `n` on a proper
scheme `X` of dimension at most one over a field,
`deg(E) = χ(X, E) - n * χ(X, 𝒪_X)`. -/
@[stacks 0BRX] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_def :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (hdim : topologicalKrullDim X ≤ 1) (ℰ : X.Modules) (n : ℕ)
      [IsFiniteLocallyFreeOfRank n ℰ],
      let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      let _ : ℰ.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank n ℰ
      curveDegree f hdim ℰ n =
        Scheme.Hom.eulerCharacteristic f ℰ -
          (n : ℤ) * Scheme.Hom.eulerCharacteristic f
            (SheafOfModules.unit X.ringCatSheaf : X.Modules))
