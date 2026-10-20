/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Submersive
import StacksCheckRecall

open CategoryTheory

universe u

/- Theorem 41.10.3: a faithfully flat quasi-compact morphism is a quotient map for the
Zariski topology. -/
@[stacks 0256] #check
  (AlgebraicGeometry.instSubmersiveOfFlatOfQuasiCompactOfSurjective :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.Surjective f],
      AlgebraicGeometry.Submersive f)

#check
  (AlgebraicGeometry.Scheme.Hom.isQuotientMap :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Submersive f],
      Topology.IsQuotientMap f)
