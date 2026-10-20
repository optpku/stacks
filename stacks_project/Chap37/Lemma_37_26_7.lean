/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.26.7: for a flat proper morphism of finite presentation, the locus in the
target where the fibres are geometrically reduced is open. -/
@[stacks 0C0E] #check
  (AlgebraicGeometry.Scheme.Hom.isOpen_geometricallyReducedFiberLocus :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsProper f] [FinitePresentation f],
      IsOpen f.geometricallyReducedFiberLocus)

end AlgebraicGeometry.Scheme.Hom
