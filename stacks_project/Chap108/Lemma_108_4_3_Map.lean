/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.StructureMorphism

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The structure morphism of the stack of coherent sheaves. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.forget :
  {S : Scheme.{u}} → {X B : AlgebraicSpace S} →
    (f : X ⟶ B) → [FinitePresentation f] →
      AlgebraicGeometry.AlgebraicSpace.CohStack.toGroupoids f ⟶
        AlgebraicGeometry.GroupScheme.Classifying.toGroupoids B)
