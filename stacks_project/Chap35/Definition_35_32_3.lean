/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal
import StacksCheckRecall

universe u

/- Definition 35.32.3: a property of scheme morphisms is étale local on source-and-target
when it is stable under étale precomposition and base change and satisfies pointwise locality
for commutative squares with étale vertical morphisms. -/
@[stacks 04QZ] #check (AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget :
  CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u} → Prop)
