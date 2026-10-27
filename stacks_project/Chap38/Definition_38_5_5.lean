/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissage.StandardShrinking
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 38.5.5: A standard shrinking of a complete dévissage is a
compatible family of standard-open one-step shrinkings over a common base,
together with the resulting complete dévissage of the restricted module. The ranks
are unchanged and all comparison maps are the canonical restrictions. -/
@[stacks 05HL]
#check (AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint.StandardShrinking :
  {S X : Scheme.{u}} → {f : X ⟶ S} → {F : X.Modules} →
    [LocallyOfFiniteType f] → [F.IsQuasicoherent] → [F.IsFiniteType] →
      {x : X} → AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint f F x →
        Type (u + 1))

#check AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint.StandardShrinking.restriction_spec
