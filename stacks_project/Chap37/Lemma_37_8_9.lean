/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.FormallyEtale
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.8.9: A scheme morphism is étale if and only if it is locally of finite
presentation and formally étale. -/
@[stacks 02HM] #check
  (AlgebraicGeometry.Etale.iff_locallyOfFinitePresentation_and_formallyEtale :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Etale f ↔
        AlgebraicGeometry.LocallyOfFinitePresentation f ∧ AlgebraicGeometry.FormallyEtale f)
