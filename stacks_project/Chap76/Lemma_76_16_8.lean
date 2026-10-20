/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Etale.FormallyEtale
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 76.16.8: A morphism of algebraic spaces is étale if and only if it is
locally of finite presentation and formally étale. -/
@[stacks 0616] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.iff_locallyOfFinitePresentation_and_formallyEtale :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.Etale f ↔
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f ∧
          AlgebraicGeometry.AlgebraicSpace.FormallyEtale f)
