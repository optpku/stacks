/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
import StacksCheckRecall

/-!
# Étale morphisms of algebraic spaces are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.39.8: An étale morphism of algebraic spaces is locally of finite presentation. -/
@[stacks 0468] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_etale :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [AlgebraicGeometry.AlgebraicSpace.Etale f] →
        AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f)
