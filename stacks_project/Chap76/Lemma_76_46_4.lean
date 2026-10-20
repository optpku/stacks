/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent.FinitePresentation
import StacksCheckRecall

/-!
# Pseudo-coherent morphisms of algebraic spaces are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 76.46.4: A pseudo-coherent morphism is locally of finite presentation. -/
@[stacks 06BU] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_pseudoCoherent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.PseudoCoherent f],
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f)
