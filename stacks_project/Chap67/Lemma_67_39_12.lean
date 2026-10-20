/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Etale.Unramified
import StacksCheckRecall

/-!
# Locally finitely presented, flat, unramified morphisms of algebraic spaces
are étale
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.39.12: A locally finitely presented, flat, unramified morphism of
algebraic spaces is étale. -/
@[stacks 06LU] #check
  (AlgebraicGeometry.AlgebraicSpace.etale_of_locallyOfFinitePresentation_of_flat_of_unramified :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFinitePresentation f] [Flat f] [Unramified f], Etale f)

end AlgebraicGeometry.AlgebraicSpace
