/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Lifting
import StacksCheckRecall

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Definition 37.11.1: a scheme morphism is formally smooth if and only if it has the
lifting property against every affine first-order thickening of schemes. -/
@[stacks 02H0] #check
  (AlgebraicGeometry.FormallySmooth.iff_hasLiftingProperty :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      FormallySmooth f ↔
        ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
          [IsFirstOrderThickening i], HasLiftingProperty i f)

end AlgebraicGeometry
