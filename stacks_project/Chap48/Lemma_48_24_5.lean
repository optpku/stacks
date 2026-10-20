/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 48.24.5: If `f : Y ⟶ X` is a local complete intersection morphism and
`X` is Gorenstein, then `Y` is Gorenstein. -/
@[stacks 0BVA] #check
  (AlgebraicGeometry.Scheme.gorenstein_of_isLocalCompleteIntersection :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [LocallyOfType RingHom.IsLocalCompleteIntersection f] [Gorenstein X],
      Gorenstein Y)

end AlgebraicGeometry.Scheme
