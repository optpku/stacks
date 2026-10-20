/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.TorIndependentOver

/- Lemma 36.22.4: flat base change preserves Tor independence of two schemes over a
common base. -/
@[stacks 0FXW] #check
  (AlgebraicGeometry.Scheme.TorIndependentOver.pullback :
    ∀ {S S' : Scheme.{u}} {X Y : Over S} (h : TorIndependentOver X Y)
      (f : S' ⟶ S) [Flat f],
      TorIndependentOver ((Over.pullback f).obj X) ((Over.pullback f).obj Y))

end AlgebraicGeometry.Scheme.TorIndependentOver
