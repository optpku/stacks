/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Regular
import StacksCheckRecall

@[expose] public section

universe u

/-
Lemma 28.9.4: A regular scheme is normal.
-/
@[stacks 0569] #check
  (AlgebraicGeometry.Scheme.Regular.isNormal :
    {X : AlgebraicGeometry.Scheme.{u}} →
      AlgebraicGeometry.Scheme.Regular X → AlgebraicGeometry.Scheme.isNormal X)

end
