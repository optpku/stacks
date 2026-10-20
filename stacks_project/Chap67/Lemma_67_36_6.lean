/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.Flat
import StacksCheckRecall

/-!
# Syntomic morphisms of algebraic spaces are flat
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.36.6: A syntomic morphism is flat. -/
@[stacks 0DEZ] #check (AlgebraicGeometry.AlgebraicSpace.Syntomic.flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Syntomic f], Flat f)

end AlgebraicGeometry.AlgebraicSpace
