/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Compactification

/-!
# Compactifications of algebraic spaces

The compactification predicate is owned by the reusable algebraic-space
library; this file preserves its source-facing compatibility entry.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.HasCompactification :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B), Prop)

end AlgebraicGeometry.AlgebraicSpace
