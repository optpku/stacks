/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Syntomic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 48.25.5: A syntomic morphism is Gorenstein. Equivalently, a flat local
complete-intersection morphism is Gorenstein. -/
@[stacks 0C15] #check (AlgebraicGeometry.instGorensteinOfSyntomic :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.Syntomic f], AlgebraicGeometry.Gorenstein f)

end AlgebraicGeometry
