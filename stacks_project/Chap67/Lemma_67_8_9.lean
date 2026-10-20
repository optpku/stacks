/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiCompact.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.8.9: if `f ≫ g` is quasi-compact and `g` is quasi-separated, then
`f` is quasi-compact. -/
@[stacks 03KS] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiCompact (f ≫ g)] [QuasiSeparated g],
      QuasiCompact f)
