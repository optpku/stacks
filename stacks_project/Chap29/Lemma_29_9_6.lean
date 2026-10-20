/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.9.6: a quasi-compact composite with a surjective left factor has a quasi-compact
right factor. -/
@[stacks 04ZD] #check
  (AlgebraicGeometry.QuasiCompact.of_comp_surjective :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}}
      {f : X ⟶ Y} {g : Y ⟶ Z} [AlgebraicGeometry.Surjective f],
      AlgebraicGeometry.QuasiCompact (f ≫ g) → AlgebraicGeometry.QuasiCompact g)
