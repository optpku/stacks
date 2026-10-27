/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.ObjectPullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 96.11.3: a sheaf of modules on a category fibred in groupoids over the
big fppf site is quasi-coherent exactly when its pullback to the big fppf site of
the scheme underlying every object is quasi-coherent. -/
@[stacks 06WI] #check (AlgebraicGeometry.GroupoidsOver.isQuasicoherent_iff_objectPullback :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    (F : SheafOfModules.{u} (GroupoidsOver.structureSheaf X)),
    F.IsQuasicoherent ↔
      ∀ x : X.total, ((GroupoidsOver.objectPullback X x).obj F).IsQuasicoherent)
