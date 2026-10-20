/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.RelativeAmple
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.36.3: if the quasi-compact and quasi-separated scheme `Y` has the resolution
property and some module on `X` is relatively ample over `f : X ⟶ Y`, then `X` has the
resolution property. -/
@[stacks 0FDD] #check
  (AlgebraicGeometry.Scheme.hasResolutionProperty_of_exists_relativelyAmple :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y]
      [QuasiSeparatedSpace Y], AlgebraicGeometry.Scheme.HasResolutionProperty Y →
        (∃ L : X.Modules, AlgebraicGeometry.RelativelyAmple f L) →
          AlgebraicGeometry.Scheme.HasResolutionProperty X)
