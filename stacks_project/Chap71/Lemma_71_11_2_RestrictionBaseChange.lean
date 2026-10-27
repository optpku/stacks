/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.ExtensionBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.ExtensionMonoidal

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
universe u
variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T Z : Over S}

#check (AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme.extensionPullbackIso :
    ∀ (t : T ⟶ Z),
    Scheme.Modules.pullback t.left ⋙ extension T ≅
      extension Z ⋙ Modules.pullback (ofOverMap t))
