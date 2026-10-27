/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.ExtensionComposition

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
universe u
variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T Z : Over S}

#check (AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme.extensionCompositePullbackIso :
    ∀ (g : ofOver Z ⟶ X) (t : T ⟶ Z)
    (M : X.Modules) [M.IsQuasicoherent],
    (extension T).obj ((Scheme.Modules.pullback t.left).obj
      ((Modules.restrictToScheme Z).obj ((Modules.pullback g).obj M))) ≅
        (Modules.pullback (ofOverMap t ≫ g)).obj M)
