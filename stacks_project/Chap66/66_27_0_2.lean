/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RingedLocalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- 66.27.0.2: if `f : X ⟶ Y` is étale between algebraic spaces, then `X` is an object of
`Y_spaces,étale` and the ringed sites are identified
`(X_spaces,étale, 𝒪_X) = (Y_spaces,étale / X, 𝒪_Y |_{Y_spaces,étale / X})` as
`spacesEtaleLocalizationIso`. -/
@[stacks 04LZ] #check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationIso :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Etale f],
    CategoryTheory.RingedSiteMap.Iso
      (AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology X)
      (AlgebraicGeometry.AlgebraicSpace.spacesStructureSheaf X)
      ((AlgebraicGeometry.AlgebraicSpace.spacesEtaleTopology Y).over
        (AlgebraicGeometry.AlgebraicSpace.spacesEtaleSite.mk f))
      ((AlgebraicGeometry.AlgebraicSpace.spacesStructureSheaf Y).over
        (AlgebraicGeometry.AlgebraicSpace.spacesEtaleSite.mk f)))
