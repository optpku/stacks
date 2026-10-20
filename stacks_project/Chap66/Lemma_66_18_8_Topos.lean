/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos

import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.18.8 (3): transporting along Lemma 66.18.3 yields a morphism of topoi
`f_small : Sh(X_étale) ⟶ Sh(Y_étale)` compatible with composition. -/
@[stacks 03G2] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (X ⟶ Y) → MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X))

#check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoiComp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      (smallEtaleMorphismOfTopoi (f ≫ g)).inverseImage ≅
        ((smallEtaleMorphismOfTopoi g).comp (smallEtaleMorphismOfTopoi f)).inverseImage)

