/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RepresentablePullback

import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.18.8 (4): if `f` is representable, then `f_small` comes from the morphism of
small étale sites given by `V ↦ X ×_Y V`. -/
@[stacks 03G2] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtalePullback_isMorphismOfSites :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f),
      IsMorphismOfSites (smallEtaleTopology Y) (smallEtaleTopology X)
        (smallEtalePullback f hf))

#check
  (AlgebraicGeometry.AlgebraicSpace.smallEtalePullbackCompInclusion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f),
      smallEtalePullback f hf ⋙ smallEtaleToSpaces X ≅
        smallEtaleToSpaces Y ⋙ spacesEtalePullback f)

#check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoiRepresentableInverseImageIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f),
      (smallEtaleMorphismOfTopoi f).inverseImage ≅
        (smallEtalePullback f hf).sheafPullback (Type (u + 1))
          (smallEtaleTopology Y) (smallEtaleTopology X))
