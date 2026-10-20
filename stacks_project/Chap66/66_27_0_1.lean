/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- 66.27.0.1: if `f : X ⟶ Y` is étale between algebraic spaces, then `X` is an object of
`Y_spaces,étale` and the sites are identified `X_spaces,étale = Y_spaces,étale / X` as
`spacesEtaleLocalizationEquivalence`. -/
@[stacks 04LY] #check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationEquivalence :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      spacesEtaleSite X ≌ Over (spacesEtaleSite.mk f))

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationFunctor.instIsContinuous :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      (spacesEtaleLocalizationFunctor f).IsContinuous
        (spacesEtaleTopology X) ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f)))

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationFunctor.instIsCocontinuous :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      (spacesEtaleLocalizationFunctor f).IsCocontinuous
        (spacesEtaleTopology X) ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f)))

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationFunctor.instIsMorphismOfSites :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      IsMorphismOfSites (spacesEtaleTopology X)
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f)) (spacesEtaleLocalizationFunctor f))

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationInverse.instIsContinuous :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      (spacesEtaleLocalizationInverse f).IsContinuous
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f)) (spacesEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationInverse.instIsCocontinuous :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      (spacesEtaleLocalizationInverse f).IsCocontinuous
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f)) (spacesEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleLocalizationInverse.instIsMorphismOfSites :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      IsMorphismOfSites ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
        (spacesEtaleTopology X) (spacesEtaleLocalizationInverse f))
