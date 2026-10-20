/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenRestriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.3.5: a morphism carrying `U` into `V` has a unique restriction
between the corresponding open subspaces. -/
#check LocallyRingedSpace.Hom.restrictToOpen
#check LocallyRingedSpace.Hom.restrictToOpen.fac
#check LocallyRingedSpace.Hom.restrictToOpen.isOpenRestriction
#check LocallyRingedSpace.Hom.restrictToOpen.unique
#check LocallyRingedSpace.Hom.restrictToOpenImmersion
#check LocallyRingedSpace.Hom.restrictToOpenImmersion.fac
#check LocallyRingedSpace.Hom.restrictToOpenImmersion.unique
#check LocallyRingedSpace.Hom.restrictToOpen.id
#check LocallyRingedSpace.Hom.restrictToOpen.comp
#check LocallyRingedSpace.Hom.restrictToPreimageOpen
#check LocallyRingedSpace.Hom.restrictToPreimageOpen.fac
#check LocallyRingedSpace.Hom.restrictToPreimageOpen.isOpenRestriction
#check LocallyRingedSpace.Hom.restrictToPreimageOpen.unique
#check LocallyRingedSpace.Hom.restrictToPreimageOpen.comp
#check LocallyRingedSpace.Hom.preimageOpen.id
#check LocallyRingedSpace.Hom.preimageOpen.comp
@[stacks 01HI] #check LocallyRingedSpace.Hom.restrictToOpen.existsUnique
#check LocallyRingedSpace.Hom.IsOpenRestriction
#check LocallyRingedSpace.Hom.IsOpenRestriction.eq
#check LocallyRingedSpace.Hom.IsOpenRestriction.comp
#check LocallyRingedSpace.Hom.restrictToPreimageOpen.existsUnique
