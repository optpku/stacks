/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.2.2: an isomorphism on the underlying sheafed spaces determines
an isomorphism of locally ringed spaces. -/
@[stacks 01HC] #check
  (inferInstance : LocallyRingedSpace.forgetToSheafedSpace.ReflectsIsomorphisms)
#check LocallyRingedSpace.is_sheafedSpace_iso
#check LocallyRingedSpace.isoOfSheafedSpaceIso
