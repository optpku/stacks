/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion.Locality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.4.2: closed immersion of locally ringed spaces is local on the
target. -/
@[stacks 01HL] #check LocallyRingedSpace.IsClosedImmersion.iff_exists_openCover
#check LocallyRingedSpace.IsClosedImmersion.iff_of_isOpenCover
#check LocallyRingedSpace.IsClosedImmersion.of_isOpenCover
#check LocallyRingedSpace.IsClosedImmersion.restrict
#check LocallyRingedSpace.IsClosedImmersion.restrict_of_isOpenRestriction

/- The earlier existential presentation is a thin view of the canonical inverse-image
restriction property. -/
#check LocallyRingedSpace.IsClosedImmersion.OnOpen
#check LocallyRingedSpace.IsClosedImmersion.onOpen_iff
