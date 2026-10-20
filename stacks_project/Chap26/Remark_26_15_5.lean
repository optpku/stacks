/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Representability.Zariski

@[expose] public section

open AlgebraicGeometry

/- Remark 26.15.5: a locally-ringed-space Zariski sheaf covered by
scheme-representable open subfunctors is represented by a scheme. -/
@[stacks 01JK]
#check LocallyRingedSpace.LocalRepresentability.ofSubfunctorCover

#check LocallyRingedSpace.LocalRepresentability.isRepresentableByScheme
#check LocallyRingedSpace.LocalRepresentability.isRepresentableByScheme_ofCharts
#check CategoryTheory.Functor.IsRepresentableByScheme.isRepresentable
