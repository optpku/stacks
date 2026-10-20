/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 26.3.1: open immersions of locally ringed spaces are the
canonical predicate, characterized by an open embedding and stalkwise
isomorphisms. -/
@[stacks 01HE] #check LocallyRingedSpace.IsOpenImmersion
#check LocallyRingedSpace.IsOpenImmersion.iff_isIso_stalkMap
