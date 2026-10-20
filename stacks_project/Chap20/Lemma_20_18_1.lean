/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange.Point
import StacksCheckRecall

@[expose] public section

/- [stacks 09V5] Lemma 20.18.1: if `f` is closed and separated and the fibre over `y` is
quasi-compact, the bounded-below point-inclusion base-change map is an isomorphism. -/

open AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace.Hom.BoundedBaseChange

@[stacks 09V5] #check @pointInclusionCommSq
#check @pointInclusionMap_isIso
#check @isIso_of_isMap
#check @source
#check @target
#check @app
#check @IsMapAt

end AlgebraicGeometry.RingedSpace.Hom.BoundedBaseChange
