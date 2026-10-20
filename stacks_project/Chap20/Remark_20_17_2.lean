/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

/- [stacks 02N8] Remark 20.17.2: for a commutative square of ringed spaces, without flatness or
boundedness assumptions, the derived base-change map has source `R(f)_* ⋙ L(g)^*` and target
`L(g')^* ⋙ R(f')_*`, with its component at `K` characterized by the adjunction mate equation. -/

namespace AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange

#check @source
#check @target
#check @pullbackIsoOfCompIso
#check @map
#check @app
#check @IsMapAt
#check @map_isMapAt
#check @IsMapAt.eq_app
#check @IsMap
#check @map_isMap
#check @IsMap.eq_map

end AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange
