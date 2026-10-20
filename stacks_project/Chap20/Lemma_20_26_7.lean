/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.KFlat.ShortExact
import StacksCheckRecall

@[expose] public section

/- Lemma 20.26.7: if the third term of a short exact sequence of complexes of `𝒪_X`-modules is
termwise flat, K-flatness is a two-out-of-three property.  The reusable owners are the canonical
`obj₁/₂/₃_of_shortExact` declarations; the `_of_flat` declarations are the source-facing bridge. -/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}
variable {S : ShortComplex (CochainComplex (Modules X) ℤ)}

/- Lemma 20.26.7 (1): the third complex is K-flat when the first two are K-flat. -/
@[stacks 0G6U "(1)"]
#check @IsKFlat.obj₃_of_shortExact_of_flat

/- Lemma 20.26.7 (2): the middle complex is K-flat when the outer two are K-flat. -/
@[stacks 0G6U "(2)"]
#check @IsKFlat.obj₂_of_shortExact_of_flat

/- Lemma 20.26.7 (3): the first complex is K-flat when the last two are K-flat. -/
@[stacks 0G6U "(3)"]
#check @IsKFlat.obj₁_of_shortExact_of_flat

/- Canonical termwise-flat owners used by the source-facing bridges. -/
#check @IsKFlat.obj₃_of_shortExact
#check @IsKFlat.obj₂_of_shortExact
#check @IsKFlat.obj₁_of_shortExact

end AlgebraicGeometry.RingedSpace.CochainComplex

end
