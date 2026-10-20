/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Limits

universe u

variable {S : Scheme.{u}} {X Y : Over S} (a b : X ⟶ Y)

/- Lemma 26.21.5: the equalizer is the largest locally closed subscheme of `X` on which `a`
and `b` agree. -/
@[stacks 01KM] #check equalizer.ι a b
#check equalizer.condition a b
@[stacks 01KM] #check equalizerIsEqualizer a b
@[stacks 01KM] #check (inferInstance : IsImmersion (equalizer.ι a b).left)

section

variable [QuasiSeparated Y.hom]

@[stacks 01KM] #check equalizer_quasiCompact a b

end

section

variable [IsSeparated Y.hom]

@[stacks 01KM] #check (inferInstance : IsClosedImmersion (equalizer.ι a b).left)
#check isClosedImmersion_equalizer_ι_left

end

end AlgebraicGeometry
