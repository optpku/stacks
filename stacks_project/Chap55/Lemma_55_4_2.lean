/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Picard

@[expose] public section

namespace NumericalType

variable (T : NumericalType)

/- The Picard group of a numerical type is finitely generated as an abelian group. -/
#check
  (Module.Finite.quotient ℤ (LinearMap.range T.picardMap) :
    Module.Finite ℤ T.PicardGroup)

/- Lemma 55.4.2: the Picard group of a numerical type is finitely generated
and has rank one; the preceding companion check supplies finite generation. -/
@[stacks 0C7I] #check (NumericalType.picardGroup_finrank : ∀ T : NumericalType, Module.finrank ℤ T.PicardGroup = 1)

end NumericalType
