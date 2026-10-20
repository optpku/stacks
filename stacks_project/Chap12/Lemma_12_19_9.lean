/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Subquotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject

open Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (A : FilteredObject C) {X Y : Subobject A.obj} (hXY : X ≤ Y)

/- Lemma 12.19.9 [0129] (1): the quotient filtration on `Y / X` agrees with the filtration induced
from `A / X`. -/
@[stacks 0129]
#check (Subobject.Subquotient.quotientFiltration_eq_induced A hXY :
  (A.subobject Y).filtration.quotient
      (Subobject.Subquotient.map A hXY).hom =
    (Subobject.Subquotient.object A hXY).filtration)

/- Lemma 12.19.9 [0129] (2): the canonical map from the induced filtration on `Y` to `Y / X` is
strict. -/
@[stacks 0129]
#check (Subobject.Subquotient.map_strict A hXY :
  Hom.Strict (Subobject.Subquotient.map A hXY))

end CategoryTheory.FilteredObject
