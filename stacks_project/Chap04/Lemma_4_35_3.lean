/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.StronglyCartesianSubcategory

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (p : S ⥤ C) [p.IsFibered]

/- Lemma 4.35.3: if `p : S ⥤ C` is fibred, then restricting `p` to the wide subcategory of
strongly cartesian morphisms gives a category fibred in groupoids. -/
@[stacks 03WQ]
#check (Functor.IsStronglyCartesian.projectionInGroupoids p :
  Functor.IsFibered.InGroupoids
    (Functor.IsStronglyCartesian.projection p))

end CategoryTheory
