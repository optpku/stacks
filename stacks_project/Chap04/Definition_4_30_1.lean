/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

variable (B : Type u) [Bicategory.{w, v} B]

/-
The source needs the strict `2`-category structure together with invertibility of every
`2`-morphism. The verified owners `Bicategory.Strict` and `Bicategory.IsLocallyGroupoid` match
these two parts, while `IsGroupoid.all_isIso` is only the derived pointwise instance and `Pith` is
a construction of examples. Keeping the two canonical assumptions avoids a redundant combined
class. The only generalization is that `IsLocallyGroupoid` also applies to non-strict
bicategories; paired here with `Strict`, it recovers exactly the source notion and leaves both
typeclasses directly reusable by downstream bicategory APIs.
-/

/- Companion recall: `Bicategory.Strict` supplies the strict `2`-category condition inherited
from Definition 4.29.1. -/
#check Bicategory.Strict

/- Definition 4.30.1: a strict `(2,1)`-category is canonically a type `B` with assumptions
`[Bicategory B] [Bicategory.Strict B] [Bicategory.IsLocallyGroupoid B]`; the last assumption says
that every hom-category is a groupoid, hence every `2`-morphism is an isomorphism. -/
@[stacks 003I "locally groupoidal condition: every 2-morphism is invertible"]
#check (Bicategory.IsLocallyGroupoid B : Prop)

end CategoryTheory
