/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Whiskering
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe vC uC vD uD vE uE

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]
variable {F F' : C ⥤ D} {G G' : D ⥤ E}
variable (t : F ⟶ F') (s : G ⟶ G')

/- The source's Godement product is exactly Mathlib's horizontal composition
`NatTrans.hcomp`. For `t : F ⟶ F'` and `s : G ⟶ G'`, the source writes this operation as
`s ⋆ t`, while Mathlib writes it as `t ◫ s` because `F ⋙ G` denotes the composite from the
source of `F` to the target of `G`.

The source's equality between its two componentwise formulas is exactly
`Functor.whiskerLeft_comp_whiskerRight t s`. The companion lemmas
`Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight` and
`Functor.NatTrans.hcomp_eq_whiskerRight_comp_whiskerLeft` rewrite `t ◫ s` to either side of that
equality. Thus the operation and its naturality equation already have canonical owners at the
correct level; a local alias or a second notation would only obscure the API used by later files. -/

/- Definition 4.28.1 (1): horizontal composition of natural transformations is the canonical
operation `NatTrans.hcomp`, written `t ◫ s` for the transformation denoted `s ⋆ t` in the source.
-/
@[stacks 003E "horizontal composition of natural transformations"]
#check (NatTrans.hcomp t s : F ⋙ G ⟶ F' ⋙ G')

/- Definition 4.28.1 (2): the two whiskering formulas for `s ⋆ t = t ◫ s` agree, namely
`F.whiskerLeft s ≫ Functor.whiskerRight t G' =
  Functor.whiskerRight t G ≫ F'.whiskerLeft s`. -/
@[stacks 003E "equality of the two whiskering formulas for horizontal composition"]
#check (Functor.whiskerLeft_comp_whiskerRight t s :
  F.whiskerLeft s ≫ Functor.whiskerRight t G' =
    Functor.whiskerRight t G ≫ F'.whiskerLeft s)

end CategoryTheory
