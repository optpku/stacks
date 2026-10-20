/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.OrdinalSmall
import StacksCheckRecall

/-!
# Definition 19.2.4

The reusable owner is `MorphismProperty.IsOrdinalSmall`.
-/

@[expose] public section

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]
variable (I : MorphismProperty C) (A : C) (α : Ordinal.{w})

/- Definition 19.2.4 recalls the canonical predicate for an object that is `α`-small relative
to a morphism property. -/
@[stacks 05NS] #check (MorphismProperty.IsOrdinalSmall I A α : Prop)

/- When a transition property does not contain identity morphisms, the reusable strict owner
quantifies only over transitions between distinct ordinal stages. -/
#check (MorphismProperty.IsStrictOrdinalSmall I A α : Prop)

/- For properties containing identities, the ordinary and strict owners agree. -/
#check @MorphismProperty.isOrdinalSmall_iff_isStrictOrdinalSmall
