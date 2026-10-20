/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Cover

@[expose] public section

/-!
# Projective Object-Property Covers

This leaf exposes the zero-object and epimorphic-cover consequences of
projective objects independently of cochain complexes and abelian structure.
Resolution constructions can use these canonical instances without local
bridges.
-/

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Stacks 0646: in a category with a zero object, the projective-object
property contains a zero object. -/
@[stacks 0646]
instance isProjective_containsZero [HasZeroObject C] :
    (isProjective C).ContainsZero := sorry

/-- Stacks 0646: whenever a category has enough projectives, every object has
an epimorphic cover from a projective object. -/
@[stacks 0646]
instance isProjective_hasEpiCover [EnoughProjectives C] :
    HasEpiCover (isProjective C) := sorry

end CategoryTheory
