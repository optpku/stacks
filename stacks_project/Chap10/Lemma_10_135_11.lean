/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.OverField.FieldExtension
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.135.11

@stack 00SJ
-/

/- Lemma 10.135.11, tag `00SJ`: local complete intersections of finite type
over a field are preserved and reflected by extension of the base field. -/
@[stacks 00SJ]
#check @IsLocalCompleteIntersection.iff_tensorProduct_fieldExtension
