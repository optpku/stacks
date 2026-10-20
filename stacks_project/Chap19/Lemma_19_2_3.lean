/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Presentable.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (A : Type (max u v)) [Finite A]
variable (B : J ⥤ Type (max u v))

/- Lemma 19.2.3 (05NR): for a finite set `A`, the canonical map
`colim_j Hom(A, B.obj j) → Hom(A, colim_j B.obj j)` is bijective. -/
@[stacks 05NR] #check
  (CategoryTheory.Types.colimitPost_bijective_of_finite A B :
    Function.Bijective (colimit.post B (coyoneda.obj (op A))))
