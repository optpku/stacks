/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v w

variable (R : Type u) [CommRing R] (C : Type v)

/- Definition 22.5.3 (09JQ): the homotopy category of a differential graded category is
canonically represented by `DifferentialGradedCategory.K`; its morphisms are homotopy classes
of closed degree-zero morphisms. Taking `C` to be the DG category of right modules over a
cochain DGA gives `K(Mod_(A,d))`. -/
@[stacks 09JQ] #check (K R C : Type v)

variable [DifferentialGradedCategory.{u, v, w} R C]

/- The canonical functor from closed degree-zero morphisms to their homotopy classes. -/
#check (Comp.inKFunctor : Comp R C ⥤ K R C)
