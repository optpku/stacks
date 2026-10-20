/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

/-!
# Lemma 18.27.7

Both the presheaf and sheaf assertions are specializations of the same closed-monoidal fact:
left tensoring is a left adjoint, hence preserves all colimits.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (A : C) [Closed A]

/- Lemma 18.27.7 (1) (03EP): the presheaf-module tensor functor preserves all colimits. -/
@[stacks 03EP "(1)"]
#check ((ihom.adjunction A).leftAdjoint_preservesColimits :
  Limits.PreservesColimits (tensorLeft A))

/- Lemma 18.27.7 (2) (03EP): the sheaf-module tensor functor has the same generic owner. -/
@[stacks 03EP "(2)"]
#check ((ihom.adjunction A).leftAdjoint_preservesColimits :
  Limits.PreservesColimits (tensorLeft A))
