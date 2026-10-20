/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Leray
import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.16.7: Leray Acyclicity

The reusable computation criterion is owned by the neutral bounded-derived acyclicity API.  This
source entry retains the stronger Stacks hypothesis that the right-derived indexing diagram is
essentially constant at the chosen complex; the canonical bridge supplies the weaker pointwise
existence assumption used by the reusable theorem.
-/

open CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]
  (K : HomotopyCategory.Plus A)
  [Functor.RightDerived.DefinedAt F.toBoundedBelowDerived
    (HomotopyCategory.Plus.quasiIso A) K]
  (hK : Functor.RightAcyclic.Bounded.Termwise F K)

/- Lemma 13.16.7 (015E): a bounded-below complex of right `F`-acyclic objects computes its
right-derived value whenever that value is source-defined at the complex. -/
@[stacks 015E] #check
  (Functor.RightAcyclic.Bounded.Termwise.computesAt hK :
    Functor.RightDerived.ComputesAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K)

end CategoryTheory
