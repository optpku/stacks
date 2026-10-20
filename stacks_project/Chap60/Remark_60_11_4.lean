/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianSection
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology D) (p : C ⥤ D) [IsStack.OnSite J p]

/- Remark 60.11.4: in the small crystalline site and in the big crystalline site,
a crystal in objects of `C` is a section functor whose composite with `p` is the
identity and whose image morphisms are strongly cartesian. -/
@[stacks 07IV] #check
  (CategoryTheory.Functor.IsCartesianSection p : (D ⥤ C) → Prop)

end Functor
end CategoryTheory
