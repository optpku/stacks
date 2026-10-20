/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithfulness in pseudopullbacks of stacks in groupoids

This file records the faithfulness descent property of an arbitrary bilimit pseudopullback.
It depends only on the stack-in-groupoids ambient API, not on the setoid closure of the canonical
two-fibre-product model.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids

namespace PseudoPullback

variable {X Y Z : StackOver.Groupoids J}

/-- In a bilimit pseudopullback of stacks in groupoids, local essential surjectivity of the left
cospan leg and faithfulness of the first projection imply faithfulness of the right cospan leg. -/
@[stacks 06DV]
theorem rightFaithful
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit]
    (hF : Hom.LocallyEssentiallySurjective F)
    [(Hom.toBasedFunctor P.fst).Faithful] :
    (Hom.toBasedFunctor G).Faithful := sorry

/-- Explicit-proof form of `rightFaithful`, exposing projection faithfulness as an ordinary term
for callers that do not want to install a temporary instance. -/
@[stacks 06DV "explicit right-faithfulness bridge"]
theorem rightFaithful_of_faithful
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit]
    (hF : Hom.LocallyEssentiallySurjective F)
    (hP : (Hom.toBasedFunctor P.fst).Faithful) :
    (Hom.toBasedFunctor G).Faithful := sorry

/-- The symmetric faithfulness descent statement: local essential surjectivity of the right
cospan leg and faithfulness of the second projection imply faithfulness of the left cospan leg. -/
@[stacks 06DV "symmetric"]
theorem leftFaithful
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit]
    (hG : Hom.LocallyEssentiallySurjective G)
    [(Hom.toBasedFunctor P.snd).Faithful] :
    (Hom.toBasedFunctor F).Faithful := sorry

/-- Explicit-proof form of `leftFaithful`, symmetric to `rightFaithful_of_faithful`. -/
@[stacks 06DV "explicit left-faithfulness bridge"]
theorem leftFaithful_of_faithful
    {F : X ⟶ Z} {G : Y ⟶ Z}
    (P : Bicategory.PseudoPullbackCone F G)
    [P.IsBilimit]
    (hG : Hom.LocallyEssentiallySurjective G)
    (hP : (Hom.toBasedFunctor P.snd).Faithful) :
    (Hom.toBasedFunctor F).Faithful := sorry

end PseudoPullback

end StackOver.Groupoids

end CategoryTheory
