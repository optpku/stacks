/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Injective
import ReasLib.CategoryTheory.Filtration.Derived.Projective
import ReasLib.CategoryTheory.Filtration.Derived.RightExact
import StacksCheckRecall

open CategoryTheory

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived
variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

section
variable [EnoughInjectives C]

/- Lemma 64.7.2 (1): if C has enough injectives, then the bounded-below
   filtered-injective model is the filtered derived category. -/
@[stacks 03TB] #check (CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective.isEquivalence C h_inverts :
  Functor.IsEquivalence
    (CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective.functor C h_inverts))

end

section
variable [EnoughProjectives C]

/- Lemma 64.7.2 (2): if C has enough projectives, then the bounded-above
   filtered-projective model is the filtered derived category. -/
@[stacks 03TB] #check (CategoryTheory.FilteredObject.FiniteDerived.Minus.FilteredProjective.isEquivalence C h_inverts :
  Functor.IsEquivalence
    (CategoryTheory.FilteredObject.FiniteDerived.Minus.FilteredProjective.functor C h_inverts))
end

end CategoryTheory.FilteredObject.FiniteDerived
