/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Injective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.12

The bounded-below filtered-injective model, its equivalence certificate, and the resulting
equivalence are owned by a common namespace in ReasLib. A supplied strict resolution also gives
a concrete comparison with its filtered-injective homotopy object.
-/

namespace CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective

universe v u

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
  [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

section Resolutions

variable {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
variable (R : CochainComplex.FilteredInjectivePlus.Resolution K)

/- The source proof uses the filtered-injective homotopy object carried by a strict resolution. -/
#check (resolutionObj R :
  HomotopyCategory.Plus (FilteredObject.Finite.FilteredInjective.category C))

/- The resolution comparison is a right resolution for the filtered-injective inclusion. -/
#check (rightResolution R :
  (localizer C).RightResolution
    ((HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C)).obj K))

/- In the derived category, the comparison has its explicit formal inverse. -/
#check (resolutionIso h_inverts R :
  (FilteredObject.FiniteDerived.Plus.Quotient.functor C h_inverts).obj
      ((HomotopyCategory.Plus.quotient (FilteredObject.Finite.category C)).obj K) ≅
    (functor C h_inverts).obj (resolutionObj R))

end Resolutions

variable [EnoughInjectives C]

/- Lemma 13.26.12 (`015Q`): bounded-below complexes of finite filtered-injective objects compute
the bounded-below finite filtered derived category. -/
@[stacks 015Q] #check
  (CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective.isEquivalence C h_inverts :
    Functor.IsEquivalence (functor C h_inverts))

/- The canonical functor whose equivalence is asserted by the lemma. -/
#check (functor C h_inverts :
  HomotopyCategory.Plus (FilteredObject.Finite.FilteredInjective.category C) ⥤
    FilteredObject.FiniteDerived.Plus.Category C h_inverts)

/- The proposition-level equivalence certificate used by downstream derived constructions. -/
#check (IsEquivalence C h_inverts : Prop)

variable (h_equiv : IsEquivalence C h_inverts)

/- The bundled equivalence constructed from a supplied model-equivalence certificate. -/
#check (equivalenceOfEnoughInjectives C h_inverts h_equiv :
  HomotopyCategory.Plus (FilteredObject.Finite.FilteredInjective.category C) ≌
    FilteredObject.FiniteDerived.Plus.Category C h_inverts)

end CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective
