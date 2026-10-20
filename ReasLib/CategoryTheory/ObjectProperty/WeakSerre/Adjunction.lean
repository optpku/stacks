/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.Map
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weak Serre classes transported across an adjunction

This leaf isolates the categorical core of topology-comparison arguments.  The source property
is already weak Serre, the left adjoint identifies the selected full subcategories, and exactness
of the two ambient routes transfers the four-out-of-five condition to the target property.
-/

open CategoryTheory CategoryTheory.Limits

universe vC vD uC uD

namespace CategoryTheory.ObjectProperty.IsWeakSerreClass

variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]

/-- A weak Serre class transfers across an adjunction when the left adjoint restricts to an
equivalence, the left adjoint is exact, the right adjoint is exact on the selected source
subcategory, the essential image of the source property lies in the target property, and the
adjunction unit is invertible on the selected target objects. -/
@[stacks 07A8 "weak-Serre transfer across an adjunction"]
theorem of_adjoint_restriction
    (P : ObjectProperty C) (Q : ObjectProperty D) [IsWeakSerreClass P]
    (L : D ⥤ C) (R : C ⥤ D) (adj : L ⊣ R)
    (hL : Q ≤ P.inverseImage L)
    [Functor.IsEquivalence (FullSubcategory.restrict L hL)]
    (hR : P.map R ≤ Q)
    (hLExact : exactFunctor D C L)
    (hRExact : exactFunctor P.FullSubcategory D (P.ι ⋙ R))
    (hunit : ∀ X : Q.FullSubcategory, IsIso (adj.unit.app X.obj)) :
    IsWeakSerreClass Q := sorry

/-- Variant of `of_adjoint_restriction` using strict objectwise membership for the right
adjoint.  Repleteness of the target property upgrades strict membership to the essential-image
inclusion required by the canonical theorem. -/
@[stacks 07A8 "weak-Serre transfer from objectwise right-adjoint membership"]
theorem of_adjoint_restriction_of_inverseImage
    (P : ObjectProperty C) (Q : ObjectProperty D) [IsWeakSerreClass P]
    [Q.IsClosedUnderIsomorphisms]
    (L : D ⥤ C) (R : C ⥤ D) (adj : L ⊣ R)
    (hL : Q ≤ P.inverseImage L)
    [Functor.IsEquivalence (FullSubcategory.restrict L hL)]
    (hR : P ≤ Q.inverseImage R)
    (hLExact : exactFunctor D C L)
    (hRExact : exactFunctor P.FullSubcategory D (P.ι ⋙ R))
    (hunit : ∀ X : Q.FullSubcategory, IsIso (adj.unit.app X.obj)) :
    IsWeakSerreClass Q := sorry

end CategoryTheory.ObjectProperty.IsWeakSerreClass

end
