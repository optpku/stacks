module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.InverseSystem.Sequential

/-!
# Derived categories of sequential abelian-group systems

@stack 08U4

This leaf supplies the standard derived-category model for sequential inverse
systems of additive commutative groups. It is specific to `AddCommGrpCat`;
generic functor categories continue to receive a chosen derived-category model
from their callers.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.SequentialInverseSystem

/-- The standard derived-category structure on sequential inverse systems of additive
commutative groups. -/
@[stacks 08U4 "derived category of sequential abelian-group systems"]
instance addCommGrpCatHasDerivedCategory :
    HasDerivedCategory (SequentialInverseSystem AddCommGrpCat.{u}) :=
  HasDerivedCategory.standard (SequentialInverseSystem AddCommGrpCat.{u})

end CategoryTheory.SequentialInverseSystem
