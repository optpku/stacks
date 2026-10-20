/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology after finite associated graded

This leaf identifies derived homology after the direct associated-graded homotopy functor with
the existing homology functor on finite filtered homotopy complexes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.Homology

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]

/-- Homology after finite derived associated graded agrees with associated-graded homology on
finite filtered homotopy complexes. -/
@[stacks 05S3 "finite filtered associated-graded homology comparison"]
noncomputable def factorIso (n : ℤ) :
    AssociatedGraded.homotopy C ⋙
        DerivedCategory.homologyFunctor (GradedObject ℤ C) n ≅
      Finite.AssociatedGraded.homology C n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (DerivedCategory.homologyFunctorFactorsh (GradedObject ℤ C) n)

/-- The forward component of `factorIso` is the standard derived-homology comparison evaluated
after the finite associated-graded homotopy functor. -/
@[stacks 05S3 "finite filtered associated-graded homology comparison", simp]
theorem factorIso_hom_app
    (n : ℤ) (K : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :
    (factorIso C n).hom.app K =
      (DerivedCategory.homologyFunctorFactorsh (GradedObject ℤ C) n).hom.app
        ((Finite.AssociatedGraded.homotopy C).obj K) := sorry

/-- The inverse component of `factorIso` is the inverse standard derived-homology comparison
evaluated after the finite associated-graded homotopy functor. -/
@[stacks 05S3 "finite filtered associated-graded homology comparison", simp]
theorem factorIso_inv_app
    (n : ℤ) (K : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :
    (factorIso C n).inv.app K =
      (DerivedCategory.homologyFunctorFactorsh (GradedObject ℤ C) n).inv.app
        ((Finite.AssociatedGraded.homotopy C).obj K) := sorry

end CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.Homology
