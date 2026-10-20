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
# Homology after a finite associated-graded piece

This leaf identifies homology after the direct derived graded-piece functor with the existing
two-stage graded-piece homology functor on finite filtered homotopy complexes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.Homology

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- Homology after the direct derived `p`-th graded-piece functor agrees with the existing
graded-piece homology functor on finite filtered homotopy complexes. -/
@[stacks 05S3 "finite filtered graded-piece homology comparison"]
noncomputable def factorIso (p n : ℤ) :
    GradedPiece.homotopy C p ⋙ DerivedCategory.homologyFunctor C n ≅
      Finite.GradedPiece.homology C p n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactorsh C n)

/-- The forward component of `factorIso` is the standard derived-homology comparison evaluated
after the direct `p`-th graded-piece homotopy functor. -/
@[stacks 05S3 "finite filtered graded-piece homology comparison", simp]
theorem factorIso_hom_app
    (p n : ℤ) (K : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :
    (factorIso C p n).hom.app K =
      (DerivedCategory.homologyFunctorFactorsh C n).hom.app
        ((Functor.Homotopy.comp
          (FilteredObject.Finite.AssociatedGraded.functor C) (GradedObject.eval p)).obj K) := sorry

/-- The inverse component of `factorIso` is the inverse standard derived-homology comparison
evaluated after the direct `p`-th graded-piece homotopy functor. -/
@[stacks 05S3 "finite filtered graded-piece homology comparison", simp]
theorem factorIso_inv_app
    (p n : ℤ) (K : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :
    (factorIso C p n).inv.app K =
      (DerivedCategory.homologyFunctorFactorsh C n).inv.app
        ((Functor.Homotopy.comp
          (FilteredObject.Finite.AssociatedGraded.functor C) (GradedObject.eval p)).obj K) := sorry

end CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.Homology
