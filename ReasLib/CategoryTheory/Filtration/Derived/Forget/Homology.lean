/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Forget
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology after forgetting a finite filtration

This leaf compares homology after the direct homotopy-to-derived forgetful functor with the
homology functor already defined on finite filtered homotopy complexes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived.Forget.Homology

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- Homology after `Forget.homotopy` agrees with homology after forgetting the filtration at the
homotopy level. -/
@[stacks 05S3 "finite filtered forgetful homology comparison"]
noncomputable def factorIso (n : ℤ) :
    Forget.homotopy C ⋙ DerivedCategory.homologyFunctor C n ≅ Finite.Forget.homology C n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactorsh C n)

/-- The forward component of `factorIso` is the standard derived-homology comparison evaluated
after the finite filtered forgetful homotopy functor. -/
@[stacks 05S3 "finite filtered forgetful homology comparison", simp]
theorem factorIso_hom_app
    (n : ℤ) (K : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :
    (factorIso C n).hom.app K =
      (DerivedCategory.homologyFunctorFactorsh C n).hom.app
        ((Finite.Forget.homotopy C).obj K) := sorry

/-- The inverse component of `factorIso` is the inverse standard derived-homology comparison
evaluated after the finite filtered forgetful homotopy functor. -/
@[stacks 05S3 "finite filtered forgetful homology comparison", simp]
theorem factorIso_inv_app
    (n : ℤ) (K : HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)) :
    (factorIso C n).inv.app K =
      (DerivedCategory.homologyFunctorFactorsh C n).inv.app
        ((Finite.Forget.homotopy C).obj K) := sorry

end CategoryTheory.FilteredObject.FiniteDerived.Forget.Homology
