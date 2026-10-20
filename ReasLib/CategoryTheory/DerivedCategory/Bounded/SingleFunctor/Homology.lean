module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Homology of Bounded Derived Single Objects

This module computes the homology of canonical single objects in each
boundedness variant.  It supplies diagonal recovery and off-diagonal
vanishing APIs for the bounded-above and bounded variants.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace DerivedCategory.Plus.singleFunctor

/-- Cohomology in degree `n` recovers an object concentrated in degree `n`
inside `D⁺(C)`. -/
@[stacks 015A]
noncomputable def compHomologyIso (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ⋙
        DerivedCategory.Plus.homologyFunctor C n ≅
      𝟭 C :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (DerivedCategory.Plus.singleFunctorιIso C n)
      (DerivedCategory.homologyFunctor C n) ≪≫
    DerivedCategory.singleFunctorCompHomologyFunctorIso C n

end DerivedCategory.Plus.singleFunctor

namespace DerivedCategory.Minus.singleFunctor

/-- Cohomology in degree `n` recovers an object concentrated in degree `n`
inside `D⁻(C)`. -/
@[stacks 015A]
noncomputable def compHomologyIso (n : ℤ) :
    DerivedCategory.Minus.singleFunctor C n ⋙
        DerivedCategory.Minus.homologyFunctor C n ≅
      𝟭 C :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (DerivedCategory.Minus.singleFunctorιIso C n)
      (DerivedCategory.homologyFunctor C n) ≪≫
    DerivedCategory.singleFunctorCompHomologyFunctorIso C n

/-- The cohomology of a single object in `D⁻(C)` vanishes outside its
concentrated degree. -/
@[stacks 015A]
theorem isZero_homology_of_ne (n : ℤ) (X : C) (i : ℤ) (hi : i ≠ n) :
    IsZero
      ((DerivedCategory.Minus.homologyFunctor C i).obj
        ((DerivedCategory.Minus.singleFunctor C n).obj X)) := sorry

end DerivedCategory.Minus.singleFunctor

namespace DerivedCategory.Bounded.singleFunctor

/-- Cohomology in degree `n` recovers an object concentrated in degree `n`
inside `Dᵇ(C)`. -/
@[stacks 0FCP]
noncomputable def compHomologyIso (n : ℤ) :
    DerivedCategory.Bounded.singleFunctor C n ⋙
        DerivedCategory.Bounded.homologyFunctor C n ≅
      𝟭 C :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (DerivedCategory.Bounded.singleFunctorιIso C n)
      (DerivedCategory.homologyFunctor C n) ≪≫
    DerivedCategory.singleFunctorCompHomologyFunctorIso C n

/-- The cohomology of a single object in `Dᵇ(C)` vanishes outside its
concentrated degree. -/
@[stacks 0FCP]
theorem isZero_homology_of_ne (n : ℤ) (X : C) (i : ℤ) (hi : i ≠ n) :
    IsZero
      ((DerivedCategory.Bounded.homologyFunctor C i).obj
        ((DerivedCategory.Bounded.singleFunctor C n).obj X)) := sorry

end DerivedCategory.Bounded.singleFunctor

end CategoryTheory
