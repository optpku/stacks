/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
import StacksCheckRecall

universe u

/- Definition 47.15.1: a dualizing complex over a Noetherian commutative ring has finite
injective dimension, finite cohomology modules in every degree, and invertible canonical
homothety from the tensor unit to its derived endomorphism object. -/
@[stacks 0A7B] #check (@CategoryTheory.DerivedCategory.IsDualizingComplex :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
    [CategoryTheory.MonoidalCategory
      (_root_.DerivedCategory (ModuleCat.{u} A))] →
    _root_.DerivedCategory (ModuleCat.{u} A) →
    CategoryTheory.MonoidalClosed
      (_root_.DerivedCategory (ModuleCat.{u} A)) → Prop)
