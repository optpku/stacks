/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Category
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Tangent
public import ReasLib.CategoryTheory.Functor.Exactness.ShortExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/-- The tangent functor of an injective module-valued functor is right exact over every
fixed algebra. -/
theorem tangentRightExact_of_injective {A : CommRingCat.{u}}
    (I : ModuleValuedFunctor.{u, u} A) (hI : IsInjective I) (B : Under A) :
    rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (I.tangent.fixedBase B) := sorry

/-- Applying the tangent functor of an injective module-valued functor to a short exact
complex gives an exact composable pair whose second map is epic. -/
theorem tangent_exact_and_epi_of_injective {A : CommRingCat.{u}}
    (I : ModuleValuedFunctor.{u, u} A) (hI : IsInjective I) (B : Under A)
    (S : ShortComplex (ModuleCat.{u} B.right)) (hS : S.ShortExact) :
    (ComposableArrows.mk₂ ((I.tangent.fixedBase B).map S.f)
      ((I.tangent.fixedBase B).map S.g)).Exact ∧
      Epi ((I.tangent.fixedBase B).map S.g) := sorry

end ModuleValuedFunctor
