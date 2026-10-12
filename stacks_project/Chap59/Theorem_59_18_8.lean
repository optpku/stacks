/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Derived
import StacksCheckRecall

@[expose] public section

universe w v u

/- Theorem 59.18.8: for every nonnegative degree, fixed-target Cech cohomology is naturally
isomorphic to the corresponding right-derived functor of degree-zero cohomology. -/
@[stacks 03OS] #check
  (CategoryTheory.Cech.FixedTarget.cohomologyFunctor_isIsomorphic_rightDerived :
    ∀ {C : Type u} [CategoryTheory.Category.{v} C] {U : C} {ι : Type w}
      (family : ι → CategoryTheory.Over U)
      [CategoryTheory.HasIteratedFiberProducts family]
      [CategoryTheory.Limits.HasProducts.{w} AddCommGrpCat.{max u v}] (p : ℕ),
      CategoryTheory.IsIsomorphic
        ((CategoryTheory.Cech.FixedTarget.cohomologyFunctor family p).obj)
        (((CategoryTheory.Cech.FixedTarget.cohomologyFunctor family 0).obj).rightDerived p))
