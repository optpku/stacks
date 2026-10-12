/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.TotalLeftDerived
import StacksCheckRecall

@[expose] public section

/-
Definition 24.28.2 (tag 0FTG): derived tensoring is the total left-derived functor of the
fixed-bimodule tensor source.  The first check is the reusable algebraic DG owner.  Derived
pullback has the same two-stage `Functor.Homotopy.LeftDerived.total` shape, but its ringed-site
pullback-and-tensor source functor is not yet constructed in ReasLib.
-/
@[stacks 0FTG "derived tensor product of DG modules"]
#check @DifferentialGradedBimodule.Tensor.derivedFunctor

@[stacks 0FTG "total left-derived functor underlying derived pullback"]
#check @CategoryTheory.Functor.Homotopy.LeftDerived.total

#check @DifferentialGradedBimodule.Tensor.derivedCounit
#check @CategoryTheory.Functor.Homotopy.LeftDerived.counit
