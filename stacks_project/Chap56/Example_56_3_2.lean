/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor.Properties
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v

namespace Module.Bimodule.RelativeTensor

variable {R A B : Type u} (K : Type u)
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]

/- Example 56.3.2 (1): the functor `M ↦ M ⊗[A] K` from right `A`-modules to
right `B`-modules is `R`-linear. -/
@[stacks 0GNT] #check
  (Module.Bimodule.RelativeTensor.tensorModuleFunctor.linear (R := R) (A := A) (B := B) K :
    Functor.Linear R (tensorModuleFunctor (R := R) (A := A) (B := B) K))

/- Example 56.3.2 (2): the functor `M ↦ M ⊗[A] K` from right `A`-modules to
right `B`-modules is right exact. -/
@[stacks 0GNT] #check
  (Module.Bimodule.RelativeTensor.tensorModuleFunctor.rightExact (R := R) (A := A) (B := B) K :
    rightExactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ)
      (tensorModuleFunctor (R := R) (A := A) (B := B) K))

/- Example 56.3.2 (3): the functor `M ↦ M ⊗[A] K` from right `A`-modules to
right `B`-modules preserves arbitrary direct sums. -/
@[stacks 0GNT] #check
  (Module.Bimodule.RelativeTensor.tensorModuleFunctor.preservesCoproducts
      (R := R) (A := A) (B := B) K :
    ∀ J : Type v,
    PreservesColimitsOfShape (Discrete J)
      (tensorModuleFunctor (R := R) (A := A) (B := B) K))

/- Example 56.3.2 (4): the functor `M ↦ M ⊗[A] K` from right `A`-modules to
right `B`-modules preserves all colimits. -/
@[stacks 0GNT] #check
  (Module.Bimodule.RelativeTensor.tensorModuleFunctor.preservesColimits
      (R := R) (A := A) (B := B) K :
    PreservesColimits (tensorModuleFunctor (R := R) (A := A) (B := B) K))

/- Example 56.3.2 (5): the functor `M ↦ M ⊗[A] K` from right `A`-modules to
right `B`-modules has a right adjoint. -/
@[stacks 0GNT] #check
  (Module.Bimodule.RelativeTensor.tensorModuleFunctor.isLeftAdjoint
      (R := R) (A := A) (B := B) K :
    Functor.IsLeftAdjoint (tensorModuleFunctor (R := R) (A := A) (B := B) K))

end Module.Bimodule.RelativeTensor
