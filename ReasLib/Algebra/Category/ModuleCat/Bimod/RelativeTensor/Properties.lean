/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor.ModuleFunctor
public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor.Adjunction

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

universe u v

namespace Module.Bimodule.RelativeTensor.tensorModuleFunctor

variable {R A B : Type u} (K : Type u)
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]

/-- Tensoring right `A`-modules with a fixed bimodule `K` is `R`-linear. -/
instance linear :
    Functor.Linear R (tensorModuleFunctor (R := R) (A := A) (B := B) K) := sorry

/-- Tensoring right `A`-modules with a fixed bimodule `K` is right exact. -/
theorem rightExact :
    rightExactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ)
      (tensorModuleFunctor (R := R) (A := A) (B := B) K) := sorry

/-- Tensoring right `A`-modules with a fixed bimodule `K` preserves arbitrary coproducts. -/
instance preservesCoproducts (J : Type v) :
    PreservesColimitsOfShape (Discrete J)
      (tensorModuleFunctor (R := R) (A := A) (B := B) K) := sorry

/-- Tensoring right `A`-modules with a fixed bimodule `K` preserves all colimits. -/
instance preservesColimits :
    PreservesColimits (tensorModuleFunctor (R := R) (A := A) (B := B) K) := sorry

/-- Tensoring right `A`-modules with a fixed bimodule `K` has a right adjoint. -/
instance isLeftAdjoint :
    Functor.IsLeftAdjoint (tensorModuleFunctor (R := R) (A := A) (B := B) K) := sorry

end Module.Bimodule.RelativeTensor.tensorModuleFunctor
