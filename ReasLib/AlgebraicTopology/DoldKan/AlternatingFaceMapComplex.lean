/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicTopology.DoldKan.Notations
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The alternating face map complex

This module records preservation of finite limits and colimits by the alternating face map
complex under the standard ambient assumptions. It then packages the functor through Mathlib's
canonical `ExactFunctor.of` constructor. Its notation is Mathlib's scoped notation `K[X]`.

@stack 0195
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe w w' v u

namespace AlgebraicTopology.alternatingFaceMapComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- Degreewise evaluation of the alternating face map complex agrees with evaluation of
simplicial objects at the corresponding simplex. -/
@[stacks 0195 "alternating face map complex degreewise evaluation"]
def evalIso (n : ℕ) :
    AlgebraicTopology.alternatingFaceMapComplex A ⋙
        HomologicalComplex.eval A (ComplexShape.down ℕ) n ≅
      (evaluation SimplexCategoryᵒᵖ A).obj (Opposite.op ⦋n⦌) :=
  Iso.refl _

/-- The alternating face map complex preserves limits of any shape that exists in the
coefficient category. -/
@[stacks 0195 "alternating face map complex preserves limits"]
instance preservesLimitsOfShape (J : Type w) [Category.{w'} J] [HasLimitsOfShape J A] :
    PreservesLimitsOfShape J (AlgebraicTopology.alternatingFaceMapComplex A) := sorry

/-- The alternating face map complex preserves colimits of any shape that exists in the
coefficient category. -/
@[stacks 0195 "alternating face map complex preserves colimits"]
instance preservesColimitsOfShape (J : Type w) [Category.{w'} J] [HasColimitsOfShape J A] :
    PreservesColimitsOfShape J (AlgebraicTopology.alternatingFaceMapComplex A) := sorry

/-- The alternating face map complex preserves finite limits whenever the coefficient category
has finite limits. -/
@[stacks 0195 "alternating face map complex preserves finite limits"]
instance preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (AlgebraicTopology.alternatingFaceMapComplex A) := sorry

/-- The alternating face map complex preserves finite colimits whenever the coefficient category
has finite colimits. -/
@[stacks 0195 "alternating face map complex preserves finite colimits"]
instance preservesFiniteColimits [HasFiniteColimits A] :
    PreservesFiniteColimits (AlgebraicTopology.alternatingFaceMapComplex A) := sorry

/-- The alternating face map complex, bundled as an exact functor. -/
@[stacks 0195 "bundled exact alternating face map complex"]
noncomputable def exactFunctor [HasFiniteLimits A] [HasFiniteColimits A] :
    SimplicialObject A ⥤ₑ ChainComplex A ℕ :=
  ExactFunctor.of (AlgebraicTopology.alternatingFaceMapComplex A)

end AlgebraicTopology.alternatingFaceMapComplex
