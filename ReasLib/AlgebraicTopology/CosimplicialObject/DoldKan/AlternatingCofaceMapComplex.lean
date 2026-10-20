/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019I

# The alternating coface map complex

This lightweight leaf records preservation of finite limits and colimits by alternating cofaces,
then packages the functor through Mathlib's canonical `ExactFunctor.of` constructor. It is
independent of normalized cochains and the cosimplicial Dold--Kan decomposition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe w w' u v

namespace AlgebraicTopology.alternatingCofaceMapComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- Degreewise evaluation of the alternating coface map complex agrees with evaluation of
cosimplicial objects at the corresponding simplex. -/
@[stacks 019I "alternating coface map complex degreewise evaluation"]
def evalIso (n : ℕ) :
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙
        HomologicalComplex.eval A (ComplexShape.up ℕ) n ≅
      (evaluation SimplexCategory A).obj ⦋n⦌ :=
  Iso.refl _

/-- The alternating coface map complex preserves limits of any shape that exists in the
coefficient category. -/
@[stacks 019I "alternating coface map complex preserves limits"]
instance preservesLimitsOfShape (J : Type w) [Category.{w'} J] [HasLimitsOfShape J A] :
    PreservesLimitsOfShape J (AlgebraicTopology.alternatingCofaceMapComplex A) := sorry

/-- The alternating coface map complex preserves colimits of any shape that exists in the
coefficient category. -/
@[stacks 019I "alternating coface map complex preserves colimits"]
instance preservesColimitsOfShape (J : Type w) [Category.{w'} J] [HasColimitsOfShape J A] :
    PreservesColimitsOfShape J (AlgebraicTopology.alternatingCofaceMapComplex A) := sorry

/-- The alternating coface map complex preserves finite limits whenever the coefficient category
has finite limits. -/
@[stacks 019I "alternating coface map complex preserves finite limits"]
instance preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (AlgebraicTopology.alternatingCofaceMapComplex A) := sorry

/-- The alternating coface map complex preserves finite colimits whenever the coefficient category
has finite colimits. -/
@[stacks 019I "alternating coface map complex preserves finite colimits"]
instance preservesFiniteColimits [HasFiniteColimits A] :
    PreservesFiniteColimits (AlgebraicTopology.alternatingCofaceMapComplex A) := sorry

/-- The alternating coface map complex, bundled as an exact functor. -/
@[stacks 019I "bundled exact alternating coface map complex"]
noncomputable def exactFunctor [HasFiniteLimits A] [HasFiniteColimits A] :
    CosimplicialObject A ⥤ₑ CochainComplex A ℕ :=
  ExactFunctor.of (AlgebraicTopology.alternatingCofaceMapComplex A)

end AlgebraicTopology.alternatingCofaceMapComplex
