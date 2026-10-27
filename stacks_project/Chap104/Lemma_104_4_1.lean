/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedConstantInteger
public import stacks_project.Chap104.Lemma_104_3_1_Abelian
import StacksCheckRecall

/-!
# Lemma 104.4.1

On an algebraic stack, derived abelian lower shriek of the constant integer
sheaf along the lisse-étale and flat-fppf inclusions is the constant integer
sheaf in the unbounded derived category.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u z

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/- Lemma 104.4.1: the lisse-étale derived comparison for the constant integer sheaf. -/
@[stacks 0H0Z] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriekDerived_constantInteger.instIsIso X :
    IsIso (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriekDerived_constantInteger.{u, z} X))

/- Lemma 104.4.1: the flat-fppf derived comparison for the constant integer sheaf. -/
@[stacks 0H0Z] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriekDerived_constantInteger.instIsIso X :
    IsIso (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriekDerived_constantInteger.{u, z} X))
