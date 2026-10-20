/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral.FiniteComponents
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Finite irreducible components of integral algebraic spaces

An integral algebraic space has finitely many irreducible components.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- An integral algebraic space has finitely many irreducible components. -/
#check (AlgebraicGeometry.AlgebraicSpace.instHasFiniteIrreducibleComponents_of_isIntegral :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsIntegral X],
    HasFiniteIrreducibleComponents X)

end AlgebraicGeometry.AlgebraicSpace
