/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.BifunctorAssociator
import StacksCheckRecall

@[expose] public section

open ComplexShape

/- Remark 12.18.4 [08BI]: the two iterated totalizations of a triple complex are related by
mathlib's canonical bifunctor-totalization associator. -/
@[stacks 08BI]
#check @HomologicalComplex.mapBifunctorAssociator

/- For three cochain directions the required shape associativity is canonical. -/
#check (inferInstance :
  ComplexShape.Associative (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ))
