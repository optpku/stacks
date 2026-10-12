/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Counterexamples.Specialization
import StacksCheckRecall

@[expose] public section

/- Exercise 111.36.4 (1): the closed point `(2)` of `Spec ℤ` is a specialization of the generic
point. -/
@[stacks 029R] #check (AlgebraicGeometry.DTwoModule.specializes :
  Specializes AlgebraicGeometry.DTwoModule.generic AlgebraicGeometry.DTwoModule.two)

/- Exercise 111.36.4 (2): the stalk of `moduleSheaf` at the generic point is nonzero. -/
@[stacks 029R] #check (AlgebraicGeometry.DTwoModule.stalk_generic_not_isZero :
  ¬ CategoryTheory.Limits.IsZero
    (AlgebraicGeometry.RingedSpace.stalkModuleCat AlgebraicGeometry.DTwoModule.moduleSheaf
      AlgebraicGeometry.DTwoModule.generic))

/- Exercise 111.36.4 (3): the stalk of `moduleSheaf` at the closed point `(2)` is zero. -/
@[stacks 029R] #check (AlgebraicGeometry.DTwoModule.stalk_two_isZero :
  CategoryTheory.Limits.IsZero
    (AlgebraicGeometry.RingedSpace.stalkModuleCat AlgebraicGeometry.DTwoModule.moduleSheaf
      AlgebraicGeometry.DTwoModule.two))
