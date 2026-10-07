module

public import ReasLib.RingTheory.KrullDimension.Integral.Zero
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import StacksCheckRecall

/-!
# Integral Algebras over Fields

@stack 00GS
-/

@[expose] public section

@[stacks 00GS "(1), finite-dimensional domain"]
#check @fieldOfFiniteDimensional

@[stacks 00GS "(2), integral domain"]
#check @isField_of_isIntegral_of_isField'

@[stacks 00GS "map-level zero-dimensional integral extension"]
#check @RingHom.IsIntegral.krullDimLE_zero

@[stacks 00GS "algebra-map zero-dimensional integral extension"]
#check @Algebra.IsIntegral.krullDimLE_zero

@[stacks 00GS "(3), prime ideals are maximal"]
#check @Ideal.IsPrime.isMaximal_of_isIntegral
