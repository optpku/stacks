/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Lemma 20.55.4 (0GT6): for a generator `f` of the stalk of a regular
ideal, the stalk of the sheaf-level Berthelot-Ogus eta complex agrees with
the integer-indexed local eta complex at `f`. -/

@[stacks 0GT6]
#check @IdealSheaf.Eta.Stalk.termwiseRegular

@[stacks 0GT6 "stalkwise eta domain"]
#check @IdealSheaf.Eta.Stalk.domainFunctor

@[stacks 0GT6 "degreewise stalk comparison"]
#check @IdealSheaf.Eta.Stalk.objStalk_isomorphic

@[stacks 0GT6 "complex stalk comparison"]
#check @IdealSheaf.Eta.Stalk.complex_isomorphic

@[stacks 0GT6 "natural stalk comparison"]
#check @IdealSheaf.Eta.Stalk.functor_isomorphic

@[stacks 0GT6 "stalk generator"]
#check @IdealSheaf.IsStalkGenerator

