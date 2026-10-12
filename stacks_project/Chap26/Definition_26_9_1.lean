/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 26.9.1: schemes and their morphisms are the canonical mathlib category of schemes. -/
@[stacks 01IJ] #check Scheme
#check Scheme.forgetToLocallyRingedSpace
#check Scheme.Hom.toLRSHom
