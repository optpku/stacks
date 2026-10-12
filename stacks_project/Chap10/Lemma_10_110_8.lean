/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GlobalDimension.Regular
import StacksCheckRecall

/-!
# Finite Global Dimension and Regular Rings

@stack 00OE
-/

@[expose] public section

@[stacks 00OE "finite-global-dimension characterization"]
#check @IsFiniteGlobalDimensionRing.exists_globalDimension_eq_iff

@[stacks 00OE "finite global dimension implies regularity"]
#check @IsFiniteGlobalDimensionRing.isRegularRing

@[stacks 00OE "Krull dimension equals global dimension"]
#check @IsFiniteGlobalDimensionRing.ringKrullDim_eq_globalDimension

@[stacks 00OE "maximal-local criterion"]
#check @IsFiniteGlobalDimensionRing.exists_globalDimension_eq_of_regularAtMaximal

@[stacks 00OE "regular-ring converse"]
#check @IsRegularRing.exists_globalDimension_eq
